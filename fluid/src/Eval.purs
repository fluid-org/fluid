module Eval where

import Prelude hiding (absurd, apply)

import Bind (Name, dottedName, prefixOf, varAnon, varThis)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldM, foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (head, last, snoc, unsnoc)
import Data.List.NonEmpty (fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd, uncurry)
import Classes (ClassTable, ancestors, arity, askClasses, checkArity, fieldNames)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Exception (Error)
import Expr (Branch(..), Def(..), Expr(..), Import(..), Module(..), Pattern(..), Qualifier(..), Stmt(..), assigns, fv)
import File (withClasses)
import DepGraph (DepGraph, Support, VisibleGraph, attachDoc, bindings, construct, controlDep, materialise, reuse, dataDep, tupling)
import Lattice (DepKind, Raw)
import Literal (Literal(..), eqLiteral)
import Module.Defs (ModuleName, builtins, submods)
import Operator (binopSymbol, unopSymbol)
import Path (Position, Step(..), Vertex, followedBy, ε)
import Pretty (prettyP)
import Types (Type(..)) as T
import Primitive (applyBinop, boolean, dropα, int, string, typeMismatch, unopFun, unpack, unpack')
import Types.Defs (cComplex)
import Util (type (×), absurd, check, definitely', error, isEmpty, orElse, orThrow, quoted, singleton, throw, withMsg, (×))
import Util.Map (get, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..), value) as V
import Val (class HasModuleStore, class MonadEval, class MonadProgram, ModuleState(..), loadedEnv, DictRep(..), Env(..), EnvAt, ForeignOp(..), ForeignOp'(..), GVal, Label, MatrixRep(..), ValAt, Val(..), elementCount, forDefs, modifyModuleStore, moduleStore, child, valAt)
import Val.Dependence (applyDepFun, bindingAt, bindingsAt, childAt, concatOf, deliver, dictionary, elementAt, elementsAt, elementStep, explode, lengthPositions, newEnv, newExtendEnv, newValue, positionsIn, reuseAt, sequenceOf)

-- Returned value, or environment of bindings introduced and any new control positions
data Result = Returns ValAt | Assigns EnvAt (Set Position)

asReturns :: Result -> ValAt
asReturns (Returns pv) = pv
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: Result -> EnvAt × Set Position
asAssigns (Assigns pρ ps) = pρ × ps
asAssigns (Returns _) = error "Assigns expected"

-- Environment ρ at vertex b extended with bindings ρ', and vertex of the extended environment
extendEnv
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Semiring s
   => Dict (Raw Val)
   -> Vertex
   -> Dict (GVal s)
   -> m (Dict (Raw Val) × Vertex)
extendEnv ρ b ρ'
   | isEmpty ρ' = pure (ρ × b)
   | otherwise = newExtendEnv ((b × ε) × Env ρ) ρ' <#> \((b' × _) × Env ρ'') -> ρ'' × b'

controlledBy :: Set Position -> Set Position -> Set Position
controlledBy qs ps = if isEmpty qs then ps else qs

-- Variables bound if the pattern matches the value at a position; also each inspected position
matches :: forall s. Semiring s => ClassTable -> ValAt -> Pattern -> Maybe (Dict (GVal s)) × List Position
matches _ pv (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x (reuseAt pv)) × Nil
matches _ _ PWild = Just empty × Nil
matches classes pv (PAs p x) = first (map (_ `unionWith_never` maplet x (reuseAt pv))) (matches classes pv p)
matches classes pv@(q × Val _ v) p = second (q : _) case v, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Obj c' xvs, PConstr c ps Nil
      | c `elem` ancestors classes c' ->
           matchesMany classes ((\(x × _) -> childAt (Field x) pv) <$> take (length ps) xvs) ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs $> (x × childAt (DictVal x) pv × p')) xps of
         Just kvs -> second ((kvs <#> \(x × _) -> fst (childAt (DictKey x) pv)) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps -> matchesMany classes (elementsAt pv) ps
   V.Tuple vs, PTuple ps | A.length vs == length ps -> matchesMany classes (elementsAt pv) ps
   _, _ -> Nothing × Nil

matchesMany :: forall s. Semiring s => ClassTable -> List ValAt -> List Pattern -> Maybe (Dict (GVal s)) × List Position
matchesMany _ Nil Nil = Just empty × Nil
matchesMany classes (pv : pvs) (p : ps) = case matches classes pv p of
   Nothing × qs -> Nothing × qs
   Just ρ × qs -> case matchesMany classes pvs ps of
      Nothing × qs' -> Nothing × (qs <> qs')
      Just ρ' × qs' -> Just (ρ `unionWith_never` ρ') × (qs <> qs')
matchesMany _ _ _ = error absurd

-- Bindings of the first matching case; also every position inspected in trying the cases
dispatch :: forall s b. Semiring s => ClassTable -> List (Pattern × b) -> ValAt -> Maybe (Dict (GVal s) × b) × Set Position
dispatch classes cases pv = second Set.fromFoldable (go cases)
   where
   go :: List (Pattern × b) -> Maybe (Dict (GVal s) × b) × List Position
   go Nil = Nothing × Nil
   go ((p × b) : cases') = case matches classes pv p of
      Just ρ × qs -> Just (ρ × b) × qs
      Nothing × qs -> second (qs <> _) (go cases')

-- dispatch on a single pattern, which must match.
destructure :: forall m s. MonadError Error m => Semiring s => ClassTable -> Pattern -> ValAt -> m (Dict (GVal s) × Set Position)
destructure classes p pv = case dispatch classes (singleton (p × unit)) pv of
   Just (ρ × _) × qs -> pure (ρ × qs)
   Nothing × _ -> throw ("Pattern mismatch: " <> prettyP (snd pv) <> " does not match " <> prettyP p)

object :: forall s. Semiring s => ClassTable -> Support (Set Position) s -> Name -> List (GVal s) -> GVal s
object classes support c vs = Val unit (V.Obj c (zip (fieldNames classes c) (fst <$> vs))) ×
   construct support (Map.fromFoldable (zip (Field <$> fieldNames classes c) (snd <$> vs)))

-- Closure which captures ρ from the environment at position p; root depends on control positions ps
closure :: forall s. Semiring s => Set Position -> Position -> Dict (Raw Val) -> Dict Def -> Def -> GVal s
closure ps p ρ ds d = Val unit (V.Fun (V.Closure (Env ρ) ds d)) ×
   construct (controlDep ps) (maplet ClosureEnv (tupling (bindings (mapWithKey captured ρ))))
   where
   captured x _ = reuse (p `followedBy` singleton (Binding x))

closeDefs :: forall s. Semiring s => Set Position -> Position -> Dict (Raw Val) -> Dict Def -> Dict (GVal s)
closeDefs ps p ρ ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      closure ps p (restrict (fv ds' ∪ fv d) ρ) ds' d

-- ======================
-- Evaluation
-- ======================

-- Evaluator specialised to its class dictionaries once per use
eval
   :: forall m s
    . MonadEval s m
   => { stmt :: Dict (Raw Val) -> Vertex -> Set Position -> Stmt -> m Result
      , program :: Dict (Raw Val) -> Vertex -> Set Position -> Stmt -> m ValAt
      }
eval = { stmt, program }
   where
   expr :: Dict (Raw Val) -> Vertex -> Set Position -> Expr -> m ValAt
   expr ρ b ps = case _ of
      e'@(DocExpr e _) -> do
         pv@((a × _) × _) <- value e' >>= newValue
         (a' × _) × _ <- extendEnv ρ b (maplet varThis (reuseAt pv)) >>= \(ρ' × b') -> expr ρ' b' ps e
         attachDoc a a' $> pv
      e -> value e >>= newValue
      where
      literal ℓ = Val unit (V.Lit ℓ) × construct (controlDep ps) Map.empty

      -- Value of an expression, before vertex is allocated
      value :: Expr -> m (GVal s)
      value = case _ of
         Var x -> pure (deliver ps (get x ρ × reuse (b × singleton (Binding x))))
         Lit ℓ -> pure (literal ℓ)
         Imaginary y -> askClasses <#> \classes ->
            object classes (controlDep ps) cComplex (literal (Float 0.0) : literal (Float y) : Nil)
         Dictionary ees -> for ees (\(Pair e e') -> dictEntry ρ b ps e e') <#> \kvs ->
            deliver ps (dictionary (controlDep ps) (kvs <#> \(pv × pv') -> reuseAt pv × reuseAt pv'))
         DictComp e e' gs -> do
            pv@(p × _) <- qualifiers (\ρ' b' ps' -> singletonList ps' <<< entry <$> dictEntry ρ' b' ps' e e') ρ b ps gs
            pure $ deliver ps $ dictionary (dataDep p) $
               elementsAt pv <#> \pv' -> reuseAt (childAt (Element 0) pv') × reuseAt (childAt (Element 1) pv')
         List es -> sequenceOf V.List (controlDep ps) <<< map reuseAt <$> traverse (expr ρ b ps) es
         Tuple es -> sequenceOf V.Tuple (controlDep ps) <<< map reuseAt <$> traverse (expr ρ b ps) es
         ListComp e gs ->
            reuseAt <$> qualifiers (\ρ' b' ps' -> expr ρ' b' ps' e <#> (reuseAt >>> singletonList ps')) ρ b ps gs
         Constr c es -> do
            classes <- askClasses
            checkArity c (length es) classes
            object classes (controlDep ps) c <<< map reuseAt <$> traverse (expr ρ b ps) es
         Matrix e (x × y) e' -> do
            pv@(_ × v) <- expr ρ b ps e'
            i' × j' <- case v of
               Val _ (V.Tuple [ Val _ (V.Lit (Int i')), Val _ (V.Lit (Int j')) ]) -> pure (i' × j')
               Val _ u -> throw (typeMismatch u "pair of int")
            check
               (i' × j' >= 1 × 1)
               ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
            rss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j ->
               extendEnv ρ b (maplet x (index pv 0 i) `unionWith_never` maplet y (index pv 1 j)) >>= \(ρ' × b') -> expr ρ' b' ps e
            pure $ Val unit (V.Matrix (MatrixRep ((map snd <$> rss) × child (Element 0) v × child (Element 1) v))) ×
               construct (controlDep ps)
                  ( Map.fromFoldable $
                       [ MatrixRows × reuse (fst (childAt (Element 0) pv)), MatrixCols × reuse (fst (childAt (Element 1) pv)) ]
                          <> A.concat (mapWithIndex (\i -> mapWithIndex (\j (q × _) -> MatrixElement i j × reuse q)) rss)
                  )
            where
            -- Index n along dimension k of the matrix with dimensions pv
            index :: ValAt -> Int -> Int -> GVal s
            index pv k n = Val unit (V.Lit (Int n)) × construct (controlDep (singleton (fst (childAt (Element k) pv)))) Map.empty
         Lambda d -> pure (closure ps (b × ε) (restrict (fv d) ρ) empty d)
         Type τ -> pure (Val unit (V.Fun (V.Type τ)) × construct (controlDep ps) Map.empty)
         Attribute e x -> do
            pv@(p × v) <- expr ρ b ps e
            case v of
               Val _ (V.Obj c xvs) -> do
                  _ <- elemIndex x (fst <$> xvs) # orElse (quoted (dottedName c) <> " does not have field " <> quoted x)
                  pure (deliver (singleton p) (reuseAt (childAt (Field x) pv)))
               _ -> throw $ "Found " <> prettyP v <> ", expected object"
         Subscript e e' -> do
            pv@(_ × v) <- expr ρ b ps e
            pv'@(_ × v') <- expr ρ b ps e'
            let
               Val _ u = v
               Val _ u' = v'
            case u, u' of
               V.Dictionary (DictRep d), V.Lit (Str k) -> do
                  _ <- withMsg "Dict lookup" $ lookup k d # orElse ("Key \"" <> k <> "\" not found")
                  subscript (singleton (fst (childAt (DictKey k) pv))) pv pv' (reuseAt (childAt (DictVal k) pv))
               V.Dictionary _, _ -> throw $ "Found " <> prettyP v' <> ", expected str"
               _, V.Lit (Int i) | Just n <- elementCount v -> do
                  let i' = if i < 0 then n + i else i
                  unless (0 <= i' && i' < n) $ throw ("Index " <> show i <> " out of range")
                  subscript empty pv pv' (elementAt i' pv)
               V.List _, _ -> throw $ "Found " <> prettyP v' <> ", expected int"
               V.Tuple _, _ -> throw $ "Found " <> prettyP v' <> ", expected int"
               V.Lit (Str _), _ -> throw $ "Found " <> prettyP v' <> ", expected int"
               V.Matrix (MatrixRep (_ × m × n)), V.Tuple [ Val _ (V.Lit (Int i)), Val _ (V.Lit (Int j)) ] -> do
                  unless (0 <= i && i < dropα (unpack' int m) && 0 <= j && j < dropα (unpack' int n)) $ throw ("Index (" <> show i <> ", " <> show j <> ") out of range")
                  subscript empty pv pv' (reuseAt (childAt (MatrixElement i j) pv))
               V.Matrix _, _ -> throw $ "Found " <> prettyP v' <> ", expected pair of int"
               _, _ -> throw $ "Found " <> prettyP v <> ", expected list, tuple, str, dict or matrix"
            where
            -- Child u at index pv' of pv; qs are further control positions
            subscript :: Set Position -> ValAt -> ValAt -> GVal s -> m (GVal s)
            subscript qs (p × _) pv' u = pure (deliver (singleton p ∪ qs ∪ positionsIn pv') u)
         ModMember q x -> do
            { modules } <- moduleStore
            let pρ@(_ × Env ρ') = definitely' (loadedEnv (get q modules))
            withMsg "Module member" (lookup' x ρ') $> deliver ps (reuseAt (bindingAt x pρ))
         App e es -> do
            pv <- expr ρ b ps e
            pvs <- traverse (expr ρ b ps) es
            withMsg ("In " <> funName e) $ apply pv pvs
         BinOp e op e' -> do
            pv <- expr ρ b ps e
            pv' <- expr ρ b ps e'
            withMsg ("In " <> binopSymbol op) $ orThrow (applyBinop op ps pv pv')
         UnOp op e -> do
            pv <- expr ρ b ps e
            withMsg ("In " <> unopSymbol op) $ orThrow (applyDepFun (unopFun op) Set.empty ps (pv : Nil))
         And e e' -> do
            { holds, pv: pv@(p × _) } <- condition ρ b ps e
            if holds then reuseAt <$> expr ρ b (singleton p) e' else pure (reuseAt pv)
         Or e e' -> do
            { holds, pv: pv@(p × _) } <- condition ρ b ps e
            if holds then pure (reuseAt pv) else reuseAt <$> expr ρ b (singleton p) e'
         Cond e1 e e2 -> do
            { holds, pv: p × _ } <- condition ρ b ps e
            reuseAt <$> expr ρ b (singleton p) (if holds then e1 else e2)
         DocExpr _ e -> reuseAt <$> expr ρ b ps e

   -- Positions of key e and value e'
   dictEntry :: Dict (Raw Val) -> Vertex -> Set Position -> Expr -> Expr -> m (ValAt × ValAt)
   dictEntry ρ b ps e e' = do
      pv <- expr ρ b ps e
      _ <- orThrow (unpack string (snd pv))
      (pv × _) <$> expr ρ b ps e'

   -- Tuple of key and value
   entry :: ValAt × ValAt -> GVal s
   entry (pv × pv') = sequenceOf V.Tuple mempty (reuseAt pv : reuseAt pv' : Nil)

   funName :: Expr -> String
   funName (Var x) = quoted x
   funName (App e _) = funName e
   funName _ = "unknown"

   -- Evaluate e as a Boolean
   condition :: Dict (Raw Val) -> Vertex -> Set Position -> Expr -> m { holds :: Boolean, pv :: ValAt }
   condition ρ b ps e = do
      pv <- expr ρ b ps e
      holds × _ <- orThrow (unpack boolean (snd pv))
      pure { holds, pv }

   singletonList :: Set Position -> GVal s -> GVal s
   singletonList ps v = sequenceOf V.List (controlDep ps) (v : Nil)

   -- Evaluate qualifiers gs and return list of elements; body returns list of one element
   qualifiers
      :: (Dict (Raw Val) -> Vertex -> Set Position -> m (GVal s))
      -> Dict (Raw Val)
      -> Vertex
      -> Set Position
      -> List Qualifier
      -> m ValAt
   qualifiers body ρ b ps gs = elements gs >>= newValue
      where
      -- List of elements, before vertex is allocated
      elements :: List Qualifier -> m (GVal s)
      elements Nil = body ρ b ps
      elements (Guard e : gs') = do
         { holds, pv: q × _ } <- condition ρ b ps e
         if holds then reuseAt <$> qualifiers body ρ b (singleton q) gs'
         else pure (Val unit (V.List []) × construct (controlDep (singleton q)) Map.empty)
      elements (Generator p e : gs') = do
         pv@(_ × v) <- expr ρ b ps e
         n <- case elementCount v of
            Just n -> pure n
            Nothing -> throw ("Found " <> prettyP v <> ", expected list, tuple, str or dict")
         classes <- askClasses
         pvs <- case traverse (flip elementStep v) (L.take n (L.range 0 n)) of
            Just steps -> pure (flip childAt pv <$> steps)
            Nothing -> elementsAt <$> newValue (explode pv)
         pvs' × ps' <- fold <$> for pvs \pv' ->
            case dispatch classes (singleton (p × unit)) pv' of
               Nothing × qs -> pure (Nil × qs)
               Just (ρ' × _) × qs -> do
                  ρ'' × b' <- extendEnv ρ b ρ'
                  qualifiers body ρ'' b' (lengthPositions pv ∪ qs) gs' <#> singleton >>> (_ × empty)
         pure (concatOf V.List (controlDep (lengthPositions pv ∪ ps')) pvs')
      elements (Decl p e : gs') = do
         pv <- expr ρ b ps e
         classes <- askClasses
         ρ' × qs <- destructure classes p pv
         ρ'' × b' <- extendEnv ρ b ρ'
         reuseAt <$> qualifiers body ρ'' b' (controlledBy qs ps) gs'

   stmt :: Dict (Raw Val) -> Vertex -> Set Position -> Stmt -> m Result
   stmt ρ b ps = case _ of
      Return e -> expr ρ b ps e >>= returns
      If bs s_opt -> go (NEL.toList bs) ps
         where
         go Nil ps' = maybe (assigns empty ps') (branch ps') s_opt
         go (Branch e s' : bs') ps' = do
            { holds, pv: q × _ } <- condition ρ b ps' e
            if holds then branch (singleton q) s' else go bs' (singleton q)

         branch ps' s' = stmt ρ b ps' s' >>= case _ of
            Returns pv -> returns pv
            Assigns pρ qs -> flip Assigns (controlledBy qs ps') <$> newExtendEnv pρ empty
      Match e bs -> do
         pv <- expr ρ b ps e
         classes <- askClasses
         case dispatch classes (NEL.toList bs) pv of
            Nothing × qs -> assigns empty qs
            Just (ρ' × s') × qs -> do
               ρ'' × b' <- extendEnv ρ b ρ'
               stmt ρ'' b' (controlledBy qs ps) s' >>= case _ of
                  Returns pv' -> returns pv'
                  Assigns pρ qs' -> assigns (ρ' <+> bindingsAt pρ) (controlledBy qs' qs)
      Declare _ -> assigns empty empty
      Assign p e -> do
         pv <- expr ρ b ps e
         classes <- askClasses
         destructure classes p pv >>= uncurry assigns
      DefRegion ds -> assigns (closeDefs ps (b × ε) ρ ds) empty
      Pass -> assigns empty empty
      ExprStmt e -> expr ρ b ps e *> assigns empty empty
      Assert e e_opt -> do
         { holds, pv: q × _ } <- condition ρ b ps e
         if holds then assigns empty (singleton q)
         else case e_opt of
            Nothing -> throw "AssertionError"
            Just e' -> do
               _ × Val _ u <- expr ρ b (singleton q) e'
               throw ("AssertionError: " <> either (\_ -> prettyP u) identity (string.unpack u))
      Dataclass c -> assigns (maplet (last c) (Val unit (V.Fun (V.Type (T.ClassTy c Nil))) × constant)) empty
      TypeAlias x αs τ -> assigns (maplet x (Val unit (V.TypeAlias αs τ) × constant)) empty
      s@(Seq _ _) -> block empty empty ρ b ps s
      where
      constant = construct (controlDep ps) Map.empty

   -- Evaluate remaining statements of block; statements already evaluated gave bindings ρ' and control positions qs
   block :: Dict (GVal s) -> Set Position -> Dict (Raw Val) -> Vertex -> Set Position -> Stmt -> m Result
   block ρ' qs ρ b ps (Seq s s') = stmt ρ b ps s >>= case _ of
      Returns pv -> returns pv
      Assigns pρ qs' -> do
         ρ'' × b' <- extendEnv ρ b (bindingsAt pρ)
         block (ρ' <+> bindingsAt pρ) (controlledBy qs' qs) ρ'' b' (controlledBy qs' ps) s'
   block ρ' qs ρ b ps s = stmt ρ b ps s >>= case _ of
      Returns pv -> returns pv
      Assigns pρ qs' -> assigns (ρ' <+> bindingsAt pρ) (controlledBy qs' qs)

   returns :: ValAt -> m Result
   returns pv = Returns <$> newValue (reuseAt pv)

   assigns :: Dict (GVal s) -> Set Position -> m Result
   assigns ρ qs = flip Assigns qs <$> newEnv ρ

   -- Value of the expression which ends a program
   program :: Dict (Raw Val) -> Vertex -> Set Position -> Stmt -> m ValAt
   program ρ b ps (Seq t t') = do
      pρ × qs <- asAssigns <$> stmt ρ b ps t
      ρ' × b' <- extendEnv ρ b (bindingsAt pρ)
      program ρ' b' (controlledBy qs ps) t'
   program ρ b ps (ExprStmt e) = expr ρ b ps e
   program _ _ _ _ = error absurd

   -- Apply function pv to pvs, partially if there are fewer arguments than its arity; apply the result to any
   -- arguments beyond the arity
   apply :: ValAt -> List ValAt -> m (GVal s)
   apply pv@(q × v) pvs = case v of
      Val _ (V.Fun (V.Partial _ us)) ->
         applyFun (childAt PartialFun pv) (mapWithIndex (\i _ -> childAt (PartialArg i) pv) us <> pvs)
      _ -> applyFun pv pvs
      where
      applyFun :: ValAt -> List ValAt -> m (GVal s)
      applyFun pv'@(q' × u) pvs' = case u of
         Val _ (V.Fun φ) -> do
            n <- arity'
            let k = length pvs'
            if k < n then
               pure $ Val unit (V.Fun (V.Partial u (snd <$> pvs'))) × construct (controlDep (singleton q))
                  (Map.fromFoldable ((PartialFun × reuse q') : mapWithIndex (\i (p × _) -> PartialArg i × reuse p) pvs'))
            else if k == n then call φ
            else applyFun pv' (take n pvs') >>= newValue >>= flip apply (drop n pvs')
            where
            arity' :: m Int
            arity' = case φ of
               V.Closure _ _ (Def xs _) -> pure (length xs)
               V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
               V.Type (T.ClassTy c _) -> askClasses >>= arity c
               V.Type τ -> throw ("Not callable: " <> prettyP τ)
               V.Partial _ _ -> error absurd
         _ -> throw $ "Found " <> prettyP u <> ", expected function"
         where
         call :: V.Fun Unit -> m (GVal s)
         call = case _ of
            V.Closure (Env ρ) ds (Def xs s) -> do
               newExtendEnv (p × Env ρ) ρ' >>= \((b × _) × Env ρ'') ->
                  reuseAt <<< asReturns <$> stmt ρ'' b (singleton q) s
               where
               p = q' `followedBy` singleton ClosureEnv
               args = foldl (\ρ1 (x × pu) -> if x == varAnon then ρ1 else ρ1 `unionWith_never` maplet x (reuseAt pu)) empty (zip xs pvs')
               ρ' = closeDefs (singleton q) p ρ ds <+> args
            V.Prim (ForeignOp (_ × ForeignOp' { depOp })) -> depOp (singleton q) pvs'
            V.Type (T.ClassTy c _) ->
               askClasses <#> \classes -> object classes (controlDep (singleton q)) c (reuseAt <$> pvs')
            V.Type _ -> error absurd
            V.Partial _ _ -> error absurd

-- Evaluate module q from given environment; bindings of body override module value of each submodule
evalModule :: forall m s. MonadEval s m => EnvAt -> ModuleName -> Module -> m EnvAt
evalModule ((b × _) × Env ρ) q (Module ιs s) = do
   ρ' × b' <- foldM (evalImport q) empty ιs >>= extendEnv ρ b
   { modules } <- moduleStore
   pρ × _ <- asAssigns <$> eval.stmt ρ' b' empty s
   newEnv (subMods modules <+> unbound <+> bindingsAt pρ)
   where
   subMods modules = moduleVal <$> D.fromFoldable (submods (Map.keys modules) q)
   unbound = D.fromFoldable (L.fromFoldable (assigns s) <#> (_ × (Val unit V.Unbound × construct mempty Map.empty)))

-- Allocate fresh vertex for the members ρ of a predefined module
predefinedModule :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Raw Env -> m EnvAt
predefinedModule (Env ρ) = newEnv (ρ <#> (_ × construct mempty Map.empty))

-- Bind imported members, and names of imported modules to module values.
evalImport
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> Dict (GVal s)
   -> Import
   -> m (Dict (GVal s))
evalImport enclosing ρ = case _ of
   Import q Nothing -> do
      _ <- load q
      loadAncestors Nothing q
      pure (ρ <+> maplet (head q) (moduleVal (pure (head q))))
   Import q (Just xs) -> do
      pρ <- load q
      loadAncestors (Just enclosing) q
      importsFrom q pρ ρ xs
   where
   loadAncestors bound q = case NEL.fromList (unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q pρ = foldM step
      where
      step ρ' x = do
         { modules } <- moduleStore
         when (Map.member (snoc q x) modules) (void (load (snoc q x)))
         pure (ρ' <+> maplet x (reuseAt (bindingAt x pρ)))

moduleVal :: forall s. Semiring s => ModuleName -> GVal s
moduleVal q = Val unit (V.Module q) × construct mempty Map.empty

builtinsEnv :: forall m s. HasModuleStore s m => m EnvAt
builtinsEnv = moduleStore <#> \{ modules } -> definitely' (loadedEnv (get builtins modules))

load :: forall m s. MonadEval s m => ModuleName -> m EnvAt
load q = do
   { modules } <- moduleStore
   case Map.lookup q modules of
      Just (Loaded pρ) -> pure pρ
      Just (Parsed body) -> builtinsEnv >>= \pρ -> evalModule pρ q body >>= loaded
      Nothing -> newEnv empty >>= loaded
   where
   loaded pρ = modifyModuleStore (\s -> s { modules = Map.insert q (Loaded pρ) s.modules }) $> pρ

type Eval =
   { g :: DepGraph Label DepKind
   , out :: Vertex
   }

visible :: Eval -> Set Vertex
visible { g, out } = Map.keys g.docs ∪ Set.fromFoldable (Map.values g.docs) ∪ singleton out

-- Graph of the visible vertices, which are labelled by values
visibleGraph :: Eval -> VisibleGraph Val DepKind
visibleGraph r = graph { vals = V.value <$> graph.vals }
   where
   graph = materialise r.g (visible r)

-- Vertices documented with the name x.
documentedAs :: forall s. DepGraph Label s -> String -> Array Vertex
documentedAs g x = A.fromFoldable (Map.keys (Map.filter (\d -> valAt g d == Val unit (V.Lit (Str x))) g.docs))

evalProgram
   :: forall m
    . MonadProgram m
   => Dict (GVal DepKind) -- imported bindings
   -> ClassTable
   -> Stmt
   -> m Eval
evalProgram ρ classes s =
   withClasses classes do
      { depGraph } <- moduleStore
      out × g <- flip runStateT depGraph do
         (b × _) × Env ρ' <- builtinsEnv
         ρ'' × b' <- extendEnv ρ' b ρ
         fst <<< fst <$> eval.program ρ'' b' empty s
      pure { g, out }
