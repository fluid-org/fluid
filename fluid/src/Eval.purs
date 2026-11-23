module Eval where

import Prelude hiding (absurd, apply)

import Bind (Name, dottedName, prefixOf, varAnon, varThis)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldM, foldMap, foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (head, last, snoc, unsnoc)
import Data.List.NonEmpty (fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
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
import DepGraph (DepGraph, Vertex, Path, Sources, Step(..), VisibleGraph, sourceAt, attachDoc, construct, control, extend, materialise, reuse, source, tupling, vertex)
import Lattice (DepKind, Raw)
import Literal (Literal(..), eqLiteral)
import Module.Defs (ModuleName, implicit, submods)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Types (Type(..)) as T
import Primitive (binopRel, boolean, dropα, int, string, typeMismatch, unopRel, unpack, unpack')
import Util (type (×), absurd, check, definitely', error, isEmpty, orElse, orThrow, quoted, singleton, throw, withMsg, (×))
import Util.Map (get, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..), value) as V
import Val (class HasModuleStore, class MonadEval, class MonadProgram, ModuleState(..), loadedEnv, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), GVal, Label, MatrixRep(..), Position, Val(..), computedElement, ctlAt, deliver, dictionary, derivative, elementAt, elementCount, elementStep, elementsAt, envAt, forDefs, gval, lengthPositions, members, modifyModuleStore, moduleStore, newBindings, newInputs, newValue, part, position, positionsIn, project, reuseAt, sequenceOf, valAt)

-- Environment, and inputs vertex which holds environment
type Inputs = { ρ :: Dict (Raw Val), b :: Vertex }

-- Returned value, or bindings introduced and any new sources of the control input
data Result s = Returns (Vertex × Raw Val) | Assigns (Dict (GVal s)) (Set Path)

asReturns :: forall s. Result s -> Vertex × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: forall s. Result s -> Dict (GVal s) × Set Path
asAssigns (Assigns ρ ps) = ρ × ps
asAssigns (Returns _) = error "Assigns expected"

-- Result of a statement with result r followed by a statement with result r'
override :: forall s. Result s -> Result s -> Result s
override (Assigns ρ ps) (Assigns ρ' ps') = Assigns (ρ <+> ρ') (if isEmpty ps' then ps else ps')
override _ r' = r'

-- Inputs of premise which follows bindings ρ' and new sources ps of control input
after :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Inputs -> Dict (GVal s) -> Set Path -> m Inputs
after inputs@{ ρ, b } ρ' ps
   | isEmpty ρ' && isEmpty ps = pure inputs
   | otherwise = newInputs ρ'' (extend (envAt b) (members ρ')) ctl <#> { ρ: ρ'', b: _ }
        where
        ρ'' = ρ <+> (fst <$> ρ')
        ctl = if isEmpty ps then reuse (ctlAt b) else construct (control ps) Map.empty

-- Inputs of a premise with control input dependent on the root at vertex a
controlledBy :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Vertex -> Inputs -> m Inputs
controlledBy a inputs = after inputs empty (singleton (vertex a))

-- Variables bound if the pattern matches the value at a position; also each inspected position
matches :: forall s. Semiring s => ClassTable -> Position -> Pattern -> Maybe (Dict (GVal s)) × List Path
matches _ u (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x (reuseAt u)) × Nil
matches _ _ PWild = Just empty × Nil
matches classes u (PAs p x) = first (map (_ `unionWith_never` maplet x (reuseAt u))) (matches classes u p)
matches classes u@(q × Val _ v) p = second (q : _) case v, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Obj c' xvs, PConstr c ps Nil
      | c `elem` ancestors classes c' ->
           matchesMany classes ((\(x × _) -> project (Field x) u) <$> take (length ps) xvs) ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs $> (x × project (Entry x) u × p')) xps of
         Just kvs -> second ((kvs <#> \(x × _) -> fst (project (Key x) u)) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps -> matchesMany classes (elementsAt u) ps
   V.Tuple vs, PTuple ps | A.length vs == length ps -> matchesMany classes (elementsAt u) ps
   _, _ -> Nothing × Nil

matchesMany :: forall s. Semiring s => ClassTable -> List Position -> List Pattern -> Maybe (Dict (GVal s)) × List Path
matchesMany _ Nil Nil = Just empty × Nil
matchesMany classes (u : us) (p : ps) = case matches classes u p of
   Nothing × qs -> Nothing × qs
   Just ρ × qs -> case matchesMany classes us ps of
      Nothing × qs' -> Nothing × (qs <> qs')
      Just ρ' × qs' -> Just (ρ `unionWith_never` ρ') × (qs <> qs')
matchesMany _ _ _ = error absurd

-- Bindings of the first matching case; also every position inspected in trying the cases
dispatch :: forall s b. Semiring s => ClassTable -> List (Pattern × b) -> Position -> Maybe (Dict (GVal s) × b) × Set Path
dispatch classes cases u = second Set.fromFoldable (go cases)
   where
   go :: List (Pattern × b) -> Maybe (Dict (GVal s) × b) × List Path
   go Nil = Nothing × Nil
   go ((p × b) : cases') = case matches classes u p of
      Just ρ × qs -> Just (ρ × b) × qs
      Nothing × qs -> second (qs <> _) (go cases')

-- dispatch on a single pattern, which must match.
destructure :: forall m s. MonadError Error m => Semiring s => ClassTable -> Pattern -> Position -> m (Dict (GVal s) × Set Path)
destructure classes p u = case dispatch classes (singleton (p × unit)) u of
   Just (ρ × _) × qs -> pure (ρ × qs)
   Nothing × _ -> throw ("Pattern mismatch: " <> prettyP (snd u) <> " does not match " <> prettyP p)

object :: forall s. Semiring s => ClassTable -> Sources s -> Name -> List (GVal s) -> GVal s
object classes srcs c vs = Val unit (V.Obj c (zip (fieldNames classes c) (fst <$> vs))) ×
   construct srcs (Map.fromFoldable (zip (Field <$> fieldNames classes c) (snd <$> vs)))

-- Closure which captures ρ from the environment at position p; root depends on control position ctl
closure :: forall s. Semiring s => Path -> Path -> Dict (Raw Val) -> Dict Def -> Def -> GVal s
closure ctl p ρ ds d = Val unit (V.Fun (V.Closure (Env ρ) ds d)) ×
   construct (control (singleton ctl)) (maplet ClosureEnv (tupling (members (mapWithKey captured ρ))))
   where
   captured x v = v × reuse (p <> singleton (Binding x))

closeDefs :: forall s. Semiring s => Path -> Path -> Dict (Raw Val) -> Dict Def -> Dict (GVal s)
closeDefs ctl p ρ ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      closure ctl p (restrict (fv ds' ∪ fv d) ρ) ds' d

-- Concatenation of the lists at vertices rs; root also depends on srcs
concatLists :: forall s. Semiring s => Sources s -> List (Vertex × Raw Val) -> GVal s
concatLists srcs rs = sequenceOf V.List (srcs <> foldMap (fst >>> vertex >>> source) rs) $
   rs >>= \r@(a × _) -> deliver (singleton (vertex a)) <<< reuseAt <$> elementsAt (position r)

-- ======================
-- Evaluation
-- ======================

-- Evaluator specialised to its class dictionaries once per use
eval
   :: forall m s
    . MonadEval s m
   => { stmt :: Inputs -> Stmt -> m (Result s)
      , program :: Inputs -> Stmt -> m (Vertex × Raw Val)
      }
eval = { stmt, program }
   where
   expr :: Inputs -> Expr -> m (Vertex × Raw Val)
   expr inputs e'@(DocExpr e _) = do
      r <- value inputs e' >>= newValue
      doc <- after inputs (maplet varThis (gval r)) empty >>= flip expr e
      attachDoc (fst r) (fst doc) $> r
   expr inputs e = value inputs e >>= newValue

   -- Value of an expression, before vertex is allocated
   value :: Inputs -> Expr -> m (GVal s)
   value inputs@{ ρ, b } = case _ of
      Var x -> pure (deliver ctl (get x ρ × reuse (envAt b <> singleton (Binding x))))
      Lit ℓ -> pure (Val unit (V.Lit ℓ) × construct (control ctl) Map.empty)
      Dictionary ees -> for ees (\(Pair e e') -> dictEntry inputs e e') <#> \kvs ->
         deliver ctl (dictionary (control ctl) (kvs <#> \(k × r) -> gval k × gval r))
      DictComp e e' gs -> do
         r <- qualifiers (\inputs' -> singletonList inputs' <<< entry <$> dictEntry inputs' e e') inputs gs
         pure $ deliver ctl $ dictionary (source (vertex (fst r))) $
            elementsAt (position r) <#> \kv -> reuseAt (project (Element 0) kv) × reuseAt (project (Element 1) kv)
      List es -> sequenceOf V.List (control ctl) <<< map gval <$> traverse (expr inputs) es
      Tuple es -> sequenceOf V.Tuple (control ctl) <<< map gval <$> traverse (expr inputs) es
      ListComp e gs -> gval <$> qualifiers (\inputs' -> expr inputs' e <#> (gval >>> singletonList inputs')) inputs gs
      Constr c es -> do
         classes <- askClasses
         checkArity c (length es) classes
         object classes (control ctl) c <<< map gval <$> traverse (expr inputs) es
      Matrix e (x × y) e' -> do
         a × v <- expr inputs e'
         i' × j' <- case v of
            Val _ (V.Tuple [ Val _ (V.Lit (Int i')), Val _ (V.Lit (Int j')) ]) -> pure (i' × j')
            Val _ u -> throw (typeMismatch u "pair of int")
         check
            (i' × j' >= 1 × 1)
            ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
         rss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j ->
            after inputs (maplet x (index a 0 i) `unionWith_never` maplet y (index a 1 j)) empty >>= flip expr e
         pure $ Val unit (V.Matrix (MatrixRep ((map snd <$> rss) × part (Element 0) v × part (Element 1) v))) ×
            construct (control ctl)
               ( Map.fromFoldable $
                    [ MatrixRows × reuse (sourceAt a (singleton (Element 0))), MatrixCols × reuse (sourceAt a (singleton (Element 1))) ]
                       <> A.concat (mapWithIndex (\i -> mapWithIndex (\j (a' × _) -> MatrixElement i j × reuse (vertex a'))) rss)
               )
         where
         -- Index n along dimension k of the matrix with dimensions at vertex a
         index :: Vertex -> Int -> Int -> GVal s
         index a k n = Val unit (V.Lit (Int n)) × construct (control (singleton (sourceAt a (singleton (Element k))))) Map.empty
      Lambda d -> pure (closure (ctlAt b) (envAt b) (restrict (fv d) ρ) empty d)
      Type τ -> pure (Val unit (V.Fun (V.Type τ)) × construct (control ctl) Map.empty)
      Attribute e x -> do
         r@(a × v) <- expr inputs e
         case v of
            Val _ (V.Obj c xvs) -> do
               _ <- elemIndex x (fst <$> xvs) # orElse (quoted (dottedName c) <> " does not have field " <> quoted x)
               pure (deliver (singleton (vertex a)) (reuseAt (project (Field x) (position r))))
            _ -> throw $ "Found " <> prettyP v <> ", expected object"
      Subscript e e' -> do
         r@(_ × v) <- expr inputs e
         r'@(_ × v') <- expr inputs e'
         let
            Val _ u = v
            Val _ u' = v'
         case u, u' of
            V.Dictionary (DictRep d), V.Lit (Str k) -> do
               _ <- withMsg "Dict lookup" $ lookup k d # orElse ("Key \"" <> k <> "\" not found")
               subscript r r' (reuseAt (project (Entry k) (position r))) (singleton (fst (project (Key k) (position r))))
            V.Dictionary _, _ -> throw $ "Found " <> prettyP v' <> ", expected str"
            _, V.Lit (Int i) | Just n <- elementCount v -> do
               let i' = if i < 0 then n + i else i
               unless (0 <= i' && i' < n) $ throw ("Index " <> show i <> " out of range")
               subscript r r' (elementAt i' r) empty
            V.List _, _ -> throw $ "Found " <> prettyP v' <> ", expected int"
            V.Tuple _, _ -> throw $ "Found " <> prettyP v' <> ", expected int"
            V.Lit (Str _), _ -> throw $ "Found " <> prettyP v' <> ", expected int"
            V.Matrix (MatrixRep (_ × m × n)), V.Tuple [ Val _ (V.Lit (Int i)), Val _ (V.Lit (Int j)) ] -> do
               unless (0 <= i && i < dropα (unpack' int m) && 0 <= j && j < dropα (unpack' int n)) $ throw ("Index (" <> show i <> ", " <> show j <> ") out of range")
               subscript r r' (reuseAt (project (MatrixElement i j) (position r))) empty
            V.Matrix _, _ -> throw $ "Found " <> prettyP v' <> ", expected pair of int"
            _, _ -> throw $ "Found " <> prettyP v <> ", expected list, tuple, str, dict or matrix"
         where
         -- Part u of the value at vertex r, at the index at vertex r'; ps are further control positions
         subscript :: Vertex × Raw Val -> Vertex × Raw Val -> GVal s -> Set Path -> m (GVal s)
         subscript r r' u ps = pure (deliver (singleton (vertex (fst r)) ∪ ps ∪ positionsIn r') u)
      ModMember q x -> do
         { modules } <- moduleStore
         deliver ctl <$> withMsg "Module member" (lookup' x (definitely' (loadedEnv (get q modules))))
      App e es -> do
         f <- expr inputs e
         rs <- traverse (expr inputs) es
         withMsg ("In " <> funName e) $ apply (ctlAt b) f rs
      BinOp e op e' -> do
         rs <- traverse (expr inputs) (e : e' : Nil)
         withMsg ("In " <> binopSymbol op) $ orThrow (derivative (binopRel op) ctl rs)
      UnOp op e -> do
         r <- expr inputs e
         withMsg ("In " <> unopSymbol op) $ orThrow (derivative (unopRel op) ctl (r : Nil))
      And e e' -> do
         { holds, r } <- condition inputs e
         if holds then gval <$> (controlledBy (fst r) inputs >>= flip expr e') else pure (gval r)
      Or e e' -> do
         { holds, r } <- condition inputs e
         if holds then pure (gval r) else gval <$> (controlledBy (fst r) inputs >>= flip expr e')
      Cond e1 e e2 -> do
         { holds, r } <- condition inputs e
         gval <$> (controlledBy (fst r) inputs >>= flip expr (if holds then e1 else e2))
      DocExpr _ e -> gval <$> expr inputs e
      where
      ctl = singleton (ctlAt b)

   -- Vertices of key e and value e'
   dictEntry :: Inputs -> Expr -> Expr -> m ((Vertex × Raw Val) × (Vertex × Raw Val))
   dictEntry inputs e e' = do
      k <- expr inputs e
      _ <- orThrow (unpack string (snd k))
      (k × _) <$> expr inputs e'

   -- Tuple of key and value
   entry :: (Vertex × Raw Val) × (Vertex × Raw Val) -> GVal s
   entry (k × r) = sequenceOf V.Tuple mempty (gval k : gval r : Nil)

   funName :: Expr -> String
   funName (Var x) = quoted x
   funName (App e _) = funName e
   funName _ = "unknown"

   -- Evaluate e as a Boolean at vertex r
   condition :: Inputs -> Expr -> m { holds :: Boolean, r :: Vertex × Raw Val }
   condition inputs e = do
      r <- expr inputs e
      holds × _ <- orThrow (unpack boolean (snd r))
      pure { holds, r }

   singletonList :: Inputs -> GVal s -> GVal s
   singletonList { b } v = sequenceOf V.List (control (singleton (ctlAt b))) (v : Nil)

   -- Evaluate qualifiers gs and return list of elements; body returns list of one element
   qualifiers :: (Inputs -> m (GVal s)) -> Inputs -> List Qualifier -> m (Vertex × Raw Val)
   qualifiers body inputs gs = elements gs >>= newValue
      where
      -- List of elements, before vertex is allocated
      elements :: List Qualifier -> m (GVal s)
      elements Nil = body inputs
      elements (Guard e : gs') = do
         { holds, r: a × _ } <- condition inputs e
         if holds then gval <$> (controlledBy a inputs >>= \inputs' -> qualifiers body inputs' gs')
         else pure (Val unit (V.List []) × construct (control (singleton (vertex a))) Map.empty)
      elements (Generator p e : gs') = do
         r@(_ × v) <- expr inputs e
         n <- case elementCount v of
            Just n -> pure n
            Nothing -> throw ("Found " <> prettyP v <> ", expected list, tuple, str or dict")
         classes <- askClasses
         rs × ps <- fold <$> for (L.take n (L.range 0 n)) \i -> do
            u <- case elementStep i v of
               Just step -> pure (project step (position r))
               Nothing -> position <$> newValue (computedElement i r)
            case dispatch classes (singleton (p × unit)) u of
               Nothing × qs -> pure (Nil × qs)
               Just (ρ' × _) × qs ->
                  after inputs ρ' (lengthPositions r ∪ qs) >>= \inputs' -> qualifiers body inputs' gs' <#> \r' -> singleton r' × empty
         pure (concatLists (control (lengthPositions r ∪ ps)) rs)
      elements (Decl p e : gs') = do
         r <- expr inputs e
         classes <- askClasses
         ρ' × ps <- destructure classes p (position r)
         gval <$> (after inputs ρ' ps >>= \inputs' -> qualifiers body inputs' gs')

   stmt :: Inputs -> Stmt -> m (Result s)
   stmt inputs s = result inputs s >>= case _ of
      Returns r -> Returns <$> newValue (gval r)
      Assigns ρ ps -> flip Assigns ps <<< snd <$> newBindings ρ

   -- Result of a statement, before vertex is allocated
   result :: Inputs -> Stmt -> m (Result s)
   result inputs@{ ρ, b } = case _ of
      Return e -> Returns <$> expr inputs e
      If bs s_opt -> go (NEL.toList bs) inputs
         where
         go Nil inputs' = maybe (pure (Assigns empty (singleton (ctlAt inputs'.b)))) (branch inputs') s_opt
         go (Branch e s' : bs') inputs' = do
            { holds, r: a × _ } <- condition inputs' e
            inputs'' <- controlledBy a inputs'
            if holds then branch inputs'' s' else go bs' inputs''

         branch inputs' s' = override (Assigns empty (singleton (ctlAt inputs'.b))) <$> stmt inputs' s'
      Match e bs -> do
         r <- expr inputs e
         classes <- askClasses
         case dispatch classes (NEL.toList bs) (position r) of
            Nothing × ps -> pure (Assigns empty ps)
            Just (ρ' × s') × ps -> override (Assigns ρ' ps) <$> (after inputs ρ' ps >>= flip stmt s')
      Declare _ -> pure (Assigns empty empty)
      Assign p e -> do
         r <- expr inputs e
         classes <- askClasses
         uncurry Assigns <$> destructure classes p (position r)
      DefRegion ds -> pure (Assigns (closeDefs (ctlAt b) (envAt b) ρ ds) empty)
      Pass -> pure (Assigns empty empty)
      ExprStmt e -> expr inputs e $> Assigns empty empty
      Assert e e_opt -> do
         { holds, r: a × _ } <- condition inputs e
         if holds then pure (Assigns empty (singleton (vertex a)))
         else case e_opt of
            Nothing -> throw "AssertionError"
            Just e' -> do
               _ × Val _ u <- controlledBy a inputs >>= flip expr e'
               throw ("AssertionError: " <> either (\_ -> prettyP u) identity (string.unpack u))
      Dataclass c -> pure (Assigns (maplet (last c) (Val unit (V.Fun (V.Type (T.ClassTy c Nil))) × constant)) empty)
      TypeAlias x αs τ -> pure (Assigns (maplet x (Val unit (V.TypeAlias αs τ) × constant)) empty)
      Seq s s' -> stmt inputs s >>= case _ of
         r@(Returns _) -> pure r
         r@(Assigns ρ' ps) -> override r <$> (after inputs ρ' ps >>= flip stmt s')
      where
      constant = construct (control (singleton (ctlAt b))) Map.empty

   program :: Inputs -> Stmt -> m (Vertex × Raw Val)
   program inputs s = output inputs s >>= \r -> newValue (gval r) $> r
      where
      output inputs' (Seq t t') = asAssigns <$> stmt inputs' t >>= \(ρ × ps) -> after inputs' ρ ps >>= flip output t'
      output inputs' (ExprStmt e) = expr inputs' e
      output _ _ = error absurd

   -- Apply f to rs at a new vertex; a partial application depends on control position ctl
   application :: Path -> Vertex × Raw Val -> List (Vertex × Raw Val) -> m (Vertex × Raw Val)
   application ctl f rs = apply ctl f rs >>= newValue

   -- Apply f to rs, partially if rs is shorter than the arity of f; apply the result to any arguments beyond
   -- the arity
   apply :: Path -> Vertex × Raw Val -> List (Vertex × Raw Val) -> m (GVal s)
   apply ctl f@(a × v) rs = case v of
      Val _ (V.Fun (V.Partial _ us)) -> do
         f' <- newValue (deliver (singleton (vertex a)) (reuseAt (project PartialFun (position f))))
         rs' <- for (mapWithIndex const us) \i -> newValue (reuseAt (project (PartialArg i) (position f)))
         apply ctl f' (rs' <> rs)
      Val _ (V.Fun φ) -> do
         n <- arity'
         let k = length rs
         if k < n then
            pure $ Val unit (V.Fun (V.Partial v (snd <$> rs))) × construct (control (singleton ctl))
               (Map.fromFoldable ((PartialFun × reuse (vertex a)) : mapWithIndex (\i (a' × _) -> PartialArg i × reuse (vertex a')) rs))
         else if k == n then call φ
         else application ctl f (take n rs) >>= \f' -> apply ctl f' (drop n rs)
         where
         arity' :: m Int
         arity' = case φ of
            V.Closure _ _ (Def xs _) -> pure (length xs)
            V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
            V.Type (T.ClassTy c _) -> askClasses >>= arity c
            V.Type τ -> throw ("Not callable: " <> prettyP τ)
            V.Partial _ _ -> error absurd
      _ -> throw $ "Found " <> prettyP v <> ", expected function"
      where
      -- Call function with arguments rs; control input depends on the root of the function value
      call :: V.Fun Unit -> m (GVal s)
      call = case _ of
         V.Closure (Env ρ) ds (Def xs s) -> do
            b <- newInputs ρ'' (extend p (members ρ')) (construct (control (singleton (vertex a))) Map.empty)
            gval <<< asReturns <$> stmt { ρ: ρ'', b } s
            where
            p = sourceAt a (singleton ClosureEnv)
            args = foldl (\ρ1 (x × r) -> if x == varAnon then ρ1 else ρ1 `unionWith_never` maplet x (gval r)) empty (zip xs rs)
            ρ' = closeDefs (vertex a) p ρ ds <+> args
            ρ'' = ρ <+> (fst <$> ρ')
         V.Prim (ForeignOp (_ × ForeignOp' { depOp })) -> depOp (application (vertex a)) (vertex a) rs
         V.Type (T.ClassTy c _) ->
            askClasses <#> \classes -> object classes (control (singleton (vertex a))) c (gval <$> rs)
         V.Type _ -> error absurd
         V.Partial _ _ -> error absurd

-- Inputs vertex for environment ρ; control position depends on nothing
topLevel :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Dict (GVal s) -> m Inputs
topLevel ρ = newInputs (fst <$> ρ) (tupling (members ρ)) (construct mempty Map.empty) <#> { ρ: fst <$> ρ, b: _ }

-- Evaluate module q at a new vertex; bindings of body override module value of each submodule
evalModule
   :: forall m s
    . MonadEval s m
   => Dict (GVal s)
   -> ModuleName
   -> Module
   -> m (Dict (GVal s))
evalModule ρ0 q (Module ιs s) = do
   ρ <- foldM (evalImport q) ρ0 ιs
   { modules } <- moduleStore
   ρ' × _ <- asAssigns <$> (topLevel ρ >>= flip eval.stmt s)
   snd <$> newBindings (subMods modules <+> unbound <+> ρ')
   where
   subMods modules = moduleVal <$> D.fromFoldable (submods (Map.keys modules) q)
   unbound = D.fromFoldable (L.fromFoldable (assigns s) <#> (_ × (Val unit V.Unbound × construct mempty Map.empty)))

-- Construct members ρ of a predefined module at a new vertex
predefinedModule :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Raw Env -> m (Dict (GVal s))
predefinedModule (Env ρ) = snd <$> newBindings (ρ <#> (_ × construct mempty Map.empty))

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
      ρ_q <- load q
      loadAncestors (Just enclosing) q
      importsFrom q ρ_q ρ xs
   where
   loadAncestors bound q = case NEL.fromList (unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q ρ_q = foldM step
      where
      step ρ' x = do
         { modules } <- moduleStore
         when (Map.member (snoc q x) modules) (void (load (snoc q x)))
         pure (ρ' <+> maplet x (get x ρ_q))

moduleVal :: forall s. Semiring s => ModuleName -> GVal s
moduleVal q = Val unit (V.Module q) × construct mempty Map.empty

-- Members of the implicit modules loaded so far.
implicitMembers :: forall m s. HasModuleStore s m => m (Dict (GVal s))
implicitMembers = moduleStore <#> \{ modules } ->
   foldl (\ρ q -> ρ <+> fromMaybe empty (Map.lookup q modules >>= loadedEnv)) empty implicit

load
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> m (Dict (GVal s))
load q = do
   { modules } <- moduleStore
   case Map.lookup q modules of
      Just (Loaded ρ_q) -> pure ρ_q
      Just (Parsed body) -> do
         ρ0 <- implicitMembers
         evalModule ρ0 q body >>= loaded
      Nothing -> loaded empty
   where
   loaded ρ_q = modifyModuleStore (\s -> s { modules = Map.insert q (Loaded ρ_q) s.modules }) $> ρ_q

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
   => Dict (GVal DepKind) -- top-level environment
   -> ClassTable
   -> Stmt
   -> m Eval
evalProgram ρ classes s =
   withClasses classes do
      { depGraph } <- moduleStore
      out × g <- flip runStateT depGraph (fst <$> (topLevel ρ >>= flip eval.program s))
      pure { g, out }
