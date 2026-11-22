module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon, varThis)
import Control.Alt ((<|>))
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldM, foldl, sum)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..), product)
import Data.Identity (Identity(..))
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (head, last, snoc, unsnoc)
import Data.List.NonEmpty (cons', fromList, tail, toList) as NEL
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
import DepGraph (DepGraph, Deriv, PosLineage, VisibleGraph, addTrace, attachDoc, materialise, zeros)
import Lattice (class DepSemiring, DepKind, Raw)
import Literal (Literal(..), eqLiteral)
import Module.Defs (ModuleName, implicit, submods)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Trace as Tr
import Types (Type(..)) as T
import Primitive (binopRel, boolean, concatLists, dropα, int, string, typeMismatch, unopRel, unpack, unpack')
import Util (type (×), Endo, absurd, check, definitely', error, orElse, orThrow, quoted, singleton, throw, withMsg, (×))
import Util.Map (get, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..), Label(..), dictEntry, value) as V
import Val (class HasModuleStore, class MonadEval, class MonadProgram, BaseVal, Ctrl, ModuleState(..), loadedEnv, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), GVal, Label, MatrixRep(..), Val(..), closureEnv, construct, constructFrom, deliver, field, forDefs, fromTotalRel, fun, gval, element, elementCount, lengthDep, matrixElement, modifyModuleStore, moduleStore, newAssigns, newValue, partialArg, partialFun, project, fromRel, raw, root, toDict, valAt, via)

type Inputs s = { ctrl :: Ctrl s, ρ :: Dict (GVal s) }

-- Returned value, or the bindings and control position introduced
data Result s = Returns (Deriv × Raw Val) | Assigns (Dict (GVal s)) (Maybe (Ctrl s))

asReturns :: forall s. Result s -> Deriv × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: forall s. Result s -> Dict (GVal s) × Maybe (Ctrl s)
asAssigns (Assigns ρ ctrl) = ρ × ctrl
asAssigns (Returns _) = error "Assigns expected"

-- Result of a statement with result r followed by a statement with result r'
override :: forall s. Result s -> Result s -> Result s
override (Assigns ρ ctrl) (Assigns ρ' ctrl') = Assigns (ρ <+> ρ') (ctrl' <|> ctrl)
override _ r' = r'

-- Same as override, except that a control input is always present
after :: forall s. Inputs s -> Dict (GVal s) -> Maybe (Ctrl s) -> Inputs s
after { ctrl, ρ } ρ' ctrl' = { ctrl: fromMaybe ctrl ctrl', ρ: ρ <+> ρ' }

-- Variables bound if the pattern matches the value, with the dependence of each inspected position.
matches :: forall s. DepSemiring s => ClassTable -> GVal s -> Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matches _ v (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x v) × Nil
matches _ _ PWild = Just empty × Nil
matches classes v (PAs p x) = first (map (_ `unionWith_never` maplet x v)) (matches classes v p)
matches classes v p = second (via root v : _) case u, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Obj c' xvs, PConstr c ps Nil
      | c `elem` ancestors classes c' ->
           matchesMany classes
              (mapWithIndex (\i _ -> project (field i) v) (take (length ps) xvs))
              ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs $> (x × project (V.dictEntry x >>> snd) v × p')) xps of
         Just kvs -> second ((kvs <#> \(x × _) -> via (V.dictEntry x >>> fst) v) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps -> matchesElements vs ps
   V.Tuple vs, PTuple ps | A.length vs == length ps -> matchesElements vs ps
   _, _ -> Nothing × Nil
   where
   Val _ u = raw v
   matchesElements vs ps = matchesMany classes (mapWithIndex (\i _ -> project (element i) v) (L.fromFoldable vs)) ps

matchesMany :: forall s. DepSemiring s => ClassTable -> List (GVal s) -> List Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matchesMany _ Nil Nil = Just empty × Nil
matchesMany classes (v : vs) (p : ps) = case matches classes v p of
   Nothing × ctrls -> Nothing × ctrls
   Just ρ × ctrls -> case matchesMany classes vs ps of
      Nothing × ctrls' -> Nothing × (ctrls <> ctrls')
      Just ρ' × ctrls' -> Just (ρ `unionWith_never` ρ') × (ctrls <> ctrls')
matchesMany _ _ _ = error absurd

-- Bindings of the first matching case, with the control position introduced if the cases tried inspect any
-- position
dispatch :: forall s b. DepSemiring s => ClassTable -> List (Pattern × b) -> GVal s -> Maybe (Dict (GVal s) × b) × Maybe (Ctrl s)
dispatch classes cases v = second (map fold <<< NEL.fromList) (go cases)
   where
   go :: List (Pattern × b) -> Maybe (Dict (GVal s) × b) × List (Ctrl s)
   go Nil = Nothing × Nil
   go ((p × b) : cases') = case matches classes v p of
      Just ρ × ctrls -> Just (ρ × b) × ctrls
      Nothing × ctrls -> second (ctrls <> _) (go cases')

-- dispatch on a single pattern, which must match.
destructure :: forall m s. MonadError Error m => DepSemiring s => ClassTable -> Pattern -> GVal s -> m (Dict (GVal s) × Maybe (Ctrl s))
destructure classes p v = case dispatch classes (singleton (p × unit)) v of
   Just (ρ × _) × ctrl -> pure (ρ × ctrl)
   Nothing × _ -> throw ("Pattern mismatch: " <> prettyP (raw v) <> " does not match " <> prettyP p)

closure :: forall s. DepSemiring s => Ctrl s -> Dict (GVal s) -> Dict Def -> Def -> GVal s
closure ctrl ρ ds d = constructFrom ctrl (\ρ' -> V.Fun (V.Closure (Env ρ') ds d)) ρ

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict Def -> Dict (GVal s)
closeDefs { ctrl, ρ } ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      closure ctrl (restrict (fv ds' ∪ fv d) ρ) ds' d

-- ======================
-- Evaluation
-- ======================

-- Evaluator specialised to its class dictionaries once per use
eval
   :: forall m s
    . MonadEval s m
   => { stmt :: Inputs s -> Stmt -> m (Result s)
      , program :: Inputs s -> Stmt -> m (Deriv × Raw Val)
      }
eval = { stmt, program }
   where
   expr :: Inputs s -> Expr -> m (Deriv × Raw Val)
   expr inputs@{ ρ } e'@(DocExpr e _) = do
      r <- value inputs e' >>= recordExpr
      doc <- expr (inputs { ρ = ρ <+> maplet varThis (gval r) }) e
      attachDoc (fst r) (fst doc) $> r
   expr inputs e = value inputs e >>= recordExpr

   recordExpr :: GVal s × Tr.ExprTrace (Label Unit) Deriv -> m (Deriv × Raw Val)
   recordExpr (v × trace) = do
      r <- newValue v
      addTrace (fst r) (Tr.ExprTrace trace)
      pure r

   --value-only trace fallback, temporary
   untraced :: m (GVal s) -> m (GVal s × Tr.ExprTrace (Label Unit) Deriv)
   untraced computation = do
      v <- computation
      pure (v × Tr.valueTrace (V.Value (raw v)))

   -- Value of an expression, before vertex is allocated
   value :: Inputs s -> Expr -> m (GVal s × Tr.ExprTrace (Label Unit) Deriv)
   value inputs@{ ctrl, ρ } = case _ of
      Var x -> pure (deliver ctrl (get x ρ) × Tr.Variable x)
      Lit ℓ -> pure (constructFrom ctrl (const (V.Lit ℓ)) Nil × Tr.Literal ℓ)
      Dictionary ees -> do
         entries <- for ees (\(Pair e e') -> dictEntry inputs e e')
         v <- dict ctrl (constructFrom ctrl (A.fromFoldable >>> V.List) (fst <$> entries))
         pure (v × Tr.DictLiteral (snd <$> entries))
      DictComp e e' gs -> untraced $ qualifiers body inputs gs >>= dict ctrl
         where
         body inputs' = do
            entry × _ <- dictEntry inputs' e e'
            pure (singletonList inputs' entry)
      List es -> do
         results <- traverse (expr inputs) es
         pure (constructFrom ctrl (A.fromFoldable >>> V.List) (gval <$> results) × Tr.ListLiteral (fst <$> results))
      Tuple es -> do
         results <- traverse (expr inputs) es
         pure (constructFrom ctrl (A.fromFoldable >>> V.Tuple) (gval <$> results) × Tr.TupleLiteral (fst <$> results))
      ListComp e gs -> untraced $ qualifiers (\inputs' -> expr inputs' e <#> (gval >>> singletonList inputs')) inputs gs
      Constr c es -> do
         classes <- askClasses
         checkArity c (length es) classes
         args <- traverse (expr inputs) es
         pure
            ( constructFrom ctrl (V.Obj c <<< zip (fieldNames classes c)) (gval <$> args)
                 × Tr.ObjectConstructor c (fst <$> args)
            )
      Matrix e (x × y) e' -> do
         dimsResult <- expr inputs e'
         let dims = gval dimsResult
         i' × j' <- case raw dims of
            Val _ (V.Tuple [ Val _ (V.Lit (Int i')), Val _ (V.Lit (Int j')) ]) -> pure (i' × j')
            Val _ u -> throw (typeMismatch u "pair of int")
         check
            (i' × j' >= 1 × 1)
            ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
         vssResults <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
            let ρ' = maplet x (index dims 0 i) `unionWith_never` maplet y (index dims 1 j)
            expr (inputs { ρ = ρ <+> ρ' }) e
         let vss = map (map gval) vssResults
         pure
            ( constructFrom ctrl mat (product (Compose vss) (Identity dims))
                 × Tr.Matrix (fst dimsResult) (map (map fst) vssResults)
            )
         where
         index :: GVal s -> Int -> Int -> GVal s
         index dims k n = constructFrom (via (element k >>> root) dims) (const (V.Lit (Int n))) Nil

         mat :: forall a. Product (Compose Array Array) Identity (Val a) -> BaseVal a
         mat (Product (Compose vss × Identity p)) = V.Matrix (MatrixRep (vss × element 0 p × element 1 p))
      Lambda d -> pure (closure ctrl (restrict (fv d) ρ) empty d × Tr.Lambda d)
      Type τ -> untraced $ pure (constructFrom ctrl (const (V.Fun (V.Type τ))) Nil)
      Attribute e x -> do
         targ <- expr inputs e
         let v = gval targ
         case raw v of
            Val _ (V.Obj c xvs) -> do
               i <- elemIndex x (fst <$> xvs) # orElse (quoted (dottedName c) <> " has no field " <> quoted x)
               pure (deliver (ctrl <> via root v) (project (field i) v) × Tr.Attribute x (fst targ))
            _ -> throw $ "Found " <> prettyP (raw v) <> ", expected object"
      Subscript e e' -> do
         container <- expr inputs e
         index <- expr inputs e'
         let
            v = gval container
            v' = gval index
            Val _ u = raw v
            Val _ u' = raw v'
         selected <- case u, u' of
            V.Dictionary (DictRep d), V.Lit (Str s) -> do
               _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
               subscript v v' (V.dictEntry s >>> snd) (via root v <> via (V.dictEntry s >>> fst) v)
            V.Dictionary _, _ -> throw $ "Found " <> prettyP (raw v') <> ", expected str"
            _, V.Lit (Int i) | Just n <- elementCount (raw v) -> do
               let i' = if i < 0 then n + i else i
               unless (0 <= i' && i' < n) $ throw ("Index " <> show i <> " out of range")
               subscript v v' (element i') (via root v)
            V.List _, _ -> throw $ "Found " <> prettyP (raw v') <> ", expected int"
            V.Tuple _, _ -> throw $ "Found " <> prettyP (raw v') <> ", expected int"
            V.Lit (Str _), _ -> throw $ "Found " <> prettyP (raw v') <> ", expected int"
            V.Matrix (MatrixRep (_ × m × n)), V.Tuple [ Val _ (V.Lit (Int i)), Val _ (V.Lit (Int j)) ] -> do
               unless (0 <= i && i < dropα (unpack' int m) && 0 <= j && j < dropα (unpack' int n)) $ throw ("Index (" <> show i <> ", " <> show j <> ") out of range")
               subscript v v' (matrixElement i j) (via root v)
            V.Matrix _, _ -> throw $ "Found " <> prettyP (raw v') <> ", expected pair of int"
            _, _ -> throw $ "Found " <> prettyP (raw v) <> ", expected list, tuple, str, dict or matrix"
         pure (selected × Tr.Subscript (fst container) (fst index))
         where
         subscript :: GVal s -> GVal s -> (forall a. Endo (Val a)) -> Ctrl s -> m (GVal s)
         subscript v v' proj ctrl' =
            pure (deliver (ctrl <> ctrl' <> via sum v') (project proj v))
      ModMember q x -> untraced do
         { modules } <- moduleStore
         deliver ctrl <$> withMsg "Module member" (lookup' x (definitely' (loadedEnv (get q modules))))
      App e es -> untraced do
         f <- gval <$> expr inputs e
         vs <- traverse (expr inputs >>> map gval) es
         withMsg ("In " <> funName e) $ apply ctrl f vs
      BinOp e op e' -> do
         left <- expr inputs e
         right <- expr inputs e'
         v <- withMsg ("In " <> binopSymbol op) $
            fromRel (binopRel op) (application ctrl) ctrl (gval left : gval right : Nil)
         pure (v × Tr.Binary op (fst left) (fst right))
      UnOp op e -> do
         operand <- expr inputs e
         v <- withMsg ("In " <> unopSymbol op) $
            fromRel (unopRel op) (application ctrl) ctrl (gval operand : Nil)
         pure (v × Tr.Unary op (fst operand))
      And e e' -> do
         { holds, ctrl: ctrl', value: v, vertex: left } <- condition inputs e
         if holds then do
            right <- expr (inputs { ctrl = ctrl' }) e'
            pure (gval right × Tr.AndFull left (fst right))
         else pure (v × Tr.AndShort left e')
      Or e e' -> do
         { holds, ctrl: ctrl', value: v, vertex: left } <- condition inputs e
         if holds then pure (v × Tr.OrShort left e')
         else do
            right <- expr (inputs { ctrl = ctrl' }) e'
            pure (gval right × Tr.OrFull left (fst right))
      Cond e1 e e2 -> do
         { holds, ctrl: ctrl', vertex } <- condition inputs e
         if holds then do
            chosen <- expr (inputs { ctrl = ctrl' }) e1
            pure (gval chosen × Tr.CondTrue vertex (fst chosen) e2)
         else do
            chosen <- expr (inputs { ctrl = ctrl' }) e2
            pure (gval chosen × Tr.CondFalse vertex e1 (fst chosen))
      DocExpr _ e -> untraced $ gval <$> expr inputs e

   -- Tuple of key e and value e', with their vertex IDs
   dictEntry :: Inputs s -> Expr -> Expr -> m (GVal s × Pair Deriv)
   dictEntry inputs' e e' = do
      k <- expr inputs' e
      _ <- orThrow (unpack string (snd k))
      v <- expr inputs' e'
      pure
         ( constructFrom mempty (A.fromFoldable >>> V.Tuple) (gval k : gval v : Nil)
              × Pair (fst k) (fst v)
         )

   -- Dictionary from list v of key-value tuples
   dict :: Ctrl s -> GVal s -> m (GVal s)
   dict ctrl v = fromTotalRel toDict (application ctrl) ctrl (v : Nil)

   funName :: Expr -> String
   funName (Var x) = quoted x
   funName (App e _) = funName e
   funName _ = "unknown"

   -- Evaluate e as a Boolean, taking the root of the resulting value as control input for later evaluation
   condition :: Inputs s -> Expr -> m { holds :: Boolean, ctrl :: Ctrl s, value :: GVal s, vertex :: Deriv }
   condition inputs e = do
      r <- expr inputs e
      let v = gval r
      holds × _ <- orThrow (unpack boolean (raw v))
      pure { holds, ctrl: via root v, value: v, vertex: fst r }

   singletonList :: Inputs s -> GVal s -> GVal s
   singletonList { ctrl } v = constructFrom ctrl (A.fromFoldable >>> V.List) (v : Nil)

   -- Evaluate qualifiers gs and return list of elements; body returns list of one element
   qualifiers :: (Inputs s -> m (GVal s)) -> Inputs s -> List Qualifier -> m (GVal s)
   qualifiers body inputs@{ ρ } gs = gval <$> (elements gs >>= newValue)
      where
      -- List of elements, before vertex is allocated
      elements :: List Qualifier -> m (GVal s)
      elements Nil = body inputs
      elements (Guard e : gs') = do
         { holds, ctrl } <- condition inputs e
         if holds then qualifiers body (inputs { ctrl = ctrl }) gs'
         else pure (constructFrom ctrl (const (V.List [])) Nil)
      elements (Generator p e : gs') = do
         v <- gval <$> expr inputs e
         n <- case elementCount (raw v) of
            Just n -> pure n
            Nothing -> throw ("Found " <> prettyP (raw v) <> ", expected list, tuple, str or dict")
         classes <- askClasses
         vs × ctrl <- fold <$> for (L.take n (L.range 0 n)) \i -> do
            let u = project (element i) v
            case dispatch classes (singleton (p × unit)) u of
               Nothing × ctrl -> pure (Nil × fold ctrl)
               Just (ρ' × _) × ctrl ->
                  qualifiers body (inputs { ctrl = via lengthDep v <> fold ctrl, ρ = ρ <+> ρ' }) gs'
                     <#> \v' -> singleton v' × mempty
         pure (construct (via lengthDep v <> ctrl) concatLists vs)
      elements (Decl p e : gs') = do
         v <- gval <$> expr inputs e
         classes <- askClasses
         ρ' × ctrl <- destructure classes p v
         qualifiers body (after inputs ρ' ctrl) gs'

   stmt :: Inputs s -> Stmt -> m (Result s)
   stmt inputs s = result inputs s >>= case _ of
      Returns r -> Returns <$> newValue (gval r)
      Assigns ρ ctrl -> uncurry Assigns <$> newAssigns ρ ctrl

   -- Result of a statement, before vertex is allocated
   result :: Inputs s -> Stmt -> m (Result s)
   result inputs = case _ of
      Return e -> Returns <$> expr inputs e
      If bs s_opt -> go (NEL.toList bs) inputs.ctrl
         where
         go Nil ctrl = maybe (pure (Assigns empty (Just ctrl))) (branch ctrl) s_opt
         go (Branch e s' : bs') ctrl = do
            { holds, ctrl: ctrl' } <- condition (inputs { ctrl = ctrl }) e
            if holds then branch ctrl' s' else go bs' ctrl'

         branch ctrl s' = override (Assigns empty (Just ctrl)) <$> stmt (inputs { ctrl = ctrl }) s'
      Match e bs -> do
         v <- gval <$> expr inputs e
         classes <- askClasses
         case dispatch classes (NEL.toList bs) v of
            Nothing × ctrl -> pure (Assigns empty ctrl)
            Just (ρ' × s') × ctrl -> override (Assigns ρ' ctrl) <$> stmt (after inputs ρ' ctrl) s'
      Declare _ -> pure (Assigns empty Nothing)
      Assign p e -> do
         v <- gval <$> expr inputs e
         classes <- askClasses
         uncurry Assigns <$> destructure classes p v
      DefRegion ds -> pure (Assigns (closeDefs inputs ds) Nothing)
      Pass -> pure (Assigns empty Nothing)
      ExprStmt e -> expr inputs e $> Assigns empty Nothing
      Assert e e_opt -> do
         { holds, ctrl } <- condition inputs e
         if holds then pure (Assigns empty (Just ctrl))
         else case e_opt of
            Nothing -> throw "AssertionError"
            Just e' -> do
               _ × Val _ u <- expr (inputs { ctrl = ctrl }) e'
               throw ("AssertionError: " <> either (\_ -> prettyP u) identity (string.unpack u))
      Dataclass c -> do
         let v = constructFrom inputs.ctrl (const (V.Fun (V.Type (T.ClassTy c Nil)))) Nil
         pure (Assigns (maplet (last c) v) Nothing)
      TypeAlias x αs τ -> do
         let v = constructFrom inputs.ctrl (const (V.TypeAlias αs τ)) Nil
         pure (Assigns (maplet x v) Nothing)
      Seq s s' -> stmt inputs s >>= case _ of
         r@(Returns _) -> pure r
         r@(Assigns ρ ctrl) -> override r <$> stmt (after inputs ρ ctrl) s'

   program :: Inputs s -> Stmt -> m (Deriv × Raw Val)
   program inputs s = output inputs s >>= \r -> newValue (gval r) $> r
      where
      output inputs' (Seq t t') = asAssigns <$> stmt inputs' t >>= \(ρ × ctrl) -> output (after inputs' ρ ctrl) t'
      output inputs' (ExprStmt e) = expr inputs' e
      output _ _ = error absurd

   -- Apply f to vs at a new vertex
   application :: Ctrl s -> GVal s -> List (GVal s) -> m (GVal s)
   application ctrl f vs = gval <$> (apply ctrl f vs >>= newValue)

   -- Apply f to vs, partially if vs is shorter than the arity of f; apply the result to any arguments beyond
   -- the arity
   apply :: Ctrl s -> GVal s -> List (GVal s) -> m (GVal s)
   apply ctrl f vs = case raw f of
      Val _ (V.Fun (V.Partial _ us)) ->
         apply ctrl (project partialFun f) (mapWithIndex (\i _ -> project (partialArg i) f) us <> vs)
      Val _ (V.Fun φ) -> do
         n <- arity'
         let k = length vs
         if k < n then pure (partial unit)
         else if k == n then call φ vs
         else application ctrl f (take n vs) >>= \v -> apply ctrl v (drop n vs)
         where
         arity' :: m Int
         arity' = case φ of
            V.Closure _ _ (Def xs _) -> pure (length xs)
            V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
            V.Type (T.ClassTy c _) -> askClasses >>= arity c
            V.Type τ -> throw ("Not callable: " <> prettyP τ)
            V.Partial _ _ -> error absurd

         -- Partial application, with root and function part dependent on the function value, and stored
         -- arguments dependent on the argument values
         partial :: Unit -> GVal s
         partial _ = construct ctrl
            (\xs -> Val (root (head xs)) (V.Fun (V.Partial (fun (head xs)) (NEL.tail xs))))
            (NEL.cons' f vs)
      _ -> throw $ "Found " <> prettyP (raw f) <> ", expected function"
      where
      -- Apply φ to vs', taking the root of the function value as control input
      call :: V.Fun Unit -> List (GVal s) -> m (GVal s)
      call φ vs' = case φ of
         V.Closure (Env ρ1) ds (Def xs s) -> do
            let
               ρ1' = mapWithKey (\y _ -> project (closureEnv >>> get y) f) ρ1
               ρ2 = closeDefs { ctrl: ctrl', ρ: ρ1' } ds
               ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip xs vs')
            gval <<< asReturns <$> stmt { ctrl: ctrl', ρ: ρ1' <+> ρ2 <+> ρ3 } s
         V.Prim (ForeignOp (_ × ForeignOp' { depOp })) -> depOp (application ctrl') ctrl' vs'
         V.Type (T.ClassTy c _) ->
            askClasses <#> \classes -> constructFrom ctrl' (V.Obj c <<< zip (fieldNames classes c)) vs'
         V.Type _ -> error absurd
         V.Partial _ _ -> error absurd
         where
         ctrl' = via root f

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
   ρ' × _ <- asAssigns <$> eval.stmt { ctrl: mempty, ρ } s
   fst <$> newAssigns (subMods modules <+> unbound <+> ρ') Nothing
   where
   subMods modules = moduleVal <$> D.fromFoldable (submods (Map.keys modules) q)
   unbound = D.fromFoldable (L.fromFoldable (assigns s) <#> (_ × constructFrom mempty (const V.Unbound) Nil))

-- Construct members ρ of a predefined module at a new vertex
predefinedModule :: forall m s. MonadState (DepGraph Label s) m => DepSemiring s => Raw Env -> m (Dict (GVal s))
predefinedModule (Env ρ) =
   fst <$> newAssigns (ρ <#> \(Val _ u) -> constructFrom mempty (const (zeros u)) Nil) Nothing

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

moduleVal :: forall s. DepSemiring s => ModuleName -> GVal s
moduleVal q = constructFrom mempty (const (V.Module q)) Nil

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
   { g :: DepGraph Label (PosLineage DepKind)
   , out :: Deriv
   }

visible :: Eval -> Set Deriv
visible { g, out } = Map.keys g.docs ∪ Set.fromFoldable (Map.values g.docs) ∪ singleton out

-- Graph of the visible vertices, which are labelled by values
visibleGraph :: Eval -> VisibleGraph Val DepKind
visibleGraph r = graph { vals = V.value <$> graph.vals }
   where
   graph = materialise r.g (visible r)

-- Vertices documented with the name x.
documentedAs :: forall s. DepGraph Label s -> String -> Array Deriv
documentedAs g x = A.fromFoldable (Map.keys (Map.filter (\d -> valAt g d == Val unit (V.Lit (Str x))) g.docs))

evalProgram
   :: forall m
    . MonadProgram m
   => Dict (GVal (PosLineage DepKind)) -- top-level environment
   -> ClassTable
   -> Stmt
   -> m Eval
evalProgram inputs classes s =
   withClasses classes do
      { depGraph } <- moduleStore
      out × g <- flip runStateT depGraph (fst <$> eval.program { ctrl: mempty, ρ: inputs } s)
      pure { g, out }
