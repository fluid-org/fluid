module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon, varThis)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.State (runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldM, foldl, sum)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..), product)
import Data.Identity (Identity(..))
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), concat, drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (fromList, head, last, snoc, toList, unsnoc) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DefiniteAssignment (ancestors)
import DataType (class HasClasses, ClassTable, arity, askClasses, checkArity, fieldsOf)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Branch(..), Def(..), Expr(..), Import(..), Module(..), Pattern(..), Qualifier(..), RecDefs(..), Stmt(..), fv, paramVar)
import File (class LoadFile, FileCxt, withClasses)
import DepGraph (DepGraph, Rel, Deriv, Pos, attachDoc, deriv, zeros)
import Lattice (class DepSemiring, DepKind, Lineage, Raw, ctrlWeight)
import Literal (Literal(..), eqLiteral)
import ModuleGraph (ModuleName, implicit, submodules)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Primitive (binop, binopRel, boolean, int, string, typeMismatch, unop, unopRel, unpack, unpackVal)
import Util (type (×), absurd, check, definitely', definitelyRight, error, orElse, orThrow, singleton, throw, withMsg, (×))
import Util.Map (get, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, class MonadEval, BaseVal, Ctrl, ModuleState(..), loadedEnv, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), GVal, MatrixRep(..), Val(..), closureEnv, construct, constructWith, constructed, deliver, dictEntry, dictionary, field, forDefs, fun, gval, gvalAt, element, elementCount, lengthDep, matrixElement, modifyModuleStore, moduleStore, partialArg, partialFun, record, root, via, viaAll)

type Inputs s = { ctrl :: Ctrl s, env :: Dict (GVal s) }

data Result s = Returns (Deriv × Raw Val) | Assigns (Dict (GVal s)) (Ctrl s)

asReturns :: forall s. Result s -> Deriv × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: forall s. Result s -> Dict (GVal s) × Ctrl s
asAssigns (Assigns ρ ctrl) = ρ × ctrl
asAssigns (Returns _) = error "Assigns expected"

-- Variables bound if the pattern matches the value, with the dependence of each inspected position.
matches :: forall s. ClassTable -> GVal s -> Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matches _ v (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x v) × Nil
matches _ _ PWild = Just empty × Nil
matches classes v (PAs p x) = first (map (_ `unionWith_never` maplet x v)) (matches classes v p)
matches classes v@{ val: Val _ u } p = second (via root v : _) case u, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Constr c' vs, PConstr c ps Nil
      | c `elem` ancestors (get (dottedName c') classes) ->
           matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (field i) v }) (take (length ps) vs)) ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs <#> \(_ × val) -> x × { val, inEdges: via (dictEntry x >>> snd) v } × p') xps of
         Just kvs -> second ((kvs <#> \(x × _) -> via (dictEntry x >>> fst) v) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps -> matchesElements vs ps
   V.Tuple vs, PTuple ps | A.length vs == length ps -> matchesElements vs ps
   _, _ -> Nothing × Nil
   where
   matchesElements vs ps = matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (element i) v }) (L.fromFoldable vs)) ps

matchesMany :: forall s. ClassTable -> List (GVal s) -> List Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matchesMany _ Nil Nil = Just empty × Nil
matchesMany classes (v : vs) (p : ps) = case matches classes v p of
   Nothing × ctrls -> Nothing × ctrls
   Just ρ × ctrls -> case matchesMany classes vs ps of
      Nothing × ctrls' -> Nothing × (ctrls <> ctrls')
      Just ρ' × ctrls' -> Just (ρ `unionWith_never` ρ') × (ctrls <> ctrls')
matchesMany _ _ _ = error absurd

-- Bindings of the first case whose pattern matches, with the control input afterwards: the positions inspected
-- by the cases tried, or unchanged if nothing is inspected.
dispatch :: forall s b. ClassTable -> List (Pattern × b) -> GVal s -> Ctrl s -> Maybe (Dict (GVal s) × b) × Ctrl s
dispatch _ Nil _ ctrl = Nothing × ctrl
dispatch classes ((p × b) : cases) v ctrl = case matches classes v p of
   Just ρ × Nil -> Just (ρ × b) × ctrl
   Just ρ × ctrls -> Just (ρ × b) × concat ctrls
   Nothing × ctrls -> second (concat ctrls <> _) (dispatch classes cases v Nil)

-- dispatch on a single pattern, which must match.
destructure :: forall m s. MonadError Error m => ClassTable -> Pattern -> GVal s -> Ctrl s -> m (Dict (GVal s) × Ctrl s)
destructure classes p v ctrl = case dispatch classes (singleton (p × unit)) v ctrl of
   Just (ρ × _) × ctrl' -> pure (ρ × ctrl')
   Nothing × _ -> throw ("Pattern mismatch: " <> prettyP v.val <> " does not match " <> prettyP p)

closure :: forall s. Semiring s => Dict (GVal s) -> Dict Def -> Def -> GVal s
closure ρ ds d = { val: clo (_.val <$> ρ), inEdges: viaAll clo ρ }
   where
   clo :: forall a. Semiring a => Dict (Val a) -> Val a
   clo ρ' = Val zero (V.Fun (V.Closure (Env ρ') ds d))

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict Def -> Dict (GVal s)
closeDefs inputs ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      constructed inputs.ctrl (closure (restrict (fv ds' ∪ fv d) inputs.env) ds' d)

-- ======================
-- Evaluation
-- ======================

eval
   :: forall m s
    . MonadEval s m
   => Inputs s
   -> Expr
   -> m (Deriv × Raw Val)
eval inputs = case _ of
   Var x -> deliver inputs.ctrl (get x inputs.env)
   Lit ℓ -> construct inputs.ctrl { val: Val unit (V.Lit ℓ), inEdges: Nil }
   Dictionary ees -> do
      kvs <- for ees \(Pair e e') -> evalEntry inputs e e'
      dictionary inputs.ctrl kvs
   DictComp e e' gs -> do
      cs × ctrl <- qualifiers inputs gs
      kvs <- for cs \inputs' -> evalEntry inputs' e e'
      dictionary ctrl kvs
   List es -> do
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.List) vs
   Tuple es -> do
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.Tuple) vs
   ListComp e gs -> do
      cs × ctrl <- qualifiers inputs gs
      vs <- for cs \inputs' -> gval <$> eval inputs' e
      constructWith ctrl (A.fromFoldable >>> V.List) vs
   Constr c es -> do
      askClasses >>= checkArity (dottedName c) (length es)
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (V.Constr c) vs
   Matrix e (x × y) e' -> do
      dims <- gval <$> eval inputs e'
      i' × j' <- case dims.val of
         Val _ (V.Tuple [ Val _ (V.Lit (Int i')), Val _ (V.Lit (Int j')) ]) -> pure (i' × j')
         Val _ u -> throw (typeMismatch u "pair of int")
      check
         (i' × j' >= 1 × 1)
         ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
      vss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
         let ρ' = maplet x (index dims 0 i) `unionWith_never` maplet y (index dims 1 j)
         gval <$> eval (inputs { env = inputs.env <+> ρ' }) e
      constructWith inputs.ctrl mat (product (Compose vss) (Identity dims))
      where
      index :: GVal s -> Int -> Int -> GVal s
      index dims k n =
         { val: Val unit (V.Lit (Int n))
         , inEdges: via (\p -> Val (ctrlWeight * root (element k p)) (V.Lit (Int n))) dims
         }

      mat :: forall a. Product (Compose Array Array) Identity (Val a) -> BaseVal a
      mat (Product (Compose vss × Identity p)) = V.Matrix (MatrixRep (vss × element 0 p × element 1 p))
   Lambda d -> construct inputs.ctrl (closure (restrict (fv d) inputs.env) empty d)
   Attribute e x -> do
      v <- gval <$> eval inputs e
      case v.val of
         Val _ (V.Constr c _) -> do
            xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
            i <- elemIndex x xs # orElse (dottedName c <> " has no field " <> x)
            deliver (inputs.ctrl <> via root v) { val: field i v.val, inEdges: via (field i) v }
         _ -> throw $ "Found " <> prettyP v.val <> ", expected object"
   Subscript e e' -> do
      v@{ val: Val _ u } <- gval <$> eval inputs e
      v'@{ val: Val _ u' } <- gval <$> eval inputs e'
      case u, u' of
         V.Dictionary (DictRep d), V.Lit (Str s) -> do
            _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
            subscript v v' (dictEntry s >>> snd) (\z -> root z + fst (dictEntry s z))
         V.Dictionary _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected str"
         _, V.Lit (Int i) | Just n <- elementCount v.val -> do
            let i' = if i < 0 then n + i else i
            unless (0 <= i' && i' < n) $ throw ("Index " <> show i <> " out of range")
            subscript v v' (element i') root
         V.List _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
         V.Tuple _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
         V.Lit (Str _), _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
         V.Matrix (MatrixRep (_ × m × n)), V.Tuple [ Val _ (V.Lit (Int i)), Val _ (V.Lit (Int j)) ] -> do
            unless (0 <= i && i < unpackVal int m && 0 <= j && j < unpackVal int n) $ throw ("Index (" <> show i <> ", " <> show j <> ") out of range")
            subscript v v' (matrixElement i j) root
         V.Matrix _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected pair of int"
         _, _ -> throw $ "Found " <> prettyP v.val <> ", expected list, tuple, str, dict or matrix"
      where
      -- Element selected from the container, depending at weight c on the consumed positions and the index.
      subscript :: GVal s -> GVal s -> (forall a. Val a -> Val a) -> Rel (Val s) s -> m (Deriv × Raw Val)
      subscript v v' select consumed =
         deliver (inputs.ctrl <> via consumed v <> via sum v') { val: select v.val, inEdges: via select v }
   ModMember q x -> do
      { modules } <- moduleStore
      let ρ_q = definitely' (loadedEnv (get q modules))
      p <- withMsg "Module member" $ lookup' x ρ_q
      gvalAt p >>= deliver inputs.ctrl
   App e es -> do
      f <- gval <$> eval inputs e
      vs <- traverse (eval inputs >>> map gval) es
      withMsg ("In " <> funName e) $ apply inputs.ctrl f vs
   BinOp e op e' -> do
      v <- gval <$> eval inputs e
      v' <- gval <$> eval inputs e'
      u <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op v.val v'.val) <#> fst
      let depRel x y = definitelyRight (binopRel op x y)
      deliver inputs.ctrl
         { val: Val unit u
         , inEdges: via (\x -> depRel x (zeros v'.val)) v <> via (\y -> depRel (zeros v.val) y) v'
         }
   UnOp op e -> do
      v <- gval <$> eval inputs e
      u <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op v.val) <#> fst
      deliver inputs.ctrl { val: Val unit u, inEdges: via (unopRel op >>> definitelyRight) v }
   And e e' -> do
      { holds, ctrl, value } <- condition inputs e
      if holds then eval (inputs { ctrl = ctrl }) e' else pure value
   Or e e' -> do
      { holds, ctrl, value } <- condition inputs e
      if holds then pure value else eval (inputs { ctrl = ctrl }) e'
   Cond e1 e e2 -> do
      { holds, ctrl } <- condition inputs e
      eval (inputs { ctrl = ctrl }) (if holds then e1 else e2)
   DocExpr e e' -> do
      r <- eval inputs e'
      doc <- eval (inputs { env = inputs.env <+> maplet varThis (gval r) }) e
      attachDoc (fst r) (fst doc)
      pure r
   where
   evalEntry :: Inputs s -> Expr -> Expr -> m (String × GVal s × GVal s)
   evalEntry inputs' e e' = do
      k <- eval inputs' e
      s <- orThrow (unpack string (snd k)) <#> fst
      u <- eval inputs' e'
      pure (s × gval k × gval u)

   funName :: Expr -> String
   funName (Var x) = x
   funName (App e _) = funName e
   funName _ = "unknown"

-- Condition as a Boolean; its root is the control input for what follows.
condition
   :: forall m s
    . MonadEval s m
   => Inputs s
   -> Expr
   -> m { holds :: Boolean, ctrl :: Ctrl s, value :: Deriv × Raw Val }
condition inputs e = do
   p × val <- eval inputs e
   holds × _ <- orThrow (unpack boolean val)
   pure { holds, ctrl: singleton (p × root), value: p × val }

-- Inputs for each pass through the qualifiers, with the control consumed on every pass, including those cut
-- short by a failed guard or an element that does not match.
qualifiers
   :: forall m s
    . MonadEval s m
   => Inputs s
   -> List Qualifier
   -> m (List (Inputs s) × Ctrl s)
qualifiers inputs Nil = pure (singleton inputs × inputs.ctrl)
qualifiers inputs (Guard e : gs) = do
   { holds, ctrl } <- condition inputs e
   if holds then qualifiers (inputs { ctrl = ctrl }) gs else pure (Nil × ctrl)
qualifiers inputs (Generator p e : gs) = do
   v <- gval <$> eval inputs e
   n <- elementCount v.val # orElse ("Found " <> prettyP v.val <> ", expected list, tuple, str or dict")
   classes <- askClasses
   fold <$> for (L.take n (L.range 0 n)) \i -> do
      let el = { val: element i v.val, inEdges: via (element i) v }
      case dispatch classes (singleton (p × unit)) el Nil of
         Nothing × ctrl -> pure (Nil × (via lengthDep v <> ctrl))
         Just (ρ' × _) × ctrl -> qualifiers (inputs { env = inputs.env <+> ρ', ctrl = via lengthDep v <> ctrl }) gs
qualifiers inputs (Decl p e : gs) = do
   v <- gval <$> eval inputs e
   classes <- askClasses
   ρ' × ctrl <- destructure classes p v inputs.ctrl
   qualifiers (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) gs

evalStmt
   :: forall m s
    . MonadEval s m
   => Inputs s
   -> Stmt
   -> m (Result s)
evalStmt inputs = case _ of
   Return e -> Returns <$> eval inputs e
   If bs s_opt -> go (NEL.toList bs) inputs.ctrl
      where
      go Nil ctrl = maybe (pure (Assigns empty ctrl)) (evalStmt (inputs { ctrl = ctrl })) s_opt
      go (Branch e s' : bs') ctrl = do
         { holds, ctrl: ctrl' } <- condition (inputs { ctrl = ctrl }) e
         if holds then evalStmt (inputs { ctrl = ctrl' }) s' else go bs' ctrl'
   Match e bs -> do
      v <- gval <$> eval inputs e
      classes <- askClasses
      case dispatch classes (NEL.toList bs) v inputs.ctrl of
         Nothing × ctrl -> pure (Assigns empty ctrl)
         Just (ρ' × s') × ctrl -> do
            r <- evalStmt (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) s'
            case r of
               Returns _ -> pure r
               Assigns ρ'' ctrl' -> pure (Assigns (ρ' <+> ρ'') ctrl')
   Assign p _ e -> do
      v <- gval <$> eval inputs e
      classes <- askClasses
      ρ' × ctrl <- destructure classes p v inputs.ctrl
      pure (Assigns ρ' ctrl)
   DefRec (RecDefs ds) -> pure (Assigns (closeDefs inputs ds) inputs.ctrl)
   Pass -> pure (Assigns empty inputs.ctrl)
   ExprStmt e -> eval inputs e $> Assigns empty inputs.ctrl
   Assert e e_opt -> do
      { holds, ctrl } <- condition inputs e
      if holds then pure (Assigns empty ctrl)
      else case e_opt of
         Nothing -> throw "AssertionError"
         Just e' -> do
            _ × Val _ w <- eval (inputs { ctrl = ctrl }) e'
            throw ("AssertionError: " <> either (\_ -> prettyP w) identity (string.unpack w))
   Dataclass c ->
      pure (Assigns (maplet (NEL.last c) (constructed inputs.ctrl { val: Val unit (V.Fun (V.Type c)), inEdges: Nil })) inputs.ctrl)
   Seq s1 s2 -> do
      r1 <- evalStmt inputs s1
      case r1 of
         Returns _ -> pure r1
         Assigns ρ' ctrl -> evalStmt (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) s2

-- Fewer arguments than the arity is a partial application; more applies the result to the rest.
apply
   :: forall m s
    . MonadEval s m
   => Ctrl s
   -> GVal s
   -> List (GVal s)
   -> m (Deriv × Raw Val)
apply ctrl f@{ val: Val _ u } vs = case u of
   V.Fun (V.Partial φ us) ->
      apply ctrl { val: Val unit (V.Fun φ), inEdges: via partialFun f }
         (mapWithIndex (\i val -> { val, inEdges: via (partialArg i) f }) us <> vs)
   V.Fun φ -> do
      n <- arity'
      let k = length vs
      if k < n then construct ctrl partial
      else if k == n then call φ vs
      else call φ (take n vs) >>= \r -> apply ctrl (gval r) (drop n vs)
      where
      arity' :: m Int
      arity' = case φ of
         V.Closure _ _ (Def xs _ _) -> pure (length xs)
         V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
         V.Type c -> askClasses >>= arity (dottedName c)
         V.Partial _ _ -> error absurd

      -- Partial application of f to vs, with root and function depending on those of f, and arguments depending on vs.
      partial :: GVal s
      partial =
         { val: Val unit (V.Fun (V.Partial φ (_.val <$> vs)))
         , inEdges: via (\x -> Val (root x) (V.Fun (V.Partial (fun x) (zeros <<< _.val <$> vs)))) f
              <> viaAll (V.Partial (zeros φ) >>> V.Fun >>> Val zero) vs
         }
   _ -> throw $ "Found " <> prettyP f.val <> ", expected function"
   where
   -- Applying a function consumes its root.
   call :: V.Fun Unit -> List (GVal s) -> m (Deriv × Raw Val)
   call φ vs' = case φ of
      V.Closure (Env ρ1) ds (Def xs _ s) -> do
         let
            ρ1' = mapWithKey (\y val -> { val, inEdges: via (closureEnv >>> get y) f }) ρ1
            ρ2 = closeDefs { ctrl: ctrl', env: ρ1' } ds
            ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip (paramVar <$> xs) vs')
         asReturns <$> evalStmt { ctrl: ctrl', env: ρ1' <+> ρ2 <+> ρ3 } s
      V.Prim (ForeignOp (_ × ForeignOp' { depOp })) -> depOp ctrl' vs'
      V.Type c -> constructWith ctrl' (V.Constr c) vs'
      V.Partial _ _ -> error absurd
      where
      ctrl' = via root f

evalModule
   :: forall m s
    . MonadEval s m
   => Dict Deriv
   -> ModuleName
   -> Module
   -> m (Dict Deriv)
evalModule ρ0 q (Module is ss) = do
   ρ_imp <- foldM (evalImport q) ρ0 is
   ρ_name <- maplet "__name__" <$> deriv (Val unit (V.Lit (Str (dottedName q))))
   { modules } <- moduleStore
   ρ_subs <- traverse moduleVal (D.fromFoldable (submodules (Map.keys modules) q))
   ρ <- traverse gvalAt (ρ_imp <+> ρ_name)
   bindings × _ <- foldM (\(ρ' × ctrl) s -> asAssigns <$> evalStmt { ctrl, env: ρ <+> ρ' } s <#> first (ρ' <+> _)) (empty × Nil) ss
   members <- traverse (record >>> map fst) bindings
   pure (ρ_name <+> ρ_subs <+> members)

-- Bind imported members, and names of imported modules to module values.
evalImport
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> Dict Deriv
   -> Import
   -> m (Dict Deriv)
evalImport enclosing ρ = case _ of
   Import q Nothing -> do
      _ <- load q
      loadAncestors Nothing q
      maplet (NEL.head q) <$> moduleVal (pure (NEL.head q)) <#> (ρ <+> _)
   Import q (Just xs) -> do
      ρ_q <- load q
      loadAncestors (Just enclosing) q
      importsFrom q ρ_q ρ xs
   where
   loadAncestors bound q = case NEL.fromList (NEL.unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q ρ_q = foldM step
      where
      step ρ' x = do
         { modules } <- moduleStore
         when (Map.member (NEL.snoc q x) modules) (void (load (NEL.snoc q x)))
         pure (ρ' <+> maplet x (get x ρ_q))

moduleVal :: forall m s. MonadEval s m => ModuleName -> m Deriv
moduleVal q = deriv (Val unit (V.Module q))

-- Members of the implicit modules loaded so far.
implicitMembers :: forall m. HasModuleStore m => m (Dict Deriv)
implicitMembers = moduleStore <#> \{ modules } ->
   foldl (\ρ q -> ρ <+> fromMaybe empty (Map.lookup q modules >>= loadedEnv)) empty implicit

load
   :: forall m s
    . MonadEval s m
   => ModuleName
   -> m (Dict Deriv)
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
   { g :: DepGraph Val (Lineage (Deriv × Pos) DepKind)
   , inputs :: Dict Deriv
   , root :: Deriv
   }

-- Documented vertices, their docs and the root.
visible :: Eval -> Set Deriv
visible { g, root } = Map.keys g.docs ∪ Set.fromFoldable (Map.values g.docs) ∪ Set.singleton root

evalProgram
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => Dict Deriv -- top-level environment, as vertices of the module store's dependence graph
   -> ClassTable
   -> Stmt
   -> m Eval
evalProgram inputs classes s =
   withClasses classes do
      { depGraph } <- moduleStore
      p × g <- flip runStateT depGraph do
         env <- traverse gvalAt inputs
         fst <<< asReturns <$> evalStmt { ctrl: Nil, env } s
      pure { g, inputs, root: p }
