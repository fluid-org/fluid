module Eval.Dep where

import Prelude hiding (absurd, apply)

import Bind (dottedName, varAnon, varThis)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, fold, foldl)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..), product)
import Data.Identity (Identity(..))
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), concat, drop, elemIndex, length, take, zip, (:))
import Data.List as L
import Data.List.NonEmpty (toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DefiniteAssignment (ancestors)
import DataType (class HasClasses, ClassTable, arity, askClasses, cPair, checkArity, fieldsOf)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (GraphConfig)
import Expr (Branch(..), Def(..), Expr(..), Pattern(..), Qualifier(..), RecDefs(..), Stmt(..), fv, paramVar)
import File (class LoadFile, FileCxt, withClasses)
import Graph.Dep (DepGraph, Rel, Vertex, attachDoc, emptyGraph, sumPositions, vertex, zeros)
import Lattice (class DepSemiring, Raw, ctrlWeight, erase)
import Literal (Literal(..), eqLiteral)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Primitive (binop, binopRel, boolean, intPair, string, unop, unopRel, unpack)
import Util (type (×), absurd, check, definitely, definitely', error, orElse, orThrow, singleton, throw, withMsg, (×))
import Util.Map (get, insert, lookup, lookup', mapWithKey, maplet, restrict, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, BaseVal, Ctrl, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), GVal, MatrixDim(..), MatrixRep(..), Val(..), closureEnv, construct, constructWith, constructed, ctrlVia, deliver, dictEntry, field, forDefs, fun, gval, listElement, matrixElement, moduleStore, partialArg, partialFun, rootOf, stripDocs, via, viaAll)

type Inputs s = { ctrl :: Ctrl s, env :: Dict (GVal s) }

data Result s = Returns (Vertex × Raw Val) | Assigns (Dict (GVal s)) (Ctrl s)

asReturns :: forall s. Result s -> Vertex × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

-- Variables bound if the pattern matches the value, with the dependence of each inspected position.
matches :: forall s. ClassTable -> GVal s -> Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matches _ v (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x v) × Nil
matches _ _ PWild = Just empty × Nil
matches classes v (PAs p x) = first (map (_ `unionWith_never` maplet x v)) (matches classes v p)
matches classes v@{ val: Val _ _ u } p = second (ctrlVia rootOf v : _) case u, p of
   V.Lit ℓ', PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   V.Constr c' vs, PConstr c ps Nil
      | c `elem` ancestors (definitely "declared class" (Map.lookup (dottedName c') classes)) ->
           matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (field i) v }) (take (length ps) vs)) ps
   V.Dictionary (DictRep xvs), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs <#> \(_ × val) -> x × { val, inEdges: via (dictEntry x >>> snd) v } × p') xps of
         Just kvs -> second ((kvs <#> \(x × _) -> ctrlVia (dictEntry x >>> fst) v) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   V.List vs, PList ps | A.length vs == length ps ->
      matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (listElement i) v }) (L.fromFoldable vs)) ps
   _, _ -> Nothing × Nil

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
   clo ρ' = Val zero Nothing (V.Fun (V.Closure (Env ρ') ds d))

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict Def -> Dict (GVal s)
closeDefs inputs ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      constructed inputs.ctrl (closure (restrict (fv ds' ∪ fv d) inputs.env) ds' d)

-- Dictionary from keys and values; later entries overwrite earlier ones.
dictionary
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> List (String × GVal s × GVal s)
   -> m (Vertex × Raw Val)
dictionary ctrl kvs = construct ctrl { val: Val unit Nothing (V.Dictionary (DictRep d)), inEdges }
   where
   winners = Map.toUnfoldable (Map.fromFoldable kvs) :: List (String × GVal s × GVal s)
   d = D.fromFoldable (winners <#> \(k × _ × v) -> k × (unit × v.val))
   zd = (\(_ × u) -> zero × zeros u) <$> d

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   inEdges = concat $ winners <#> \(k × key × v) ->
      via (\x -> dict (insert k (rootOf x × zeros v.val) zd)) key
         <> via (\y -> dict (insert k (zero × y) zd)) v

-- ======================
-- Evaluation
-- ======================

eval
   :: forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Inputs s
   -> Expr
   -> m (Vertex × Raw Val)
eval inputs = case _ of
   Var x -> deliver inputs.ctrl (get x inputs.env)
   Lit ℓ -> construct inputs.ctrl { val: Val unit Nothing (V.Lit ℓ), inEdges: Nil }
   Dictionary ees -> do
      kvs <- for ees \(Pair e e') -> do
         k <- eval inputs e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs e'
         pure (s × gval k × gval u)
      dictionary inputs.ctrl kvs
   DictComp e e' gs -> do
      cs × ctrl <- qualifiers inputs gs
      kvs <- for cs \inputs' -> do
         k <- eval inputs' e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs' e'
         pure (s × gval k × gval u)
      dictionary ctrl kvs
   List es -> do
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.List) vs
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
      (i' × _) × (j' × _) <- orThrow (unpack intPair dims.val) <#> fst
      check
         (i' × j' >= 1 × 1)
         ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
      vss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
         let ρ' = maplet x (index dims 0 i) `unionWith_never` maplet y (index dims 1 j)
         gval <$> eval (inputs { env = inputs.env <+> ρ' }) e
      constructWith inputs.ctrl (mat i' j') (product (Compose vss) (Identity dims))
      where
      index :: GVal s -> Int -> Int -> GVal s
      index dims k n =
         { val: Val unit Nothing (V.Lit (Int n))
         , inEdges: via (\p -> Val (ctrlWeight * rootOf (field k p)) Nothing (V.Lit (Int n))) dims
         }

      mat :: forall a. Int -> Int -> Product (Compose Array Array) Identity (Val a) -> BaseVal a
      mat i j (Product (Compose vss × Identity p)) =
         V.Matrix (MatrixRep (vss × MatrixDim (i × rootOf (field 0 p)) × MatrixDim (j × rootOf (field 1 p))))
   Lambda d -> construct inputs.ctrl (closure (restrict (fv d) inputs.env) empty d)
   Attribute e x -> do
      v <- gval <$> eval inputs e
      case v.val of
         Val _ _ (V.Constr c _) -> do
            xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
            i <- elemIndex x xs # orElse (dottedName c <> " has no field " <> x)
            deliver (inputs.ctrl <> ctrlVia rootOf v) { val: field i v.val, inEdges: via (field i) v }
         _ -> throw $ "Found " <> prettyP v.val <> ", expected object"
   Subscript e e' -> do
      v@{ val: Val _ _ u } <- gval <$> eval inputs e
      v'@{ val: Val _ _ u' } <- gval <$> eval inputs e'
      case u, u' of
         V.Dictionary (DictRep d), V.Lit (Str s) -> do
            _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
            subscript v v' (dictEntry s >>> snd) (\z -> rootOf z + fst (dictEntry s z))
         V.Dictionary _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected str"
         V.List vs, V.Lit (Int i) -> do
            let i' = if i < 0 then A.length vs + i else i
            _ <- vs A.!! i' # orElse ("List index " <> show i <> " out of range")
            subscript v v' (listElement i') rootOf
         V.List _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
         V.Matrix _, V.Constr c (Val _ _ (V.Lit (Int i)) : Val _ _ (V.Lit (Int j)) : Nil) | c == cPair ->
            subscript v v' (matrixElement i j) rootOf
         V.Matrix _, _ -> throw $ "Found " <> prettyP v'.val <> ", expected pair of int"
         _, _ -> throw $ "Found " <> prettyP v.val <> ", expected list, dict or matrix"
      where
      -- Element selected from the container, depending at weight c on the consumed positions and the index.
      subscript :: GVal s -> GVal s -> (forall a. Val a -> Val a) -> Rel (Val s) s -> m (Vertex × Raw Val)
      subscript v v' select consumed =
         deliver (inputs.ctrl <> ctrlVia consumed v <> ctrlVia sumPositions v') { val: select v.val, inEdges: via select v }
   ModMember q x -> do
      { moduleEnv } <- moduleStore
      let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
      u <- withMsg "Module member" $ lookup' x ρ_q
      deliver inputs.ctrl { val: stripDocs (erase u), inEdges: Nil }
   App e es -> do
      f <- gval <$> eval inputs e
      vs <- traverse (eval inputs >>> map gval) es
      withMsg ("In " <> funName e) $ apply inputs.ctrl f vs
   BinOp e op e' -> do
      v <- gval <$> eval inputs e
      v' <- gval <$> eval inputs e'
      u <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op v.val v'.val) <#> fst
      let rel x y = binopRel op x y # either (\_ -> error absurd) identity
      deliver inputs.ctrl
         { val: Val unit Nothing u
         , inEdges: via (\x -> rel x (zeros v'.val)) v <> via (\y -> rel (zeros v.val) y) v'
         }
   UnOp op e -> do
      v <- gval <$> eval inputs e
      u <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op v.val) <#> fst
      deliver inputs.ctrl { val: Val unit Nothing u, inEdges: via (unopRel op >>> either (\_ -> error absurd) identity) v }
   And e e' -> do
      p × val <- eval inputs e
      b × _ <- orThrow (unpack boolean val)
      if b then eval (inputs { ctrl = singleton (p × rootOf) }) e' else pure (p × val)
   Or e e' -> do
      p × val <- eval inputs e
      b × _ <- orThrow (unpack boolean val)
      if b then pure (p × val) else eval (inputs { ctrl = singleton (p × rootOf) }) e'
   Cond e1 e e2 -> do
      p × val <- eval inputs e
      b × _ <- orThrow (unpack boolean val)
      eval (inputs { ctrl = singleton (p × rootOf) }) (if b then e1 else e2)
   DocExpr e e' -> do
      r <- eval inputs e'
      doc <- eval (inputs { env = inputs.env <+> maplet varThis (gval r) }) e
      attachDoc (fst r) (fst doc)
      pure r
   where
   funName :: Expr -> String
   funName (Var x) = x
   funName (App e _) = funName e
   funName _ = "unknown"

-- Inputs for each pass through the qualifiers, with the control consumed on every pass, including those cut
-- short by a failed guard or an element that does not match.
qualifiers
   :: forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Inputs s
   -> List Qualifier
   -> m (List (Inputs s) × Ctrl s)
qualifiers inputs Nil = pure (singleton inputs × inputs.ctrl)
qualifiers inputs (Guard e : gs) = do
   p × val <- eval inputs e
   b × _ <- orThrow (unpack boolean val)
   let ctrl = singleton (p × rootOf)
   if b then qualifiers (inputs { ctrl = ctrl }) gs else pure (Nil × ctrl)
qualifiers inputs (Generator p e : gs) = do
   v <- gval <$> eval inputs e
   us <- case v.val of
      Val _ _ (V.List us) -> pure us
      _ -> throw $ "Found " <> prettyP v.val <> ", expected list"
   classes <- askClasses
   fold <$> for (mapWithIndex const (L.fromFoldable us)) \i -> do
      let el = { val: listElement i v.val, inEdges: via (listElement i) v }
      case dispatch classes (singleton (p × unit)) el Nil of
         Nothing × ctrl -> pure (Nil × (ctrlVia rootOf v <> ctrl))
         Just (ρ' × _) × ctrl -> qualifiers (inputs { env = inputs.env <+> ρ', ctrl = ctrlVia rootOf v <> ctrl }) gs
qualifiers inputs (Decl p e : gs) = do
   v <- gval <$> eval inputs e
   classes <- askClasses
   ρ' × ctrl <- destructure classes p v inputs.ctrl
   qualifiers (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) gs

evalStmt
   :: forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Inputs s
   -> Stmt
   -> m (Result s)
evalStmt inputs = case _ of
   Return e -> Returns <$> eval inputs e
   If bs s_opt -> go (NEL.toList bs) inputs.ctrl
      where
      go Nil ctrl = maybe (pure (Assigns empty ctrl)) (evalStmt (inputs { ctrl = ctrl })) s_opt
      go (Branch e s' : bs') ctrl = do
         p × val <- eval (inputs { ctrl = ctrl }) e
         b × _ <- orThrow (unpack boolean val)
         let ctrl' = singleton (p × rootOf)
         if b then evalStmt (inputs { ctrl = ctrl' }) s' else go bs' ctrl'
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
      p × val <- eval inputs e
      b × _ <- orThrow (unpack boolean val)
      let ctrl = singleton (p × rootOf)
      if b then pure (Assigns empty ctrl)
      else case e_opt of
         Nothing -> throw "AssertionError"
         Just e' -> do
            _ × Val _ _ w <- eval (inputs { ctrl = ctrl }) e'
            throw ("AssertionError: " <> either (\_ -> prettyP w) identity (string.unpack w))
   Seq s1 s2 -> do
      r1 <- evalStmt inputs s1
      case r1 of
         Returns _ -> pure r1
         Assigns ρ' ctrl -> evalStmt (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) s2

-- Fewer arguments than the arity is a partial application; more applies the result to the rest.
apply
   :: forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> GVal s
   -> List (GVal s)
   -> m (Vertex × Raw Val)
apply ctrl f@{ val: Val _ _ u } vs = case u of
   V.Fun (V.Partial φ us) ->
      apply ctrl { val: Val unit Nothing (V.Fun φ), inEdges: via partialFun f }
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
         { val: Val unit Nothing (V.Fun (V.Partial φ (_.val <$> vs)))
         , inEdges: via (\x -> Val (rootOf x) Nothing (V.Fun (V.Partial (fun x) (zeros <<< _.val <$> vs)))) f
              <> viaAll (V.Partial (zeros φ) >>> V.Fun >>> Val zero Nothing) vs
         }
   _ -> throw $ "Found " <> prettyP f.val <> ", expected function"
   where
   -- Applying a function consumes its root.
   call :: V.Fun Unit -> List (GVal s) -> m (Vertex × Raw Val)
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
      ctrl' = ctrlVia rootOf f

type DepEval s =
   { g :: DepGraph Val s
   , inputs :: Dict Vertex
   , root :: Vertex
   }

depEval
   :: forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => DepSemiring s
   => GraphConfig
   -> Stmt
   -> m (DepEval s)
depEval { ρ, classes } s =
   withClasses classes do
      (root × inputs) × g <- flip runStateT emptyGraph do
         ins <- for (unwrap (erase ρ) :: Dict (Raw Val)) \v -> vertex (stripDocs v) <#> (_ × stripDocs v)
         r <- evalStmt { ctrl: Nil, env: gval <$> ins } s
         pure (fst (asReturns r) × (fst <$> ins))
      pure { g, inputs, root }
