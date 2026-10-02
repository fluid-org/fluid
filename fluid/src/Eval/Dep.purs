module Eval.Dep where

import Prelude hiding (absurd, apply)

import Bind (dottedName, varAnon)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (elem, foldM, foldl, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), concat, drop, elemIndex, length, take, updateAt, zip, (:))
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
import Graph.Dep (DepGraph, Rel, Vertex, attachDoc, edge, emptyGraph, plus, scale, sumPositions, vertex, zeros)
import Lattice (class DepSemiring, Raw, ctrlWeight, erase)
import Literal (Literal(..), eqLiteral)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Primitive (binop, binopRel, boolean, intPair, string, unop, unopRel, unpack)
import Util (type (×), absurd, check, definitely, definitely', error, orElse, orThrow, singleton, throw, withMsg, (×))
import Util.Map (get, insert, lookup, lookup', mapWithKey, maplet, restrict, toUnfoldable, unionWith_never, (<+>))
import Util.Pair (Pair(..))
import Util.Set (empty, (∪))
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, BaseVal, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), MatrixDim(..), MatrixRep(..), PrimRel(..), PrimRelAt(..), Val(..), closureEnv, dictEntries, dictEntry, field, forDefs, fun, listElement, matrixElement, matrixPut, moduleStore, partialArg, partialFun, rootOf, stripDocs)

type InEdges s = List (Vertex × Rel (Val s) (Val s))
-- Value together with its dependence on values already in the graph.
type GVal s = { val :: Raw Val, inEdges :: InEdges s }
-- Dependence of the control input on values already in the graph.
type Ctrl s = List (Vertex × Rel (Val s) s)
type Inputs s = { ctrl :: Ctrl s, env :: Dict (GVal s) }

data Result s = Returns (Vertex × Raw Val) | Assigns (Dict (GVal s)) (Ctrl s)

asReturns :: forall s. Result s -> Vertex × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

-- Weight 1 at every position except beneath the root of a closure.
unitSection :: forall s. Semiring s => Raw Val -> Val s
unitSection (Val _ _ u) = Val one Nothing case u of
   V.Lit ℓ -> V.Lit ℓ
   V.Constr c vs -> V.Constr c (unitSection <$> vs)
   V.List vs -> V.List (unitSection <$> vs)
   V.Dictionary (DictRep d) -> V.Dictionary (DictRep ((\(_ × v) -> one × unitSection v) <$> d))
   V.Matrix (MatrixRep (vss × MatrixDim (i × _) × MatrixDim (j × _))) ->
      V.Matrix (MatrixRep (map (map unitSection) vss × MatrixDim (i × one) × MatrixDim (j × one)))
   V.Fun φ -> V.Fun (zeros φ)

gval :: forall s. Vertex × Raw Val -> GVal s
gval (p × val) = { val, inEdges: singleton (p × identity) }

-- Dependence on values already in the graph of a value that depends on v by r.
via :: forall s. Rel (Val s) (Val s) -> GVal s -> InEdges s
via r v = second (r <<< _) <$> v.inEdges

-- Dependence on values already in the graph of a value that depends on vs by r.
viaAll :: forall s. Semiring s => Rel (List (Val s)) (Val s) -> List (GVal s) -> InEdges s
viaAll r vs = concat (mapWithIndex (\i v -> via (\x -> r (definitely' (updateAt i x zs))) v) vs)
   where
   zs = zeros <<< _.val <$> vs

ctrlVia :: forall s. Rel (Val s) s -> GVal s -> Ctrl s
ctrlVia r v = second (r <<< _) <$> v.inEdges

-- Adds dependence on control at weight c to the positions of v in the given section.
withCtrl :: forall s. DepSemiring s => Ctrl s -> Val s -> GVal s -> GVal s
withCtrl ctrl section v =
   v { inEdges = v.inEdges <> (ctrl <#> second \r x -> scale (ctrlWeight * r x) section) }

-- Constructed value: root depends on control at weight c.
constructed :: forall s. DepSemiring s => Ctrl s -> GVal s -> GVal s
constructed ctrl v@{ val: Val _ _ u } = withCtrl ctrl (Val one Nothing (zeros u)) v

-- Variables bound if the pattern matches the value, with the dependence of each inspected position.
matches :: forall s. ClassTable -> GVal s -> Pattern -> Maybe (Dict (GVal s)) × List (Ctrl s)
matches _ v (PVar x)
   | x == varAnon = Just empty × Nil
   | otherwise = Just (maplet x v) × Nil
matches _ _ PWild = Just empty × Nil
matches classes v (PAs p x) = first (map (_ `unionWith_never` maplet x v)) (matches classes v p)
matches classes v p = second (ctrlVia rootOf v : _) case v.val, p of
   Val _ _ (V.Lit ℓ'), PLit ℓ | eqLiteral ℓ ℓ' -> Just empty × Nil
   Val _ _ (V.Constr c' vs), PConstr c ps Nil
      | c `elem` ancestors (definitely "declared class" (Map.lookup (dottedName c') classes)) ->
           matchesMany classes (mapWithIndex (\i val -> { val, inEdges: via (field i) v }) (take (length ps) vs)) ps
   Val _ _ (V.Dictionary (DictRep xvs)), PRecord xps ->
      case traverse (\(x × p') -> lookup x xvs <#> \(_ × val) -> x × { val, inEdges: via (dictEntry x >>> snd) v } × p') xps of
         Just kvs -> second ((kvs <#> \(x × _) -> ctrlVia (dictEntry x >>> fst) v) <> _)
            (matchesMany classes (fst <<< snd <$> kvs) (snd <<< snd <$> kvs))
         Nothing -> Nothing × Nil
   Val _ _ (V.List vs), PList ps | A.length vs == length ps ->
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

closure :: forall s. DepSemiring s => Ctrl s -> Dict (GVal s) -> Dict (Raw Def) -> Raw Def -> GVal s
closure ctrl ρ ds d =
   constructed ctrl { val, inEdges: viaAll (zip (fst <$> xvs) >>> D.fromFoldable >>> clo) (snd <$> xvs) }
   where
   xvs = toUnfoldable ρ :: List (String × GVal s)
   val = Val unit Nothing (V.Fun (V.Closure (Env (_.val <$> ρ)) ds d))

   clo :: Dict (Val s) -> Val s
   clo ρ' = Val zero Nothing (V.Fun (V.Closure (Env ρ') (zeros <$> ds) (zeros d)))

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict (Raw Def) -> Dict (GVal s)
closeDefs inputs ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      closure inputs.ctrl (restrict (fv ds' ∪ fv d) inputs.env) ds' d

-- ======================
-- Vertices
-- ======================

vertexOf :: forall m s. MonadState (DepGraph Val s) m => Semiring s => GVal s -> m (Vertex × Raw Val)
vertexOf { val, inEdges } = do
   p <- vertex val
   for_ inEdges \(q × r) -> edge q p r
   pure (p × val)

-- Value delivered rather than constructed: every position depends on control at weight c.
deliver :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Vertex × Raw Val)
deliver ctrl v = vertexOf (withCtrl ctrl (unitSection v.val) v)

construct :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Vertex × Raw Val)
construct ctrl v = vertexOf (constructed ctrl v)

constructWith
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> (forall a. List (Val a) -> BaseVal a)
   -> List (GVal s)
   -> m (Vertex × Raw Val)
constructWith ctrl mk vs =
   construct ctrl { val: Val unit Nothing (mk (_.val <$> vs)), inEdges: viaAll (mk >>> Val zero Nothing) vs }

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
   -> Raw Expr
   -> m (Vertex × Raw Val)
eval inputs = case _ of
   Var x -> deliver inputs.ctrl (get x inputs.env)
   Lit _ ℓ -> construct inputs.ctrl { val: Val unit Nothing (V.Lit ℓ), inEdges: Nil }
   Dictionary _ ees -> do
      kvs <- for ees \(Pair e e') -> do
         k <- eval inputs e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs e'
         pure (s × gval k × gval u)
      dictionary inputs.ctrl kvs
   DictComp _ e e' gs -> do
      cs × ctrl <- qualifiers inputs gs
      kvs <- for cs \inputs' -> do
         k <- eval inputs' e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs' e'
         pure (s × gval k × gval u)
      dictionary ctrl kvs
   List _ es -> do
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.List) vs
   ListComp _ e gs -> do
      cs × ctrl <- qualifiers inputs gs
      vs <- for cs \inputs' -> gval <$> eval inputs' e
      constructWith ctrl (A.fromFoldable >>> V.List) vs
   Constr _ c es -> do
      askClasses >>= checkArity (dottedName c) (length es)
      vs <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (V.Constr c) vs
   Matrix _ e (x × y) e' -> do
      dims <- gval <$> eval inputs e'
      (i' × _) × (j' × _) <- orThrow (unpack intPair dims.val) <#> fst
      check
         (i' × j' >= 1 × 1)
         ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
      let
         index k n = { val: Val unit Nothing (V.Lit (Int n)), inEdges: via (\p -> Val (ctrlWeight * k p) Nothing (V.Lit (Int n))) dims }
      vss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
         let ρ' = maplet x (index height i) `unionWith_never` maplet y (index width j)
         gval <$> eval (inputs { env = inputs.env <+> ρ' }) e
      let
         valss = map _.val <$> vss
         m = MatrixRep (valss × MatrixDim (i' × unit) × MatrixDim (j' × unit))
         zm = zeros m
         cell i j v = via (\z -> Val zero Nothing (V.Matrix (matrixPut i j (const z) zm))) v
         inEdges = concat (A.toUnfoldable (A.concat (mapWithIndex (\i vs -> mapWithIndex (\j v -> cell i j v) vs) vss)))
            <> via (\p -> Val zero Nothing (V.Matrix (MatrixRep (map (map zeros) valss × MatrixDim (i' × height p) × MatrixDim (j' × width p))))) dims
      construct inputs.ctrl { val: Val unit Nothing (V.Matrix m), inEdges }
      where
      height :: forall a. Val a -> a
      height = field 0 >>> rootOf

      width :: forall a. Val a -> a
      width = field 1 >>> rootOf
   Lambda _ d -> vertexOf (closure inputs.ctrl (restrict (fv d) inputs.env) empty d)
   Attribute e x -> do
      v <- gval <$> eval inputs e
      case v.val of
         Val _ _ (V.Constr c _) -> do
            xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
            i <- elemIndex x xs # orElse (dottedName c <> " has no field " <> x)
            let val = field i v.val
            deliver inputs.ctrl { val, inEdges: via (\z -> field i z `plus` scale (ctrlWeight * rootOf z) (unitSection val)) v }
         _ -> throw $ "Found " <> prettyP v.val <> ", expected object"
   Subscript e e' -> do
      v <- gval <$> eval inputs e
      v' <- gval <$> eval inputs e'
      case v.val, v'.val of
         Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Lit (Str s)) -> do
            _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
            subscript v v' (dictEntry s >>> snd) (\z -> rootOf z + fst (dictEntry s z))
         Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP v'.val <> ", expected str"
         Val _ _ (V.List vs), Val _ _ (V.Lit (Int i)) -> do
            let i' = if i < 0 then A.length vs + i else i
            _ <- vs A.!! i' # orElse ("List index " <> show i <> " out of range")
            subscript v v' (listElement i') rootOf
         Val _ _ (V.List _), _ -> throw $ "Found " <> prettyP v'.val <> ", expected int"
         Val _ _ (V.Matrix _), Val _ _ (V.Constr c (Val _ _ (V.Lit (Int i)) : Val _ _ (V.Lit (Int j)) : Nil)) | c == cPair ->
            subscript v v' (matrixElement i j) rootOf
         Val _ _ (V.Matrix _), _ -> throw $ "Found " <> prettyP v'.val <> ", expected pair of int"
         _, _ -> throw $ "Found " <> prettyP v.val <> ", expected list, dict or matrix"
      where
      -- Element selected from the container, depending at weight c on the consumed positions and the index.
      subscript :: GVal s -> GVal s -> (forall a. Val a -> Val a) -> (forall a. Semiring a => Val a -> a) -> m (Vertex × Raw Val)
      subscript v v' select consumed =
         deliver inputs.ctrl
            { val
            , inEdges: via (\z -> select z `plus` scale (ctrlWeight * consumed z) u) v
                 <> via (\w -> scale (ctrlWeight * sumPositions w) u) v'
            }
         where
         val = select v.val
         u = unitSection val
   ModMember q x -> do
      { moduleEnv } <- moduleStore
      let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
      u <- withMsg "Module member" $ lookup' x ρ_q
      deliver inputs.ctrl { val: stripDocs (erase u), inEdges: Nil }
   App e es -> do
      f <- gval <$> eval inputs e
      vs <- traverse (eval inputs >>> map gval) es
      withMsg ("In " <> funName e) $ apply inputs f vs
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
      doc <- eval inputs e
      r <- eval inputs e'
      attachDoc (fst r) (snd doc)
      pure r
   where
   funName :: forall a. Expr a -> String
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
   -> List (Raw Qualifier)
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
   passes <- for (mapWithIndex const (L.fromFoldable us)) \i -> do
      let el = { val: listElement i v.val, inEdges: via (listElement i) v }
      case dispatch classes (singleton (p × unit)) el Nil of
         Nothing × ctrl -> pure (Nil × (ctrlVia rootOf v <> ctrl))
         Just (ρ' × _) × ctrl -> qualifiers (inputs { env = inputs.env <+> ρ', ctrl = ctrlVia rootOf v <> ctrl }) gs
   pure (concat (fst <$> passes) × concat (snd <$> passes))
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
   -> Raw Stmt
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
   DefRec (RecDefs _ ds) -> pure (Assigns (closeDefs inputs ds) inputs.ctrl)
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
            throw
               ( "AssertionError: " <> case w of
                    V.Lit (Str str) -> str
                    _ -> prettyP w
               )
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
   => Inputs s
   -> GVal s
   -> List (GVal s)
   -> m (Vertex × Raw Val)
apply inputs f vs = case f.val of
   Val _ _ (V.Fun (V.Partial φ us)) ->
      apply inputs { val: Val unit Nothing (V.Fun φ), inEdges: via partialFun f }
         (mapWithIndex (\i val -> { val, inEdges: via (partialArg i) f }) us <> vs)
   Val _ _ (V.Fun φ) -> do
      n <- arity'
      let k = length vs
      if k < n then construct inputs.ctrl partial
      else if k == n then call φ vs
      else call φ (take n vs) >>= \r -> apply inputs (gval r) (drop n vs)
      where
      arity' :: m Int
      arity' = case φ of
         V.Closure _ _ (Def xs _ _) -> pure (length xs)
         V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
         V.Type c -> askClasses >>= arity (dottedName c)
         V.Partial _ _ -> error absurd

      -- Root and function from the applied function, arguments injected at their slots, control at the root.
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
            ρ2 = closeDefs { ctrl, env: ρ1' } ds
            ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip (paramVar <$> xs) vs')
         asReturns <$> evalStmt { ctrl, env: ρ1' <+> ρ2 <+> ρ3 } s
      V.Prim (ForeignOp (id × ForeignOp' { rel })) -> case rel of
         Just (PrimRelAt relAt) -> do
            PrimRel g <- relAt (_.val <$> vs')
            deliver ctrl { val: g (_.val <$> vs'), inEdges: viaAll g vs' }
         Nothing -> higherOrder (inputs { ctrl = ctrl }) id vs'
      V.Type c -> constructWith ctrl (V.Constr c) vs'
      V.Partial _ _ -> error absurd
      where
      ctrl = ctrlVia rootOf f

   higherOrder :: Inputs s -> String -> List (GVal s) -> m (Vertex × Raw Val)
   higherOrder inputs' "dict_map" (g : d : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      results <- for (toUnfoldable (dictEntries d.val)) \(k × _) -> do
         r <- apply inputs' f' (singleton (entryValue k d))
         pure (k × gval r)
      construct inputs'.ctrl (dictFrom (singleton d) results)
   higherOrder inputs' "dict_intersectionWith" (g : d1 : d2 : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      results <- for (L.filter (\(k × _) -> lookup k (dictEntries d2.val) /= Nothing) (toUnfoldable (dictEntries d1.val))) \(k × _) -> do
         r <- apply inputs' f' (entryValue k d1 : entryValue k d2 : Nil)
         pure (k × gval r)
      construct inputs'.ctrl (dictFrom (d1 : d2 : Nil) results)
   higherOrder inputs' "foldl_with_index" (g : v : d : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      r <- deliver inputs'.ctrl v
      foldM (step f') r (toUnfoldable (dictEntries d.val) :: List (String × (Unit × Raw Val)))
      where
      step f' acc (k × _) =
         apply inputs' f' (key : gval acc : entryValue k d : Nil)
         where
         key = { val: Val unit Nothing (V.Lit (Str k)), inEdges: via (\x -> Val (fst (dictEntry k x)) Nothing (V.Lit (Str k))) d }
   higherOrder _ id _ = throw ("No dependence relation for " <> id)

   entryValue :: String -> GVal s -> GVal s
   entryValue k d = { val: snd (dictEntry k d.val), inEdges: via (dictEntry k >>> snd) d }

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   -- Dictionary with the given values, its root and key positions from those of the dictionary values.
   dictFrom :: List (GVal s) -> List (String × GVal s) -> GVal s
   dictFrom ds kvs =
      { val: Val unit Nothing (V.Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × v) -> k × (unit × v.val)))))
      , inEdges: concat (ds <#> via \x -> Val (rootOf x) Nothing (V.Dictionary (DictRep (mapWithKey (\k (_ × zu) -> fst (get k (dictEntries x)) × zu) zd))))
           <> concat (kvs <#> \(k × v) -> via (\y -> dict (insert k (zero × y) zd)) v)
      }
      where
      zd = D.fromFoldable (kvs <#> \(k × v) -> k × (zero × zeros v.val))

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
   -> Raw Stmt
   -> m (DepEval s)
depEval { ρ, classes } s =
   withClasses classes do
      (root × inputs) × g <- flip runStateT emptyGraph do
         ins <- for (unwrap (erase ρ) :: Dict (Raw Val)) \v -> vertex (stripDocs v) <#> (_ × stripDocs v)
         r <- evalStmt { ctrl: Nil, env: gval <$> ins } s
         pure (fst (asReturns r) × (fst <$> ins))
      pure { g, inputs, root }
