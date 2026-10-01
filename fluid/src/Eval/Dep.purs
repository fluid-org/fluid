module Eval.Dep where

import Prelude hiding (absurd, apply)

import Bind (dottedName, varAnon)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (foldM, foldl, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), concat, drop, elemIndex, length, take, updateAt, zip, (:))
import Data.List as L
import Data.List.NonEmpty (toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DataType (class HasClasses, ClassTable, arity, askClasses, cPair, checkArity, fieldsOf)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (GraphConfig, assign, dispatch, matches)
import Expr (Branch(..), Def(..), Expr(..), Pattern, Qualifier(..), RecDefs(..), Stmt(..), fv, paramVar)
import File (class LoadFile, FileCxt, withClasses)
import Graph.Dep (DepGraph, Rel, Vertex, attachDoc, edge, emptyGraph, plus, scale, sumPositions, vertex, zeros)
import Lattice (class DepSemiring, Raw, ctrlWeight, erase)
import Literal (Literal(..))
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
type GVal s = { v :: Raw Val, inEdges :: InEdges s }
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
gval (p × v) = { v, inEdges: singleton (p × identity) }

project :: forall s. Rel (Val s) (Val s) -> GVal s -> InEdges s
project f o = second (f <<< _) <$> o.inEdges

injections :: forall s. Semiring s => (List (Val s) -> BaseVal s) -> List (GVal s) -> InEdges s
injections mk os = concat (mapWithIndex (\i o -> project (\x -> Val zero Nothing (mk (slot i x))) o) os)
   where
   zs = zeros <<< _.v <$> os
   slot i x = definitely' (updateAt i x zs)

-- Positions inspected by the patterns tried in order, up to the first that matches.
inspectedBy :: forall a. Ord a => ClassTable -> List Pattern -> Val a -> Set a
inspectedBy _ Nil _ = empty
inspectedBy classes (p : ps) x = case matches classes x p of
   Just _ × αs -> αs
   Nothing × αs -> αs ∪ inspectedBy classes ps x

inspected :: forall s. DepSemiring s => ClassTable -> Pattern -> Val s -> s
inspected classes p = inspectedBy classes (singleton p) >>> foldl add zero

-- Control input after the patterns are tried: the inspected positions, or unchanged if nothing is inspected.
afterMatch :: forall s. DepSemiring s => ClassTable -> List Pattern -> GVal s -> Ctrl s -> Ctrl s
afterMatch classes ps o ctrl
   | Set.isEmpty (inspectedBy classes ps o.v) = ctrl
   | otherwise = projectCtrl (inspectedBy classes ps >>> foldl add zero) o

-- Graph values bound by a pattern matching the value.
bindings :: forall s. DepSemiring s => ClassTable -> Pattern -> GVal s -> Dict (GVal s)
bindings classes p o = mapWithKey (\y v -> { v, inEdges: project (binding y) o }) (unwrap ρ)
   where
   ρ = definitely "pattern matches" (fst (matches classes o.v p))

   binding :: String -> Val s -> Val s
   binding y x = get y (unwrap (definitely' (fst (matches classes x p))))

-- Closure capturing the values, its root depending on control at weight c.
closure :: forall s. DepSemiring s => Ctrl s -> Dict (GVal s) -> Dict (Raw Def) -> Raw Def -> GVal s
closure ctrl ρ ds d = { v, inEdges }
   where
   v = Val unit Nothing (V.Fun (V.Closure (Env (_.v <$> ρ)) ds d))
   zρ = zeros <<< _.v <$> ρ

   clo :: Dict (Val s) -> s -> Val s
   clo ρ' α = Val α Nothing (V.Fun (V.Closure (Env ρ') (zeros <$> ds) (zeros d)))

   inEdges = concat (toUnfoldable ρ <#> \(y × o) -> project (\x -> clo (insert y x zρ) zero) o)
      <> (ctrl <#> second \r x -> clo zρ (ctrlWeight * r x))

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
vertexOf { v, inEdges } = do
   p <- vertex v
   for_ inEdges \(q × r) -> edge q p r
   pure (p × v)

-- New vertex with control dependence at weight c on the given section of the value.
vertexCtrl :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> Val s -> GVal s -> m (Vertex × Raw Val)
vertexCtrl ctrl section o = do
   p × v <- vertexOf o
   for_ ctrl \(q × r) -> edge q p \x -> scale (ctrlWeight * r x) section
   pure (p × v)

-- Value delivered rather than constructed: control dependence at every position.
deliver :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Vertex × Raw Val)
deliver ctrl o = vertexCtrl ctrl (unitSection o.v) o

-- Constructed value: control dependence at the root.
construct :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Vertex × Raw Val)
construct ctrl o@{ v: Val _ _ u } = vertexCtrl ctrl (Val one Nothing (zeros u)) o

constructWith
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> (forall a. List (Val a) -> BaseVal a)
   -> List (GVal s)
   -> m (Vertex × Raw Val)
constructWith ctrl mk os = construct ctrl { v: Val unit Nothing (mk (_.v <$> os)), inEdges: injections mk os }

-- Dictionary from keys and values; later entries overwrite earlier ones.
dictionary
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> List (String × GVal s × GVal s)
   -> m (Vertex × Raw Val)
dictionary ctrl kvs = construct ctrl { v: Val unit Nothing (V.Dictionary (DictRep d)), inEdges }
   where
   winners = Map.toUnfoldable (Map.fromFoldable kvs) :: List (String × GVal s × GVal s)
   d = D.fromFoldable (winners <#> \(k × _ × u) -> k × (unit × u.v))
   zd = (\(_ × u) -> zero × zeros u) <$> d

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   inEdges = concat $ winners <#> \(k × key × u) ->
      project (\x -> dict (insert k (rootOf x × zeros u.v) zd)) key
         <> project (\y -> dict (insert k (zero × y) zd)) u

-- ======================
-- Evaluation
-- ======================

bool :: forall m. MonadError Error m => Raw Val -> m Boolean
bool (Val _ _ u) = orThrow (boolean.unpack u)

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
   Lit _ ℓ -> construct inputs.ctrl { v: Val unit Nothing (V.Lit ℓ), inEdges: Nil }
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
      os <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.List) os
   ListComp _ e gs -> do
      cs × ctrl <- qualifiers inputs gs
      os <- for cs \inputs' -> gval <$> eval inputs' e
      constructWith ctrl (A.fromFoldable >>> V.List) os
   Constr _ c es -> do
      askClasses >>= checkArity (dottedName c) (length es)
      os <- traverse (eval inputs >>> map gval) es
      constructWith inputs.ctrl (V.Constr c) os
   Matrix _ e (x × y) e' -> do
      dims <- gval <$> eval inputs e'
      (i' × _) × (j' × _) <- orThrow (unpack intPair dims.v) <#> fst
      check
         (i' × j' >= 1 × 1)
         ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
      let
         index k n = { v: Val unit Nothing (V.Lit (Int n)), inEdges: project (\p -> Val (ctrlWeight * k p) Nothing (V.Lit (Int n))) dims }
      oss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
         let ρ' = maplet x (index height i) `unionWith_never` maplet y (index width j)
         gval <$> eval (inputs { env = inputs.env <+> ρ' }) e
      let
         vss = map _.v <$> oss
         m = MatrixRep (vss × MatrixDim (i' × unit) × MatrixDim (j' × unit))
         zm = zeros m
         cell i j o = project (\z -> Val zero Nothing (V.Matrix (matrixPut i j (const z) zm))) o
         inEdges = concat (A.toUnfoldable (A.concat (mapWithIndex (\i os -> mapWithIndex (\j o -> cell i j o) os) oss)))
            <> project (\p -> Val zero Nothing (V.Matrix (MatrixRep (map (map zeros) vss × MatrixDim (i' × height p) × MatrixDim (j' × width p))))) dims
      construct inputs.ctrl { v: Val unit Nothing (V.Matrix m), inEdges }
      where
      height :: forall a. Val a -> a
      height = field 0 >>> rootOf

      width :: forall a. Val a -> a
      width = field 1 >>> rootOf
   Lambda _ d -> vertexOf (closure inputs.ctrl (restrict (fv d) inputs.env) empty d)
   Attribute e x -> do
      o <- gval <$> eval inputs e
      case o.v of
         Val _ _ (V.Constr c _) -> do
            xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
            i <- elemIndex x xs # orElse (dottedName c <> " has no field " <> x)
            let v = field i o.v
            deliver inputs.ctrl { v, inEdges: project (\z -> field i z `plus` scale (ctrlWeight * rootOf z) (unitSection v)) o }
         _ -> throw $ "Found " <> prettyP o.v <> ", expected object"
   Subscript e e' -> do
      o <- gval <$> eval inputs e
      o' <- gval <$> eval inputs e'
      case o.v, o'.v of
         Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Lit (Str s)) -> do
            _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
            subscript o o' (dictEntry s >>> snd) (\z -> rootOf z + fst (dictEntry s z))
         Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected str"
         Val _ _ (V.List vs), Val _ _ (V.Lit (Int i)) -> do
            let i' = if i < 0 then A.length vs + i else i
            _ <- vs A.!! i' # orElse ("List index " <> show i <> " out of range")
            subscript o o' (listElement i') rootOf
         Val _ _ (V.List _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected int"
         Val _ _ (V.Matrix _), Val _ _ (V.Constr c (Val _ _ (V.Lit (Int i)) : Val _ _ (V.Lit (Int j)) : Nil)) | c == cPair ->
            subscript o o' (matrixElement i j) rootOf
         Val _ _ (V.Matrix _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected pair of int"
         _, _ -> throw $ "Found " <> prettyP o.v <> ", expected list, dict or matrix"
      where
      -- Element selected from the container, depending at weight c on the consumed positions and the index.
      subscript :: GVal s -> GVal s -> (forall a. Val a -> Val a) -> (forall a. Semiring a => Val a -> a) -> m (Vertex × Raw Val)
      subscript o o' select consumed =
         deliver inputs.ctrl
            { v
            , inEdges: project (\z -> select z `plus` scale (ctrlWeight * consumed z) u) o
                 <> project (\w -> scale (ctrlWeight * sumPositions w) u) o'
            }
         where
         v = select o.v
         u = unitSection v
   ModMember q x -> do
      { moduleEnv } <- moduleStore
      let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
      v <- withMsg "Module member" $ lookup' x ρ_q
      deliver inputs.ctrl { v: stripDocs (erase v), inEdges: Nil }
   App e es -> do
      f <- gval <$> eval inputs e
      os <- traverse (eval inputs >>> map gval) es
      withMsg ("In " <> funName e) $ apply inputs f os
   BinOp e op e' -> do
      o <- gval <$> eval inputs e
      o' <- gval <$> eval inputs e'
      u <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op o.v o'.v) <#> fst
      let rel x y = binopRel op x y # either (\_ -> error absurd) identity
      deliver inputs.ctrl
         { v: Val unit Nothing u
         , inEdges: project (\x -> rel x (zeros o'.v)) o <> project (\y -> rel (zeros o.v) y) o'
         }
   UnOp op e -> do
      o <- gval <$> eval inputs e
      u <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op o.v) <#> fst
      deliver inputs.ctrl { v: Val unit Nothing u, inEdges: project (unopRel op >>> either (\_ -> error absurd) identity) o }
   And e e' -> do
      o <- eval inputs e
      b <- bool (snd o)
      if b then eval (inputs { ctrl = singleton (fst o × rootOf) }) e' else pure o
   Or e e' -> do
      o <- eval inputs e
      b <- bool (snd o)
      if b then pure o else eval (inputs { ctrl = singleton (fst o × rootOf) }) e'
   Cond e1 e e2 -> do
      o <- eval inputs e
      b <- bool (snd o)
      eval (inputs { ctrl = singleton (fst o × rootOf) }) (if b then e1 else e2)
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
   o <- eval inputs e
   b <- bool (snd o)
   let ctrl = singleton (fst o × rootOf)
   if b then qualifiers (inputs { ctrl = ctrl }) gs else pure (Nil × ctrl)
qualifiers inputs (Generator p e : gs) = do
   o <- gval <$> eval inputs e
   vs <- case o.v of
      Val _ _ (V.List vs) -> pure vs
      _ -> throw $ "Found " <> prettyP o.v <> ", expected list"
   classes <- askClasses
   passes <- for (mapWithIndex const (L.fromFoldable vs)) \i -> do
      let
         el = { v: listElement i o.v, inEdges: project (listElement i) o }
         ctrl = projectCtrl (\x -> rootOf x + inspected classes p (listElement i x)) o
      case fst (matches classes el.v p) of
         Nothing -> pure (Nil × ctrl)
         Just _ -> qualifiers (inputs { env = inputs.env <+> bindings classes p el, ctrl = ctrl }) gs
   pure (concat (fst <$> passes) × concat (snd <$> passes))
qualifiers inputs (Decl p e : gs) = do
   o <- gval <$> eval inputs e
   classes <- askClasses
   _ <- assign classes o.v p
   qualifiers (inputs { env = inputs.env <+> bindings classes p o, ctrl = afterMatch classes (singleton p) o inputs.ctrl }) gs

projectCtrl :: forall s. Rel (Val s) s -> GVal s -> Ctrl s
projectCtrl f o = second (f <<< _) <$> o.inEdges

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
         o <- eval (inputs { ctrl = ctrl }) e
         b <- bool (snd o)
         let ctrl' = singleton (fst o × rootOf)
         if b then evalStmt (inputs { ctrl = ctrl' }) s' else go bs' ctrl'
   Match e bs -> do
      o <- gval <$> eval inputs e
      classes <- askClasses
      let ctrl = afterMatch classes (fst <$> NEL.toList bs) o inputs.ctrl
      case dispatch classes o.v (NEL.toList bs) of
         Nothing -> pure (Assigns empty ctrl)
         Just (_ × (p × s') × _) -> do
            let ρ' = bindings classes p o
            r <- evalStmt (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) s'
            case r of
               Returns _ -> pure r
               Assigns ρ'' ctrl' -> pure (Assigns (ρ' <+> ρ'') ctrl')
   Assign p _ e -> do
      o <- gval <$> eval inputs e
      classes <- askClasses
      _ <- assign classes o.v p
      pure (Assigns (bindings classes p o) (afterMatch classes (singleton p) o inputs.ctrl))
   DefRec (RecDefs _ ds) -> pure (Assigns (closeDefs inputs ds) inputs.ctrl)
   Pass -> pure (Assigns empty inputs.ctrl)
   ExprStmt e -> eval inputs e $> Assigns empty inputs.ctrl
   Assert e e_opt -> do
      o <- eval inputs e
      b <- bool (snd o)
      let ctrl = singleton (fst o × rootOf)
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
apply inputs f os = case f.v of
   Val _ _ (V.Fun (V.Partial φ vs)) ->
      apply inputs { v: Val unit Nothing (V.Fun φ), inEdges: project partialFun f }
         (mapWithIndex (\i v -> { v, inEdges: project (partialArg i) f }) vs <> os)
   Val _ _ (V.Fun φ) -> do
      n <- arity'
      let k = length os
      if k < n then construct inputs.ctrl partial
      else if k == n then call φ os
      else call φ (take n os) >>= \r -> apply inputs (gval r) (drop n os)
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
         { v: Val unit Nothing (V.Fun (V.Partial φ (_.v <$> os)))
         , inEdges: project (\x -> Val (rootOf x) Nothing (V.Fun (V.Partial (fun x) zs))) f
              <> concat (mapWithIndex (\i o -> project (\y -> Val zero Nothing (V.Fun (V.Partial (zeros φ) (definitely' (updateAt i y zs))))) o) os)
         }
         where
         zs = zeros <<< _.v <$> os
   _ -> throw $ "Found " <> prettyP f.v <> ", expected function"
   where
   -- Applying a function consumes its root.
   call :: V.Fun Unit -> List (GVal s) -> m (Vertex × Raw Val)
   call φ os' = case φ of
      V.Closure (Env ρ1) ds (Def xs _ s) -> do
         let
            ρ1' = mapWithKey (\y v -> { v, inEdges: project (closureEnv >>> get y) f }) ρ1
            ρ2 = closeDefs { ctrl, env: ρ1' } ds
            ρ3 = foldl (\ρ (x × o) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x o) empty (zip (paramVar <$> xs) os')
         asReturns <$> evalStmt { ctrl, env: ρ1' <+> ρ2 <+> ρ3 } s
      V.Prim (ForeignOp (id × ForeignOp' { rel })) -> case rel of
         Just (PrimRelAt relAt) -> do
            PrimRel g <- relAt (_.v <$> os')
            let zs = zeros <<< _.v <$> os'
            deliver ctrl
               { v: g (_.v <$> os')
               , inEdges: concat (mapWithIndex (\i o -> project (\x -> g (definitely' (updateAt i x zs))) o) os')
               }
         Nothing -> higherOrder (inputs { ctrl = ctrl }) id os'
      V.Type c -> constructWith ctrl (V.Constr c) os'
      V.Partial _ _ -> error absurd
      where
      ctrl = projectCtrl rootOf f

   higherOrder :: Inputs s -> String -> List (GVal s) -> m (Vertex × Raw Val)
   higherOrder inputs' "dict_map" (g : d : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      results <- for (toUnfoldable (dictEntries d.v)) \(k × _) -> do
         r <- apply inputs' f' (singleton (entryValue k d))
         pure (k × gval r)
      construct inputs'.ctrl (dictFrom (singleton d) results)
   higherOrder inputs' "dict_intersectionWith" (g : d1 : d2 : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      results <- for (L.filter (\(k × _) -> lookup k (dictEntries d2.v) /= Nothing) (toUnfoldable (dictEntries d1.v))) \(k × _) -> do
         r <- apply inputs' f' (entryValue k d1 : entryValue k d2 : Nil)
         pure (k × gval r)
      construct inputs'.ctrl (dictFrom (d1 : d2 : Nil) results)
   higherOrder inputs' "foldl_with_index" (g : u : d : Nil) = do
      f' <- gval <$> deliver inputs'.ctrl g
      r <- deliver inputs'.ctrl u
      foldM (step f') r (toUnfoldable (dictEntries d.v) :: List (String × (Unit × Raw Val)))
      where
      step f' acc (k × _) =
         apply inputs' f' (key : gval acc : entryValue k d : Nil)
         where
         key = { v: Val unit Nothing (V.Lit (Str k)), inEdges: project (\x -> Val (fst (dictEntry k x)) Nothing (V.Lit (Str k))) d }
   higherOrder _ id _ = throw ("No dependence relation for " <> id)

   entryValue :: String -> GVal s -> GVal s
   entryValue k d = { v: snd (dictEntry k d.v), inEdges: project (dictEntry k >>> snd) d }

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   -- Dictionary with the given values, its root and key positions from those of the dictionary values.
   dictFrom :: List (GVal s) -> List (String × GVal s) -> GVal s
   dictFrom ds kvs =
      { v: Val unit Nothing (V.Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × o) -> k × (unit × o.v)))))
      , inEdges: concat (ds <#> project \x -> Val (rootOf x) Nothing (V.Dictionary (DictRep (mapWithKey (\k (_ × zu) -> fst (get k (dictEntries x)) × zu) zd))))
           <> concat (kvs <#> \(k × o) -> project (\y -> dict (insert k (zero × y) zd)) o)
      }
      where
      zd = D.fromFoldable (kvs <#> \(k × o) -> k × (zero × zeros o.v))

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
