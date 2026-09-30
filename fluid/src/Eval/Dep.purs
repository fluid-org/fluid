module Eval.Dep where

import Prelude hiding (absurd, apply)

import Bind (dottedName, varAnon)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.State (class MonadState, runStateT)
import Data.Array as A
import Data.Either (either)
import Data.Foldable (foldM, foldl, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), concat, drop, elemIndex, length, take, updateAt, zip, (:), (!!))
import Data.List as L
import Data.List.NonEmpty (toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (second)
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
import Graph.Dep (DepGraph, Rel, Vertex, attachDoc, edge, emptyGraph, positions, vertex)
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
import Val (class HasModuleStore, BaseVal, DictRep(..), Env(..), ForeignOp(..), ForeignOp'(..), MatrixDim(..), MatrixRep(..), PrimRel(..), PrimRelAt(..), Val(..), forDefs, matrixGet, matrixPut, moduleStore, rootOf, stripDocs)

type Sources s = List (Vertex × Rel (Val s) (Val s))

-- Value with the vertices supplying its positions.
type Operand s = { v :: Raw Val, srcs :: Sources s }

-- Sources of the control input, each a relation into its weight.
type Ctrl s = List (Vertex × Rel (Val s) s)

type Inputs s = { ctrl :: Ctrl s, env :: Dict (Operand s) }

data Result s = Returns (Vertex × Raw Val) | Assigns (Dict (Operand s)) (Ctrl s)

asReturns :: forall s. Result s -> Vertex × Raw Val
asReturns (Returns r) = r
asReturns (Assigns _ _) = error "Returns expected"

-- ======================
-- Weight vectors
-- ======================

zeros :: forall f s. Functor f => Semiring s => f Unit -> f s
zeros = map (const zero)

scaleVal :: forall s. Semiring s => s -> Val s -> Val s
scaleVal a = map (mul a)

plus :: forall s. Semiring s => Val s -> Val s -> Val s
plus = lift2 add

sumPositions :: forall s. Semiring s => Val s -> s
sumPositions = positions >>> foldl add zero

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

-- Weight 1 at the root only.
rootOnly :: forall s. Semiring s => Raw Val -> Val s
rootOnly (Val _ _ u) = Val one Nothing (zeros u)

field :: forall a. Int -> Val a -> Val a
field i (Val _ _ (V.Constr _ vs)) = definitely' (vs !! i)
field _ _ = error absurd

element :: forall a. Int -> Val a -> Val a
element i (Val _ _ (V.List vs)) = definitely' (vs A.!! i)
element _ _ = error absurd

entry :: forall a. String -> Val a -> a × Val a
entry k (Val _ _ (V.Dictionary (DictRep d))) = get k d
entry _ _ = error absurd

captured :: forall a. String -> Val a -> Val a
captured y (Val _ _ (V.Fun (V.Closure (Env ρ) _ _))) = get y ρ
captured _ _ = error absurd

partialFun :: forall a. Val a -> Val a
partialFun (Val α doc (V.Fun (V.Partial φ _))) = Val α doc (V.Fun φ)
partialFun _ = error absurd

partialArg :: forall a. Int -> Val a -> Val a
partialArg i (Val _ _ (V.Fun (V.Partial _ vs))) = definitely' (vs !! i)
partialArg _ _ = error absurd

-- ======================
-- Operands
-- ======================

operand :: forall s. Vertex × Raw Val -> Operand s
operand (p × v) = { v, srcs: singleton (p × identity) }

-- Sources of the component selected by a projection.
project :: forall s. Rel (Val s) (Val s) -> Operand s -> Sources s
project f o = second (f <<< _) <$> o.srcs

-- Sources of a value built from the operands, each injected at its slot with the others zero.
injections :: forall s. Semiring s => (List (Val s) -> BaseVal s) -> List (Operand s) -> Sources s
injections mk os = concat (mapWithIndex (\i o -> project (\x -> Val zero Nothing (mk (slot i x))) o) os)
   where
   zs = zeros <<< _.v <$> os
   slot i x = definitely' (updateAt i x zs)

-- Control input after consuming positions: those at weight 1 and the old control input at weight c.
consume :: forall s. DepSemiring s => Ctrl s -> Ctrl s -> Ctrl s
consume ctrl consumed = consumed <> (second (\r -> mul ctrlWeight <<< r) <$> ctrl)

-- Sum of the weights at the positions inspected by matching the pattern.
inspected :: forall s. DepSemiring s => ClassTable -> Pattern -> Val s -> s
inspected classes p x = foldl add zero (snd (matches classes x p))

-- Sum of the weights at the positions inspected by the cases tried up to the first that matches.
inspectedByCases :: forall s. DepSemiring s => ClassTable -> List Pattern -> Val s -> s
inspectedByCases classes ps x = foldl add zero (go ps)
   where
   go Nil = empty
   go (p : ps') = case matches classes x p of
      Just _ × αs -> αs
      Nothing × αs -> αs ∪ go ps'

-- Operands bound by a pattern matching the operand.
bindings :: forall s. DepSemiring s => ClassTable -> Pattern -> Operand s -> Dict (Operand s)
bindings classes p o = mapWithKey (\y v -> { v, srcs: project (binding y) o }) (unwrap ρ)
   where
   ρ = definitely "pattern matches" (fst (matches classes o.v p))

   binding :: String -> Val s -> Val s
   binding y x = get y (unwrap (definitely' (fst (matches classes x p))))

-- Closure capturing the operands, its root depending on control at weight c.
closureOperand :: forall s. DepSemiring s => Ctrl s -> Dict (Operand s) -> Dict (Raw Def) -> Raw Def -> Operand s
closureOperand ctrl ρ ds d = { v, srcs }
   where
   v = Val unit Nothing (V.Fun (V.Closure (Env (_.v <$> ρ)) ds d))
   zρ = zeros <<< _.v <$> ρ

   clo :: Dict (Val s) -> s -> Val s
   clo ρ' α = Val α Nothing (V.Fun (V.Closure (Env ρ') (zeros <$> ds) (zeros d)))

   srcs = concat (toUnfoldable ρ <#> \(y × o) -> project (\x -> clo (insert y x zρ) zero) o)
      <> (ctrl <#> second \r x -> clo zρ (ctrlWeight * r x))

closeDefs :: forall s. DepSemiring s => Inputs s -> Dict (Raw Def) -> Dict (Operand s)
closeDefs inputs ds = ds <#> \d ->
   let
      ds' = ds `forDefs` d
   in
      closureOperand inputs.ctrl (restrict (fv ds' ∪ fv d) inputs.env) ds' d

-- ======================
-- Vertices
-- ======================

-- New vertex for a value, with edges from its sources.
vertexOf :: forall m s. MonadState (DepGraph Val s) m => Semiring s => Operand s -> m (Vertex × Raw Val)
vertexOf { v, srcs } = do
   p <- vertex v
   for_ srcs \(q × r) -> edge q p r
   pure (p × v)

-- New vertex with control dependence at weight c on the given section of the value.
vertexCtrl :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> Val s -> Operand s -> m (Vertex × Raw Val)
vertexCtrl ctrl section o = do
   p × v <- vertexOf o
   for_ ctrl \(q × r) -> edge q p \x -> scaleVal (ctrlWeight * r x) section
   pure (p × v)

-- Value delivered rather than constructed: control dependence at every position.
deliver :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> Operand s -> m (Vertex × Raw Val)
deliver ctrl o = vertexCtrl ctrl (unitSection o.v) o

-- Constructed value: control dependence at the root.
construct :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> Operand s -> m (Vertex × Raw Val)
construct ctrl o = vertexCtrl ctrl (rootOnly o.v) o

constructWith
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> (forall a. List (Val a) -> BaseVal a)
   -> List (Operand s)
   -> m (Vertex × Raw Val)
constructWith ctrl mk os = construct ctrl { v: Val unit Nothing (mk (_.v <$> os)), srcs: injections mk os }

-- Dictionary from key and value operands; later entries overwrite earlier ones.
dictionary
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> List (String × Operand s × Operand s)
   -> m (Vertex × Raw Val)
dictionary ctrl entries = construct ctrl { v: Val unit Nothing (V.Dictionary (DictRep d)), srcs }
   where
   winners = Map.toUnfoldable (Map.fromFoldable entries) :: List (String × Operand s × Operand s)
   d = D.fromFoldable (winners <#> \(k × _ × u) -> k × (unit × u.v))
   zd = (\(_ × u) -> zero × zeros u) <$> d

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   srcs = concat $ winners <#> \(k × key × u) ->
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
   Lit _ ℓ -> construct inputs.ctrl { v: Val unit Nothing (V.Lit ℓ), srcs: Nil }
   Dictionary _ ees -> do
      entries <- for ees \(Pair e e') -> do
         k <- eval inputs e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs e'
         pure (s × operand k × operand u)
      dictionary inputs.ctrl entries
   DictComp _ e e' gs -> do
      cs × ctrl <- qualifiers inputs gs
      entries <- for cs \inputs' -> do
         k <- eval inputs' e
         s <- orThrow (unpack string (snd k)) <#> fst
         u <- eval inputs' e'
         pure (s × operand k × operand u)
      dictionary ctrl entries
   List _ es -> do
      os <- traverse (eval inputs >>> map operand) es
      constructWith inputs.ctrl (A.fromFoldable >>> V.List) os
   ListComp _ e gs -> do
      cs × ctrl <- qualifiers inputs gs
      os <- for cs \inputs' -> operand <$> eval inputs' e
      constructWith ctrl (A.fromFoldable >>> V.List) os
   Constr _ c es -> do
      askClasses >>= checkArity (dottedName c) (length es)
      os <- traverse (eval inputs >>> map operand) es
      constructWith inputs.ctrl (V.Constr c) os
   Matrix _ e (x × y) e' -> do
      dims <- operand <$> eval inputs e'
      (i' × _) × (j' × _) <- orThrow (unpack intPair dims.v) <#> fst
      check
         (i' × j' >= 1 × 1)
         ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
      let
         index k n = { v: Val unit Nothing (V.Lit (Int n)), srcs: project (\p -> Val (ctrlWeight * k p) Nothing (V.Lit (Int n))) dims }
      oss <- for (A.range 0 (i' - 1)) \i -> for (A.range 0 (j' - 1)) \j -> do
         let ρ' = maplet x (index height i) `unionWith_never` maplet y (index width j)
         operand <$> eval (inputs { env = inputs.env <+> ρ' }) e
      let
         vss = map _.v <$> oss
         m = MatrixRep (vss × MatrixDim (i' × unit) × MatrixDim (j' × unit))
         zm = zeros m
         cell i j o = project (\z -> Val zero Nothing (V.Matrix (matrixPut i j (const z) zm))) o
         srcs = concat (A.toUnfoldable (A.concat (mapWithIndex (\i os -> mapWithIndex (\j o -> cell i j o) os) oss)))
            <> project (\p -> Val zero Nothing (V.Matrix (MatrixRep (map (map zeros) vss × MatrixDim (i' × height p) × MatrixDim (j' × width p))))) dims
      construct inputs.ctrl { v: Val unit Nothing (V.Matrix m), srcs }
      where
      height :: forall a. Val a -> a
      height = field 0 >>> rootOf

      width :: forall a. Val a -> a
      width = field 1 >>> rootOf
   Lambda _ d -> vertexOf (closureOperand inputs.ctrl (restrict (fv d) inputs.env) empty d)
   Attribute e x -> do
      o <- operand <$> eval inputs e
      case o.v of
         Val _ _ (V.Constr c _) -> do
            xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
            i <- elemIndex x xs # orElse (dottedName c <> " has no field " <> x)
            let v = field i o.v
            deliver inputs.ctrl { v, srcs: project (\z -> field i z `plus` scaleVal (ctrlWeight * rootOf z) (unitSection v)) o }
         _ -> throw $ "Found " <> prettyP o.v <> ", expected object"
   Subscript e e' -> do
      o <- operand <$> eval inputs e
      o' <- operand <$> eval inputs e'
      case o.v, o'.v of
         Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Lit (Str s)) -> do
            _ <- withMsg "Dict lookup" $ lookup s d # orElse ("Key \"" <> s <> "\" not found")
            subscript o o' (entry s >>> snd) (\z -> rootOf z + fst (entry s z))
         Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected str"
         Val _ _ (V.List vs), Val _ _ (V.Lit (Int i)) -> do
            let i' = if i < 0 then A.length vs + i else i
            _ <- vs A.!! i' # orElse ("List index " <> show i <> " out of range")
            subscript o o' (element i') rootOf
         Val _ _ (V.List _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected int"
         Val _ _ (V.Matrix _), Val _ _ (V.Constr c (Val _ _ (V.Lit (Int i)) : Val _ _ (V.Lit (Int j)) : Nil)) | c == cPair ->
            subscript o o' (cell i j) rootOf
         Val _ _ (V.Matrix _), _ -> throw $ "Found " <> prettyP o'.v <> ", expected pair of int"
         _, _ -> throw $ "Found " <> prettyP o.v <> ", expected list, dict or matrix"
      where
      cell :: forall a. Int -> Int -> Val a -> Val a
      cell i j (Val _ _ (V.Matrix r)) = matrixGet i j r
      cell _ _ _ = error absurd

      -- Element selected from the container, depending at weight c on the consumed positions and the index.
      subscript :: Operand s -> Operand s -> (forall a. Val a -> Val a) -> (forall a. Semiring a => Val a -> a) -> m (Vertex × Raw Val)
      subscript o o' select consumed =
         deliver inputs.ctrl
            { v
            , srcs: project (\z -> select z `plus` scaleVal (ctrlWeight * consumed z) u) o
                 <> project (\w -> scaleVal (ctrlWeight * sumPositions w) u) o'
            }
         where
         v = select o.v
         u = unitSection v
   ModMember q x -> do
      { moduleEnv } <- moduleStore
      let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
      v <- withMsg "Module member" $ lookup' x ρ_q
      deliver inputs.ctrl { v: stripDocs (erase v), srcs: Nil }
   App e es -> do
      f <- operand <$> eval inputs e
      os <- traverse (eval inputs >>> map operand) es
      withMsg ("In " <> funName e) $ apply inputs f os
   BinOp e op e' -> do
      o <- operand <$> eval inputs e
      o' <- operand <$> eval inputs e'
      u <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op o.v o'.v) <#> fst
      let rel x y = binopRel op x y # either (\_ -> error absurd) identity
      deliver inputs.ctrl
         { v: Val unit Nothing u
         , srcs: project (\x -> rel x (zeros o'.v)) o <> project (\y -> rel (zeros o.v) y) o'
         }
   UnOp op e -> do
      o <- operand <$> eval inputs e
      u <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op o.v) <#> fst
      deliver inputs.ctrl { v: Val unit Nothing u, srcs: project (unopRel op >>> either (\_ -> error absurd) identity) o }
   And e e' -> do
      o <- eval inputs e
      b <- bool (snd o)
      if b then eval (inputs { ctrl = consume inputs.ctrl (singleton (fst o × rootOf)) }) e' else pure o
   Or e e' -> do
      o <- eval inputs e
      b <- bool (snd o)
      if b then pure o else eval (inputs { ctrl = consume inputs.ctrl (singleton (fst o × rootOf)) }) e'
   Cond e1 e e2 -> do
      o <- eval inputs e
      b <- bool (snd o)
      eval (inputs { ctrl = consume inputs.ctrl (singleton (fst o × rootOf)) }) (if b then e1 else e2)
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
   let ctrl = consume inputs.ctrl (singleton (fst o × rootOf))
   if b then qualifiers (inputs { ctrl = ctrl }) gs else pure (Nil × ctrl)
qualifiers inputs (Generator p e : gs) = do
   o <- operand <$> eval inputs e
   vs <- case o.v of
      Val _ _ (V.List vs) -> pure vs
      _ -> throw $ "Found " <> prettyP o.v <> ", expected list"
   classes <- askClasses
   passes <- for (mapWithIndex const (L.fromFoldable vs)) \i -> do
      let
         el = { v: element i o.v, srcs: project (element i) o }
         ctrl = consume inputs.ctrl (projectCtrl (\x -> rootOf x + inspected classes p (element i x)) o)
      case fst (matches classes el.v p) of
         Nothing -> pure (Nil × ctrl)
         Just _ -> qualifiers (inputs { env = inputs.env <+> bindings classes p el, ctrl = ctrl }) gs
   pure (concat (fst <$> passes) × concat (snd <$> passes))
qualifiers inputs (Decl p e : gs) = do
   o <- operand <$> eval inputs e
   classes <- askClasses
   _ <- assign classes o.v p
   qualifiers (inputs { env = inputs.env <+> bindings classes p o, ctrl = consume inputs.ctrl (projectCtrl (inspected classes p) o) }) gs

-- Control sources from an operand, by a relation into the weight.
projectCtrl :: forall s. Rel (Val s) s -> Operand s -> Ctrl s
projectCtrl f o = second (f <<< _) <$> o.srcs

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
         let ctrl' = consume ctrl (singleton (fst o × rootOf))
         if b then evalStmt (inputs { ctrl = ctrl' }) s' else go bs' ctrl'
   Match e bs -> do
      o <- operand <$> eval inputs e
      classes <- askClasses
      let ctrl = consume inputs.ctrl (projectCtrl (inspectedByCases classes (fst <$> NEL.toList bs)) o)
      case dispatch classes o.v (NEL.toList bs) of
         Nothing -> pure (Assigns empty ctrl)
         Just (_ × (p × s') × _) -> do
            let ρ' = bindings classes p o
            r <- evalStmt (inputs { env = inputs.env <+> ρ', ctrl = ctrl }) s'
            case r of
               Returns _ -> pure r
               Assigns ρ'' ctrl' -> pure (Assigns (ρ' <+> ρ'') ctrl')
   Assign p _ e -> do
      o <- operand <$> eval inputs e
      classes <- askClasses
      _ <- assign classes o.v p
      pure (Assigns (bindings classes p o) (consume inputs.ctrl (projectCtrl (inspected classes p) o)))
   DefRec (RecDefs _ ds) -> pure (Assigns (closeDefs inputs ds) inputs.ctrl)
   Pass -> pure (Assigns empty inputs.ctrl)
   ExprStmt e -> eval inputs e $> Assigns empty inputs.ctrl
   Assert e e_opt -> do
      o <- eval inputs e
      b <- bool (snd o)
      let ctrl = consume inputs.ctrl (singleton (fst o × rootOf))
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
   -> Operand s
   -> List (Operand s)
   -> m (Vertex × Raw Val)
apply inputs f os = case f.v of
   Val _ _ (V.Fun (V.Partial φ vs)) ->
      apply inputs { v: Val unit Nothing (V.Fun φ), srcs: project partialFun f }
         (mapWithIndex (\i v -> { v, srcs: project (partialArg i) f }) vs <> os)
   Val _ _ (V.Fun φ) -> do
      n <- arity'
      let k = length os
      if k < n then construct inputs.ctrl partial
      else if k == n then call φ os
      else call φ (take n os) >>= \r -> apply inputs (operand r) (drop n os)
      where
      arity' :: m Int
      arity' = case φ of
         V.Closure _ _ (Def xs _ _) -> pure (length xs)
         V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
         V.Type c -> askClasses >>= arity (dottedName c)
         V.Partial _ _ -> error absurd

      -- Root and function from the applied function, arguments injected at their slots, control at the root.
      partial :: Operand s
      partial =
         { v: Val unit Nothing (V.Fun (V.Partial φ (_.v <$> os)))
         , srcs: project (\x -> Val (rootOf x) Nothing (V.Fun (V.Partial (fun x) zs))) f
              <> concat (mapWithIndex (\i o -> project (\y -> Val zero Nothing (V.Fun (V.Partial (zeros φ) (definitely' (updateAt i y zs))))) o) os)
         }
         where
         zs = zeros <<< _.v <$> os

      fun :: Val s -> V.Fun s
      fun (Val _ _ (V.Fun φ')) = φ'
      fun _ = error absurd
   _ -> throw $ "Found " <> prettyP f.v <> ", expected function"
   where
   call :: V.Fun Unit -> List (Operand s) -> m (Vertex × Raw Val)
   call φ os' = case φ of
      V.Closure (Env ρ1) ds (Def xs _ s) -> do
         let
            ctrl = consume inputs.ctrl (projectCtrl rootOf f)
            ρ1' = mapWithKey (\y v -> { v, srcs: project (captured y) f }) ρ1
            ρ2 = closeDefs { ctrl, env: ρ1' } ds
            ρ3 = foldl (\ρ (x × o) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x o) empty (zip (paramVar <$> xs) os')
         asReturns <$> evalStmt { ctrl, env: ρ1' <+> ρ2 <+> ρ3 } s
      V.Prim (ForeignOp (id × ForeignOp' { rel })) -> case rel of
         Just (PrimRelAt relAt) -> do
            PrimRel g <- relAt (_.v <$> os')
            let zs = zeros <<< _.v <$> os'
            deliver inputs.ctrl
               { v: g (_.v <$> os')
               , srcs: concat (mapWithIndex (\i o -> project (\x -> g (definitely' (updateAt i x zs))) o) os')
               }
         Nothing -> higherOrder id os'
      V.Type c -> constructWith inputs.ctrl (V.Constr c) os'
      V.Partial _ _ -> error absurd

   higherOrder :: String -> List (Operand s) -> m (Vertex × Raw Val)
   higherOrder "dict_map" (f' : d : Nil) = do
      results <- for (toUnfoldable (entries d.v)) \(k × _) -> do
         r <- apply inputs f' (singleton (entryOperand k d))
         pure (k × operand r)
      construct inputs.ctrl (dictFrom (singleton d) results)
   higherOrder "dict_intersectionWith" (f' : d1 : d2 : Nil) = do
      results <- for (L.filter (\(k × _) -> lookup k (entries d2.v) /= Nothing) (toUnfoldable (entries d1.v))) \(k × _) -> do
         r <- apply inputs f' (entryOperand k d1 : entryOperand k d2 : Nil)
         pure (k × operand r)
      construct inputs.ctrl (dictFrom (d1 : d2 : Nil) results)
   higherOrder "foldl_with_index" (f' : u : d : Nil) =
      deliver inputs.ctrl u >>= \r -> foldM step r (toUnfoldable (entries d.v) :: List (String × (Unit × Raw Val)))
      where
      step acc (k × _) =
         apply inputs f' (key : operand acc : entryOperand k d : Nil)
         where
         key = { v: Val unit Nothing (V.Lit (Str k)), srcs: project (\x -> Val (fst (entry k x)) Nothing (V.Lit (Str k))) d }
   higherOrder id _ = throw ("No dependence relation for " <> id)

   entries :: forall a. Val a -> Dict (a × Val a)
   entries (Val _ _ (V.Dictionary (DictRep d))) = d
   entries _ = error absurd

   entryOperand :: String -> Operand s -> Operand s
   entryOperand k d = { v: snd (entry k d.v), srcs: project (entry k >>> snd) d }

   dict :: Dict (s × Val s) -> Val s
   dict = DictRep >>> V.Dictionary >>> Val zero Nothing

   -- Dictionary with the given values, its root and key positions from those of the dictionary operands.
   dictFrom :: List (Operand s) -> List (String × Operand s) -> Operand s
   dictFrom ds kvs =
      { v: Val unit Nothing (V.Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × o) -> k × (unit × o.v)))))
      , srcs: concat (ds <#> project \x -> Val (rootOf x) Nothing (V.Dictionary (DictRep (mapWithKey (\k (_ × zu) -> fst (get k (entries x)) × zu) zd))))
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
         r <- evalStmt { ctrl: Nil, env: operand <$> ins } s
         pure (fst (asReturns r) × (fst <$> ins))
      pure { g, inputs, root }
