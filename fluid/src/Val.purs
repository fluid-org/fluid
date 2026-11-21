module Val where

import Prelude hiding (absurd, append, compose)

import Bind (Name, Var)
import Classes (class HasClasses)
import Types.Defs (cRange)
import Control.Apply (lift2)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (class MonadState, StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer (WriterT)
import Data.Array (cons, fromFoldable, length, zipWith, (!!)) as A
import Data.Map (Map)
import Data.Map as Map
import Data.Bitraversable (bitraverse)
import Data.Foldable (class Foldable, foldMap, foldMapDefaultL, foldl, foldrDefault, null)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Identity (Identity(..))
import Data.List (List(..), (:), zipWith)
import Data.List ((!!), range, reverse, take) as L
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.String.CodePoints (codePointAt, length, singleton) as S
import Data.Set as Set
import Data.Tuple (fst, snd)
import Data.Traversable (class Traversable, mapAccumL, sequenceDefault, traverse)
import Dict (Dict)
import Dict as D
import Expr (Def, Module, fv)
import File (class MonadLoad)
import Module.Defs (ModuleName)
import DepGraph (class Paths, Dependence, DepGraph, Labelling, Path, Rel, Sources(..), Step(..), compose, emptyGraph, newVertex, onto, pathAfter, paths, plus, positions, positionsOf, restructuring, scale, tupling, withCtrl, zeros, ε, ι, π)
import DepGraph (Deriv, Form(..), supp, valAt) as Dep
import Lattice (class BoundedLattice, class DepSemiring, DepKind(..), class JoinSemilattice, class MeetSemilattice, Lineage(..), Raw, ctrlWeight, erase, (∧), (∨))
import Literal (Literal(..))
import Types as T
import Pretty.Doc (Doc, text)
import Util (MayFail, class IsEmpty, type (×), Endo, absurd, definitely', definitelyRight, error, isEmpty, orThrow, shapeMismatch, singleton, unsafeUpdateAt, (!), (×), (∩), (≜))
import Util.Map (class Map, delete, filterKeys, get, insert, intersectionWith, keys, lookup, mapWithKey, maplet, restrict, toUnfoldable, unionWith, values)
import Util.Set (class Set, difference, empty, filter, size, union, (∈), (∪))

data Val a = Val a (BaseVal a)

data BaseVal a
   = Lit Literal
   | Obj Name (List (Var × Val a))
   | List (Array (Val a))
   | Tuple (Array (Val a))
   | Dictionary (DictRep a)
   | Matrix (MatrixRep a)
   | Fun (Fun a)
   | Opaque Name -- predefined name, fully qualified
   | Module ModuleName
   | Unbound
   | TypeAlias (List Var) T.Type

root :: forall a. Val a -> a
root (Val α _) = α

-- Label of a vertex
data Label a
   = Value (Val a) -- of an expression or returning statement
   | Assigns (Maybe a) (Env a) -- control position and bindings introduced by an assigning statement

value :: forall a. Label a -> Val a
value (Value v) = v
value _ = error absurd

instance Paths Val where
   paths = pathsFrom Nil

instance Paths Label where
   paths (Value v) = Value (paths v)
   paths (Assigns α (Env ρ)) =
      Assigns ((singleton Ctl × _) <$> α) (Env (mapWithKey (\x -> pathsFrom (singleton (Binding x))) ρ))

-- Same as paths, except that each path starts with the reverse of p
pathsFrom :: forall a. Path -> Val a -> Val (Path × a)
pathsFrom p (Val α u) = Val (L.reverse p × α) case u of
   Lit ℓ -> Lit ℓ
   Obj c xvs -> Obj c (mapWithIndex (\i (x × v) -> x × pathsFrom (Field i : p) v) xvs)
   List vs -> List (mapWithIndex (\i -> pathsFrom (Element i : p)) vs)
   Tuple vs -> Tuple (mapWithIndex (\i -> pathsFrom (Element i : p)) vs)
   Dictionary (DictRep d) ->
      Dictionary (DictRep (mapWithKey (\k (β × v) -> (L.reverse (Key k : p) × β) × pathsFrom (Entry k : p) v) d))
   Matrix (MatrixRep (vss × i × j)) -> Matrix $ MatrixRep $
      mapWithIndex (\i' -> mapWithIndex (\j' -> pathsFrom (MatrixElement i' j' : p))) vss
         × pathsFrom (RowCount : p) i
         × pathsFrom (ColumnCount : p) j
   Fun (Closure (Env ρ) ds d) -> Fun (Closure (Env (mapWithKey (\x -> pathsFrom (Captured x : p)) ρ)) ds d)
   Fun (Prim φ) -> Fun (Prim φ)
   Fun (Type τ) -> Fun (Type τ)
   Fun (Partial v vs) ->
      Fun (Partial (pathsFrom (PartialFun : p) v) (mapWithIndex (\i -> pathsFrom (PartialArg i : p)) vs))
   Opaque q -> Opaque q
   Module q -> Module q
   Unbound -> Unbound
   TypeAlias αs τ -> TypeAlias αs τ

part :: forall a. Step -> Val a -> Val a
part (Field i) v = field i v
part (Element i) v = element i v
part (Key k) v = Val (fst (dictEntry k v)) (Lit (Str k))
part (Entry k) v = snd (dictEntry k v)
part (MatrixElement i j) v = matrixElement i j v
part RowCount (Val _ (Matrix (MatrixRep (_ × i × _)))) = i
part ColumnCount (Val _ (Matrix (MatrixRep (_ × _ × j)))) = j
part (Captured x) v = get x (closureEnv v)
part PartialFun v = partialFun v
part (PartialArg i) v = partialArg i v
part _ _ = error absurd

overChildren :: forall a. Endo (Val a) -> Endo (BaseVal a)
overChildren _ (Lit ℓ) = Lit ℓ
overChildren _ (Opaque q) = Opaque q
overChildren _ (Module q) = Module q
overChildren _ Unbound = Unbound
overChildren _ (TypeAlias αs τ) = TypeAlias αs τ
overChildren f (Obj c xvs) = Obj c (map f <$> xvs)
overChildren f (List vs) = List (f <$> vs)
overChildren f (Tuple vs) = Tuple (f <$> vs)
overChildren f (Dictionary (DictRep d)) = Dictionary (DictRep (map f <$> d))
overChildren f (Matrix (MatrixRep (vss × i × j))) = Matrix (MatrixRep (map (map f) vss × i × j))
overChildren f (Fun φ) = Fun (overFun φ)
   where
   overFun (Closure (Env ρ) ds d) = Closure (Env (f <$> ρ)) ds d
   overFun (Partial v vs) = Partial (f v) (f <$> vs)
   overFun φ' = φ'

-- False at shape positions.
dataPositions :: forall a. Val a -> Val Boolean
dataPositions (Val _ u) = Val (not container) (overChildren dataPositions (false <$ u))
   where
   container = case u of
      Obj _ _ -> true
      List _ -> true
      Tuple _ -> true
      Dictionary _ -> true
      Matrix _ -> true
      _ -> false

data Fun a
   = Closure (Env a) (Dict Def) Def
   | Prim ForeignOp
   | Type T.Type
   | Partial (Val a) (List (Val a)) -- function applied to fewer arguments than arity; function is not partial

class (Highlightable a, BoundedLattice a) <= Ann a

instance Ann Boolean
instance Ann Unit

instance Highlightable a => Highlightable (a × b) where
   highlightIf (a × _) doc = highlightIf a doc

instance (Ann a, BoundedLattice b) => Ann (a × b)

-- Module parsed but not yet loaded, or loaded with its environment
data ModuleState s = Parsed Module | Loaded (Dict (GVal s))

loadedEnv :: forall s. ModuleState s -> Maybe (Dict (GVal s))
loadedEnv (Parsed _) = Nothing
loadedEnv (Loaded ρ) = Just ρ

type ModuleStore s =
   { modules :: Map ModuleName (ModuleState s)
   , depGraph :: DepGraph Label s
   }

emptyModuleStore :: forall s. ModuleStore s
emptyModuleStore = { modules: Map.empty, depGraph: emptyGraph }

class Monad m <= HasModuleStore s m | m -> s where
   moduleStore :: m (ModuleStore s)
   modifyModuleStore :: (ModuleStore s -> ModuleStore s) -> m Unit

instance (Monad m, HasModuleStore s m) => HasModuleStore s (StateT t m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore s m) => HasModuleStore s (ReaderT r m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore s m) => HasModuleStore s (ExceptT e m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore s m, Monoid w) => HasModuleStore s (WriterT w m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

-- Monad for evaluating program into dependence graph with weights in s
class
   ( HasClasses m
   , HasModuleStore s m
   , MonadLoad m
   , MonadState (DepGraph Label s) m
   , DepSemiring s
   ) <=
   MonadEval s m
   | m -> s

instance
   ( HasClasses m
   , HasModuleStore s m
   , MonadLoad m
   , MonadState (DepGraph Label s) m
   , DepSemiring s
   ) =>
   MonadEval s m

-- Monad for loading and evaluating program
class (HasClasses m, HasModuleStore DepKind m, MonadLoad m) <= MonadProgram m

instance (HasClasses m, HasModuleStore DepKind m, MonadLoad m) => MonadProgram m

-- Vertex with the vertex of its doc, if any.
type DerivWithDoc = Dep.Deriv × Maybe Dep.Deriv

withDoc :: forall f s. DepGraph f s -> Dep.Deriv -> DerivWithDoc
withDoc g p = p × Map.lookup p g.docs

-- Value with its doc, as shown in a figure.
newtype ValWithDoc a = ValWithDoc { val :: Val a, doc :: Maybe (Val a) }
newtype EnvWithDocs a = EnvWithDocs (Dict (ValWithDoc a))

-- Value at a vertex, with the value of its doc.
val :: forall a. Labelling (Val a) -> DerivWithDoc -> ValWithDoc a
val m (p × d) = ValWithDoc { val: get p m, doc: flip get m <$> d }

unval :: forall a. DerivWithDoc -> ValWithDoc a -> Labelling (Val a)
unval (p × d) (ValWithDoc { val: v, doc }) = Map.fromFoldable (A.cons (p × v) (A.fromFoldable ((×) <$> d <*> doc)))

unvals :: forall a. Dict DerivWithDoc -> EnvWithDocs a -> Labelling (Val a)
unvals ps (EnvWithDocs vs) = Map.unions (values (intersectionWith unval ps vs))

-- Value at the vertex of an expression or returning statement
valAt :: forall s. DepGraph Label s -> Dep.Deriv -> Raw Val
valAt g p = value (Dep.valAt g p)

-- Weight 1 at every position except beneath the root of a closure
unitSection :: forall a s. Semiring s => Val a -> Val s
unitSection (Val _ u) = Val one case u of
   Lit ℓ -> Lit ℓ
   Obj c xvs -> Obj c (map unitSection <$> xvs)
   List vs -> List (unitSection <$> vs)
   Tuple vs -> Tuple (unitSection <$> vs)
   Dictionary (DictRep d) -> Dictionary (DictRep ((\(_ × v) -> one × unitSection v) <$> d))
   Matrix (MatrixRep (vss × i × j)) -> Matrix (MatrixRep (map (map unitSection) vss × unitSection i × unitSection j))
   Fun φ -> Fun (zeros φ)
   Opaque q -> Opaque q
   Module q -> Module q
   Unbound -> Unbound
   TypeAlias αs τ -> TypeAlias αs τ

-- Control edge from β to the whole of v
ctrlEdge :: forall a. DepSemiring a => a -> Endo (Val a)
ctrlEdge β v = plus v (scale (ctrlWeight * β) (unitSection v))

-- Value together with its dependence on the values of vertices already in the graph
newtype GVal s = GVal { val :: Raw Val, dep :: Dependence s }
-- Positions in the values of vertices already in the graph, as sources of control dependence
type Ctrl = Set Path

raw :: forall s. GVal s -> Raw Val
raw (GVal v) = v.val

-- Sources of position q of v
supp :: forall s. Semiring s => Path -> GVal s -> Sources s
supp q (GVal v) = Dep.supp v.dep q

-- Control input from position q of v
via :: forall s. Semiring s => Path -> GVal s -> Ctrl
via q = supp q >>> positionsOf

-- Control input from every position of v
viaAll :: forall s. Semiring s => GVal s -> Ctrl
viaAll v = foldMap (\(q × _) -> via q v) (positions (paths (raw v)))

-- Control input from the length of sequence v
viaLength :: forall s. Semiring s => GVal s -> Ctrl
viaLength v = foldMap (_ `via` v) (lengthPositions (raw v))

-- Value v at position p of a vertex, as a value which depends on that position
reuse :: forall s. Semiring s => Path -> Raw Val -> GVal s
reuse p v = GVal { val: v, dep: restructuring (Dep.Reuse p) × mempty }

-- Value v of vertex a as a value which depends on a
gval :: forall s. Semiring s => Dep.Deriv × Raw Val -> GVal s
gval (a × v) = reuse (singleton (Vertex a)) v

-- Allocate vertex labelled with given value; return vertex with raw value
newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m (Dep.Deriv × Raw Val)
newValue (GVal { val: v, dep }) = newVertex (Value v) dep <#> (_ × v)

-- Allocate vertex with bindings ρ and control position ctrl as label; returned ρ and ctrl depend on the vertex
newAssigns
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Semiring s
   => Dict (GVal s)
   -> Maybe Ctrl
   -> m (Dict (GVal s) × Maybe Ctrl)
newAssigns ρ ctrl = newVertex (Assigns (void ctrl) (Env (raw <$> ρ))) (tupling (Map.union bindings ctl)) <#> \a ->
   mapWithKey (\x v -> reuse (Vertex a : Binding x : Nil) (raw v)) ρ × (ctrl $> singleton (Vertex a : Ctl : Nil))
   where
   bindings = Map.fromFoldable ((toUnfoldable ρ :: List _) <#> \(x × GVal v) -> Binding x × v.dep)
   ctl = Map.fromFoldable $
      ctrl <#> \ps -> Ctl × (restructuring Dep.Zero × onto (Sources Set.empty (Set.toMap ps $> one)))

-- Part of v at step
project :: forall s. Semiring s => Step -> GVal s -> GVal s
project step (GVal { val: v, dep: θ × r }) = GVal { val: part step v, dep: pathAfter p θ × π p r }
   where
   p = singleton step

-- Pass on v; every position outside a function value also depends on ctrl
deliver :: forall s. Ctrl -> GVal s -> GVal s
deliver ctrl (GVal v@{ dep: θ × r }) = GVal (v { dep = withCtrl ctrl θ × r })

-- Value u with the given parts; root depends on ctrl
construct :: forall s. DepSemiring s => Ctrl -> Raw BaseVal -> List (Step × GVal s) -> GVal s
construct ctrl = constructFrom ctrl Nil

-- Same as construct, except that the root also depends on the root of each of vs
constructFrom :: forall s. DepSemiring s => Ctrl -> List (GVal s) -> Raw BaseVal -> List (Step × GVal s) -> GVal s
constructFrom ctrl vs u parts =
   GVal { val: Val unit u, dep: θ × (onto (Sources ctrl Map.empty <> foldMap (supp ε) vs) <> r) }
   where
   θ × r =
      if null parts then restructuring Dep.Zero × mempty
      else tupling (Map.fromFoldable (map (\(GVal v) -> v.dep) <$> parts))

-- Result of f at vs, if any; result depends on vs through the derivative of f at vs
applyRel
   :: forall t s
    . Traversable t
   => DepSemiring s
   => (forall a. DepSemiring a => t (Val a) -> MayFail (Val a))
   -> t (GVal s)
   -> MayFail (GVal s)
applyRel f vs = f (arg <$> vs') <#> \v ->
   GVal { val: erase v, dep: compose (restructuring Dep.Zero × foldl row mempty (positions (paths v))) (tupling args) }
   where
   vs' = (mapAccumL (\i v -> { accum: i + 1, value: i × v }) 0 vs).value
   args = Map.fromFoldable (vs' <#> \(i × GVal v) -> Arg i × v.dep)

   arg :: Int × GVal s -> Val (Lineage Path s)
   arg (i × GVal v) = paths v.val <#> \(p × _) -> Lineage (zero × Map.singleton (Arg i : p) one)

   row :: Rel s -> Path × Lineage Path s -> Rel s
   row r (p × Lineage (_ × ws))
      | Map.isEmpty ws = r
      | otherwise = r <> ι p (onto (Sources Set.empty ws))

-- Element i of sequence v: part of v for list, tuple or dictionary, computed from v otherwise
elementOf :: forall s. DepSemiring s => Int -> GVal s -> GVal s
elementOf i v = case raw v of
   Val _ (List _) -> project (Element i) v
   Val _ (Tuple _) -> project (Element i) v
   Val _ (Dictionary (DictRep d)) -> project (Key (fst (definitely' (toUnfoldable d L.!! i)))) v
   _ -> definitelyRight (applyRel (\(Identity u) -> pure (element i u)) (Identity v))

elementsOf :: forall s. DepSemiring s => GVal s -> List (GVal s)
elementsOf v = (\i -> elementOf i v) <$> L.take n (L.range 0 n)
   where
   n = definitely' (elementCount (raw v))

-- Dictionary from list v of key-value tuples; a later entry overrides an earlier entry with the same key
toDict :: forall s. DepSemiring s => GVal s -> GVal s
toDict v = constructFrom mempty (singleton v)
   (Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × _ × u) -> k × unit × raw u))))
   (kvs >>= \(k × key × u) -> (Key k × key) : (Entry k × u) : Nil)
   where
   kvs = elementsOf v <#> \kv -> case project (Element 0) kv of
      key@(GVal { val: Val _ (Lit (Str k)) }) -> k × key × project (Element 1) kv
      _ -> error absurd

-- Concatenation of lists vs; each element also depends on the root of its list
concatLists :: forall s. DepSemiring s => Ctrl -> List (GVal s) -> GVal s
concatLists ctrl vs =
   constructFrom ctrl vs (List (A.fromFoldable (raw <$> us))) (mapWithIndex (\i u -> Element i × u) us)
   where
   us = vs >>= \v -> deliver (via ε v) <$> elementsOf v

-- Application of a function to arguments at a new vertex
type Apply m s = GVal s -> List (GVal s) -> m (GVal s)

-- Foreign function of control input and arguments; evaluator supplies operation for applying a function argument
type DepOp =
   forall m s
    . HasClasses m
   => MonadLoad m
   => DepSemiring s
   => Apply m s
   -> Ctrl
   -> List (GVal s)
   -> m (GVal s)

-- Foreign function with derivative given by f; application of f may fail
fromRel :: (forall a. DepSemiring a => List (Val a) -> MayFail (Val a)) -> DepOp
fromRel f _ ctrl vs = deliver ctrl <$> orThrow (applyRel f vs)

data ForeignOp' = ForeignOp'
   { arity :: Int
   , depOp :: DepOp
   }

newtype ForeignOp = ForeignOp (String × ForeignOp') -- string is unique identifier for Eq

instance Eq ForeignOp where
   eq (ForeignOp (s × _)) (ForeignOp (s' × _)) = s == s'

instance Ord ForeignOp where
   compare (ForeignOp (s × _)) (ForeignOp (s' × _)) = compare s s'

newtype Env a = Env (Dict (Val a))

instance IsEmpty (Env a) where
   isEmpty (Env ρ) = isEmpty ρ

instance Set (Env a) String where
   empty = Env empty
   filter p (Env ρ) = Env (filter p ρ)
   size (Env ρ) = size ρ
   member x (Env ρ) = x ∈ ρ
   difference (Env ρ) (Env ρ') = Env (difference ρ ρ')
   union (Env ρ) (Env ρ') = Env (union ρ ρ')

instance Map (Env a) String (Val a) where
   maplet k v = Env (maplet k v)
   keys (Env ρ) = keys ρ
   values (Env ρ) = values ρ
   filterKeys p (Env ρ) = Env (filterKeys p ρ)
   unionWith f (Env ρ) (Env ρ') = Env (unionWith f ρ ρ')
   lookup k (Env ρ) = lookup k ρ
   delete k (Env ρ) = Env (delete k ρ)
   insert k v (Env ρ) = Env (insert k v ρ)
   toUnfoldable (Env ρ) = toUnfoldable ρ

reaches :: Dict Def -> Endo (Set Var)
reaches ds xs = go (Set.toUnfoldable xs) empty
   where
   dom_ds = keys ds

   go :: List Var -> Endo (Set Var)
   go Nil acc = acc
   go (x : xs') acc | x ∈ acc = go xs' acc
   go (x : xs') acc | otherwise =
      go (Set.toUnfoldable (fv d ∩ dom_ds) <> xs') (singleton x ∪ acc)
      where
      d = get x ds

forDefs :: Dict Def -> Def -> Dict Def
forDefs ds d = restrict (reaches ds (fv d ∩ Set.fromFoldable (keys ds))) ds

-- Wrap internal representations to provide foldable/traversable instances.
newtype DictRep a = DictRep (Dict (a × Val a))
-- Elements with row and column counts, as int values.
newtype MatrixRep a = MatrixRep (Array2 (Val a) × Val a × Val a)
type Array2 a = Array (Array a)

matrixGet :: forall a. Int -> Int -> MatrixRep a -> Val a
matrixGet i j (MatrixRep (vss × _ × _)) = definitely' ((_ A.!! j) =<< vss A.!! i)

matrixElement :: forall a. Int -> Int -> Val a -> Val a
matrixElement i j (Val _ (Matrix r)) = matrixGet i j r
matrixElement _ _ _ = error absurd

field :: forall a. Int -> Val a -> Val a
field i (Val _ (Obj _ xvs)) = snd (xvs ! i)
field _ _ = error absurd

attr :: forall a. Var -> Val a -> Val a
attr x (Val _ (Obj _ xvs)) = get x (D.fromFoldable xvs)
attr _ _ = error absurd

-- i-th element of a sequence: element of a list or tuple, character of a string, key of a dictionary, integer of a range.
element :: forall a. Int -> Val a -> Val a
element i (Val _ (List vs)) = definitely' (vs A.!! i)
element i (Val _ (Tuple vs)) = definitely' (vs A.!! i)
element i (Val α (Lit (Str s))) = Val α (Lit (Str (definitely' (S.singleton <$> S.codePointAt i s))))
element i (Val _ (Dictionary (DictRep d))) = let k × (β × _) = definitely' (toUnfoldable d L.!! i) in Val β (Lit (Str k))
element i (Val _ (Obj c ((_ × Val β (Lit (Int m))) : _ : Nil))) | c == cRange = Val β (Lit (Int (m + i)))
element _ _ = error absurd

elements :: forall a. Val a -> List (Val a)
elements v = (\i -> element i v) <$> L.take n (L.range 0 n)
   where
   n = definitely' (elementCount v)

-- Positions which determine the length of a sequence: the root, plus start and stop of a range
lengthPositions :: forall a. Val a -> List Path
lengthPositions (Val _ (Obj c _)) | c == cRange = ε : singleton (Field 0) : singleton (Field 1) : Nil
lengthPositions _ = singleton ε

elementCount :: forall a. Val a -> Maybe Int
elementCount (Val _ (List vs)) = Just (A.length vs)
elementCount (Val _ (Tuple vs)) = Just (A.length vs)
elementCount (Val _ (Obj c ((_ × Val _ (Lit (Int m))) : (_ × Val _ (Lit (Int n))) : Nil))) | c == cRange =
   Just (max 0 (n - m))
elementCount (Val _ (Lit (Str s))) = Just (S.length s)
elementCount (Val _ (Dictionary (DictRep d))) = Just (size d)
elementCount _ = Nothing

dictEntries :: forall a. Val a -> Dict (a × Val a)
dictEntries (Val _ (Dictionary (DictRep d))) = d
dictEntries _ = error absurd

dictEntry :: forall a. String -> Val a -> a × Val a
dictEntry k = dictEntries >>> get k

closureEnv :: forall a. Val a -> Env a
closureEnv (Val _ (Fun (Closure ρ _ _))) = ρ
closureEnv _ = error absurd

partialFun :: forall a. Val a -> Val a
partialFun (Val _ (Fun (Partial v _))) = v
partialFun _ = error absurd

partialArg :: forall a. Int -> Val a -> Val a
partialArg i (Val _ (Fun (Partial _ vs))) = definitely' (vs L.!! i)
partialArg _ _ = error absurd

matrixPut :: forall a. Int -> Int -> Endo (Val a) -> Endo (MatrixRep a)
matrixPut i j δv (MatrixRep (vss × h × w)) =
   MatrixRep (vss' × h × w)
   where
   vs_i = vss ! i
   v_j = vs_i ! j
   vss' = unsafeUpdateAt i (unsafeUpdateAt j (δv v_j) vs_i) vss

class Highlightable a where
   highlightIf :: a -> Endo Doc

instance Highlightable Unit where
   highlightIf _ = identity

instance Highlightable Boolean where
   highlightIf false = identity
   highlightIf true = \doc -> text "⸨" <> doc <> text "⸩"

instance Highlightable DepKind where
   highlightIf Zero = identity
   highlightIf Ctrl = \doc -> text "⟪" <> doc <> text "⟫"
   highlightIf Data = \doc -> text "⸨" <> doc <> text "⸩"

-- ======================
-- boilerplate
-- ======================
derive instance Functor DictRep
derive instance Functor MatrixRep
derive instance Functor Val
derive instance Functor Env
derive instance Functor ValWithDoc
derive instance Functor EnvWithDocs
derive instance Functor Fun
derive instance Functor BaseVal
derive instance Functor Label
derive instance Traversable Val
derive instance Traversable BaseVal
derive instance Traversable Label
derive instance Traversable Fun
derive instance Traversable Env
derive instance Traversable ValWithDoc
derive instance Traversable EnvWithDocs
derive instance Foldable Val
derive instance Foldable BaseVal
derive instance Foldable Label
derive instance Foldable Fun
derive instance Foldable Env
derive instance Foldable ValWithDoc
derive instance Foldable EnvWithDocs

instance Apply Val where
   apply (Val fα fv) (Val α v) = Val (fα α) (fv <*> v)

instance Apply ValWithDoc where
   apply (ValWithDoc f) (ValWithDoc v) = ValWithDoc { val: f.val <*> v.val, doc: lift2 (<*>) f.doc v.doc }

instance Apply EnvWithDocs where
   apply (EnvWithDocs fρ) (EnvWithDocs ρ) = EnvWithDocs (((<*>) <$> fρ) <*> ρ)

instance Apply BaseVal where
   apply (Lit ℓ) (Lit ℓ') = Lit (ℓ ≜ ℓ')
   apply (Obj c fxes) (Obj c' xes) = Obj (c ≜ c') (zipWith (\(x × f) (x' × e) -> (x ≜ x') × (f <*> e)) fxes xes)
   apply (List fvs) (List vs) = List (A.zipWith (<*>) fvs vs)
   apply (Tuple fvs) (Tuple vs) = Tuple (A.zipWith (<*>) fvs vs)
   apply (Dictionary fxvs) (Dictionary xvs) = Dictionary (fxvs <*> xvs)
   apply (Matrix fm) (Matrix m) = Matrix (fm <*> m)
   apply (Fun ff) (Fun f) = Fun (ff <*> f)
   apply (Opaque q) (Opaque q') = Opaque (q ≜ q')
   apply (Module q) (Module q') = Module (q ≜ q')
   apply Unbound Unbound = Unbound
   apply (TypeAlias αs τ) (TypeAlias αs' τ') = TypeAlias (αs ≜ αs') (τ ≜ τ')
   apply _ _ = shapeMismatch unit

instance Apply Fun where
   apply (Closure fρ ds d) (Closure ρ _ _) = Closure (fρ <*> ρ) ds d
   apply (Prim op) (Prim _) = Prim op
   apply (Type τ) (Type τ') = Type (τ ≜ τ')
   apply (Partial fv fvs) (Partial v vs) = Partial (fv <*> v) (zipWith (<*>) fvs vs)
   apply _ _ = shapeMismatch unit

-- Should require equal domains?
instance Apply DictRep where
   apply (DictRep fxvs) (DictRep xvs) =
      DictRep $ intersectionWith (\(fα × fv) (α × v) -> fα α × (fv <*> v)) fxvs xvs

instance Apply MatrixRep where
   apply (MatrixRep (fvss × fn × fm)) (MatrixRep (vss × n × m)) =
      MatrixRep $ (A.zipWith (A.zipWith (<*>)) fvss vss) × (fn <*> n) × (fm <*> m)

instance Apply Env where
   apply (Env fρ) (Env ρ) = Env (((<*>) <$> fρ) <*> ρ)

instance Foldable DictRep where
   foldl f acc (DictRep d) = foldl (\acc' (a × v) -> foldl f (acc' `f` a) v) acc d
   foldr f = foldrDefault f
   foldMap f = foldMapDefaultL f

instance Traversable DictRep where
   traverse f (DictRep d) = DictRep <$> traverse (bitraverse f (traverse f)) d
   sequence = sequenceDefault

instance Foldable MatrixRep where
   foldl f acc (MatrixRep (vss × i × j)) = foldl (foldl (foldl f)) (foldl f (foldl f acc i) j) vss
   foldr f = foldrDefault f
   foldMap f = foldMapDefaultL f

instance Traversable MatrixRep where
   traverse f (MatrixRep m) =
      MatrixRep <$> bitraverse (traverse (traverse (traverse f)))
         (bitraverse (traverse f) (traverse f))
         m
   sequence = sequenceDefault

instance JoinSemilattice a => JoinSemilattice (DictRep a) where
   join (DictRep svs) (DictRep svs') = DictRep (svs ∨ svs')

instance JoinSemilattice a => JoinSemilattice (MatrixRep a) where
   join (MatrixRep (vss × i × j)) (MatrixRep (vss' × i' × j')) =
      MatrixRep ((vss ∨ vss') × ((i ∨ i') × (j ∨ j')))

instance JoinSemilattice a => JoinSemilattice (Val a) where
   join (Val α u) (Val α' v) = Val (α ∨ α') (u ∨ v)

-- Not equivalent to sequence (join <$> x <*> y) because Dict.join only requires compatibility
-- whereas Dict.apply requires domains to be equal.
instance JoinSemilattice a => JoinSemilattice (BaseVal a) where
   join (Lit ℓ) (Lit ℓ') = Lit (ℓ ≜ ℓ')
   join (Dictionary d) (Dictionary d') = Dictionary (d ∨ d')
   join (Obj c xvs) (Obj c' xus) = Obj (c ≜ c') (zipWith (\(x × v) (x' × u) -> (x ≜ x') × (v ∨ u)) xvs xus)
   join (List vs) (List us) = List (vs ∨ us)
   join (Tuple vs) (Tuple us) = Tuple (vs ∨ us)
   join (Matrix m) (Matrix m') = Matrix (m ∨ m')
   join (Fun φ) (Fun φ') = Fun (φ ∨ φ')
   join x y = (∨) <$> x <*> y

instance JoinSemilattice a => JoinSemilattice (Fun a) where
   join (Closure ρ ds d) (Closure ρ' _ _) = Closure (ρ ∨ ρ') ds d
   join (Prim φ) (Prim _) = Prim φ -- TODO: require φ == φ'
   join (Type τ) (Type τ') = Type (τ ≜ τ')
   join (Partial v vs) (Partial v' vs') = Partial (v ∨ v') (vs ∨ vs')
   join _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (Env a) where
   join (Env ρ) (Env ρ') = Env (ρ ∨ ρ')

instance MeetSemilattice a => MeetSemilattice (Val a) where
   meet = lift2 (∧)

instance MeetSemilattice a => MeetSemilattice (ValWithDoc a) where
   meet = lift2 (∧)

instance MeetSemilattice a => MeetSemilattice (Env a) where
   meet = lift2 (∧)

derive instance Eq a => Eq (Val a)
derive newtype instance Eq a => Eq (ValWithDoc a)
derive newtype instance Eq a => Eq (EnvWithDocs a)
derive instance Eq a => Eq (BaseVal a)
derive instance Eq a => Eq (DictRep a)
derive instance Eq a => Eq (MatrixRep a)
derive instance Eq a => Eq (Fun a)
derive instance Eq a => Eq (Env a)

derive instance Newtype (Env a) _
derive instance Newtype (ValWithDoc a) _
derive instance Newtype (EnvWithDocs a) _
