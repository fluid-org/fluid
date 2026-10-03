module Val where

import Prelude hiding (absurd, append)

import Bind (Name, Var)
import DataType (class HasClasses)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (class MonadReader, ReaderT)
import Control.Monad.State (class MonadState, StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer (WriterT)
import Data.Array (concat, zipWith, (!!)) as A
import Data.Map (Map)
import Data.Map as Map
import Data.Bitraversable (bitraverse)
import Data.Foldable (class Foldable, fold, foldMapDefaultL, foldl, foldrDefault, for_)
import Data.Functor.Compose (Compose(..))
import Data.List (List(..), (:), zipWith)
import Data.List ((!!)) as L
import Data.Either (Either)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set, unions)
import Data.Set as Set
import Data.Profunctor.Strong (second)
import Data.Traversable (class Traversable, mapAccumL, sequenceDefault, traverse)
import Dict (Dict)
import Dict as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Def, Module, fv)
import File (class LoadFile, FileCxt)
import ModuleGraph (ModuleName)
import Foreign.Object (foldMap)
import Graph (class TypeName, class Vertices, DVertex'(..), Vertex(..), VertexData, pack, typeName, unpack, vertices)
import Graph.Dep (DepGraph, Rel, edge, scale, vertex, zeros)
import Graph.Dep (Vertex) as Dep
import Graph.WithGraph (class MonadWithGraphAlloc, new)
import Lattice (class BoundedJoinSemilattice, class BoundedLattice, class DepSemiring, class Expandable, DepKind(..), class JoinSemilattice, class MeetSemilattice, Raw, ctrlWeight, expand, (∧), (∨))
import Literal (Literal)
import Pretty.Doc (Doc, text)
import Unsafe.Coerce (unsafeCoerce)
import Util (class IsEmpty, type (×), Endo, absurd, definitely, definitely', definitelyRight, error, isEmpty, orThrow, shapeMismatch, singleton, unsafeUpdateAt, (!), (×), (∩), (≜))
import Util.Pair (Pair(..))
import Util.Map (class Map, delete, filterKeys, get, insert, intersectionWith, keys, lookup, maplet, restrict, toUnfoldable, unionWith, values)
import Util.Set (class Set, difference, empty, filter, size, union, (∈), (∪))

data Val a = Val a (Maybe (Val a)) (BaseVal a)

data Result a = Returns (Val a) | Assigns (Env a) (Set.Set a)

asReturns :: forall a. Result a -> Val a
asReturns (Returns v) = v
asReturns (Assigns _ _) = error "Returns expected"

asAssigns :: forall a. Result a -> Env a × Set.Set a
asAssigns (Assigns ρ αs) = ρ × αs
asAssigns (Returns _) = error "Assigns expected"

data BaseVal a
   = Lit Literal
   | Constr Name (List (Val a)) -- always saturated
   | List (Array (Val a))
   | Dictionary (DictRep a)
   | Matrix (MatrixRep a)
   | Fun (Fun a)

val :: forall m. MonadWithGraphAlloc m => Maybe (Val Vertex) -> Set Vertex -> BaseVal Vertex -> m (Val Vertex)
val doc_opt = new (flip Val doc_opt)

asVal :: VertexData -> Maybe (Val Vertex)
asVal e = if unpack typeName e == "Val" then Just (unpack unsafeCoerce e) else Nothing

root :: forall a. Val a -> a
root (Val α _ _) = α

-- Docs are vertices in the dependence graph; retire with the α-graph.
stripDocs :: forall a. Val a -> Val a
stripDocs (Val α _ u) = Val α Nothing case u of
   Constr c vs -> Constr c (stripDocs <$> vs)
   List vs -> List (stripDocs <$> vs)
   Dictionary (DictRep d) -> Dictionary (DictRep (map stripDocs <$> d))
   Matrix (MatrixRep (vss × i × j)) -> Matrix (MatrixRep (map (map stripDocs) vss × i × j))
   Fun (Closure (Env ρ) ds d) -> Fun (Closure (Env (stripDocs <$> ρ)) ds d)
   Fun (Partial φ vs) -> Fun (Partial φ (stripDocs <$> vs))
   _ -> u

data Fun a
   = Closure (Env a) (Dict Def) Def
   | Prim ForeignOp
   | Type Name -- class as a value, as at the Python runtime
   | Partial (Fun a) (List (Val a)) -- fewer arguments than the arity of the function, which is not itself partial

class (Highlightable a, BoundedLattice a) <= Ann a

instance Ann Boolean
instance Ann Unit

instance Highlightable a => Highlightable (a × b) where
   highlightIf (a × _) doc = highlightIf a doc

instance (Ann a, BoundedLattice b) => Ann (a × b)

type ModuleStore =
   { ρ0 :: Env Vertex -- members of the implicit modules
   , moduleBody :: Map ModuleName Module
   , moduleEnv :: Map ModuleName (Env Vertex)
   }

emptyModuleStore :: ModuleStore
emptyModuleStore = { ρ0: empty, moduleBody: Map.empty, moduleEnv: Map.empty }

class Monad m <= HasModuleStore m where
   moduleStore :: m ModuleStore
   modifyModuleStore :: (ModuleStore -> ModuleStore) -> m Unit

instance (Monad m, HasModuleStore m) => HasModuleStore (StateT s m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore m) => HasModuleStore (ReaderT r m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore m) => HasModuleStore (ExceptT e m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

instance (Monad m, HasModuleStore m, Monoid w) => HasModuleStore (WriterT w m) where
   moduleStore = lift moduleStore
   modifyModuleStore = lift <<< modifyModuleStore

type Op =
   forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => Maybe (Val Vertex) -- optional doc context
   -> List (Val Vertex)
   -> m (Val Vertex)

type InEdges s = List (Dep.Vertex × Rel (Val s) (Val s))
-- Value together with its dependence on values already in the graph.
type GVal s = { val :: Raw Val, inEdges :: InEdges s }
-- Dependence of the control input on values already in the graph.
type Ctrl s = List (Dep.Vertex × Rel (Val s) s)

-- Weight 1 at every position except beneath the root of a closure.
unitSection :: forall s. Semiring s => Raw Val -> Val s
unitSection (Val _ _ u) = Val one Nothing case u of
   Lit ℓ -> Lit ℓ
   Constr c vs -> Constr c (unitSection <$> vs)
   List vs -> List (unitSection <$> vs)
   Dictionary (DictRep d) -> Dictionary (DictRep ((\(_ × v) -> one × unitSection v) <$> d))
   Matrix (MatrixRep (vss × MatrixDim (i × _) × MatrixDim (j × _))) ->
      Matrix (MatrixRep (map (map unitSection) vss × MatrixDim (i × one) × MatrixDim (j × one)))
   Fun φ -> Fun (zeros φ)

gval :: forall s. Dep.Vertex × Raw Val -> GVal s
gval (p × v) = { val: v, inEdges: singleton (p × identity) }

-- Dependence on values already in the graph of a value that depends on v by r.
via :: forall s b. Rel (Val s) b -> GVal s -> List (Dep.Vertex × Rel (Val s) b)
via r v = second (r <<< _) <$> v.inEdges

-- Dependence on values already in the graph of a value that depends on vs by r.
viaAll :: forall t s. Traversable t => Semiring s => Rel (t (Val s)) (Val s) -> t (GVal s) -> InEdges s
viaAll r vs = fold (ivs <#> \(i × v) -> via (\x -> r (zs <#> \(j × z) -> if i == j then x else z)) v)
   where
   ivs = (mapAccumL (\i v -> { accum: i + 1, value: i × v }) 0 vs).value
   zs = map (zeros <<< _.val) <$> ivs

-- Adds dependence on control at weight c to the positions of v in the given section.
withCtrl :: forall s. DepSemiring s => Ctrl s -> Val s -> GVal s -> GVal s
withCtrl ctrl section v =
   v { inEdges = v.inEdges <> (ctrl <#> second \r x -> scale (ctrlWeight * r x) section) }

-- Constructed value: root depends on control at weight c.
constructed :: forall s. DepSemiring s => Ctrl s -> GVal s -> GVal s
constructed ctrl v@{ val: Val _ _ u } = withCtrl ctrl (Val one Nothing (zeros u)) v

vertexOf :: forall m s. MonadState (DepGraph Val s) m => Semiring s => GVal s -> m (Dep.Vertex × Raw Val)
vertexOf { val: v, inEdges } = do
   p <- vertex v
   for_ inEdges \(q × r) -> edge q p r
   pure (p × v)

-- Value delivered rather than constructed: every position depends on control at weight c.
deliver :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Dep.Vertex × Raw Val)
deliver ctrl v = vertexOf (withCtrl ctrl (unitSection v.val) v)

construct :: forall m s. MonadState (DepGraph Val s) m => DepSemiring s => Ctrl s -> GVal s -> m (Dep.Vertex × Raw Val)
construct ctrl v = vertexOf (constructed ctrl v)

constructWith
   :: forall t m s
    . Traversable t
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> (forall a. t (Val a) -> BaseVal a)
   -> t (GVal s)
   -> m (Dep.Vertex × Raw Val)
constructWith ctrl mk vs =
   construct ctrl { val: Val unit Nothing (mk (_.val <$> vs)), inEdges: viaAll (mk >>> Val zero Nothing) vs }

-- Dictionary from keys and values; later entries overwrite earlier ones.
dictionary
   :: forall m s
    . MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> List (String × GVal s × GVal s)
   -> m (Dep.Vertex × Raw Val)
dictionary ctrl kvs =
   constructWith ctrl mk (Compose (D.fromFoldable (kvs <#> \(k × key × v) -> k × Pair key v)))
   where
   mk :: forall a. Compose Dict Pair (Val a) -> BaseVal a
   mk (Compose d) = Dictionary (DictRep (d <#> \(Pair key v) -> root key × v))

type DepOp =
   forall m s
    . HasClasses m
   => HasModuleStore m
   => MonadError Error m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadState (DepGraph Val s) m
   => DepSemiring s
   => Ctrl s
   -> List (GVal s)
   -> m (Dep.Vertex × Raw Val)

-- Primitive given by its dependence relation, a linear map from argument weight vectors to the result weight
-- vector; at Unit, the value itself.
fromRel :: (forall a. DepSemiring a => List (Val a) -> Val a) -> DepOp
fromRel g ctrl vs = deliver ctrl { val: g (_.val <$> vs), inEdges: viaAll g vs }

-- Relation of a primitive without effects, checked at the argument values.
pureRel :: (forall a. DepSemiring a => List (Val a) -> Either String (Val a)) -> DepOp
pureRel f ctrl vs = do
   _ <- orThrow (f (_.val <$> vs))
   fromRel (f >>> definitelyRight) ctrl vs

data ForeignOp' = ForeignOp'
   { arity :: Int
   , op :: Op
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
newtype DictKey a = DictKey (String × a)
newtype MatrixDim a = MatrixDim (Int × a)
newtype MatrixRep a = MatrixRep (Array2 (Val a) × MatrixDim a × MatrixDim a)
type Array2 a = Array (Array a)

matrixGet :: forall a. Int -> Int -> MatrixRep a -> Val a
matrixGet i j (MatrixRep (vss × _ × _)) = definitely "matrix indices within bounds" $ do
   us <- vss A.!! i
   us A.!! j

matrixElement :: forall a. Int -> Int -> Val a -> Val a
matrixElement i j (Val _ _ (Matrix r)) = matrixGet i j r
matrixElement _ _ _ = error absurd

field :: forall a. Int -> Val a -> Val a
field i (Val _ _ (Constr _ vs)) = definitely' (vs L.!! i)
field _ _ = error absurd

listElement :: forall a. Int -> Val a -> Val a
listElement i (Val _ _ (List vs)) = definitely' (vs A.!! i)
listElement _ _ = error absurd

dictEntries :: forall a. Val a -> Dict (a × Val a)
dictEntries (Val _ _ (Dictionary (DictRep d))) = d
dictEntries _ = error absurd

dictEntry :: forall a. String -> Val a -> a × Val a
dictEntry k = dictEntries >>> get k

fun :: forall a. Val a -> Fun a
fun (Val _ _ (Fun φ)) = φ
fun _ = error absurd

closureEnv :: forall a. Val a -> Env a
closureEnv (Val _ _ (Fun (Closure ρ _ _))) = ρ
closureEnv _ = error absurd

partialFun :: forall a. Val a -> Val a
partialFun (Val α doc (Fun (Partial φ _))) = Val α doc (Fun φ)
partialFun _ = error absurd

partialArg :: forall a. Int -> Val a -> Val a
partialArg i (Val _ _ (Fun (Partial _ vs))) = definitely' (vs L.!! i)
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

instance Highlightable Vertex where
   highlightIf (Vertex α) = \doc -> doc <> text "_" <> text ("⟨" <> α <> "⟩")

-- ======================
-- boilerplate
-- ======================
derive instance Functor DictRep
derive instance Functor MatrixRep
derive instance Functor MatrixDim
derive instance Functor Val
derive instance Functor Env
derive instance Functor Fun
derive instance Functor BaseVal
derive instance Traversable MatrixDim
derive instance Traversable Val
derive instance Traversable BaseVal
derive instance Traversable Fun
derive instance Traversable Env
derive instance Foldable MatrixDim
derive instance Foldable Val
derive instance Foldable BaseVal
derive instance Foldable Fun
derive instance Foldable Env

instance Apply Val where
   apply (Val fα Nothing fv) (Val α Nothing v) = Val (fα α) Nothing (fv <*> v)
   apply (Val fα (Just fdoc) fv) (Val α (Just doc) v) = Val (fα α) (Just (fdoc <*> doc)) (fv <*> v)
   apply _ _ = shapeMismatch unit

instance Apply BaseVal where
   apply (Lit ℓ) (Lit ℓ') = Lit (ℓ ≜ ℓ')
   apply (Constr c fes) (Constr c' es) = Constr (c ≜ c') (zipWith (<*>) fes es)
   apply (List fvs) (List vs) = List (A.zipWith (<*>) fvs vs)
   apply (Dictionary fxvs) (Dictionary xvs) = Dictionary (fxvs <*> xvs)
   apply (Matrix fm) (Matrix m) = Matrix (fm <*> m)
   apply (Fun ff) (Fun f) = Fun (ff <*> f)
   apply _ _ = shapeMismatch unit

instance Apply Fun where
   apply (Closure fρ ds d) (Closure ρ _ _) = Closure (fρ <*> ρ) ds d
   apply (Prim op) (Prim _) = Prim op
   apply (Type c) (Type c') = Type (c ≜ c')
   apply (Partial fφ fvs) (Partial φ vs) = Partial (fφ <*> φ) (zipWith (<*>) fvs vs)
   apply _ _ = shapeMismatch unit

-- Should require equal domains?
instance Apply DictRep where
   apply (DictRep fxvs) (DictRep xvs) =
      DictRep $ intersectionWith (\(fα × fv) (α × v) -> fα α × (fv <*> v)) fxvs xvs

instance Apply MatrixRep where
   apply (MatrixRep (fvss × fn × fm)) (MatrixRep (vss × n × m)) =
      MatrixRep $ (A.zipWith (A.zipWith (<*>)) fvss vss) × (fn <*> n) × (fm <*> m)

instance Apply MatrixDim where
   apply (MatrixDim (n × fnα)) (MatrixDim (n' × nα)) = MatrixDim ((n ≜ n') × (fnα nα))

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
   foldl f acc (MatrixRep (vss × MatrixDim (_ × βi) × MatrixDim (_ × βj))) = foldl (foldl (foldl f)) (acc `f` βi `f` βj) vss
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

instance JoinSemilattice a => JoinSemilattice (MatrixDim a) where
   join (MatrixDim (i × α)) (MatrixDim (i' × α')) = MatrixDim ((i ≜ i') × (α ∨ α'))

instance JoinSemilattice a => JoinSemilattice (Val a) where
   join (Val α doc u) (Val α' doc' v) = Val (α ∨ α') (doc ∨ doc') (u ∨ v)

-- Not equivalent to sequence (join <$> x <*> y) because Dict.join only requires compatibility
-- whereas Dict.apply requires domains to be equal.
instance JoinSemilattice a => JoinSemilattice (BaseVal a) where
   join (Lit ℓ) (Lit ℓ') = Lit (ℓ ≜ ℓ')
   join (Dictionary d) (Dictionary d') = Dictionary (d ∨ d')
   join (Constr c vs) (Constr c' us) = Constr (c ≜ c') (vs ∨ us)
   join (List vs) (List us) = List (vs ∨ us)
   join (Matrix m) (Matrix m') = Matrix (m ∨ m')
   join (Fun φ) (Fun φ') = Fun (φ ∨ φ')
   join x y = (∨) <$> x <*> y

instance JoinSemilattice a => JoinSemilattice (Fun a) where
   join (Closure ρ ds d) (Closure ρ' _ _) = Closure (ρ ∨ ρ') ds d
   join (Prim φ) (Prim _) = Prim φ -- TODO: require φ == φ'
   join (Type c) (Type c') = Type (c ≜ c')
   join (Partial φ vs) (Partial φ' vs') = Partial (φ ∨ φ') (vs ∨ vs')
   join _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (Env a) where
   join (Env ρ) (Env ρ') = Env (ρ ∨ ρ')

instance MeetSemilattice a => MeetSemilattice (Val a) where
   meet = lift2 (∧)

instance MeetSemilattice a => MeetSemilattice (Env a) where
   meet = lift2 (∧)

instance BoundedJoinSemilattice a => Expandable (DictRep a) (Raw DictRep) where
   expand (DictRep svs) (DictRep svs') = DictRep (expand svs svs')

instance BoundedJoinSemilattice a => Expandable (MatrixRep a) (Raw MatrixRep) where
   expand (MatrixRep (vss × i × j)) (MatrixRep (vss' × i' × j')) =
      MatrixRep (expand vss vss' × expand i i' × expand j j')

instance BoundedJoinSemilattice a => Expandable (MatrixDim a) (Raw MatrixDim) where
   expand (MatrixDim (i × α)) (MatrixDim (i' × _)) = MatrixDim ((i ≜ i') × α)

instance BoundedJoinSemilattice a => Expandable (Val a) (Raw Val) where
   expand (Val α doc u) (Val _ doc' v) = Val α (expand doc doc') (expand u v)

instance BoundedJoinSemilattice a => Expandable (BaseVal a) (Raw BaseVal) where
   expand (Lit ℓ) (Lit ℓ') = Lit (ℓ ≜ ℓ')
   expand (Dictionary d) (Dictionary d') = Dictionary (expand d d')
   expand (Constr c vs) (Constr c' us) = Constr (c ≜ c') (expand vs us)
   expand (List vs) (List us) = List (expand vs us)
   expand (Matrix m) (Matrix m') = Matrix (expand m m')
   expand (Fun φ) (Fun φ') = Fun (expand φ φ')
   expand _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Fun a) (Raw Fun) where
   expand (Closure ρ ds d) (Closure ρ' _ _) = Closure (expand ρ ρ') ds d
   expand (Prim φ) (Prim _) = Prim φ -- TODO: require φ == φ'
   expand (Type c) (Type c') = Type (c ≜ c')
   expand (Partial φ vs) (Partial φ' vs') = Partial (expand φ φ') (expand vs vs')
   expand _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Env a) (Raw Env) where
   expand (Env ρ) (Env ρ') = Env (expand ρ ρ')

derive instance Eq a => Eq (Val a)
derive instance Eq a => Eq (BaseVal a)
derive instance Eq a => Eq (DictRep a)
derive instance Eq a => Eq (MatrixRep a)
derive instance Eq a => Eq (MatrixDim a)
derive instance Eq a => Eq (Fun a)
derive instance Eq a => Eq (Env a)

derive instance Newtype (Env a) _

instance TypeName (Val a) where
   typeName _ = "Val"

instance TypeName (MatrixDim a) where
   typeName _ = "MatrixDim"

instance TypeName (DictKey a) where
   typeName _ = "DictKey"

instance Vertices (Val Vertex) where
   vertices v@(Val α _ v') = singleton (DVertex (α × pack v)) ∪ vertices v'

instance Vertices (BaseVal Vertex) where
   vertices (Lit _) = empty
   vertices (Constr _ vs) = unions (vertices <$> vs)
   vertices (List vs) = unions (vertices <$> vs)
   vertices (Dictionary d) = vertices d
   vertices (Matrix m) = vertices m
   vertices (Fun f) = vertices f

instance Vertices (DictRep Vertex) where
   vertices (DictRep d) = foldMap (\k (α × v) -> vertices (DictKey (k × α)) ∪ vertices v) (unwrap d)

instance Vertices (DictKey Vertex) where
   vertices dk@(DictKey (_ × α)) = singleton (DVertex (α × pack dk))

instance Vertices (MatrixRep Vertex) where
   vertices (MatrixRep (vss × i × j)) =
      unions (A.concat (map vertices <$> vss))
         ∪ vertices i
         ∪ vertices j

instance Vertices (MatrixDim Vertex) where
   vertices md@(MatrixDim (_ × α)) = singleton (DVertex (α × pack md))

instance Vertices (Fun Vertex) where
   vertices (Closure ρ _ _) = vertices ρ
   vertices (Prim _) = empty
   vertices (Type _) = empty
   vertices (Partial φ vs) = vertices φ ∪ unions (vertices <$> vs)

instance Vertices (Env Vertex) where
   vertices (Env ρ) = unions (vertices <$> values ρ)
