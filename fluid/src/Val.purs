module Val where

import Prelude hiding (absurd, append)

import Bind (Name, Var)
import DataType (class HasClasses, cFalse, cNone, cTrue)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except (ExceptT)
import Control.Monad.Reader (class MonadReader, ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer (WriterT)
import Data.Array (concat, (!!))
import Data.Map (Map)
import Data.Map as Map
import Data.Array (zipWith) as A
import Data.Bitraversable (bitraverse)
import Data.Foldable (class Foldable, foldMapDefaultL, foldl, foldrDefault)
import Data.Int (toNumber)
import Data.List (List(..), (:), zipWith)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set, unions)
import Data.Set as Set
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Dict (Dict)
import Dict as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Def, Module, Stmt, fv)
import File (class LoadFile, FileCxt)
import ModuleGraph (ModuleName)
import Foreign.Object (foldMap)
import Graph (class TypeName, class Vertices, DVertex'(..), Vertex(..), VertexData, pack, typeName, unpack, vertices)
import Graph.WithGraph (class MonadWithGraphAlloc, new)
import Lattice (class BoundedJoinSemilattice, class BoundedLattice, class Expandable, class JoinSemilattice, class MeetSemilattice, Raw, expand, (∧), (∨))
import Literal (Literal)
import Literal as L
import Pretty.Doc (Doc, text)
import Unsafe.Coerce (unsafeCoerce)
import Util (class IsEmpty, type (×), Endo, definitely, error, isEmpty, shapeMismatch, singleton, unsafeUpdateAt, (!), (×), (∩), (≜))
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
   = Int Int
   | Float Number
   | Str String
   | Constr Name (List (Val a)) -- always saturated
   | Dictionary (DictRep a)
   | Matrix (MatrixRep a)
   | Fun (Fun a)

val :: forall m. MonadWithGraphAlloc m => Maybe (Val Vertex) -> Set Vertex -> BaseVal Vertex -> m (Val Vertex)
val doc_opt = new (flip Val doc_opt)

literalVal :: forall a. Literal -> BaseVal a
literalVal (L.Int n) = Int n
literalVal (L.Float x) = Float x
literalVal (L.Str s) = Str s
literalVal (L.Bool b) = Constr (if b then cTrue else cFalse) Nil
literalVal L.None = Constr cNone Nil

-- Equality of a value with a literal, numeric across int and float as in Python.
literalMatches :: forall a. Literal -> BaseVal a -> Boolean
literalMatches (L.Int n) (Float x) = toNumber n == x
literalMatches (L.Float x) (Int n) = x == toNumber n
literalMatches ℓ v = case literalVal ℓ, v of
   Int n, Int n' -> n == n'
   Float x, Float x' -> x == x'
   Str s, Str s' -> s == s'
   Constr c Nil, Constr c' Nil -> c == c'
   _, _ -> false

asVal :: VertexData -> Maybe (Val Vertex)
asVal e = if unpack typeName e == "Val" then Just (unpack unsafeCoerce e) else Nothing

data Fun a
   = Closure (Env a) (Dict (Def a)) (Def a)
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
   { ρ0 :: Env Vertex -- the members of the predefined modules (lib.builtins, which owns the primitives, and lib.prelude)
   , moduleBody :: Map ModuleName (Module Vertex)
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

data ForeignOp' = ForeignOp'
   { arity :: Int
   , op :: Op
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

data EnvStmt a = EnvStmt (Env a) (Stmt a)

reaches :: forall a. Dict (Def a) -> Endo (Set Var)
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

forDefs :: forall a. Dict (Def a) -> Def a -> Dict (Def a)
forDefs ds d = restrict (reaches ds (fv d ∩ Set.fromFoldable (keys ds))) ds

-- Wrap internal representations to provide foldable/traversable instances.
newtype DictRep a = DictRep (Dict (a × Val a))
newtype DictKey a = DictKey (String × a)
newtype MatrixDim a = MatrixDim (Int × a)
newtype MatrixRep a = MatrixRep (Array2 (Val a) × MatrixDim a × MatrixDim a)
type Array2 a = Array (Array a)

matrixGet :: forall a. Int -> Int -> MatrixRep a -> Val a
matrixGet i j (MatrixRep (vss × _ × _)) = definitely "matrix indices within bounds" $ do
   us <- vss !! i
   us !! j

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
derive instance Functor EnvStmt
derive instance Traversable MatrixDim
derive instance Traversable Val
derive instance Traversable BaseVal
derive instance Traversable Fun
derive instance Traversable Env
derive instance Traversable EnvStmt
derive instance Foldable MatrixDim
derive instance Foldable Val
derive instance Foldable BaseVal
derive instance Foldable Fun
derive instance Foldable Env
derive instance Foldable EnvStmt

instance Apply Val where
   apply (Val fα Nothing fv) (Val α Nothing v) = Val (fα α) Nothing (fv <*> v)
   apply (Val fα (Just fdoc) fv) (Val α (Just doc) v) = Val (fα α) (Just (fdoc <*> doc)) (fv <*> v)
   apply _ _ = shapeMismatch unit

instance Apply BaseVal where
   apply (Int n) (Int n') = Int (n ≜ n')
   apply (Float n) (Float n') = Float (n ≜ n')
   apply (Str s) (Str s') = Str (s ≜ s')
   apply (Constr c fes) (Constr c' es) = Constr (c ≜ c') (zipWith (<*>) fes es)
   apply (Dictionary fxvs) (Dictionary xvs) = Dictionary (fxvs <*> xvs)
   apply (Matrix fm) (Matrix m) = Matrix (fm <*> m)
   apply (Fun ff) (Fun f) = Fun (ff <*> f)
   apply _ _ = shapeMismatch unit

instance Apply Fun where
   apply (Closure fρ fds fd) (Closure ρ ds d) = Closure (fρ <*> ρ) (((<*>) <$> fds) <*> ds) (fd <*> d)
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

instance Apply EnvStmt where
   apply (EnvStmt fρ fs) (EnvStmt ρ s) = EnvStmt (fρ <*> ρ) (fs <*> s)

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
   join (Int n) (Int n') = Int (n ≜ n')
   join (Float n) (Float n') = Float (n ≜ n')
   join (Str s) (Str s') = Str (s ≜ s')
   join (Dictionary d) (Dictionary d') = Dictionary (d ∨ d')
   join (Constr c vs) (Constr c' us) = Constr (c ≜ c') (vs ∨ us)
   join (Matrix m) (Matrix m') = Matrix (m ∨ m')
   join (Fun φ) (Fun φ') = Fun (φ ∨ φ')
   join x y = (∨) <$> x <*> y

instance JoinSemilattice a => JoinSemilattice (Fun a) where
   join (Closure ρ ds d) (Closure ρ' ds' d') =
      Closure (ρ ∨ ρ') (ds ∨ ds') (d ∨ d')
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
   expand (Int n) (Int n') = Int (n ≜ n')
   expand (Float n) (Float n') = Float (n ≜ n')
   expand (Str s) (Str s') = Str (s ≜ s')
   expand (Dictionary d) (Dictionary d') = Dictionary (expand d d')
   expand (Constr c vs) (Constr c' us) = Constr (c ≜ c') (expand vs us)
   expand (Matrix m) (Matrix m') = Matrix (expand m m')
   expand (Fun φ) (Fun φ') = Fun (expand φ φ')
   expand _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Fun a) (Raw Fun) where
   expand (Closure ρ ds d) (Closure ρ' ds' d') =
      Closure (expand ρ ρ') (expand ds ds') (expand d d')
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
derive instance Eq a => Eq (EnvStmt a)

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
   vertices (Int _) = empty
   vertices (Float _) = empty
   vertices (Str _) = empty
   vertices (Constr _ vs) = unions (vertices <$> vs)
   vertices (Dictionary d) = vertices d
   vertices (Matrix m) = vertices m
   vertices (Fun f) = vertices f

instance Vertices (DictRep Vertex) where
   vertices (DictRep d) = foldMap (\k (α × v) -> vertices (DictKey (k × α)) ∪ vertices v) (unwrap d)

instance Vertices (DictKey Vertex) where
   vertices dk@(DictKey (_ × α)) = singleton (DVertex (α × pack dk))

instance Vertices (MatrixRep Vertex) where
   vertices (MatrixRep (vss × i × j)) =
      unions (concat (map vertices <$> vss))
         ∪ vertices i
         ∪ vertices j

instance Vertices (MatrixDim Vertex) where
   vertices md@(MatrixDim (_ × α)) = singleton (DVertex (α × pack md))

instance Vertices (Fun Vertex) where
   vertices (Closure ρ ds d) = vertices ρ ∪ vertices ds ∪ vertices d
   vertices (Prim _) = empty
   vertices (Type _) = empty
   vertices (Partial φ vs) = vertices φ ∪ unions (vertices <$> vs)

instance Vertices (Env Vertex) where
   vertices (Env ρ) = unions (vertices <$> values ρ)

instance Vertices (EnvStmt Vertex) where
   vertices (EnvStmt ρ s) = vertices ρ ∪ vertices s
