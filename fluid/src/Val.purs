module Val where

import Prelude hiding (absurd, append)

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
import Data.Foldable (class Foldable, foldMapDefaultL, foldl, foldrDefault)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:), zipWith)
import Data.List ((!!), range, reverse, take) as L
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.String.CodePoints (codePointAt, length, singleton) as S
import Data.Set as Set
import Data.Tuple (fst, snd)
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Dict (Dict)
import Dict as D
import Expr (Def, Module, fv)
import File (class MonadLoad)
import Module.Defs (ModuleName)
import DepGraph (class Paths, DepGraph, Dependence, Labelling, emptyGraph, paths)
import Lattice (class BoundedLattice, class DepSemiring, class JoinSemilattice, class MeetSemilattice, DepKind(..), Raw, (∧), (∨))
import Literal (Literal(..))
import Path (Path, Step(..), Vertex)
import Types as T
import Pretty.Doc (Doc, text)
import Util (MayFail, class IsEmpty, type (×), Endo, absurd, definitely', error, isEmpty, shapeMismatch, singleton, unsafeUpdateAt, (!), (×), (∩), (≜))
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

data Fun a
   = Closure (Env a) (Dict Def) Def
   | Prim ForeignOp
   | Type T.Type
   | Partial (Val a) (List (Val a)) -- function applied to fewer arguments than arity; function is not partial

newtype Env a = Env (Dict (Val a))

-- Wrap internal representations to provide foldable and traversable instances
newtype DictRep a = DictRep (Dict (a × Val a))
-- Elements, then row count and column count as int values
newtype MatrixRep a = MatrixRep (Array2 (Val a) × Val a × Val a)
type Array2 a = Array (Array a)

data ForeignOp' = ForeignOp'
   { arity :: Int
   , depOp :: DepOp
   }

newtype ForeignOp = ForeignOp (String × ForeignOp') -- string is unique identifier for Eq

root :: forall a. Val a -> a
root (Val α _) = α

-- Label of a vertex
data Label a
   = Value (Val a) -- of an expression or returning statement
   | Bindings (Env a) -- introduced by an assigning statement, or members of a module
   | Inputs a (Env a) -- control position and environment of a premise

value :: forall a. Label a -> Val a
value (Value v) = v
value _ = error absurd

instance Paths Val where
   paths = pathsFrom Nil

instance Paths Label where
   paths (Value v) = Value (paths v)
   paths (Bindings (Env ρ)) = Bindings (Env (mapWithKey (\x -> pathsFrom (singleton (Binding x))) ρ))
   paths (Inputs α (Env ρ)) =
      Inputs (singleton InputsCtl × α) (Env (mapWithKey (\x -> pathsFrom (Binding x : InputsEnv : Nil)) ρ))

-- Same as paths, except that each path starts with the reverse of p
pathsFrom :: forall a. Path -> Val a -> Val (Path × a)
pathsFrom p (Val α u) = Val (L.reverse p × α) case u of
   Lit ℓ -> Lit ℓ
   Obj c xvs -> Obj c (xvs <#> \(x × v) -> x × pathsFrom (Field x : p) v)
   List vs -> List (mapWithIndex (\i -> pathsFrom (Element i : p)) vs)
   Tuple vs -> Tuple (mapWithIndex (\i -> pathsFrom (Element i : p)) vs)
   Dictionary (DictRep d) ->
      Dictionary (DictRep (mapWithKey (\k (β × v) -> (L.reverse (DictKey k : p) × β) × pathsFrom (DictVal k : p) v) d))
   Matrix (MatrixRep (vss × i × j)) -> Matrix $ MatrixRep $
      mapWithIndex (\i' -> mapWithIndex (\j' -> pathsFrom (MatrixElement i' j' : p))) vss
         × pathsFrom (MatrixRows : p) i
         × pathsFrom (MatrixCols : p) j
   Fun (Closure (Env ρ) ds d) -> Fun (Closure (Env (mapWithKey (\x -> pathsFrom (Binding x : ClosureEnv : p)) ρ)) ds d)
   Fun (Prim φ) -> Fun (Prim φ)
   Fun (Type τ) -> Fun (Type τ)
   Fun (Partial v vs) ->
      Fun (Partial (pathsFrom (PartialFun : p) v) (mapWithIndex (\i -> pathsFrom (PartialArg i : p)) vs))
   Opaque q -> Opaque q
   Module q -> Module q
   Unbound -> Unbound
   TypeAlias αs τ -> TypeAlias αs τ

matrixGet :: forall a. Int -> Int -> MatrixRep a -> Val a
matrixGet i j (MatrixRep (vss × _ × _)) = definitely' ((_ A.!! j) =<< vss A.!! i)

matrixElement :: forall a. Int -> Int -> Val a -> Val a
matrixElement i j (Val _ (Matrix r)) = matrixGet i j r
matrixElement _ _ _ = error absurd

attr :: forall a. Var -> Val a -> Val a
attr x (Val _ (Obj _ xvs)) = get x (D.fromFoldable xvs)
attr _ _ = error absurd

-- Element of list or tuple, character of string, key of dictionary or integer of range at index i
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

matrixPut :: forall a. Int -> Int -> Endo (Val a) -> Endo (MatrixRep a)
matrixPut i j δv (MatrixRep (vss × h × w)) =
   MatrixRep (vss' × h × w)
   where
   vs_i = vss ! i
   v_j = vs_i ! j
   vss' = unsafeUpdateAt i (unsafeUpdateAt j (δv v_j) vs_i) vss

child :: forall a. Step -> Val a -> Val a
child (Field x) v = attr x v
child (Element i) v = element i v
child (DictKey k) v = Val (fst (dictEntry k v)) (Lit (Str k))
child (DictVal k) v = snd (dictEntry k v)
child (MatrixElement i j) v = matrixElement i j v
child MatrixRows (Val _ (Matrix (MatrixRep (_ × i × _)))) = i
child MatrixCols (Val _ (Matrix (MatrixRep (_ × _ × j)))) = j
child PartialFun (Val _ (Fun (Partial v _))) = v
child (PartialArg i) (Val _ (Fun (Partial _ vs))) = definitely' (vs L.!! i)
child _ _ = error absurd

-- False at shape positions.
dataPositions :: forall a. Val a -> Val Boolean
dataPositions (Val _ u) = Val (not container) (overChildren (false <$ u))
   where
   container = case u of
      Obj _ _ -> true
      List _ -> true
      Tuple _ -> true
      Dictionary _ -> true
      Matrix _ -> true
      _ -> false

   overChildren :: Endo (BaseVal Boolean)
   overChildren (Obj c xvs) = Obj c (map dataPositions <$> xvs)
   overChildren (List vs) = List (dataPositions <$> vs)
   overChildren (Tuple vs) = Tuple (dataPositions <$> vs)
   overChildren (Dictionary (DictRep d)) = Dictionary (DictRep (map dataPositions <$> d))
   overChildren (Matrix (MatrixRep (vss × i × j))) = Matrix (MatrixRep (map (map dataPositions) vss × i × j))
   overChildren (Fun (Closure (Env ρ) ds d)) = Fun (Closure (Env (dataPositions <$> ρ)) ds d)
   overChildren (Fun (Partial v vs)) = Fun (Partial (dataPositions v) (dataPositions <$> vs))
   overChildren u' = u'

forDefs :: Dict Def -> Def -> Dict Def
forDefs ds d = restrict (reaches (Set.toUnfoldable (fv d ∩ dom_ds)) empty) ds
   where
   dom_ds = keys ds

   reaches :: List Var -> Endo (Set Var)
   reaches Nil acc = acc
   reaches (x : xs) acc
      | x ∈ acc = reaches xs acc
      | otherwise = reaches (Set.toUnfoldable (fv (get x ds) ∩ dom_ds) <> xs) (singleton x ∪ acc)

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

class (Highlightable a, BoundedLattice a) <= Ann a

instance Ann Boolean
instance Ann Unit

instance Highlightable a => Highlightable (a × b) where
   highlightIf (a × _) doc = highlightIf a doc

instance (Ann a, BoundedLattice b) => Ann (a × b)

-- Vertex with the vertex of its doc, if any.
type VertexWithDoc = Vertex × Maybe Vertex

-- Value with its doc, as shown in a figure.
newtype ValWithDoc a = ValWithDoc { val :: Val a, doc :: Maybe (Val a) }
newtype EnvWithDocs a = EnvWithDocs (Dict (ValWithDoc a))

-- Value at a vertex, with the value of its doc.
val :: forall a. Labelling (Val a) -> VertexWithDoc -> ValWithDoc a
val m (p × d) = ValWithDoc { val: get p m, doc: flip get m <$> d }

unval :: forall a. VertexWithDoc -> ValWithDoc a -> Labelling (Val a)
unval (p × d) (ValWithDoc { val: v, doc }) = Map.fromFoldable (A.cons (p × v) (A.fromFoldable ((×) <$> d <*> doc)))

unvals :: forall a. Dict VertexWithDoc -> EnvWithDocs a -> Labelling (Val a)
unvals ps (EnvWithDocs vs) = Map.unions (values (intersectionWith unval ps vs))

-- Value at the vertex of an expression or returning statement
valAt :: forall s. DepGraph Label s -> Vertex -> Raw Val
valAt g p = value (get p g.vals)

-- Value with its dependence on the values of vertices already in the graph
type GVal s = Raw Val × Dependence (Set Path) s

-- Source position, then value at that position
type ValAt = Path × Raw Val

-- Function on annotated values; dependence left to the annotations
type DepFun = forall a. DepSemiring a => List (Val a) -> MayFail (Val a)

-- Foreign function of control position and arguments
type DepOp =
   forall m s
    . HasClasses m
   => MonadLoad m
   => DepSemiring s
   => Path
   -> List ValAt
   -> m (GVal s)

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

instance Eq ForeignOp where
   eq (ForeignOp (s × _)) (ForeignOp (s' × _)) = s == s'

instance Ord ForeignOp where
   compare (ForeignOp (s × _)) (ForeignOp (s' × _)) = compare s s'

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
