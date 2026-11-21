module DepGraph where

import Prelude hiding (absurd, compose)

import Bind (Var)
import Control.Apply (lift2)
import Control.Monad.State (class MonadState, evalState, execState, gets, modify_, state)
import Data.Foldable (any, foldMap, foldl, foldr)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map, fromFoldableWith, insertWith, lookup, unionWith)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (fst, snd)
import Lattice (class DepSemiring, ctrlWeight)
import Util (type (×), Endo, absurd, error, singleton, (×))
import Util.Map (get, maplet)
import Util.Set ((∪))
import Unsafe.Reference (unsafeRefEq)

newtype Deriv = Deriv Int

type Pos = Int -- index under the position ordering of a value

-- Step from a value to one of its parts, or from a family of values to one of its members
data Step
   = Vertex Deriv
   | Binding Var -- variable of environment
   | Field Int -- field of object
   | Element Int -- element of list or tuple
   | Key String -- key of dictionary entry
   | Entry String -- value of dictionary entry
   | MatrixElement Int Int
   | RowCount -- of matrix
   | ColumnCount
   | Uncl -- environment of closure
   | PartialFun -- function of partial application
   | PartialArg Int -- stored argument of partial application

type Path = List Step

ε :: Path
ε = Nil

-- Position p in the value of vertex a
at :: Deriv -> Path -> Path
at a p = Vertex a : p

vertex :: Deriv -> Path
vertex a = at a ε

-- Whether the step leads from a function value to a value held by the function
uncl :: Step -> Boolean
uncl Uncl = true
uncl PartialFun = true
uncl (PartialArg _) = true
uncl _ = false

-- Labels with a path to each position
class Traversable f <= Paths f where
   paths :: forall a. f a -> f (Path × a)

positions :: forall f a. Traversable f => f a -> List a
positions = traverse (\a -> modify_ (a : _)) >>> flip execState Nil >>> L.reverse

mapPositions :: forall f a b. Traversable f => (Pos -> b) -> f a -> f b
mapPositions h = traverse (\_ -> state \n -> h n × (n + 1)) >>> flip evalState 0

zeros :: forall f a s. Functor f => Semiring s => f a -> f s
zeros = map (const zero)

scale :: forall f s. Functor f => Semiring s => s -> f s -> f s
scale a = map (mul a)

plus :: forall f s. Apply f => Semiring s => f s -> f s -> f s
plus = lift2 add

-- Same as union, except that a result equal to ps or ps' is that argument
unionShared :: Set Path -> Set Path -> Set Path
unionShared ps ps'
   | unsafeRefEq ps ps' = ps
   | otherwise = argument (ps ∪ ps')
        where
        argument qs
           | Set.size qs == Set.size ps = ps
           | Set.size qs == Set.size ps' = ps'
           | otherwise = qs

-- Sources of a target position: set of sources with control weight, then non-zero weight of every other source
data Sources s = Sources (Set Path) (Map Path s)

instance Semiring s => Semigroup (Sources s) where
   append (Sources ps ws) (Sources ps' ws') = Sources (unionShared ps ps') (unionWith add ws ws')

instance Semiring s => Monoid (Sources s) where
   mempty = Sources Set.empty Map.empty

-- Control dependence on each of ps
control :: forall s. Set Path -> Sources s
control ps = Sources ps Map.empty

-- Dependence on p with weight one
source :: forall s. Semiring s => Path -> Sources s
source p = Sources Set.empty (Map.singleton p one)

positionsOf :: forall s. Sources s -> Set Path
positionsOf (Sources ps ws) = ps ∪ Map.keys ws

weights :: forall s. DepSemiring s => Sources s -> Map Path s
weights (Sources ps ws) = unionWith add (Set.toMap ps $> ctrlWeight) ws

-- Product of non-zero w with the weight of every source; unchanged for a source with control weight
scaleSources :: forall s. Eq s => Semiring s => s -> Endo (Sources s)
scaleSources w srcs@(Sources ps ws)
   | w == one = srcs
   | otherwise = Sources ps (mul w <$> ws)

-- Sources of the target root, then relation into each part; zero relations absent
data Rel s = Rel (Sources s) (Map Step (Rel s))

instance Semiring s => Semigroup (Rel s) where
   append (Rel srcs rs) (Rel srcs' rs') = Rel (srcs <> srcs') (unionWith append rs rs')

instance Semiring s => Monoid (Rel s) where
   mempty = Rel mempty Map.empty

nonZero :: forall s. Rel s -> Maybe (Rel s)
nonZero r@(Rel (Sources ps ws) rs)
   | Set.isEmpty ps && Map.isEmpty ws && Map.isEmpty rs = Nothing
   | otherwise = Just r

-- Relation of the target root to the given sources
onto :: forall s. Sources s -> Rel s
onto srcs = Rel srcs Map.empty

ι :: forall s. Semiring s => Path -> Endo (Rel s)
ι p r = foldr (\step r' -> Rel mempty (maybe Map.empty (maplet step) (nonZero r'))) r p

π :: forall s. Semiring s => Path -> Endo (Rel s)
π Nil r = r
π (step : p) (Rel _ rs) = maybe mempty (π p) (lookup step rs)

-- Control dependence of the target on a set of source positions, with a form
data Restructuring = Restructuring (Set Path) Form

data Form
   = Reuse Path -- subvalue of source at path
   | Zero -- nothing reused
   | Family (Map Step Restructuring) -- restructuring into each part
   | Extend Restructuring (Map Step Restructuring) -- restructuring into environment; restructuring into each replacement member

restructuring :: Form -> Restructuring
restructuring = Restructuring Set.empty

withCtrl :: Set Path -> Endo Restructuring
withCtrl ps' (Restructuring ps ψ) = Restructuring (unionShared ps ps') ψ

pathAfter :: Path -> Restructuring -> Restructuring
pathAfter Nil θ = θ
pathAfter p@(step : p') (Restructuring ps ψ) = (if any uncl p then identity else withCtrl ps) case ψ of
   Reuse q -> restructuring (Reuse (q <> p))
   Zero -> restructuring Zero
   Family θs -> pathAfter p' (get step θs)
   Extend θ θs -> case lookup step θs of
      Just θ' -> pathAfter p' θ'
      Nothing -> pathAfter p θ

type Dependence s = Restructuring × Rel s

reuse :: forall s. Semiring s => Path -> Dependence s
reuse p = restructuring (Reuse p) × mempty

-- Add control dependence of the target on each of ps
under :: forall s. Set Path -> Endo (Dependence s)
under ps (θ × r) = withCtrl ps θ × r

supp :: forall s. Semiring s => Dependence s -> Path -> Sources s
supp (θ × r) q = case pathAfter q θ of
   Restructuring ps (Reuse p) -> Sources ps (Map.singleton p one)
   Restructuring ps _ -> Sources ps Map.empty <> srcs
   where
   Rel srcs _ = π q r

-- Sources of every position in qs
supps :: forall s. Semiring s => Dependence s -> Set Path -> Set Path
supps δ qs = positionsOf (foldMap (supp δ) qs)

restructuringAfter :: forall s. Semiring s => Restructuring -> Dependence s -> Restructuring
restructuringAfter (Restructuring ps ψ) δ@(θ × _) = withCtrl (supps δ ps) case ψ of
   Reuse p -> pathAfter p θ
   Zero -> restructuring Zero
   Family θs -> restructuring (Family (flip restructuringAfter δ <$> θs))
   Extend θ' θs -> restructuring (Extend (restructuringAfter θ' δ) (flip restructuringAfter δ <$> θs))

restructuringAfterRel :: forall s. Semiring s => Restructuring -> Rel s -> Rel s
restructuringAfterRel (Restructuring _ ψ) r = case ψ of
   Reuse p -> π p r
   Zero -> mempty
   Family θs -> Rel mempty (members θs)
   Extend θ θs -> case restructuringAfterRel θ r of
      Rel srcs rs -> Rel srcs (Map.union (members θs) (Map.difference rs θs))
   where
   members = Map.mapMaybe (flip restructuringAfterRel r >>> nonZero)

-- Relation after the relation of a dependence
relAfter :: forall s. DepSemiring s => Rel s -> Dependence s -> Rel s
relAfter (Rel (Sources ps ws) rs) δ =
   Rel (foldlWithIndex (\p srcs w -> srcs <> scaleSources w (supp δ p)) (Sources (supps δ ps) Map.empty) ws)
      (Map.mapMaybe (flip relAfter δ >>> nonZero) rs)

compose :: forall s. DepSemiring s => Dependence s -> Dependence s -> Dependence s
compose (θ' × r') δ@(_ × r) = restructuringAfter θ' δ × (restructuringAfterRel θ' r <> relAfter r' δ)

tupling :: forall s. Semiring s => Map Step (Dependence s) -> Dependence s
tupling δs = restructuring (Family (fst <$> δs)) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Dependence of a value built around parts δs, or with nothing reused if δs is empty; root depends on srcs
construct :: forall s. Semiring s => Sources s -> Map Step (Dependence s) -> Dependence s
construct srcs δs
   | Map.isEmpty δs = restructuring Zero × onto srcs
   | otherwise = map (onto srcs <> _) (tupling δs)

-- Dependence of the environment at position p with members δs replaced or added
extend :: forall s. Semiring s => Path -> Map Step (Dependence s) -> Dependence s
extend p δs = restructuring (Extend (restructuring (Reuse p)) (fst <$> δs)) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Vertices which hold the source positions
vertices :: forall s. Dependence s -> Set Deriv
vertices (θ × r) = Set.map holder (ofRestructuring θ ∪ ofRel r)
   where
   ofRestructuring (Restructuring ps ψ) = Set.mapMaybe L.head ps ∪ case ψ of
      Reuse p -> Set.mapMaybe L.head (singleton p)
      Zero -> Set.empty
      Family θs -> foldMap ofRestructuring θs
      Extend θ' θs -> ofRestructuring θ' ∪ foldMap ofRestructuring θs
   ofRel (Rel srcs rs) = Set.mapMaybe L.head (positionsOf srcs) ∪ foldMap ofRel rs

   holder (Vertex a) = a
   holder _ = error absurd

type Labelling a = Map Deriv a
type Edges r = Labelling (Labelling r) -- target ↦ source ↦ dependence relation

-- Vertices labelled by values of shape f; at most one edge into each vertex
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Labelling (f Unit)
   , docs :: Labelling Deriv -- documented vertex ↦ vertex of doc
   , edges :: Labelling (Set Deriv × Dependence s) -- target ↦ sources, with dependence on their values
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

valAt :: forall f s. DepGraph f s -> Deriv -> f Unit
valAt g a = get a g.vals

newVertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> Dependence s -> m Deriv
newVertex v δ = do
   size <- gets _.size
   let a = Deriv size
   modify_ \g -> g { size = size + 1, vals = Map.insert a v g.vals, edges = Map.insert a (vertices δ × δ) g.edges }
   pure a

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Deriv -> Deriv -> m Unit
attachDoc a b = modify_ \g -> g { docs = Map.insert a b g.docs }

-- Pair present exactly when its weight is non-zero
newtype SparseRel s = SparseRel
   { out :: Map Pos (Map Pos s) -- source ↦ labelled target neighbours
   , in_ :: Map Pos (Map Pos s) -- target ↦ labelled source neighbours
   }

sparseRel :: forall s. Map Pos (Map Pos s) -> SparseRel s
sparseRel in_ = SparseRel { out, in_ }
   where
   out = fromFoldableWith Map.union
      (Map.toUnfoldable in_ >>= \(j × m) -> (Map.toUnfoldable m :: List _) <#> \(i × w) -> i × maplet j w)

-- Visible vertices with their values; edges labelled by the dependence relations left by hiding every other vertex
type VisibleGraph (f :: Type -> Type) s =
   { vals :: Labelling (f Unit)
   , edges :: Edges (SparseRel s)
   }

-- Relies on edges running from earlier to later vertices in evaluation order.
materialise :: forall f s. Paths f => DepSemiring s => DepGraph f s -> Set Deriv -> VisibleGraph f s
materialise g visible =
   { vals
   , edges: (foldl step { θs: Map.empty, rs: Map.empty, edges: Map.empty } (Map.toUnfoldable g.edges :: List _)).edges
   }
   where
   vals = Map.filterKeys (_ `Set.member` visible) g.vals

   -- Tupled dependence of every vertex so far on the visible vertices, as restructurings θs and relations rs
   step { θs, rs, edges } (a × (_ × δ)) =
      if Set.member a visible then
         { θs: free a (Map.insert (Vertex a) (restructuring (Reuse (singleton (Vertex a)))) θs)
         , rs: free a rs
         , edges: Map.insert a (sparseRel <$> edgesInto a (θ' × r')) edges
         }
      else { θs: free a (Map.insert (Vertex a) θ' θs), rs: free a (Map.alter (const (nonZero r')) (Vertex a) rs), edges }
      where
      θ' × r' = compose δ (restructuring (Family θs) × Rel mempty rs)

   -- Free the entry of each vertex which has a as last dependent
   free :: forall a. Deriv -> Endo (Map Step a)
   free a xs = foldr (Vertex >>> Map.delete) xs (fromMaybe Nil (lookup a byLastDependent))

   -- Last dependent of each vertex; vertex without dependents counts as dependent on itself
   lastDependent :: Labelling Deriv
   lastDependent = foldlWithIndex dependent Map.empty g.edges
      where
      dependent a m (bs × _) = foldl (\m' b -> Map.insert b a m') (Map.insert a a m) bs

   byLastDependent :: Labelling (List Deriv)
   byLastDependent = fromFoldableWith (<>) $
      (Map.toUnfoldable lastDependent :: List _) <#> \(b × a) -> a × (b : Nil)

   -- Index of each position of a visible vertex
   indices :: Labelling (Map Path Pos)
   indices = vals <#> \v -> Map.fromFoldable (mapWithIndex (\i (p × _) -> p × i) (positions (paths v)))

   -- Edges into a visible vertex from each visible vertex
   edgesInto :: Deriv -> Dependence s -> Labelling (Map Pos (Map Pos s))
   edgesInto a δ = foldl (unionWith Map.union) Map.empty $
      mapWithIndex (\j (q × _) -> maplet j <$> bySource (weights (supp δ q))) (positions (paths (get a vals)))

   bySource :: Map Path s -> Labelling (Map Pos s)
   bySource row = fromFoldableWith Map.union $
      (Map.toUnfoldable row :: List _) <#> case _ of
         (Vertex b : p) × w -> b × maplet (get p (get b indices)) w
         _ -> error absurd

-- Restrict every dependence relation to the positions where the predicate holds.
mask :: forall f s. Traversable f => (Deriv -> f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = mapWithIndex (\q -> mapWithIndex (rel q)) g.edges }
   where
   kept = mapWithIndex (\p -> keep p >>> selected) g.vals
   rel q p (SparseRel r) = SparseRel { in_: only ks_q ks_p r.in_, out: only ks_p ks_q r.out }
      where
      ks_q = get q kept
      ks_p = get p kept
   only ks ks' m = Map.filter (not <<< Map.isEmpty) $
      Map.filterKeys (_ `Set.member` ks') <$> Map.filterKeys (_ `Set.member` ks) m

-- Positions carrying true.
selected :: forall f. Traversable f => f Boolean -> Set Pos
selected v = Set.fromFoldable $
   L.mapMaybe identity (mapWithIndex (\i b -> if b then Just i else Nothing) (positions v))

-- Sparse dependence relation applied to sparse weights.
applySparse :: forall s. Semiring s => Map Pos (Map Pos s) -> Map Pos s -> Map Pos s
applySparse r w = foldl (unionWith add) Map.empty $
   mapWithIndex (\i a -> maybe Map.empty (map (a * _)) (lookup i r)) w

-- Add weights at a vertex.
add' :: forall s. Semiring s => Deriv -> Map Pos s -> Labelling (Map Pos s) -> Labelling (Map Pos s)
add' = insertWith (unionWith add)

-- Weight 1 at the selected positions.
unitWeights :: forall s. Semiring s => Labelling (Set Pos) -> Labelling (Map Pos s)
unitWeights = map (Set.toMap >>> map (const one))

-- Weights at each visible vertex as a value, zero where absent.
dense :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Labelling (Map Pos s) -> Labelling (f s)
dense g ws = g.vals # mapWithIndex \p ->
   mapPositions (\i -> fromMaybe zero (lookup p ws >>= lookup i))

-- Forward and backward queries, each the transpose of the other.
type ConjugatePair a b = { fwd :: a -> b, bwd :: a -> b }

dimap :: forall a a' b b'. (a' -> a) -> (b -> b') -> ConjugatePair a b -> ConjugatePair a' b'
dimap f g pair = { fwd: g <<< pair.fwd <<< f, bwd: g <<< pair.bwd <<< f }

queries :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> ConjugatePair (Labelling (Set Pos)) (Labelling (f s))
queries g = { fwd: fwd g, bwd: bwd g }

-- Dependence of the selection on the positions of each visible vertex.
bwd :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Labelling (Set Pos) -> Labelling (f s)
bwd g selection = dense g (foldr step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step (p × sources) ws = case lookup p ws of
      Nothing -> ws
      Just w -> foldlWithIndex (\q ws' (SparseRel r) -> add' q (applySparse r.in_ w) ws') ws sources

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Labelling (Set Pos) -> Labelling (f s)
fwd g selection = dense g (foldl step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step ws (p × sources) = foldlWithIndex (\q ws' r -> maybe ws' (into p ws' r) (lookup q ws)) ws sources
   into p ws (SparseRel r) w = add' p (applySparse r.out w) ws

-- ======================
-- boilerplate
-- ======================
derive instance Eq Deriv
derive instance Ord Deriv
derive instance Eq Step
derive instance Ord Step
derive instance Generic Step _

instance Show Step where
   show = genericShow

derive instance Newtype Deriv _
derive newtype instance Show Deriv
