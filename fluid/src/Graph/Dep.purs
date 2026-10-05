module Graph.Dep where

import Prelude

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, evalState, execState, gets, modify_, state)
import Data.Foldable (foldl, foldr)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map, alter, fromFoldableWith, insertWith, lookup, unionWith)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Lattice (class DepSemiring, Lineage(..))
import Util (type (×), definitely', (×))

newtype Deriv = Deriv Int

type Pos = Int -- index under the position ordering of a value

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

-- Linear map between free semimodules over the positions of a and b.
type Rel a b = a -> b

sumRel :: forall a f s. Apply f => Semiring s => Rel a (f s) -> Rel a (f s) -> Rel a (f s)
sumRel r r' x = r x `plus` r' x

-- Pair present exactly when its weight is non-zero.
newtype SparseRel s = SparseRel
   { out :: Map Pos (Map Pos s) -- source ↦ labelled target neighbours
   , in_ :: Map Pos (Map Pos s) -- target ↦ labelled source neighbours, the lineage
   }

sparseRel :: forall s. Map Pos (Map Pos s) -> SparseRel s
sparseRel in_ = SparseRel { out, in_ }
   where
   out = fromFoldableWith Map.union
      (Map.toUnfoldable in_ >>= \(j × m) -> (Map.toUnfoldable m :: List _) <#> \(i × w) -> i × Map.singleton j w)

type Edges r = Map Deriv (Map Deriv r) -- target ↦ source ↦ dependence relation

-- Vertices labelled by values of shape f; edges labelled by dependence relations, parallel edges summed.
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Map Deriv (f Unit)
   , docs :: Map Deriv Deriv -- vertex ↦ vertex of its doc
   , edges :: Edges (Rel (f s) (f s))
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

valAt :: forall f s. DepGraph f s -> Deriv -> f Unit
valAt g p = definitely' (lookup p g.vals)

deriv :: forall f s m. MonadState (DepGraph f s) m => f Unit -> m Deriv
deriv v = do
   size <- gets _.size
   let p = Deriv size
   modify_ \g -> g { size = size + 1, vals = Map.insert p v g.vals }
   pure p

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Deriv -> Deriv -> m Unit
attachDoc p q = modify_ \g -> g { docs = Map.insert p q g.docs }

addEdge :: forall f s m. MonadState (DepGraph f s) m => Apply f => Semiring s => Deriv -> Deriv -> Rel (f s) (f s) -> m Unit
addEdge p q r =
   modify_ \g -> g { edges = alter (Just <<< insertWith (flip sumRel) p r <<< fromMaybe Map.empty) q g.edges }

-- Visible vertices with their values; edges labelled by dependence relations summed over hidden paths.
type VisibleGraph (f :: Type -> Type) s =
   { vals :: Map Deriv (f Unit)
   , edges :: Edges (SparseRel s)
   }

-- Relies on every edge running from an earlier to a later vertex in evaluation order.
materialise
   :: forall f s
    . Traversable f
   => Apply f
   => DepSemiring s
   => DepGraph f (Lineage (Deriv × Pos) s)
   -> Set Deriv
   -> VisibleGraph f s
materialise g visible =
   { vals: Map.filterKeys (_ `Set.member` visible) g.vals
   , edges: (foldl step { weightsAt: Map.empty, rels: Map.empty } (Map.toUnfoldable g.vals :: List _)).rels
   }
   where
   step { weightsAt, rels } (p × v) =
      if Set.member p visible then
         { weightsAt: Map.insert p (mapPositions (\i -> Lineage (zero × Map.singleton (p × i) one)) v) weightsAt
         , rels: Map.insert p (sparseRel <$> edgesInto) rels
         }
      else { weightsAt: Map.insert p weights weightsAt, rels }
      where
      weights = foldl
         (\acc (q × r) -> maybe acc (\x -> acc `plus` r x) (lookup q weightsAt))
         (zeros v)
         (maybe Nil Map.toUnfoldable (lookup p g.edges))

      -- Edges into p from each visible vertex, read off the lineage at every position of p.
      edgesInto :: Map Deriv (Map Pos (Map Pos s))
      edgesInto = foldl (unionWith Map.union) Map.empty $
         mapWithIndex (\j (Lineage (_ × m)) -> Map.singleton j <$> bySource m) (positions weights)

      bySource :: Map (Deriv × Pos) s -> Map Deriv (Map Pos s)
      bySource m = fromFoldableWith Map.union $
         (Map.toUnfoldable m :: List _) <#> \((q × i) × w) -> q × Map.singleton i w

-- Keep at each vertex only the positions where the predicate holds.
mask :: forall f s. Traversable f => (f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = g.edges # mapWithIndex \q -> mapWithIndex \p (SparseRel r) -> SparseRel { in_: only q p r.in_, out: only p q r.out } }
   where
   kept p = selected (keep (definitely' (lookup p g.vals)))
   only p q m = Map.filter (not <<< Map.isEmpty) (Map.filterKeys (_ `Set.member` kept q) <$> Map.filterKeys (_ `Set.member` kept p) m)

-- Positions carrying true.
selected :: forall f. Traversable f => f Boolean -> Set Pos
selected v = Set.fromFoldable (L.mapMaybe identity (mapWithIndex (\i b -> if b then Just i else Nothing) (positions v)))

-- Sparse dependence relation applied to sparse weights.
applyRel :: forall s. Semiring s => Map Pos (Map Pos s) -> Map Pos s -> Map Pos s
applyRel r w = foldl (unionWith add) Map.empty $
   mapWithIndex (\i a -> maybe Map.empty (map (a * _)) (lookup i r)) w

-- Add weights at a vertex.
add' :: forall s. Semiring s => Deriv -> Map Pos s -> Map Deriv (Map Pos s) -> Map Deriv (Map Pos s)
add' = insertWith (unionWith add)

-- Weight 1 at the selected positions.
unitWeights :: forall s. Semiring s => Map Deriv (Set Pos) -> Map Deriv (Map Pos s)
unitWeights = map (Set.toMap >>> map (const one))

-- Weights at each visible vertex as a value, zero where absent.
dense :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Map Deriv (Map Pos s) -> Map Deriv (f s)
dense g ws = g.vals # mapWithIndex \p ->
   mapPositions (\i -> fromMaybe zero (lookup p ws >>= lookup i))

-- Dependence of the selection on the positions of each visible vertex.
bwd :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Map Deriv (Set Pos) -> Map Deriv (f s)
bwd g selection = dense g (foldr step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step (p × sources) ws = case lookup p ws of
      Nothing -> ws
      Just w -> foldlWithIndex (\q ws' (SparseRel r) -> add' q (applyRel r.in_ w) ws') ws sources

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Traversable f => Semiring s => VisibleGraph f s -> Map Deriv (Set Pos) -> Map Deriv (f s)
fwd g selection = dense g (foldl step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step ws (p × sources) = foldlWithIndex (\q ws' (SparseRel r) -> maybe ws' (into p ws' r) (lookup q ws)) ws sources
   into p ws r w = add' p (applyRel r.out w) ws

-- ======================
-- boilerplate
-- ======================
derive instance Eq Deriv
derive instance Ord Deriv
derive instance Newtype Deriv _
derive newtype instance Show Deriv
