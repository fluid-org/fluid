module Graph.Dep where

import Prelude

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, evalState, execState, gets, modify_, state)
import Data.Foldable (foldl, length)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (snd)
import Lattice (class DepSemiring, Lineage(..))
import Util (type (×), (×))

newtype Vertex = Vertex Int

type Pos = Int -- index under the position ordering of a value

-- Second function maps the annotations that are not positions (documentation, syntax).
class Positions f where
   traversePositions :: forall m a b. Applicative m => (a -> m b) -> (a -> b) -> f a -> m (f b)

positions :: forall f a. Positions f => f a -> List a
positions = traversePositions (\a -> modify_ (a : _)) (const unit) >>> flip execState Nil >>> L.reverse

width :: forall f a. Positions f => f a -> Int
width = positions >>> length

mapPositions :: forall f a b. Positions f => (Pos -> a -> b) -> (a -> b) -> f a -> f b
mapPositions h g = traversePositions (\a -> state \n -> h n a × (n + 1)) g >>> flip evalState 0

basis :: forall f a s. Positions f => Semiring s => f a -> Pos -> f s
basis v i = mapPositions (\n _ -> if n == i then one else zero) (const zero) v

zeros :: forall f a s. Functor f => Semiring s => f a -> f s
zeros = map (const zero)

scale :: forall f s. Functor f => Semiring s => s -> f s -> f s
scale a = map (mul a)

plus :: forall f s. Apply f => Semiring s => f s -> f s -> f s
plus = lift2 add

sumPositions :: forall f s. Positions f => Semiring s => f s -> s
sumPositions = positions >>> foldl add zero

-- Linear map between free semimodules over the positions of a and b.
type Rel a b = a -> b

sumRel :: forall a f s. Apply f => Semiring s => Rel a (f s) -> Rel a (f s) -> Rel a (f s)
sumRel r r' x = r x `plus` r' x

scaleRel :: forall a f s. Functor f => Semiring s => s -> Rel a (f s) -> Rel a (f s)
scaleRel s r = scale s <<< r

-- Pair present exactly when its weight is non-zero.
newtype SparseRel s = SparseRel
   { out :: Map Pos (Map Pos s) -- source ↦ labelled target neighbours
   , in_ :: Map Pos (Map Pos s) -- target ↦ labelled source neighbours, the lineage
   }

sparseRel :: forall s. Map Pos (Map Pos s) -> SparseRel s
sparseRel in_ = SparseRel { out, in_ }
   where
   out = Map.fromFoldableWith Map.union
      (Map.toUnfoldable in_ >>= \(j × m) -> (Map.toUnfoldable m :: List _) <#> \(i × w) -> i × Map.singleton j w)

-- Vertices labelled by values of shape f; edges labelled by relations, parallel edges summed.
type DepGraph (f :: Type -> Type) s =
   { next :: Int
   , vals :: Map Vertex (f Unit)
   , docs :: Map Vertex (f Unit)
   , edges :: Map Vertex (Map Vertex (Rel (f s) (f s))) -- target ↦ source ↦ relation
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { next: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

vertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> m Vertex
vertex v = do
   n <- gets _.next
   let α = Vertex n
   modify_ \g -> g { next = n + 1, vals = Map.insert α v g.vals }
   pure α

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Vertex -> f Unit -> m Unit
attachDoc α v = modify_ \g -> g { docs = Map.insert α v g.docs }

edge :: forall f s m. MonadState (DepGraph f s) m => Apply f => Semiring s => Vertex -> Vertex -> Rel (f s) (f s) -> m Unit
edge α β r = modify_ \g -> g { edges = Map.alter (Just <<< Map.insertWith (flip sumRel) α r <<< fromMaybe Map.empty) β g.edges }

-- ======================
-- boilerplate
-- ======================
derive instance Eq Vertex
derive instance Ord Vertex
derive instance Newtype Vertex _
derive newtype instance Show Vertex

-- Relies on every edge running from an earlier to a later vertex in evaluation order.
materialise
   :: forall f s
    . Positions f
   => Apply f
   => DepSemiring s
   => DepGraph f (Lineage (Vertex × Pos) s)
   -> Set Vertex
   -> Map (Vertex × Vertex) (SparseRel s)
materialise g visible = sparseRel <$> (foldl step (Map.empty × Map.empty) (Map.toUnfoldable g.vals :: List _) # snd)
   where
   step (vecs × rels) (p × v) =
      if Set.member p visible then
         Map.insert p (mapPositions (\i _ -> Lineage (zero × Map.singleton (p × i) one)) (const zero) v) vecs
            × Map.unionWith (Map.unionWith Map.union) rels (Map.fromFoldableWith (Map.unionWith Map.union) (entries vec))
      else Map.insert p vec vecs × rels
      where
      vec = foldl
         (\acc (q × r) -> maybe acc (\x -> acc `plus` r x) (Map.lookup q vecs))
         (zeros v)
         (maybe Nil Map.toUnfoldable (Map.lookup p g.edges))

      entries :: f (Lineage (Vertex × Pos) s) -> List ((Vertex × Vertex) × Map Pos (Map Pos s))
      entries x = mapWithIndex (\j (Lineage (_ × m)) -> j × m) (positions x) >>= \(j × m) ->
         (Map.toUnfoldable m :: List _) <#> \((q × i) × w) -> (q × p) × Map.singleton j (Map.singleton i w)

-- Weights at the positions of a source vertex related to the selected positions of a target vertex.
lineage :: forall f s. Positions f => Semiring s => Map (Vertex × Vertex) (SparseRel s) -> Vertex -> Set Pos -> Vertex -> f Unit -> f s
lineage edges target selected source v = mapPositions (\i _ -> weight i) (const zero) v
   where
   in_ = maybe Map.empty (\(SparseRel r) -> r.in_) (Map.lookup (source × target) edges)
   weight i = foldl add zero ((Set.toUnfoldable selected :: List Pos) <#> \j -> fromMaybe zero (Map.lookup j in_ >>= Map.lookup i))
