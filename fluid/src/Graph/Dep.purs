module Graph.Dep where

import Prelude

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, evalState, execState, gets, modify_, state)
import Data.Foldable (foldl, sum)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Lattice (class DepSemiring, Lineage(..))
import Util (type (×), (×))

newtype Vertex = Vertex Int

type Pos = Int -- index under the position ordering of a value

positions :: forall f a. Traversable f => f a -> List a
positions = traverse (\a -> modify_ (a : _)) >>> flip execState Nil >>> L.reverse

mapPositions :: forall f a b. Traversable f => (Pos -> a -> b) -> f a -> f b
mapPositions h = traverse (\a -> state \n -> h n a × (n + 1)) >>> flip evalState 0

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
   out = Map.fromFoldableWith Map.union
      (Map.toUnfoldable in_ >>= \(j × m) -> (Map.toUnfoldable m :: List _) <#> \(i × w) -> i × Map.singleton j w)

-- Vertices labelled by values of shape f; edges labelled by relations, parallel edges summed.
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Map Vertex (f Unit)
   , docs :: Map Vertex Vertex -- vertex ↦ vertex of its doc
   , edges :: Map Vertex (Map Vertex (Rel (f s) (f s))) -- target ↦ source ↦ relation
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

vertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> m Vertex
vertex v = do
   size <- gets _.size
   let α = Vertex size
   modify_ \g -> g { size = size + 1, vals = Map.insert α v g.vals }
   pure α

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Vertex -> Vertex -> m Unit
attachDoc α β = modify_ \g -> g { docs = Map.insert α β g.docs }

edge :: forall f s m. MonadState (DepGraph f s) m => Apply f => Semiring s => Vertex -> Vertex -> Rel (f s) (f s) -> m Unit
edge α β r =
   modify_ \g -> g { edges = Map.alter (Just <<< Map.insertWith (flip sumRel) α r <<< fromMaybe Map.empty) β g.edges }

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
    . Traversable f
   => Apply f
   => DepSemiring s
   => DepGraph f (Lineage (Vertex × Pos) s)
   -> Set Vertex
   -> Map Vertex (Map Vertex (SparseRel s)) -- target ↦ source ↦ relation
materialise g visible =
   (foldl step { vecs: Map.empty, rels: Map.empty } (Map.toUnfoldable g.vals :: List _)).rels
   where
   step { vecs, rels } (p × v) =
      if Set.member p visible then
         { vecs: Map.insert p (mapPositions (\i _ -> Lineage (zero × Map.singleton (p × i) one)) v) vecs
         , rels: Map.insert p (sparseRel <$> edgesInto vec) rels
         }
      else { vecs: Map.insert p vec vecs, rels }
      where
      vec = foldl
         (\acc (q × r) -> maybe acc (\x -> acc `plus` r x) (Map.lookup q vecs))
         (zeros v)
         (maybe Nil Map.toUnfoldable (Map.lookup p g.edges))

      -- Edges into p from each visible vertex, read off the lineage at every position of p.
      edgesInto :: f (Lineage (Vertex × Pos) s) -> Map Vertex (Map Pos (Map Pos s))
      edgesInto x = foldl (Map.unionWith Map.union) Map.empty $
         mapWithIndex (\j (Lineage (_ × m)) -> Map.singleton j <$> bySource m) (positions x)

      bySource :: Map (Vertex × Pos) s -> Map Vertex (Map Pos s)
      bySource m = Map.fromFoldableWith Map.union ((Map.toUnfoldable m :: List _) <#> \((q × i) × w) -> q × Map.singleton i w)

-- Weights at the positions of a source vertex related to the selected positions of a target vertex.
lineage :: forall f s. Traversable f => Semiring s => Map Vertex (Map Vertex (SparseRel s)) -> Vertex -> Set Pos -> Vertex -> f Unit -> f s
lineage edges target selected source v = mapPositions (\i _ -> weight i) v
   where
   in_ = maybe Map.empty (\(SparseRel r) -> r.in_) (Map.lookup target edges >>= Map.lookup source)
   weight i = sum ((Set.toUnfoldable selected :: List Pos) <#> \j -> fromMaybe zero (Map.lookup j in_ >>= Map.lookup i))
