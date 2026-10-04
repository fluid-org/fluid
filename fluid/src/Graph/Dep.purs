module Graph.Dep where

import Prelude

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, evalState, execState, gets, modify_, state)
import Data.Foldable (foldl, sum)
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
import Util (type (×), (×))

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

-- Vertices labelled by values of shape f; edges labelled by relations, parallel edges summed.
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Map Deriv (f Unit)
   , docs :: Map Deriv Deriv -- vertex ↦ vertex of its doc
   , edges :: Map Deriv (Map Deriv (Rel (f s) (f s))) -- target ↦ source ↦ relation
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

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

-- Relies on every edge running from an earlier to a later vertex in evaluation order.
materialise
   :: forall f s
    . Traversable f
   => Apply f
   => DepSemiring s
   => DepGraph f (Lineage (Deriv × Pos) s)
   -> Set Deriv
   -> Map Deriv (Map Deriv (SparseRel s)) -- target ↦ source ↦ relation
materialise g visible =
   (foldl step { weightsAt: Map.empty, rels: Map.empty } (Map.toUnfoldable g.vals :: List _)).rels
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

-- Weights at the positions of a source vertex related to the selected positions of a target vertex.
dep :: forall f s. Traversable f => Semiring s => Map Deriv (Map Deriv (SparseRel s)) -> Deriv -> Set Pos -> Deriv -> f Unit -> f s
dep edges target selected source = mapPositions weight
   where
   in_ = maybe Map.empty (\(SparseRel r) -> r.in_) (lookup target edges >>= lookup source)
   weight i = sum ((Set.toUnfoldable selected :: List Pos) <#> \j -> fromMaybe zero (lookup j in_ >>= lookup i))

-- ======================
-- boilerplate
-- ======================
derive instance Eq Deriv
derive instance Ord Deriv
derive instance Newtype Deriv _
derive newtype instance Show Deriv
