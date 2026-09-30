module Graph.Dep where

import Prelude

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, gets, modify_)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)

newtype Vertex = Vertex Int

-- Linear map between free semimodules over the positions of a and b.
type Rel a b = a -> b

sumRel :: forall a f s. Apply f => Semiring s => Rel a (f s) -> Rel a (f s) -> Rel a (f s)
sumRel r r' x = lift2 add (r x) (r' x)

scaleRel :: forall a f s. Functor f => Semiring s => s -> Rel a (f s) -> Rel a (f s)
scaleRel s r = map (mul s) <<< r

-- Vertices labelled by values of shape f; edges labelled by relations, parallel edges summed.
type DepGraph (f :: Type -> Type) s =
   { next :: Int
   , vals :: Map Vertex (f Unit)
   , edges :: Map Vertex (Map Vertex (Rel (f s) (f s))) -- target ↦ source ↦ relation
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { next: 0, vals: Map.empty, edges: Map.empty }

vertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> m Vertex
vertex v = do
   n <- gets _.next
   let α = Vertex n
   modify_ \g -> g { next = n + 1, vals = Map.insert α v g.vals }
   pure α

relabel :: forall f s m. MonadState (DepGraph f s) m => Vertex -> f Unit -> m Unit
relabel α v = modify_ \g -> g { vals = Map.insert α v g.vals }

edge :: forall f s m. MonadState (DepGraph f s) m => Apply f => Semiring s => Vertex -> Vertex -> Rel (f s) (f s) -> m Unit
edge α β r = modify_ \g -> g { edges = Map.alter (Just <<< Map.insertWith (flip sumRel) α r <<< fromMaybe Map.empty) β g.edges }

-- ======================
-- boilerplate
-- ======================
derive instance Eq Vertex
derive instance Ord Vertex
derive instance Newtype Vertex _
derive newtype instance Show Vertex
