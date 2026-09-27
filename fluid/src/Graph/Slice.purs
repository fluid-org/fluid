module Graph.Slice where

import Prelude hiding (map)

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.List (List(..), (:))
import Data.List as L
import Data.Set (Set, empty, insert)
import Data.Tuple (fst)
import Graph (class Graph, DVertex'(..), Vertex, addresses, outN, vertexData)
import Graph.WithGraph (WithGraph, extend, runWithGraph_spy)
import Test.Util.Debug (checking)
import Util (type (×), validateWhen, (×), (⊆))
import Util.Set ((∈))

data Visit = Enter Vertex | Exit Vertex

type BwdConfig =
   { visited :: Set Vertex
   , visits :: List Visit
   }

-- Extend with each vertex after its out-neighbours, as fromEdgeList requires
bwdSlice :: forall g. Graph g => Set Vertex × g -> g
bwdSlice (αs × g) = fst $
   αs
      -- No outputsAreSources analog of inputAreSinks; we do however need to restrict to sources (see #818).
      # validateWhen checking.outputsInGraph "inputs are sinks" (_ ⊆ addresses g)
      -- # (\_ -> αs ∩ sources g)
      # \αs' -> runWithGraph_spy (tailRecM go { visited: empty, visits: Enter <$> L.fromFoldable αs' }) empty
   where

   go :: BwdConfig -> WithGraph (Step BwdConfig Unit)
   go { visits: Nil } = pure $ Done unit
   go { visited, visits: Enter α : visits }
      | α ∈ visited = pure $ Loop { visited, visits }
      | otherwise = pure $ Loop { visited: insert α visited, visits: (Enter <$> L.fromFoldable (outN g α)) <> (Exit α : visits) }
   go { visited, visits: Exit α : visits } = do
      extend (DVertex (α × vertexData g α)) (outN g α)
      pure $ Loop { visited, visits }
