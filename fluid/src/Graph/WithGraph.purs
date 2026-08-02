module Graph.WithGraph where

import Prelude hiding (map)

import Control.Monad.Except (class MonadError, lift)
import Control.Monad.State (StateT, modify, modify_, runStateT)
import Data.Foldable (foldMap)
import Data.Identity (Identity)
import Data.List (List(..), filter, range, (:))
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Newtype (class Newtype, over, unwrap)
import Data.Profunctor.Strong (first)
import Data.Set (Set, isEmpty)
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (fst, swap)
import Effect.Exception (Error)
import Graph (class Graph, class TypeName, class Vertices, DVertex, DVertex'(..), HyperEdge, Vertex(..), addresses, fromEdgeList, pack, showEdgeList, showGraph, showVertices, toEdgeList)
import Lattice (Raw)
import Test.Util.Debug (checking, tracing)
import Util (type (×), Endo, assertWhen, check, spy, spyFunWhenM, spyWhen, (×))
import Util.Set ((\\), (∈))

class Monad m <= MonadWithGraph m where
   -- Extend graph with existing vertex and its accompanying data pointing to set of existing vertices.
   extend :: DVertex -> Set Vertex -> m Unit

class Monad m <= MonadAlloc m where
   fresh :: m Vertex

-- Fix exceptions at Error, the type of JavaScript exceptions, because Aff requires Error, and
-- I can't see a way to convert MonadError Error m (for example) to MonadError Error m.
class (MonadAlloc m, MonadError Error m, MonadWithGraph m) <= MonadWithGraphAlloc m where
   -- Extend with a freshly allocated vertex.
   new :: forall f g. TypeName (g Vertex) => (Vertex -> f Vertex -> g Vertex) -> Set Vertex -> f Vertex -> m (g Vertex)

   -- Mark α as never to be contracted away. No-op unless the graph is being contracted.
   retain :: Vertex -> m Unit

type AllocT m = StateT Int m
type Alloc = AllocT Identity
type WithGraphAllocT m = WithGraphT (AllocT m)
type WithGraphT = StateT (List HyperEdge)
type WithGraph = WithGraphT Identity

instance Monad m => MonadAlloc (AllocT m) where
   fresh = do
      n <- modify $ (+) 1
      pure (Vertex $ show n)

instance MonadError Error m => MonadWithGraphAlloc (WithGraphAllocT m) where
   new constr αs vd = do
      α <- fresh
      let v = constr α vd
      extend (DVertex (α × pack v)) αs
      pure v

   retain _ = pure unit

instance Monad m => MonadWithGraph (WithGraphT m) where
   extend α αs = void $ modify_ $ (:) (α × αs)

-- ======================
-- Contracting variant
-- ======================

-- Graph retaining only inputs ∪ retained ∪ outputs; dropping α splices it out by rewiring α's
-- consumers to the union of α's producers' frontiers, preserving reachability and fwd's conjunction.
type ContractRec =
   { edges :: List HyperEdge -- all vertices, reverse creation order; filtered on freeze
   , resolved :: Map Vertex (Set Vertex) -- frontiers of vertices dropped at creation
   , kept :: Set Vertex -- seeded with inputs, extended by retain
   , keepAll :: Boolean -- contraction becomes identity
   }

-- Newtype rather than synonym: a bare record is not a legal instance head.
newtype ContractState = ContractState ContractRec

derive instance Newtype ContractState _

type ContractT = StateT ContractState
type ContractAllocT m = ContractT (AllocT m)

keep :: ContractRec -> Vertex -> Boolean
keep s α = s.keepAll || α ∈ s.kept

-- Nearest retained ancestors of β; a β neither retained nor extended is treated as retained.
frontier :: ContractRec -> Vertex -> Set Vertex
frontier s β
   | keep s β = Set.singleton β
   | otherwise = fromMaybe (Set.singleton β) (M.lookup β s.resolved)

instance Monad m => MonadWithGraph (ContractT m) where
   extend dv@(DVertex (α × _)) βs = modify_ $ over ContractState \s ->
      let
         βs' = foldMap (frontier s) βs
      in
         s
            { edges = (dv × βs') : s.edges
            , resolved = if keep s α then s.resolved else M.insert α βs' s.resolved
            }

instance Monad m => MonadAlloc (ContractAllocT m) where
   fresh = lift fresh

instance MonadError Error m => MonadWithGraphAlloc (ContractAllocT m) where
   new constr αs vd = do
      α <- fresh
      let v = constr α vd
      extend (DVertex (α × pack v)) αs
      pure v

   retain α = modify_ $ over ContractState \s -> s { kept = Set.insert α s.kept }

initialContractState :: Boolean -> Set DVertex -> ContractState
initialContractState keepAll αs = ContractState
   { edges: Nil
   , resolved: M.empty
   , kept: Set.map (fst <<< unwrap) αs
   , keepAll
   }

-- Outputs are not identifiable at creation (a vertex can have consumers and still be returned), so
-- they are recovered from the result here.
freezeContracted
   :: forall g m a
    . Monad m
   => Graph g
   => Boolean
   -> (a -> Set Vertex)
   -> ContractT m a
   -> Set DVertex
   -> m (g × a)
freezeContracted keepAll outputs m αs = do
   a × ContractState s <- runStateT m (initialContractState keepAll αs)
   let
      kept = s.kept `Set.union` outputs a
      retained (DVertex (α × _) × _) = s.keepAll || α ∈ kept
   pure (fromEdgeList αs (filter retained s.edges) × a)

alloc :: forall m f. MonadAlloc m => Traversable f => Raw f -> m (f Vertex)
alloc = traverse (const fresh)

runAllocT :: forall m a. Monad m => AllocT m a -> Int -> m (Int × Set Vertex × a)
runAllocT m n = do
   a × n' <- runStateT m n
   let fresh_αs = Set.fromFoldable $ (Vertex <<< show) <$> range' (n + 1) n'
   pure (n' × fresh_αs × a)
   where
   -- built-in range function is singularly useless
   range' :: Int -> Int -> List Int
   range' n1 n2 = if n2 < n1 then Nil else range n1 n2

runWithGraphT :: forall g m a. Monad m => Graph g => WithGraphT m a -> Set DVertex -> m (g × a)
runWithGraphT m αs = do
   g × a <- freezeGraph m αs
   -- only check one direction for now
   assertWhen checking.edgeListGC "edgeListGC" (\_ -> g == fromEdgeList mempty (toEdgeList g)) $
      pure (g × a)

freezeGraph :: forall g m a. Monad m => Graph g => WithGraphT m a -> Set DVertex -> m (g × a)
freezeGraph m αs = runStateT m Nil <#> swap <#> first (fromEdgeList αs <<< report "edge list" showEdgeList)
   where
   report :: forall c b. String -> (c -> b) -> Endo c
   report msg = spyWhen tracing.runWithGraphT ("runWithGraphT " <> msg)

-- ======================
-- Diagnostics
-- ======================

-- Verify round-tripping of x' = alloc x and vertices x'. (Only makes sense if m is ~ alloc x.)
alloc_check :: forall m a. Vertices a => MonadError Error m => String -> AllocT m a -> m Unit
alloc_check msg m = do
   n × αs × x <- runAllocT m 0
   let report = spy (show n <> " allocations, unaccounted for") showVertices
   check (report (αs \\ addresses x) # isEmpty) $ "alloc " <> msg <> " round-trip"

runWithGraphT_spy :: forall g m a. Monad m => Graph g => WithGraphT m a -> Set DVertex -> m (g × a)
runWithGraphT_spy =
   runWithGraphT
      >>> spyFunWhenM tracing.runWithGraphT "runWithGraphT" (Set.map (fst <<< unwrap) >>> showVertices) (fst >>> showGraph)

runWithGraph_spy :: forall g a. Graph g => WithGraph a -> Set DVertex -> g × a
runWithGraph_spy m = runWithGraphT_spy m >>> unwrap

-- ======================
-- Boilerplate
-- ======================
runAlloc :: forall a. Alloc a -> Int -> Int × Set Vertex × a
runAlloc m = runAllocT m >>> unwrap

runWithGraph :: forall g a. Graph g => WithGraph a -> Set DVertex -> g × a
runWithGraph m = runWithGraphT m >>> unwrap

instance Monad m => MonadAlloc (WithGraphAllocT m) where
   fresh = lift fresh
