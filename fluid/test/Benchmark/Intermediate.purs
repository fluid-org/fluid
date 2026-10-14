module Test.Benchmark.Intermediate where

import Prelude hiding (top)

import App.Util (Selector, getPersistent, unselected)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Array (concatMap, drop, elem, filter, head, zip)
import Data.Array (fromFoldable, index, length, null, sort) as A
import Data.Array.NonEmpty (fromArray, singleton) as NEA
import Data.Foldable (foldl, for_, maximum, sum)
import Data.Int (floor, toNumber)
import Data.List.Lazy (replicateM)
import Data.List (List(..), reverse, (:))
import Data.Map (fromFoldable, lookup) as Map
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Number (fromString) as Number
import Data.Number.Format (fixed, toStringWith)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), contains, joinWith, split, trim)
import Data.String.CodeUnits (dropWhile, takeWhile) as CU
import Data.Traversable (for)
import Data.Tuple (fst, snd)
import Effect.Aff (Error)
import Effect.Aff.Class (class MonadAff)
import Effect.Class.Console (log)
import Eval (GraphEval, graphEval, graphEvalContracted, graphGC, withOp)
import File (class LoadFile, File(..), FileCxt, loadFile)
import Graph (DVertex'(..), Vertex, addresses, inEdges, inEdges', inN, outN, select𝔹s, selectαs, sinks, size, sources, topologicalSort, vertices)
import Graph.GraphImpl (GraphImpl)
import Lattice (neg, top, 𝔹)
import Module (prepConfig)
import Primitive.Defs (primitives)
import Test.Benchmark.Util (BenchAcc(..), BenchRow, time)
import Test.Util (fluidSrcPaths, testContracted)
import Test.Util.Suite (TestBwdIntermediateSpec, intermediateTest)
import Util (type (×), AffError, Endo, Thunk, (×))
import Val (EnvStmt, Val, intermediateVertices)

-- Suffix distinguishing the two arms of a paired benchmark: without-@doc, and contracted.
docSuffix :: String
docSuffix = "°"

contractedSuffix :: String
contractedSuffix = "ᶜ"

-- Each fixture with and without its @doc annotations.
benchmarkIntermediates
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Int
   -> Array TestBwdIntermediateSpec
   -> AffError m Unit
benchmarkIntermediates n specs = do
   rows <- for specs \s -> perFixture s.file (intermediateTest n s)
   emit "intermediate-doc" docSuffix rows

-- Each fixture evaluated uncontracted and contracted, asserting the two agree on the selections.
benchmarkIntermediatesContracted
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Int
   -> Array TestBwdIntermediateSpec
   -> AffError m Unit
benchmarkIntermediatesContracted n specs = do
   rows <- for specs \s ->
      perFixture s.file (testContracted (File s.file) primitives { δv: s.δv, fwd_expect: "", bwd_expect: Nothing } (n × true))
   emit "intermediate-contracted" contractedSuffix rows

-- Splits each sliced query into its stages, to separate graph traversal from the walks over the
-- EnvStmt/Val structure that graphGC does either side of it.
probeStages
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Int
   -> Array TestBwdIntermediateSpec
   -> AffError m Unit
probeStages n specs = do
   log "==== BENCH BEGIN stages.csv ===="
   log "Test-Name,Arm,Query,Select-In,Slice,Vertices,Select-Out"
   for_ specs \s -> do
      fluidSrc <- loadFile fluidSrcPaths (File s.file)
      { e, gconfig } <- prepConfig primitives fluidSrc
      u <- graphEval gconfig e
      c <- graphEvalContracted gconfig e
      stagesFor n s.file "uncontracted" s.δv u
      stagesFor n s.file "contracted" s.δv c
   log "==== BENCH END stages.csv ===="

stagesFor
   :: forall m
    . MonadAff m
   => Int
   -> String
   -> String
   -> Selector Val
   -> GraphEval GraphImpl EnvStmt Val
   -> AffError m Unit
stagesFor n file arm δv graphed = do
   stageRowB n file arm "Demands" out0 graphed.outα graphed.graph_bwd graphed.g graphed.inα
   stageRowF n file arm "Suffices" in0 graphed.inα graphed.graph_fwd graphed.g graphed.outα
   stageRowF n file arm "DemBy-Dir" in0 gop.outα gop.graph_bwd gop.g gop.inα
   stageRowF n file arm "DemBy-Suff" (neg in0) graphed.inα graphed.graph_fwd graphed.g graphed.outα
   where
   v = map (const top) graphed.outα :: Val 𝔹
   out0 = fst (δv (const unselected <$> v)) <#> getPersistent
   in0 = fst ((graphGC graphed).bwd out0)
   gop = withOp graphed

-- Times selectαs, the slice itself, harvesting its vertices, and select𝔹s, each averaged over n.
-- Two monomorphic variants: Selectαs's fundep runs a -> b, so the result type needs pinning.
stageRowB
   :: forall m
    . MonadAff m
   => Int
   -> String
   -> String
   -> String
   -> Val 𝔹
   -> Val Vertex
   -> (Set Vertex -> Endo GraphImpl)
   -> GraphImpl
   -> EnvStmt Vertex
   -> AffError m Unit
stageRowB n file arm q sel selα slice g outα = do
   t1 <- timeN n \_ -> pure (selectαs sel selα)
   let αs = selectαs sel selα
   t2 <- timeN n \_ -> pure (slice αs g)
   let g' = slice αs g
   t3 <- timeN n \_ -> pure (vertices g')
   let vs = vertices g'
   t4 <- timeN n \_ -> pure (select𝔹s outα vs :: EnvStmt 𝔹)
   log (joinWith "," [ file, arm, q, fmt3 t1, fmt3 t2, fmt3 t3, fmt3 t4 ])

stageRowF
   :: forall m
    . MonadAff m
   => Int
   -> String
   -> String
   -> String
   -> EnvStmt 𝔹
   -> EnvStmt Vertex
   -> (Set Vertex -> Endo GraphImpl)
   -> GraphImpl
   -> Val Vertex
   -> AffError m Unit
stageRowF n file arm q sel selα slice g outα = do
   t1 <- timeN n \_ -> pure (selectαs sel selα)
   let αs = selectαs sel selα
   t2 <- timeN n \_ -> pure (slice αs g)
   let g' = slice αs g
   t3 <- timeN n \_ -> pure (vertices g')
   let vs = vertices g'
   t4 <- timeN n \_ -> pure (select𝔹s outα vs :: Val 𝔹)
   log (joinWith "," [ file, arm, q, fmt3 t1, fmt3 t2, fmt3 t3, fmt3 t4 ])

timeN :: forall m a. MonadAff m => Int -> Thunk (m a) -> m Number
timeN n th = do
   ts <- replicateM n (time th)
   pure (sum (fst <$> ts) / toNumber n)

fmt3 :: Number -> String
fmt3 = toStringWith (fixed 3)

-- Bracket each fixture with its own output, so a run that dies partway still says which fixture
-- it was on and what the completed ones measured.
perFixture :: forall m. MonadAff m => String -> AffError m BenchRow -> AffError m (String × BenchRow)
perFixture file result = do
   log ("---- BENCH FIXTURE start " <> file)
   row <- result
   log ("---- BENCH FIXTURE done " <> file <> "\n" <> show (BenchAcc (NEA.singleton (file × row))))
   pure (file × row)

-- Delimit each table so a run's console output can be split into files.
emit :: forall m. MonadAff m => String -> String -> Array (String × BenchRow) -> AffError m Unit
emit tag suffix rows = maybe (log ("no benchmark files for " <> tag)) emit' (NEA.fromArray rows)
   where
   emit' rows' = do
      log ("==== BENCH BEGIN " <> tag <> ".csv ====")
      log csv
      log ("==== BENCH END " <> tag <> ".csv ====")
      log ("==== BENCH BEGIN " <> tag <> ".tex ====")
      log (latexFromCsv suffix csv)
      log ("==== BENCH END " <> tag <> ".tex ====")
      where
      csv = show (BenchAcc rows')

latexFromCsv :: String -> String -> String
latexFromCsv suffix csv =
   joinWith "\n" ([ headerLine ] <> map rowLine dataRows)
   where
   rows = filter (_ /= "") (map trim (split (Pattern "\n") csv))
   header = maybe [] (split (Pattern ",")) (head rows)
   dataRows = drop 1 rows
   bases = filter (\c -> not (contains (Pattern suffix) c) && (c <> suffix) `elem` header) header

   headerLine =
      joinWith " & " ([ "File" ] <> concatMap (\b -> [ b, b <> suffix, b <> " ratio" ]) bases) <> " \\\\"

   rowLine line = joinWith " & " ([ name ] <> concatMap cellsFor bases) <> " \\\\"
      where
      cells = split (Pattern ",") line
      dict = Map.fromFoldable (zip header cells)
      name = fromMaybe "?" (head cells)
      col c = mean (fromMaybe "" (Map.lookup c dict))
      cellsFor b = [ fmt (col b), fmt (col (b <> suffix)), ratio (col b) (col (b <> suffix)) ]

mean :: String -> Number
mean s = fromMaybe 0.0 (Number.fromString (CU.takeWhile numeric (CU.dropWhile (not <<< numeric) s)))
   where
   numeric c = (c >= '0' && c <= '9') || c == '.' || c == '-'

fmt :: Number -> String
fmt = toStringWith (fixed 1)

ratio :: Number -> Number -> String
ratio a b
   | b == 0.0 = "--"
   | otherwise = toStringWith (fixed 3) (a / b)

-- Structural statistics of every graph, both arms, and of the slice each of the four timed queries
-- takes in each arm. Graph structure is deterministic, so one run per fixture suffices.
probeGraphStats
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Array TestBwdIntermediateSpec
   -> AffError m Unit
probeGraphStats specs = do
   rows <- for specs \s -> do
      log ("---- STATS FIXTURE " <> s.file)
      fluidSrc <- loadFile fluidSrcPaths (File s.file)
      { e, gconfig } <- prepConfig primitives fluidSrc
      u <- graphEval gconfig e
      c <- graphEvalContracted gconfig e
      pure
         ( [ graphRow s.file "uncontracted" u, graphRow s.file "contracted" c ]
              × (sliceRows s.file "uncontracted" s.δv u <> sliceRows s.file "contracted" s.δv c)
         )
   block "graph-stats.csv" graphHeader (concatMap fst rows)
   block "slice-stats.csv" sliceHeader (concatMap snd rows)
   where
   block name header lines = do
      log ("==== BENCH BEGIN " <> name <> " ====")
      log (joinWith "\n" ([ header ] <> lines))
      log ("==== BENCH END " <> name <> " ====")

graphHeader :: String
graphHeader = joinWith ","
   [ "Test-Name"
   , "Arm"
   , "Vertices"
   , "Edges"
   , "Inputs"
   , "Outputs"
   , "Doc"
   , "Other"
   , "Sources"
   , "Sinks"
   , "Out-Max"
   , "Out-Mean"
   , "Out-P50"
   , "Out-P90"
   , "Out-P99"
   , "In-Max"
   , "In-Mean"
   , "In-P50"
   , "In-P90"
   , "In-P99"
   , "Longest-Path"
   ]

-- Inputs and outputs are the addresses of inα and outα present in the graph; Doc the @doc-annotated
-- vertices; Other everything else, which contraction should leave empty.
graphRow :: String -> String -> GraphEval GraphImpl EnvStmt Val -> String
graphRow file arm { g, inα, outα } =
   joinWith "," $
      [ file, arm ]
         <> map show [ size g, sum outDegs, Set.size ins, Set.size outs, Set.size docs, Set.size others ]
         <> map show [ Set.size (sources g), Set.size (sinks g) ]
         <> degreeStats outDegs
         <> degreeStats inDegs
         <> [ show (longestPath g) ]
   where
   αs = addresses g
   ins = Set.intersection αs (addresses inα)
   outs = Set.intersection αs (addresses outα)
   docs = Set.map (\(DVertex (α × _)) -> α) (intermediateVertices (vertices g))
   others = Set.difference αs (Set.unions [ ins, outs, docs ])
   outDegs = A.fromFoldable αs <#> \α -> Set.size (outN g α)
   inDegs = A.fromFoldable αs <#> \α -> Set.size (inN g α)

degreeStats :: Array Int -> Array String
degreeStats ds = [ show (fromMaybe 0 (maximum ds)), fmt3 mean', pct 0.5, pct 0.9, pct 0.99 ]
   where
   sorted = A.sort ds
   n = A.length ds
   mean' = if n == 0 then 0.0 else toNumber (sum ds) / toNumber n
   pct p = show (fromMaybe 0 (A.index sorted (floor (p * toNumber (n - 1)))))

-- Longest path in edges. The topological order's direction is not documented, so try both; the
-- right one gives the exact length and the wrong one a lower bound.
longestPath :: GraphImpl -> Int
longestPath g = max (pathLen order) (pathLen (reverse order))
   where
   order = topologicalSort g
   pathLen vs = fromMaybe 0 (maximum (M.values (foldl step M.empty vs)))
   step acc α = M.insert α len acc
      where
      ws = A.fromFoldable (outN g α)
      len = if A.null ws then 0 else 1 + fromMaybe 0 (maximum (ws <#> \w -> fromMaybe 0 (M.lookup w acc)))

sliceHeader :: String
sliceHeader = joinWith "," [ "Test-Name", "Arm", "Query", "Graph-Vertices", "Select-In", "Slice-Vertices", "Slice-Edges", "Visited" ]

-- The four timed queries, seeded as testProperties seeds them. Visited is the slice for the
-- backward queries, which return everything they visit; for the forward ones it adds the vertices
-- considered but never made available.
sliceRows :: String -> String -> Selector Val -> GraphEval GraphImpl EnvStmt Val -> Array String
sliceRows file arm δv graphed =
   [ row "Demands" (selectαs out0 graphed.outα) graphed.graph_bwd graphed.g false
   , row "Suffices" (selectαs in0 graphed.inα) graphed.graph_fwd graphed.g true
   , row "DemBy-Dir" (selectαs in0 gop.outα) gop.graph_bwd gop.g false
   , row "DemBy-Suff" (selectαs (neg in0) graphed.inα) graphed.graph_fwd graphed.g true
   ]
   where
   v = map (const top) graphed.outα :: Val 𝔹
   out0 = fst (δv (const unselected <$> v)) <#> getPersistent
   in0 = fst ((graphGC graphed).bwd out0)
   gop = withOp graphed
   row q αs slice g fwd =
      joinWith "," [ file, arm, q, show (size g), show (Set.size αs), show (size g'), show edges', show visited ]
      where
      g' = slice αs g
      edges' = sum (A.fromFoldable (addresses g') <#> \α -> Set.size (outN g' α))
      visited = if fwd then Set.size (fwdVisited g αs) else size g'

-- fwdSlice's traversal, returning every vertex it considers rather than the slice.
fwdVisited :: GraphImpl -> Set Vertex -> Set Vertex
fwdVisited g αs = tailRec go (αs × M.empty × inEdges g αs)
   where
   go (seen × _ × Nil) = Done seen
   go (seen × pending × ((α × β) : es)) =
      if βs == outN g α then Loop (Set.insert α seen × M.delete α pending × (inEdges' g α <> es))
      else Loop (Set.insert α seen × M.insert α βs pending × es)
      where
      βs = maybe (Set.singleton β) (Set.insert β) (M.lookup α pending)
