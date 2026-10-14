module Test.Benchmark.Intermediate where

import Prelude

import App.Util (Selector, getPersistent, unselected)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array (concatMap, drop, elem, filter, head, zip)
import Data.Array.NonEmpty (fromArray, singleton) as NEA
import Data.Foldable (for_, sum)
import Data.Int (toNumber)
import Data.List.Lazy (replicateM)
import Data.Map (fromFoldable, lookup) as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Number (fromString) as Number
import Data.Number.Format (fixed, toStringWith)
import Data.Set (Set)
import Data.String (Pattern(..), contains, joinWith, split, trim)
import Data.String.CodeUnits (dropWhile, takeWhile) as CU
import Data.Traversable (for)
import Data.Tuple (fst)
import Effect.Aff (Error)
import Effect.Aff.Class (class MonadAff)
import Effect.Class.Console (log)
import Eval (GraphEval, graphEval, graphEvalContracted, graphGC, withOp)
import File (class LoadFile, File(..), FileCxt, loadFile)
import Graph (Vertex, select𝔹s, selectαs, vertices)
import Graph.GraphImpl (GraphImpl)
import Lattice (neg, 𝔹)
import Module (prepConfig)
import Primitive.Defs (primitives)
import Test.Benchmark.Util (BenchAcc(..), BenchRow, time)
import Test.Util (fluidSrcPaths, testContracted)
import Test.Util.Suite (TestBwdIntermediateSpec, intermediateTest)
import Util (type (×), AffError, Endo, Thunk, (×))
import Val (EnvStmt, Val)

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
