module Test.Test where

import Prelude

import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array (concat, filter, elem)
import Data.Array.NonEmpty (fromArray) as NEA
import Data.Maybe (maybe)
import Data.Profunctor.Strong (second)
import Data.Traversable (sequence, traverse)
import Effect (Effect)
import Effect.Class.Console (log)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import File (class LoadFile, FileCxt(..))
import Module.Web (runWebT)
import Test.Specs.Bwd (bwd_cases)
import Test.Specs.BwdIntermediate (bwdIntermediate_cases)
import Test.Specs.IllFormed (illFormed_cases, purepy_cases)
import Test.Specs.Comments (comments_cases)
import Test.Specs.Desugar (desugar_cases)
import Test.Specs.Graphics (graphics_cases)
import Test.Specs.LinkedInputs (linkedInputs_cases)
import Test.Specs.LinkedOutputs (linkedOutputs_cases)
import Test.Specs.Misc (misc_cases)
import Test.Specs.Paragraph (paragraph_cases)
import Test.Benchmark.Intermediate (probeGraphStats)
import Test.Benchmark.Util (BenchAcc(..))
import Test.Util (TestSuite, fluidSrcPaths)
import Test.Util.Mocha (run)
import Test.Util.Suite (BenchSuite, SuiteFactory, bwdSuite, illFormedSuite, linkedInputsSuite, linkedOutputsSuite, suite)
import Util ((×))

main :: Effect Unit
main = run (second (runWebT (FileCxt { fluidSrcPaths })) <$> tests)

tests :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestSuite m
tests = scratchpad

-- Set tests = scratchpad to run the intermediate-value benchmarks. They report through the
-- console, so capture the run and split it with script/util/extract-bench.mjs; see
-- docs/reports/intermediate-perf-notes.md.
scratchpad :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestSuite m
scratchpad =
   [ "graph-stats" × probeGraphStats bwdIntermediate_cases
   ]

benchmarkAll :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Int -> m Unit
benchmarkAll n = do
   rows <- traverse sequence (concat (benchmarks <#> (_ $ (n × true))))
   maybe (log "no benchmarks") (log <<< show <<< BenchAcc) (NEA.fromArray rows)

filterSuite :: forall m r. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array String -> Array { file :: String | r } -> SuiteFactory r m -> TestSuite m
filterSuite files cases makeSuite =
   second void <$> makeSuite (filter (\c -> c.file `elem` files) cases) (1 × false)

allTests :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestSuite m
allTests = concat (benchmarks <#> asTestSuite) <> linkingTests <> illFormedTests

linkingTests :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestSuite m
linkingTests = linkedOutputsSuite linkedOutputs_cases <> linkedInputsSuite linkedInputs_cases

illFormedTests :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestSuite m
illFormedTests = illFormedSuite (purepy_cases <> illFormed_cases)

asTestSuite :: forall m. MonadAff m => MonadError Error m => LoadFile m => BenchSuite m -> TestSuite m
asTestSuite suite = second void <$> suite (1 × false)

benchmarks :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array (BenchSuite m)
benchmarks =
   [ suite desugar_cases
   , suite misc_cases
   , suite comments_cases
   , suite paragraph_cases
   , bwdSuite bwd_cases
   , suite graphics_cases
   ]
