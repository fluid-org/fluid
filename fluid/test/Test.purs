module Test.Test where

import Prelude

import Control.Monad.Error.Class (class MonadError)
import Val (class MonadProgram)
import Data.Array (concat, filter, elem)
import Data.Profunctor.Strong (second)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import File (class LoadFile, Folder(..), emptyFileCxt, withRoots)
import Module.Web (runWebT)
import Test.Specs.IllFormed (illFormed_cases, shadow_cases)
import Test.Specs.Comments (comments_cases)
import Test.Specs.Comprehension (comprehension_cases)
import Test.Specs.Dependence (dep_cases)
import Test.Specs.Graphics (graphics_cases)
import Test.Specs.Intermediates (intermediates_cases)
import Test.Specs.LinkedInputs (linkedInputs_cases)
import Test.Specs.LinkedOutputs (linkedOutputs_cases)
import Test.Specs.Misc (misc_cases)
import Test.Specs.Paragraph (paragraph_cases)
import Test.Util (TestSuite, fluidSrcPaths)
import Test.Util.Mocha (run)
import Test.Util.Suite (BenchSuite, SuiteFactory, depSuite, illFormedSuite, intermediatesSuite, linkedInputsSuite, linkedOutputsSuite, suite)
import Util ((×))

main :: Effect Unit
main = run (second (runWebT emptyFileCxt <<< withRoots fluidSrcPaths) <$> tests)

tests :: forall m. MonadProgram m => TestSuite m
tests = allTests

scratchpad :: forall m. MonadProgram m => TestSuite m
scratchpad = illFormedSuite (filter (\c -> c.file `elem` [ "matrix_dim_type.fld" ]) illFormed_cases)

filterSuite
   :: forall m r
    . MonadProgram m
   => Array String
   -> Array { file :: String | r }
   -> SuiteFactory r m
   -> TestSuite m
filterSuite files cases makeSuite =
   second void <$> makeSuite (filter (\c -> c.file `elem` files) cases) (1 × false)

allTests :: forall m. MonadProgram m => TestSuite m
allTests = concat (benchmarks <#> asTestSuite) <> depSuite dep_cases <> linkingTests <> illFormedTests

linkingTests :: forall m. MonadProgram m => TestSuite m
linkingTests = linkedOutputsSuite linkedOutputs_cases <> linkedInputsSuite linkedInputs_cases
   <> intermediatesSuite intermediates_cases

illFormedTests :: forall m. MonadProgram m => TestSuite m
illFormedTests = illFormedSuite illFormed_cases <> (second (withRoots [ Folder "test/lib/predefined" ]) <$> illFormedSuite shadow_cases)

asTestSuite :: forall m. MonadAff m => MonadError Error m => LoadFile m => BenchSuite m -> TestSuite m
asTestSuite suite = second void <$> suite (1 × false)

benchmarks :: forall m. MonadProgram m => Array (BenchSuite m)
benchmarks =
   [ suite comprehension_cases
   , suite misc_cases
   , suite comments_cases
   , suite paragraph_cases
   , suite graphics_cases
   ]
