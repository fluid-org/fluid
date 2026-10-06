module Test.Util.Suite where

import Prelude

import App.Fig (loadFig, selectInput, selectOutput, selectionResult)
import App.Util (SelStates, Selector, isInert, isPersistent, isTransient, selStates, 𝕊)
import App.Util.Selector (ConstrArg, constrArg, sel𝔹)
import App.View.Util (Fig, Options)
import Bind (Bind)
import DataType (class HasClasses)
import Control.Monad.Error.Class (class MonadError, catchError)
import Control.Monad.Reader (class MonadReader)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe)
import Data.Profunctor.Strong ((&&&))
import Data.Tuple (uncurry)
import Effect.Aff (Error, message)
import Eval (graphEval)
import Effect.Aff.Class (class MonadAff)
import File (class LoadFile, File(..), FileCxt, Folder(..), loadFile, (</>))
import Lattice (𝔹)
import Module (prepConfig)
import Test.Benchmark.Util (BenchRow, logTimeWhen)
import Test.Util (DepSpec, TestSuite, checkEq, checkSelection, depName, fluidSrcPaths, test, testDep)
import Test.Util.Debug (timing)
import Util (type (×), throw, (×))
import Val (class HasModuleStore, Val, Env)

-- benchmarks parameterised on number of iterations
type BenchSuite m = Int × Boolean -> Array (String × m BenchRow)

type TestSpec =
   { file :: String
   , fwd_expect :: String
   }

type TestLinkedOutputsSpec =
   { spec :: Options
   , δ_out :: ConstrArg -> Selector Val
   , out_expect :: ConstrArg -> Selector Val
   , inert_expect :: ConstrArg -> Maybe (Selector Val)
   , file :: String
   }

type TestLinkedInputsSpec =
   { spec :: Options
   , δ_in :: Bind (Selector Val)
   , in_expect :: Selector Env
   , file :: String
   }

type SuiteFactory r m = MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array { file :: String | r } -> BenchSuite m

suite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array TestSpec -> BenchSuite m
suite specs (n × is_bench) = specs <#> (_.file &&& asTest)
   where
   asTest :: TestSpec -> m BenchRow
   asTest { file, fwd_expect } = do
      test (File file) fwd_expect (n × is_bench)

depSuite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array DepSpec -> TestSuite m
depSuite specs = specs >>= \{ file, queries } -> queries <#> \query -> depName file query × testDep (File file) query

selected :: SelStates 𝕊 -> SelStates 𝔹
selected s = selStates (isInert s) (isPersistent s) (isTransient s)

linkedOutputsTest :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => TestLinkedOutputsSpec -> m Fig
linkedOutputsTest { spec, δ_out, out_expect, inert_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig0 <- loadFig spec fluidSrc
   let arg = constrArg fig0.fieldIndex
   let fig = selectOutput (δ_out arg) fig0
   v <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).v
   checkSelection (out_expect arg) (selected <$> v)
   for_ (inert_expect arg) \sel -> checkEq "inert" "inert_expect" (isInert <$> v) (sel𝔹 sel v)
   pure fig

linkedOutputsSuite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array TestLinkedOutputsSpec -> Array (String × m Unit)
linkedOutputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedOutputsTest >>> void))

linkedInputsTest :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => TestLinkedInputsSpec -> m Fig
linkedInputsTest { spec, δ_in, in_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- loadFig spec fluidSrc <#> uncurry selectInput δ_in
   ρ <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).ρ
   checkSelection in_expect (selected <$> ρ)
   pure fig

linkedInputsSuite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array TestLinkedInputsSpec -> Array (String × m Unit)
linkedInputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedInputsTest >>> void))

type IllFormedSpec =
   { file :: String
   , expected_error :: String
   }

illFormedSuite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array IllFormedSpec -> Array (String × m Unit)
illFormedSuite specs = specs <#> (_.file &&& asTest)
   where
   folder = Folder "ill_formed"

   asTest :: IllFormedSpec -> m Unit
   asTest { file, expected_error } = do
      fluidSrc <- loadFile fluidSrcPaths (folder </> File file)
      result <- catchError (run fluidSrc *> pure (Left unit)) (pure <<< Right)
      case result of
         Right err ->
            when (message err /= expected_error)
               $ throw
               $ "Expected error: " <> expected_error <> "; got: " <> message err
         Left _ -> throw $ "Expected ill-formed: " <> file

   run :: String -> m Unit
   run fluidSrc = do
      { e, gconfig } <- prepConfig fluidSrc
      void $ graphEval gconfig e
