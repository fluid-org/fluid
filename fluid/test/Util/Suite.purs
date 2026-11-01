module Test.Util.Suite where

import Prelude

import App.Fig (loadFig, selectInput, selectOutput, selectionResult)
import App.Util (SelStates, Selector, isInert, isPersistent, isTransient, selStates, 𝕊)
import App.Util.Selector (ObjArg, objArg, sel𝔹, valOf)
import App.View.Util (Fig, Options)
import Bind (Bind)
import Classes (class HasClasses)
import Control.Monad.Error.Class (catchError)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe)
import Data.Profunctor.Strong ((&&&))
import Data.Tuple (uncurry)
import Effect.Aff (message)
import Eval (evalProgram)
import File (class MonadLoad, File(..), Folder(..), loadFile, (</>))
import Lattice (𝔹)
import Module (prepConfig, throwParseFailure)
import Test.Benchmark.Util (BenchRow, logTimeWhen)
import Test.Util (DepSpec, TestSuite, checkEq, checkSelection, depName, fluidSrcPaths, test, testDep)
import Test.Util.Debug (timing)
import Util (type (×), throw, (×))
import Val (class HasModuleStore, Val, EnvWithDocs)

-- benchmarks parameterised on number of iterations
type BenchSuite m = Int × Boolean -> Array (String × m BenchRow)

type TestSpec =
   { file :: String
   , fwd_expect :: String
   }

type TestLinkedOutputsSpec =
   { spec :: Options
   , δ_out :: ObjArg -> Selector Val
   , out_expect :: ObjArg -> Selector Val
   , inert_expect :: ObjArg -> Maybe (Selector Val)
   , file :: String
   }

type TestLinkedInputsSpec =
   { spec :: Options
   , δ_in :: Bind (Selector Val)
   , in_expect :: Selector EnvWithDocs
   , file :: String
   }

type SuiteFactory r m = HasClasses m => HasModuleStore m => MonadLoad m => Array { file :: String | r } -> BenchSuite m

suite :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Array TestSpec -> BenchSuite m
suite specs (n × is_bench) = specs <#> (_.file &&& asTest)
   where
   asTest :: TestSpec -> m BenchRow
   asTest { file, fwd_expect } = do
      test (File file) fwd_expect (n × is_bench)

depSuite :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Array DepSpec -> TestSuite m
depSuite specs = specs >>= \{ file, queries } -> queries <#> \query -> depName file query × testDep (File file) query

selected :: SelStates 𝕊 -> SelStates 𝔹
selected s = selStates (isInert s) (isPersistent s) (isTransient s)

linkedOutputsTest :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => TestLinkedOutputsSpec -> m Fig
linkedOutputsTest { spec, δ_out, out_expect, inert_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig0 <- logTimeWhen timing.loadFig (file <> " loadFig") \_ -> loadFig spec fluidSrc
   let arg = objArg
   let fig = selectOutput (valOf (δ_out arg)) fig0
   v <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).v
   checkSelection (valOf (out_expect arg)) (selected <$> v)
   for_ (inert_expect arg) \sel -> checkEq "inert" "inert_expect" (isInert <$> v) (sel𝔹 (valOf sel) v)
   pure fig

linkedOutputsSuite :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Array TestLinkedOutputsSpec -> Array (String × m Unit)
linkedOutputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedOutputsTest >>> void))

linkedInputsTest :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => TestLinkedInputsSpec -> m Fig
linkedInputsTest { spec, δ_in, in_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- logTimeWhen timing.loadFig (file <> " loadFig") (\_ -> loadFig spec fluidSrc) <#> uncurry selectInput (valOf <$> δ_in)
   ρ <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).ρ
   checkSelection in_expect (selected <$> ρ)
   pure fig

linkedInputsSuite :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Array TestLinkedInputsSpec -> Array (String × m Unit)
linkedInputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedInputsTest >>> void))

type IllFormedSpec =
   { file :: String
   , expected_error :: String
   }

illFormedSuite :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Array IllFormedSpec -> Array (String × m Unit)
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
      { e, inputs, classes } <- throwParseFailure (prepConfig fluidSrc)
      void $ evalProgram inputs classes e
