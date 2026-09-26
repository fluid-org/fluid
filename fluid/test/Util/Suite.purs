module Test.Util.Suite where

import Prelude

import App.Fig (loadFig, selectInput, selectOutput, selectionResult)
import App.Util (SelectionType(..), Selector, isInert, isPersistent, isTransient, selStates)
import App.Util.Selector (ConstrArg, constrArg, sel𝔹)
import App.View.Util (Fig, Options)
import Bind (Bind)
import DataType (class HasClasses)
import Control.Monad.Error.Class (class MonadError, catchError)
import Control.Monad.Reader (class MonadReader, local)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Profunctor.Strong (second, (&&&))
import Data.Tuple (fst, uncurry)
import Effect.Aff (Error, message)
import Eval (graphEval)
import Effect.Aff.Class (class MonadAff)
import File (class LoadFile, File(..), FileCxt(..), Folder(..), loadFile, (</>))
import Lattice (botOf)
import Module (prepConfig)
import Test.Benchmark.Util (BenchRow, logTimeWhen)
import Test.Util (checkEq, fluidSrcPaths, test)
import Test.Util.Debug (timing)
import Util (type (×), throw, (×))
import Val (class HasModuleStore, Val, Env)

-- benchmarks parameterised on number of iterations
type BenchSuite m = Int × Boolean -> Array (String × m BenchRow)

type TestSpec =
   { file :: String
   , fwd_expect :: String
   }

type TestBwdSpec =
   { file :: String
   , bwd_expect :: ConstrArg -> Selector Env
   , δv :: ConstrArg -> Selector Val
   , fwd_expect :: String
   , inputs :: Array String
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
      test (File file) { δv: \_ -> identity >>> (_ × Persistent), fwd_expect, bwd_expect: Nothing, inputs: [] } (n × is_bench)

bwdSuite :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array TestBwdSpec -> BenchSuite m
bwdSuite specs (n × is_bench) = specs <#> ((_.file >>> File >>> (folder </> _) >>> show) &&& asTest)
   where
   folder = Folder "slicing"

   asTest :: TestBwdSpec -> m BenchRow
   asTest { file, bwd_expect, δv, fwd_expect, inputs } = do
      test (folder </> File file) { δv, fwd_expect, bwd_expect: Just bwd_expect, inputs } (n × is_bench)

linkedOutputsTest :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => TestLinkedOutputsSpec -> m Fig
linkedOutputsTest { spec, δ_out, out_expect, inert_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig0 <- loadFig spec fluidSrc
   let arg = constrArg fig0.fieldIndex
   let fig = selectOutput (δ_out arg) fig0
   v <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).v
   checkEq "selected" "expected" (selStates <$> (isInert <$> v) <*> (isPersistent <$> v) <*> (isTransient <$> v)) (fst $ out_expect arg (botOf <$> v))
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
   checkEq "selected" "expected" (selStates <$> (isInert <$> ρ) <*> (isPersistent <$> ρ) <*> (isTransient <$> ρ)) (fst $ in_expect (botOf <$> ρ))
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

-- Ill-formed suite with further source roots on search path
illFormedSuiteIn :: forall m. MonadAff m => MonadError Error m => HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => Array Folder -> Array IllFormedSpec -> Array (String × m Unit)
illFormedSuiteIn roots = illFormedSuite >>> map (second (local (\(FileCxt cxt) -> FileCxt cxt { fluidSrcPaths = cxt.fluidSrcPaths <> roots })))
