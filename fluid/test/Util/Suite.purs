module Test.Util.Suite where

import Prelude

import App.Fig (loadFig, loadFigWith, selectInput, selectOutput, selectionResult)
import App.Util (SelectionType(..), Selector, getPersistent, isInert, isPersistent, isTransient, selStates)
import App.Util.Selector (sel𝔹)
import App.View.Util (Fig, Options)
import Bind (Bind)
import Control.Monad.Error.Class (class MonadError, catchError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.Writer.Trans (runWriterT)
import Data.Either (Either(..))
import Data.List.Lazy (replicateM)
import Data.Maybe (Maybe(..))
import Data.Profunctor.Strong ((&&&))
import Data.Tuple (fst, uncurry)
import Effect.Aff (Error, message)
import Effect.Aff.Class (class MonadAff)
import Pretty (prettyP)
import File (class LoadFile, File(..), FileCxt, Folder(..), loadFile, (</>))
import Lattice (botOf, (≽))
import Module (prepConfig, prepConfigNoDoc)
import Primitive.Defs (primitives)
import Test.Benchmark.Util (BenchRow, benchmark, divRow, logTimeWhen)
import Test.Util (checkEq, test)
import Test.Util.Debug (timing)
import Util (type (×), throw, (×))
import Val (Val, Env)

-- benchmarks parameterised on number of iterations
type BenchSuite m = Int × Boolean -> Array (String × m BenchRow)

type TestSpec =
   { file :: String
   , fwd_expect :: String
   }

type TestBwdSpec =
   { file :: String
   , bwd_expect :: Selector Env
   , δv :: Selector Val
   , fwd_expect :: String
   }

type TestBwdIntermediateSpec =
   { spec :: Options
   , δv :: Selector Val
   , δ_in :: Bind (Selector Val)
   , intermediate_expect :: Selector Env
   , file :: String
   }

type TestLinkedOutputsSpec =
   { spec :: Options
   , δ_out :: Selector Val
   , out_expect :: Selector Val
   , file :: String
   }

type TestLinkedInputsSpec =
   { spec :: Options
   , δ_in :: Bind (Selector Val)
   , in_expect :: Selector Env
   , file :: String
   }

type SuiteFactory r m = MonadError Error m => MonadReader FileCxt m => LoadFile m => Array { file :: String | r } -> BenchSuite m

suite :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array TestSpec -> BenchSuite m
suite specs (n × is_bench) = specs <#> (_.file &&& asTest)
   where
   asTest :: TestSpec -> m BenchRow
   asTest { file, fwd_expect } = do
      test (File file) primitives { δv: identity >>> (_ × Persistent), fwd_expect, bwd_expect: Nothing } (n × is_bench)

bwdSuite :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array TestBwdSpec -> BenchSuite m
bwdSuite specs (n × is_bench) = specs <#> ((_.file >>> File >>> (folder </> _) >>> show) &&& asTest)
   where
   folder = Folder "slicing"

   asTest :: TestBwdSpec -> m BenchRow
   asTest { file, bwd_expect, δv, fwd_expect } = do
      test (folder </> File file) primitives { δv, fwd_expect, bwd_expect: Just bwd_expect } (n × is_bench)

intermediateTest :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Int -> TestBwdIntermediateSpec -> m BenchRow
intermediateTest n s = do
   withDoc <- half prepConfig identity true
   without <- half prepConfigNoDoc (_ <> "°") false
   pure (withDoc <> without)
   where
   half prep decorate check = do
      fluidSrc <- loadFile s.spec.fluidSrcPaths (File s.file)
      _ × row <- runWriterT (replicateM n (iter prep decorate check fluidSrc))
      pure (row `divRow` n)

   iter prep decorate check fluidSrc = do
      fig <- benchmark (decorate "Eval") \_ -> loadFigWith prep s.spec fluidSrc
      res <- benchmark (decorate "Demands") \_ -> pure (selectionResult (selectOutput s.δv fig))
      when check do
         let actual = getPersistent <$> res.ι
         -- force the demanded intermediates
         void (pure (prettyP actual))
         let expected = sel𝔹 s.intermediate_expect res.ι
         unless (actual ≽ expected) $
            throw ("intermediate_expect mismatch (" <> s.file <> "):\nactual\n" <> prettyP actual <> "\nexpected\n" <> prettyP expected)
      void $ benchmark (decorate "Suffices") \_ -> pure (selectionResult (uncurry selectInput s.δ_in fig))

linkedOutputsTest :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestLinkedOutputsSpec -> m Fig
linkedOutputsTest { spec, δ_out, out_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- loadFig spec fluidSrc <#> selectOutput δ_out
   v <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).v
   checkEq "selected" "expected" (selStates <$> (isInert <$> v) <*> (isPersistent <$> v) <*> (isTransient <$> v)) (fst $ out_expect (botOf <$> v))
   pure fig

linkedOutputsSuite :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array TestLinkedOutputsSpec -> Array (String × m Unit)
linkedOutputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedOutputsTest >>> void))

linkedInputsTest :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => TestLinkedInputsSpec -> m Fig
linkedInputsTest { spec, δ_in, in_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- loadFig spec fluidSrc <#> uncurry selectInput δ_in
   γ <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).γ
   checkEq "selected" "expected" (selStates <$> (isInert <$> γ) <*> (isPersistent <$> γ) <*> (isTransient <$> γ)) (fst $ in_expect (botOf <$> γ))
   pure fig

linkedInputsSuite :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array TestLinkedInputsSpec -> Array (String × m Unit)
linkedInputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedInputsTest >>> void))

type IllFormedSpec =
   { file :: String
   , expected_error :: String
   }

illFormedSuite :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Array IllFormedSpec -> Array (String × m Unit)
illFormedSuite specs = specs <#> (_.file &&& asTest)
   where
   folder = Folder "ill_formed"

   asTest :: IllFormedSpec -> m Unit
   asTest { file, expected_error } = do
      fluidSrc <- loadFile [ Folder "fluid", Folder "test/fluid" ] (folder </> File file)
      result <- catchError (prepConfig primitives fluidSrc *> pure (Left unit)) (pure <<< Right)
      case result of
         Right err ->
            when (message err /= expected_error)
               $ throw
               $ "Expected error: " <> expected_error <> "; got: " <> message err
         Left _ -> throw $ "Expected ill-formed: " <> file
