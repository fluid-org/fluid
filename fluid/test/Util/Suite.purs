module Test.Util.Suite where

import Prelude

import App.Fig (figure, selectInput, selectIntermediate, selectOutput, selectionResult)
import App.Fig.Build (figGraph)
import App.Fig.Graph (decodeFigGraph, encodeFigGraph)
import App.Util (SelState(..), SelStates, SelectionType(..), Selector, isInert, isPersistent, isTransient, pairSel, projSel, selStates, selector, 𝕊)
import App.Util.Selector (ObjArg, SelSetter, objArg, select, sel𝔹, valOf)
import App.View.Util (Fig, Options)
import Bind (Bind)
import Control.Monad.Error.Class (catchError)
import Data.Argonaut.Core (stringify)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as A
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Profunctor.Strong ((&&&))
import Data.Tuple (uncurry)
import Effect.Aff (message)
import Eval (evalProgram)
import File (File(..), Folder(..), loadFile, (</>))
import Lattice (class BoundedJoinSemilattice, 𝔹, bot)
import Module (prepConfig, throwParseFailure)
import Test.Benchmark.Util (BenchRow, logRow, logTimeWhen)
import Test.Util (DepSpec, TestSuite, checkEq, checkSelection, depName, fluidSrcPaths, test, testDep)
import Test.Util.Debug (timing)
import Util (type (×), orThrow, throw, (!), (×))
import Util.Map (get)
import Val (class MonadProgram, Val, EnvWithDocs)
import Web.Event.Event (EventType(..))

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

type TestIntermediatesSpec =
   { spec :: Options
   , δ_out :: ObjArg -> Selector Val
   , intermediate :: Int -- index in evaluation order among documented intermediates
   , transient :: SelSetter Val Val -- position in intermediate
   , in_expect :: Selector EnvWithDocs
   , out_expect :: ObjArg -> Selector Val
   , file :: String
   }

type SuiteFactory r m = MonadProgram m => Array { file :: String | r } -> BenchSuite m

suite :: forall m. MonadProgram m => Array TestSpec -> BenchSuite m
suite specs (n × is_bench) = specs <#> (_.file &&& asTest)
   where
   asTest :: TestSpec -> m BenchRow
   asTest { file, fwd_expect } = do
      test (File file) fwd_expect (n × is_bench)

depSuite :: forall m. MonadProgram m => Array DepSpec -> TestSuite m
depSuite specs = specs >>= \{ file, queries } -> queries <#> \query ->
   depName file query ×
      (testDep (File file) query >>= \row -> when timing.benchmark (logRow (depName file query) row))

selected :: SelStates 𝕊 -> SelStates 𝔹
selected s = selStates (isInert s) (isPersistent s) (isTransient s)

-- Build a figure from the figure graph after a round trip through JSON
loadFig :: forall m. MonadProgram m => Options -> String -> m Fig
loadFig spec fluidSrc =
   figGraph spec fluidSrc >>= (encodeFigGraph >=> (stringify >>> jsonParser) >=> decodeFigGraph) >>> orThrow
      <#> figure

linkedOutputsTest :: forall m. MonadProgram m => TestLinkedOutputsSpec -> m Fig
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

linkedOutputsSuite :: forall m. MonadProgram m => Array TestLinkedOutputsSpec -> Array (String × m Unit)
linkedOutputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedOutputsTest >>> void))

linkedInputsTest :: forall m. MonadProgram m => TestLinkedInputsSpec -> m Fig
linkedInputsTest { spec, δ_in, in_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- logTimeWhen timing.loadFig (file <> " loadFig") (\_ -> loadFig spec fluidSrc) <#> uncurry selectInput (valOf <$> δ_in)
   ρ <- logTimeWhen timing.selectionResult file \_ ->
      pure (selectionResult fig).ρ
   checkSelection in_expect (selected <$> ρ)
   pure fig

linkedInputsSuite :: forall m. MonadProgram m => Array TestLinkedInputsSpec -> Array (String × m Unit)
linkedInputsSuite testSpecs = testSpecs <#> (_.file &&& (linkedInputsTest >>> void))

-- Move transient selection to persistent selection; expectations check persistent selection only
asPersistent :: forall a. BoundedJoinSemilattice a => Eq a => SelStates a -> SelStates 𝔹
asPersistent s = pairSel ((_ /= bot) <$> projSel Transient s) (Reactive false)

-- Select output, then make transient selection on intermediate displayed by output selection
intermediatesTest :: forall m. MonadProgram m => TestIntermediatesSpec -> m Unit
intermediatesTest { spec, δ_out, intermediate, transient, in_expect, out_expect, file } = do
   fluidSrc <- loadFile spec.fluidSrcPaths (File file)
   fig <- loadFig spec fluidSrc <#> selectOutput (valOf (δ_out objArg))
   let
      p = A.fromFoldable (Map.keys fig.inertι) ! intermediate
      { ρ, v, ι } = selectionResult $
         selectIntermediate p (valOf (transient (selector (EventType "mouseenter")))) (fig { ι = (selectionResult fig).ι })
   checkSelection in_expect (asPersistent <$> ρ)
   checkSelection (valOf (out_expect objArg)) (asPersistent <$> v)
   checkSelection (valOf (transient select)) (asPersistent <$> get p ι)

intermediatesSuite :: forall m. MonadProgram m => Array TestIntermediatesSpec -> Array (String × m Unit)
intermediatesSuite testSpecs = testSpecs <#>
   ((\{ file, intermediate } -> file <> ", transient selection on intermediate " <> show intermediate) &&& intermediatesTest)

type IllFormedSpec =
   { file :: String
   , expected_error :: String
   }

illFormedSuite :: forall m. MonadProgram m => Array IllFormedSpec -> Array (String × m Unit)
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
