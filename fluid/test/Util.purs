module Test.Util where

import Prelude hiding (absurd, compare)

import App.Util (Selector, getPersistent, unselected)
import App.Util.Selector (ConstrArg, constrArg, sel𝔹)
import DataType (class HasClasses, fieldIndex)
import Data.Array (null) as Array
import Data.Foldable (and, for_, sum)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List)
import Data.List as L
import Data.Map (Map)
import Data.Map as Map
import Data.Set as Set
import Control.Monad.Error.Class (class MonadError, class MonadThrow)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.Writer.Class (class MonadWriter)
import Control.Monad.Writer.Trans (runWriterT)
import Data.List.Lazy (replicateM)
import Data.Maybe (Maybe(..))
import Data.String (joinWith, null, trim)
import Data.Tuple (fst, snd)
import Effect.Class (class MonadEffect)
import Effect.Class.Console (log)
import Effect.Exception (Error)
import Eval (GraphConfig, graphEval, depsOf)
import Eval.Dep (DepEval, depEval)
import Graph.Dep (Pos, SparseRel, Vertex, lineage, materialise, positions)
import File (class LoadFile, File, FileCxt, Folder(..), loadFile)
import Lattice (class BotOf, class MeetSemilattice, class Neg, Chain(..), Lineage, erase, 𝔹, (≽))
import Module (prepConfig)
import Parse (parseProgram)
import Pretty (class Pretty, compare, prettyP)
import Expr (Stmt) as Expr
import SExpr (Stmt) as SE
import Test.Benchmark.Util (BenchRow, benchmark, divRow, recordDepGraphSize, recordGraphSize)
import Test.Util.Debug (tracing)
import Util (type (×), AffError, EffectError, Endo, Thunk, check, definitely, log', spyWhen, throw, throwLeft, withMsg, (×))
import Util.Map (get, keys, restrict, toUnfoldable, values)
import Val (class HasModuleStore, Env(..), Val, stripDocs)

type TestSuite m = Array (String × m Unit)

type SelectionSpec =
   { δv :: ConstrArg -> Selector Val
   , fwd_expect :: String -- prettyprinted value after bwd then fwd round-trip
   , bwd_expect :: Maybe (ConstrArg -> Selector Env) -- Nothing for tests that don't perturb output
   , inputs :: Array String -- data inputs to slice forward through; [] = all (no restriction)
   }

fluidSrcPaths :: Array Folder
fluidSrcPaths = [ Folder "lib", Folder "test/lib" ]

test ∷ forall m. HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => File -> SelectionSpec -> Int × Boolean -> AffError m BenchRow
test file spec (n × _) = do
   fluidSrc <- loadFile fluidSrcPaths file
   log' ("**** prepConfig")
   { s, e, gconfig } <- prepConfig fluidSrc
   testPretty s
   _ × res <- runWriterT (replicateM n (testProperties s e gconfig spec))
   pure $ res `divRow` n

graphBenchmark :: forall m a. MonadWriter BenchRow m => String -> Thunk (m a) -> EffectError m a
graphBenchmark name = benchmark ("G" <> "-" <> name)

benchNames
   :: { eval :: String
      , dep :: String
      , materialise :: String
      , bwd :: String
      , fwd :: String
      }

benchNames =
   { eval: "Eval"
   , dep: "Dep"
   , materialise: "Materialise"
   , bwd: "Demands"
   , fwd: "DemBy"
   }

testProperties
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadWriter BenchRow m
   => SE.Stmt
   -> Expr.Stmt
   -> GraphConfig
   -> SelectionSpec
   -> AffError m Unit
testProperties _ s' gconfig { δv, bwd_expect, fwd_expect, inputs } = do

   graphed@{ g, outα } <- graphBenchmark benchNames.eval \_ ->
      graphEval gconfig s'
   dep <- graphBenchmark benchNames.dep \_ ->
      depEval gconfig s' :: m (DepEval (Lineage (Vertex × Pos) Chain))
   let out_dep = definitely "root labelled" (Map.lookup dep.root dep.g.vals)
   when tracing.depEval $ log
      ("depEval: " <> show (Map.size dep.g.vals) <> " vertices, " <> show (sum (Map.size <$> Map.values dep.g.edges)) <> " edges")
   unless (out_dep == stripDocs (erase outα)) $
      throw ("depEval mismatch:\nactual\n" <> prettyP out_dep <> "\nexpected\n" <> prettyP (erase outα))
   let evalG_bwd = fst <<< (depsOf graphed).bwd
   let evalG_op_bwd = fst <<< (depsOf graphed).fwd
   let ρ_raw = erase graphed.inα
   let inputs' = if Array.null inputs then keys ρ_raw else Set.fromFoldable inputs

   let arg = constrArg (fieldIndex gconfig.classes)
   let v = map (const top) outα :: Val 𝔹
   let out0 = fst (δv arg (const unselected <$> v)) <#> getPersistent

   in_ρ <- do
      let report = spyWhen tracing.bwdSelection "Selection for bwd" prettyP
      graphBenchmark benchNames.bwd \_ -> pure (evalG_bwd (report out0))

   -- Lineage of the output selection includes the α-graph's backward slice, input by input.
   edges <- graphBenchmark benchNames.materialise \_ -> pure (materialiseEnds dep dep.root)
   let Env ρ_dep = inputLineage dep dep.root edges (stripDocs out0)
   for_ (toUnfoldable ρ_dep :: List (String × Val Chain)) \(x × sel_new) -> do
      let sel_old = stripDocs (get x in_ρ)
      unless (and (L.zipWith (\b w -> not b || w /= Zero) (positions sel_old) (positions sel_new))) $
         throw ("lineage of " <> x <> " misses α-graph slice:\nlineage\n" <> prettyP sel_new <> "\nα-graph\n" <> prettyP sel_old)

   out1 <- graphBenchmark benchNames.fwd \_ -> pure (evalG_op_bwd (restrict inputs' in_ρ))

   case bwd_expect of
      Nothing -> pure unit
      Just sel -> do
         let expected = sel𝔹 (sel arg) in_ρ
         unless (in_ρ ≽ expected) $
            throw ("bwd_expect mismatch:\nactual in_ρ\n" <> prettyP in_ρ <> "\nexpected (sel𝔹)\n" <> prettyP expected)
   unless (null fwd_expect) do
      let report = spyWhen tracing.fwdAfterBwd "fwd ⚬ bwd" prettyP
      withMsg "fwd_expect" $ checkPretty fwd_expect (prettyP (report out1))

   recordGraphSize g
   recordDepGraphSize dep.g

type DepSpec =
   { file :: String
   , doc :: Boolean -- select on the doc of the output
   , δv :: ConstrArg -> Selector Val
   , expect :: String -- input environment with lineage of the selection, data ⸨ ⸩ and control ⟪ ⟫
   }

-- Materialised relations from the inputs to the given vertex, with every other vertex hidden.
materialiseEnds :: DepEval (Lineage (Vertex × Pos) Chain) -> Vertex -> Map (Vertex × Vertex) (SparseRel Chain)
materialiseEnds dep p = materialise dep.g (Set.fromFoldable (values dep.inputs) `Set.union` Set.singleton p)

inputLineage :: DepEval (Lineage (Vertex × Pos) Chain) -> Vertex -> Map (Vertex × Vertex) (SparseRel Chain) -> Val 𝔹 -> Env Chain
inputLineage dep p edges out = Env $ dep.inputs <#> \q ->
   lineage edges p selected q (definitely "input labelled" (Map.lookup q dep.g.vals))
   where
   selected = Set.fromFoldable (mapWithIndex (\j b -> j × b) (positions out) # L.filter snd <#> fst)

testDep :: forall m. HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => File -> DepSpec -> AffError m Unit
testDep file { doc, δv, expect } = do
   fluidSrc <- loadFile fluidSrcPaths file
   { e, gconfig } <- prepConfig fluidSrc
   dep <- depEval gconfig e :: m (DepEval (Lineage (Vertex × Pos) Chain))
   let
      p = if doc then definitely "output documented" (Map.lookup dep.root dep.g.docs) else dep.root
      out = definitely "vertex labelled" (Map.lookup p dep.g.vals)
      arg = constrArg (fieldIndex gconfig.classes)
      out0 = fst (δv arg (const unselected <$> (map (const top) out :: Val 𝔹))) <#> getPersistent
   let Env ρ = inputLineage dep p (materialiseEnds dep p) out0
   withMsg "expect" $ checkPretty expect $ joinWith "\n" $
      (toUnfoldable ρ :: Array (String × Val Chain)) <#> \(x × v) -> x <> ": " <> prettyP v

checkEq
   :: forall m a
    . BotOf a a
   => Neg a
   => MeetSemilattice a
   => Eq a
   => Pretty a
   => MonadError Error m
   => String
   -> String
   -> a
   -> a
   -> m Unit
checkEq op1 op2 x y = do
   let left × right = compare op1 op2 x y
   check (left == "") left
   check (right == "") right

testPretty :: forall m. SE.Stmt -> AffError m Unit
testPretty s = do
   log' ("**** prettyP")
   log' (prettyP s)
   s' × _ <- throwLeft <#> withMsg "testPretty" $ parseProgram (prettyP s)
   unless (s == s') $
      throw ("parse/prettyP round trip:\nOriginal\n" <> prettyP s <> "\nNew\n" <> prettyP s')

checkPretty :: forall m. String -> String -> EffectError m Unit
checkPretty expect actual = do
   unless (trim expect `eq` actual) $
      throw ("checkPretty:\nExpected\n" <> expect <> "\nReceived\n" <> actual)

testOutcome :: Boolean -> Endo String
testOutcome b s = "\x1b[" <> (if b then "32" else "31") <> "m " <> (if b then "✔" else "✖") <> "\x1b[0m " <> s

testCondition :: forall m. MonadThrow Error m => MonadEffect m => String -> Boolean -> String -> m Unit
testCondition testName b msg = do
   log (testOutcome b msg')
   when (not b) $
      throw "Test failed" -- could improve this to accumulate test failures rather than "failing fast"
   where
   msg' = testName <> ": " <> msg

