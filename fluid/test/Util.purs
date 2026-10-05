module Test.Util where

import Prelude hiding (absurd, compare)

import App.Util (Selector, getPersistent, unselected)
import App.Util.Selector (ConstrArg, constrArg, sel𝔹)
import DataType (class HasClasses, fieldIndex)
import Data.Array (null) as Array
import Data.Array as A
import Data.Foldable (and, any, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List)
import Data.List as L
import Data.Map as Map
import Data.Set (Set)
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
import Eval.Dep (depEval, visible)
import Graph.Dep (Deriv, Pos, bwd, fwd, materialise, positions, valAt)
import File (class LoadFile, File, FileCxt, Folder(..), loadFile)
import Lattice (class BotOf, class MeetSemilattice, class Neg, DepKind(..), erase, 𝔹, (≽))
import Module (prepConfig)
import Parse (parseProgram)
import Pretty (class Pretty, compare, prettyP)
import Expr (Stmt) as Expr
import SExpr (Stmt) as SE
import Test.Benchmark.Util (BenchRow, benchmark, divRow, recordDepGraphSize, recordGraphSize)
import Test.Util.Debug (tracing)
import Util (type (×), AffError, EffectError, Endo, Thunk, check, definitely, error, log', spyWhen, throw, throwLeft, withMsg, (×))
import Util.Map (get, keys, restrict, toUnfoldable, values)
import Val (class HasModuleStore, Env, Val(..), moduleStore, stripDocs)

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
   eval <- graphBenchmark benchNames.dep \_ ->
      depEval gconfig s'
   let out_dep = valAt eval.g eval.root
   unless (out_dep == stripDocs (erase outα)) $
      throw ("depEval mismatch:\nactual\n" <> prettyP out_dep <> "\nexpected\n" <> prettyP (erase outα))
   let evalG_bwd = fst <<< (depsOf graphed).bwd
   let evalG_op_bwd = fst <<< (depsOf graphed).fwd
   let inputs' = if Array.null inputs then keys (erase graphed.inα) else Set.fromFoldable inputs

   let arg = constrArg (fieldIndex gconfig.classes)
   let out0 = selectOn δv arg outα

   in_ρ <- do
      let report = spyWhen tracing.bwdSelection "Selection for bwd" prettyP
      graphBenchmark benchNames.bwd \_ -> pure (evalG_bwd (report out0))

   -- Dependence of the output selection includes the α-graph's backward slice, input by input.
   visibleGraph <- graphBenchmark benchNames.materialise \_ ->
      pure (materialise eval.g (visible eval `Set.union` Set.fromFoldable (values eval.inputs)))
   let deps = bwd visibleGraph (Map.singleton eval.root (selected (stripDocs out0)))
   for_ (toUnfoldable eval.inputs :: List (String × Deriv)) \(x × q) ->
      includes ("dependence on " <> x) (definitely "visible" (Map.lookup q deps)) (stripDocs (get x in_ρ))

   out1 <- graphBenchmark benchNames.fwd \_ -> pure (evalG_op_bwd (restrict inputs' in_ρ))
   -- Likewise the forward slice from the inputs, at the output.
   let from = Set.fromFoldable (values (restrict inputs' eval.inputs))
   let deps' = fwd visibleGraph (nonZero <$> Map.filterKeys (_ `Set.member` from) deps)
   includes "dependence of output" (definitely "visible" (Map.lookup eval.root deps')) (stripDocs out1)

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
   recordDepGraphSize eval.g

-- Visible vertex carrying the selection.
data Visible
   = Output
   | Input String -- variable defined as a documented value; by convention the doc is the variable's name
   | Intermediate Int -- index among documented vertices of the program, in evaluation order
   | Doc Visible

-- Selection and expected documented vertices, then output, with dependence: data ⸨ ⸩, control ⟪ ⟫. A doc is
-- shown only if it has dependence.
data Query
   = Bwd Visible (ConstrArg -> Selector Val) String
   | Fwd Visible (ConstrArg -> Selector Val) String

type DepSpec = { file :: String, queries :: Array Query }

selected :: Val 𝔹 -> Set Pos
selected v = Set.fromFoldable (mapWithIndex (\j b -> j × b) (positions v) # L.filter snd <#> fst)

nonZero :: Val DepKind -> Set Pos
nonZero = map (_ /= Zero) >>> selected

-- Dependence is non-zero wherever the α-graph slice is selected.
includes :: forall m. String -> Val DepKind -> Val 𝔹 -> EffectError m Unit
includes msg dep_ slice =
   unless (and (L.zipWith (\b w -> not b || w /= Zero) (positions slice) (positions dep_))) $
      throw (msg <> " misses α-graph slice:\ndependence\n" <> prettyP dep_ <> "\nα-graph\n" <> prettyP slice)

depName :: String -> Query -> String
depName file = case _ of
   Bwd on _ _ -> file <> ", bwd from " <> name on
   Fwd on _ _ -> file <> ", fwd from " <> name on
   where
   name = case _ of
      Output -> "output"
      Input x -> x
      Intermediate n -> "intermediate " <> show n
      Doc on -> "doc of " <> name on

testDep :: forall m. HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => File -> Query -> AffError m Unit
testDep file query = do
   fluidSrc <- loadFile fluidSrcPaths file
   { e, gconfig } <- prepConfig fluidSrc
   { depGraph } <- moduleStore
   eval <- depEval gconfig e
   let
      docs = eval.g.docs
      input x = case A.fromFoldable <<< Map.keys <$> Map.lookup (get x eval.inputs) eval.g.edges of
         Just [ p ] | Map.member p docs -> p
         _ -> error ("input " <> x <> " not bound to documented value")
      intermediates = A.filter (not <<< (_ `Map.member` depGraph.vals)) (A.fromFoldable (Map.keys docs))
      vertex = case _ of
         Output -> eval.root
         Input x -> input x
         Intermediate n -> definitely "intermediate" (A.index intermediates n)
         Doc on -> definitely "documented" (Map.lookup (vertex on) docs)
      arg = constrArg (fieldIndex gconfig.classes)
      selection on δv = let p = vertex on in Map.singleton p (selected (selectOn δv arg (valAt eval.g p)))
      visibleGraph = materialise eval.g (visible eval)
      deps × expect = case query of
         Bwd on δv expect' -> bwd visibleGraph (selection on δv) × expect'
         Fwd on δv expect' -> fwd visibleGraph (selection on δv) × expect'
      at q = definitely "visible" (Map.lookup q deps)
      documented = Map.toUnfoldable docs <#> \(q × d) ->
         let Val w _ u = at q in prettyP (Val w (if any (_ /= Zero) (at d) then Just (at d) else Nothing) u)
      output = if Map.member eval.root docs then [] else [ prettyP (at eval.root) ]
   withMsg "expect" $ checkPretty expect $ joinWith "\n" (documented <> output)

-- Persistent selection made by δv on the output.
selectOn :: forall a. (ConstrArg -> Selector Val) -> ConstrArg -> Val a -> Val 𝔹
selectOn δv arg v = fst (δv arg (const unselected <$> (map (const top) v :: Val 𝔹))) <#> getPersistent

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

