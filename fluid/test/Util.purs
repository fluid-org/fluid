module Test.Util where

import Prelude hiding (absurd, compare)

import App.Util (SelStates, SelectionType(..), Selector, SetSel, getPersistent, unselected)
import App.Util.Selector (ConstrArg, constrArg, none, sel𝔹)
import DataType (class HasClasses, fieldIndex)
import Data.Array (null) as Array
import Data.Array as A
import Data.Foldable (and, any, for_, minimum)
import Data.List (List)
import Data.List as L
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Control.Monad.Writer.Class (class MonadWriter)
import Control.Monad.Writer.Trans (runWriterT)
import Data.List.Lazy (replicateM)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith, trim)
import Data.String (Pattern(..), codePointFromChar, drop, length, null, split) as S
import Data.String.CodePoints (takeWhile) as S
import Data.Tuple (fst)
import Effect.Exception (Error)
import Eval (GraphConfig, graphEval, depsOf)
import Eval.Dep (DepEval, depEval, visible)
import Graph.Dep (DepGraph, Deriv, Labelling, Pos, bwd, fwd, materialise, positions, selected, valAt)
import File (class LoadFile, File, FileCxt, Folder(..), loadFile)
import Lattice (class BotOf, class MeetSemilattice, class Neg, DepKind(..), botOf, erase, 𝔹, (≽))
import Module (prepConfig)
import Parse (parseProgram)
import Pretty (class Pretty, compare, prettyP)
import Expr (Stmt) as Expr
import SExpr (Stmt) as SE
import Test.Benchmark.Util (BenchRow, benchmark, divRow, recordDepGraphSize, recordGraphSize)
import Test.Util.Debug (tracing)
import Util (type (×), AffError, EffectError, Thunk, assertWith, check, error, log', spyWhen, throw, throwLeft, withMsg, (!), (×))
import Util.Map (get, keys, maplet, restrict, toUnfoldable, values)
import Literal (Literal(..))
import Val (class HasModuleStore, BaseVal(..), Env, Val(..), moduleStore, stripDocs)

type TestSuite m = Array (String × m Unit)

data SelectionSpec
   = Evaluation String -- printed output
   | Selection
        { δv :: ConstrArg -> Selector Val
        , bwd_expect :: ConstrArg -> Selector Env
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
testProperties _ s' gconfig spec = do

   graphed@{ g, outα } <- graphBenchmark benchNames.eval \_ ->
      graphEval gconfig s'
   eval <- graphBenchmark benchNames.dep \_ ->
      depEval gconfig s'
   let out_dep = valAt eval.g eval.root
   unless (out_dep == stripDocs (erase outα)) $
      throw ("depEval mismatch:\nactual\n" <> prettyP out_dep <> "\nexpected\n" <> prettyP (erase outα))
   let bwdα = fst <<< (depsOf graphed).bwd
   let fwdα = fst <<< (depsOf graphed).fwd
   let
      δv × inputs = case spec of
         Evaluation _ -> (\_ -> none) × []
         Selection sel -> sel.δv × sel.inputs
      inputs' = if Array.null inputs then keys (erase graphed.inα) else Set.fromFoldable inputs
      arg = constrArg (fieldIndex gconfig.classes)
      out0 = selectOn δv arg outα

   in_ρ <- do
      let report = spyWhen tracing.bwdSelection "Selection for bwd" prettyP
      graphBenchmark benchNames.bwd \_ -> pure (bwdα (report out0))

   -- Dependence of the output selection includes the α-graph's backward slice, input by input.
   visibleGraph <- graphBenchmark benchNames.materialise \_ ->
      pure (materialise eval.g (visible eval `Set.union` Set.fromFoldable (values eval.inputs)))
   let deps = bwd visibleGraph (maplet eval.root (selected (stripDocs out0)))
   for_ (toUnfoldable eval.inputs :: List (String × Deriv)) \(x × q) ->
      includes ("dependence on " <> x) (get q deps) (stripDocs (get x in_ρ))

   out1 <- graphBenchmark benchNames.fwd \_ -> pure (fwdα (restrict inputs' in_ρ))
   -- Likewise the forward slice from the inputs, at the output.
   let from = Set.fromFoldable (values (restrict inputs' eval.inputs))
   let deps' = fwd visibleGraph (nonZero <$> Map.filterKeys (_ `Set.member` from) deps)
   includes "dependence of output" (get eval.root deps') (stripDocs out1)

   case spec of
      Evaluation expect -> withMsg "fwd_expect" $ checkPretty expect (prettyP out1)
      Selection { bwd_expect } -> do
         let expected = sel𝔹 (bwd_expect arg) in_ρ
         unless (in_ρ ≽ expected) $
            throw ("bwd_expect mismatch:\nactual in_ρ\n" <> prettyP in_ρ <> "\nexpected (sel𝔹)\n" <> prettyP expected)

   recordGraphSize g
   recordDepGraphSize eval.g

-- Visible vertex carrying the selection.
data VertexSpec
   = Output
   | Input String -- vertex documented with the name
   | Intermediate Int -- index among documented vertices of the program, in evaluation order
   | Doc VertexSpec

-- Selection and expected dependence, as given by showDeps: data ⸨ ⸩, control ⟪ ⟫.
data Query
   = Bwd VertexSpec (ConstrArg -> Selector Val) String
   | Fwd VertexSpec (ConstrArg -> Selector Val) String

type DepSpec = { file :: String, queries :: Array Query }

nonZero :: Val DepKind -> Set Pos
nonZero = map (_ /= Zero) >>> selected

-- Dependence is non-zero wherever the α-graph slice is selected.
includes :: forall m. String -> Val DepKind -> Val 𝔹 -> EffectError m Unit
includes msg dep_ slice =
   unless (and (L.zipWith (\b w -> not b || w /= Zero) (positions slice) (positions dep_))) $
      throw (msg <> " misses α-graph slice:\ndependence\n" <> prettyP dep_ <> "\nα-graph\n" <> prettyP slice)

depName :: String -> Query -> String
depName file = case _ of
   Bwd vertex _ _ -> file <> ", bwd from " <> name vertex
   Fwd vertex _ _ -> file <> ", fwd from " <> name vertex
   where
   name = case _ of
      Output -> "output"
      Input x -> x
      Intermediate n -> "intermediate " <> show n
      Doc vertex -> "doc of " <> name vertex

-- depGraph holds the vertices created by loading the modules, before the program ran.
deriv :: forall s. DepGraph Val s -> DepEval -> VertexSpec -> Deriv
deriv depGraph eval@{ g: g@{ docs }, root } = case _ of
   Output -> root
   Input x -> case A.filter (\(_ × d) -> valAt g d == Val unit Nothing (Lit (Str x))) (Map.toUnfoldable docs) of
      [ p × _ ] -> p
      _ -> error ("no vertex documented " <> show x)
   Intermediate n -> intermediates ! n
   Doc vertex -> get (deriv depGraph eval vertex) docs
   where
   intermediates = A.filter (not <<< (_ `Map.member` depGraph.vals)) (A.fromFoldable (Map.keys docs))

-- Documented vertices in evaluation order, each with its doc if the doc has dependence, then the output.
showDeps :: DepEval -> Labelling (Val DepKind) -> String
showDeps { g: { docs }, root } deps = joinWith "\n" (documented <> output)
   where
   dep p = get p deps
   documented = Map.toUnfoldable docs <#> \(p × d) ->
      let Val w _ u = dep p in prettyP (Val w (if any (_ /= Zero) (dep d) then Just (dep d) else Nothing) u)
   output = if Map.member root docs then [] else [ prettyP (dep root) ]

selection
   :: forall s
    . GraphConfig
   -> DepGraph Val s
   -> DepEval
   -> VertexSpec
   -> (ConstrArg -> Selector Val)
   -> Labelling (Set Pos)
selection { classes } depGraph eval vertex δv =
   maplet p (selected (selectOn δv (constrArg (fieldIndex classes)) (valAt eval.g p)))
   where
   p = deriv depGraph eval vertex

testDep :: forall m. HasClasses m => HasModuleStore m => MonadReader FileCxt m => LoadFile m => File -> Query -> AffError m Unit
testDep file query = do
   fluidSrc <- loadFile fluidSrcPaths file
   { e, gconfig } <- prepConfig fluidSrc
   { depGraph } <- moduleStore
   eval <- depEval gconfig e
   let
      visibleGraph = materialise eval.g (visible eval)
      deps × expect = case query of
         Bwd vertex δv expect' -> bwd visibleGraph (selection gconfig depGraph eval vertex δv) × expect'
         Fwd vertex δv expect' -> fwd visibleGraph (selection gconfig depGraph eval vertex δv) × expect'
   withMsg "expect" $ checkPretty expect (showDeps eval deps)

-- Persistent selection made by δv on the output.
selectOn :: forall a. (ConstrArg -> Selector Val) -> ConstrArg -> Val a -> Val 𝔹
selectOn δv arg v = fst (δv arg (const unselected <$> (map (const top) v :: Val 𝔹))) <#> getPersistent

-- Result at this position, printed with its persistent selections, must match; leave it unselected.
at :: forall f. Functor f => Pretty (f 𝔹) => String -> SetSel (f (SelStates 𝔹))
at expected v =
   assertWith ("at:\nExpected\n" <> expected <> "\nReceived\n" <> actual) (dedent expected == actual) (botOf <$> v) × Persistent
   where
   actual = prettyP (getPersistent <$> v)

-- Expectation applied to the selection must cancel it.
checkSelection :: forall m f. MonadError Error m => Functor f => Eq (f (SelStates 𝔹)) => Pretty (f (SelStates 𝔹)) => Selector f -> f (SelStates 𝔹) -> m Unit
checkSelection expect v =
   check (residual == (botOf <$> v)) ("selection differs from expectation at:\n" <> prettyP residual)
   where
   residual = fst (expect v)

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

-- Drop surrounding blank lines and common indentation, so that an expectation can be indented with the code.
dedent :: String -> String
dedent s = joinWith "\n" (S.drop indent <$> lines)
   where
   lines = A.dropWhile blank (A.reverse (A.dropWhile blank (A.reverse (S.split (S.Pattern "\n") s))))
   blank = trim >>> S.null
   indent = fromMaybe 0 (minimum (S.length <<< S.takeWhile (_ == S.codePointFromChar ' ') <$> A.filter (not <<< blank) lines))

checkPretty :: forall m. String -> String -> EffectError m Unit
checkPretty expect actual = do
   unless (dedent expect `eq` actual) $
      throw ("checkPretty:\nExpected\n" <> expect <> "\nReceived\n" <> actual)
