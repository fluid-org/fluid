module App.Fig where

import Prelude hiding (absurd, compare)

import App.CodeMirror (EditorView, addEditorView, dispatch, getContentsLength, update)
import App.Util (SelState, SelStates, Selection, SelectionType(..), Selector, 𝕊, pairSel, primary, primaryOrSecondary, selState, selStates, projSel, to𝔹, to𝕊)
import App.Util.Selector (constrArg, envVal, sel𝔹, ViewSetter)
import App.View (view')
import App.View.Util (Direction(..), Fig, Options, HTMLId, View, drawView)
import App.View.Util.D3 (remove, rootSelect)
import Bind (Var)
import DataType (class HasClasses, fieldIndex)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array as A
import Data.Foldable (elem, or)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_, sequence_)
import Data.Tuple (Tuple(..), fst)
import Dict (Dict)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval.Dep (depEval, visible)
import File (class LoadFile, File(..), FileCxt)
import Graph.Dep (ConjugatePair, DepGraph, Deriv, Labelling, Pos, dimap, mask, materialise, queries, selected)
import Lattice (DepKind(..), 𝔹, botOf, erase)
import Module (prepConfig)
import Pretty (prettyP)
import Test.Util.Debug (tracing)
import Util (type (×), Endo, spyWhen, (×))
import Util.Map (get, insert, intersectionWith, lookup, mapWithKey, restrict, values)
import Util.Set ((\\), (∈), (∪))
import Val (class HasModuleStore, Env(..), Val(..), dataPositions)

str
   :: { output :: String -- pseudo-variable to use as name of output view
      , input :: String -- prefix for input views
      , intermediate :: String
      }
str =
   { output: "output"
   , input: "input"
   , intermediate: "intermediate"
   }

selectOutput :: Selector Val -> Endo Fig
selectOutput δv fig@{ v, dir, ρ } = fig { v = v', ρ = ρ', dir = dir' }
   where
   v' × selType = δv v
   ρ' × dir' = case selType of
      Persistent | dir.persistent /= LinkedOutputs -> botOf ρ × dir { persistent = LinkedOutputs }
      Transient | dir.transient /= LinkedOutputs -> ρ × dir { transient = LinkedOutputs }
      _ -> ρ × dir

setOutputView :: ViewSetter Fig View
setOutputView δvw fig = fig
   { out_view = fig.out_view <#> δvw }

selectInput :: Var -> Selector Val -> Endo Fig
selectInput x δv fig@{ v, dir, ρ } = fig { v = v', ρ = ρ', dir = dir' }
   where
   ρ' × selType = envVal x δv ρ
   v' × dir' = case selType of
      Persistent | dir.persistent /= LinkedInputs -> botOf v × dir { persistent = LinkedInputs }
      Transient | dir.transient /= LinkedInputs -> v × dir { transient = LinkedInputs }
      _ -> v × dir

setInputView :: Var -> ViewSetter Fig View
setInputView x δvw fig = fig
   { in_views = insert x (lookup x fig.in_views # join <#> δvw) fig.in_views
   }

selectIntermediate :: Deriv -> Selector Val -> Endo Fig
selectIntermediate p δv fig@{ ι, dir, ρ, v } = fig { ι = ι_final, ρ = ρ', v = v', dir = dir' }
   where
   ι' × selType = first (\u -> Map.insert p u ι) (δv (get p ι))
   ρ' × v' × dir' × ι_final = case selType of
      Transient | dir.transient /= Intermediates -> ρ × v × dir { transient = Intermediates } × ι'
      Transient -> ρ × v × dir × ι'
      _ -> ρ × v × dir × ι

setIntermediateView :: Deriv -> ViewSetter Fig View
setIntermediateView p δvw fig =
   fig { intermediate_views = Map.insert p (Map.lookup p fig.intermediate_views # join <#> δvw) fig.intermediate_views }

type SelectionResult =
   { v :: Val (SelStates 𝕊)
   , ρ :: Env (SelStates 𝕊)
   , ι :: Labelling (Val (SelStates 𝔹))
   }

-- Query in the given direction, with the selection primary and what it reaches secondary.
queryResult :: Fig -> SelectionType -> Direction -> Env (SelState 𝕊) × Val (SelState 𝕊) × Labelling (Val 𝔹)
queryResult fig@{ v, ρ, ι } selType = case _ of
   LinkedOutputs -> fig.linkedOutputs selType v # first primary >>> (second <<< first) (primaryOrSecondary selType v)
   LinkedInputs -> fig.linkedInputs selType ρ # first (primaryOrSecondary selType ρ) >>> second (first primary)
   Intermediates -> fig.linkIntermediates ι # first primary >>> second (first primary)

selectionResult :: Fig -> SelectionResult
selectionResult fig@{ dir } =
   { v: reportOut (pairSel <$> v1 <*> v2)
   , ρ: reportIn (pairSel <$> ρ1 <*> ρ2)
   , ι: intermediates fig { persistent: ιs, transient: ιs' }
   }
   where
   ρ1 × v1 × ιs = queryResult fig Persistent dir.persistent
   ρ2 × v2 × ιs' = queryResult fig Transient dir.transient
   reportIn = spyWhen tracing.mediatingData ("Mediating inputs") (prettyP <<< erase)
   reportOut = spyWhen tracing.mediatingData ("Mediating outputs") (prettyP <<< erase)

-- Intermediates reachable from either selection.
intermediates :: Fig -> Selection (Labelling (Val 𝔹)) -> Labelling (Val (SelStates 𝔹))
intermediates { inertι } ιs =
   Map.filterKeys (_ ∈ (Map.keys ιs.persistent ∪ Map.keys ιs.transient)) inertι # mapWithIndex \p inert ->
      selStates <$> inert <*> sel ιs.persistent p inert <*> sel ιs.transient p inert
   where
   sel ι p inert = fromMaybe (false <$ inert) (Map.lookup p ι)

drawFig :: HTMLId -> Fig -> Effect Unit
drawFig divId fig = do
   drawView arg { divId, suffix: str.output, view: view' options str.output v } (selectOutput >>> redraw)
   sequence_ $ unwrap ρ # mapWithKey \x u ->
      drawView arg { divId: divId <> "-" <> str.input, suffix: x, view: view' options x u } (selectInput x >>> redraw)
   for_ (Map.keys fig.ι \\ Map.keys ι) \p -> rootSelect ("#" <> prefix <> "-" <> show p) >>= remove
   sequence_ $ ι # mapWithIndex \p u ->
      drawView arg { divId: prefix, suffix: show p, view: view' options str.intermediate (map to𝕊 <$> u) }
         (selectIntermediate p >>> redraw)
   where
   { v, ρ, ι } = selectionResult fig
   arg = constrArg fig.fieldIndex
   options = { fieldIndex: fig.fieldIndex, rowFilter: fig.spec.rowFilter }
   redraw = (_ $ fig { ι = ι }) >>> drawFig divId
   prefix = divId <> "-" <> str.intermediate

drawFile :: File × String -> Effect Unit
drawFile (File fileName × src) =
   addEditorView (codeMirrorDiv fileName) >>= loadCode src

-- Vertex shown as one value with the vertex of its doc, if any.
type WithDoc = Deriv × Maybe Deriv

val :: forall a. Labelling (Val a) -> WithDoc -> Val a
val m (p × d) = let Val α _ u = get p m in Val α (flip get m <$> d) u

unval :: forall a. WithDoc -> Val a -> Labelling (Val a)
unval (p × d) (Val α doc u) = Map.fromFoldable (A.cons (p × Val α Nothing u) (A.fromFoldable (Tuple <$> d <*> doc)))

unvals :: forall a. Dict WithDoc -> Dict (Val a) -> Labelling (Val a)
unvals ps vs = Map.unions (values (intersectionWith unval ps vs))

-- Documented vertex defining an environment entry.
definition :: forall s. DepGraph Val s -> Deriv -> Maybe Deriv
definition g q = case A.fromFoldable <<< Map.keys <$> Map.lookup q g.edges of
   Just [ p ] | Map.member p g.docs -> Just p
   _ -> Nothing

-- Queries over Boolean selections.
boolean
   :: ConjugatePair (Labelling (Set Pos)) (Labelling (Val DepKind))
   -> ConjugatePair (Labelling (Val 𝔹)) (Labelling (Val 𝔹))
boolean = dimap (map selected) (map (map (_ /= Zero)))

loadFig :: forall m. HasClasses m => HasModuleStore m => MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Options -> String -> m Fig
loadFig options@{ inputs, linking, query, ignoreInputs } fluidSrc = do
   { s, e, gconfig } <- prepConfig fluidSrc
   eval@{ g: g@{ docs }, root } <- depEval gconfig e
   let
      out = root × Map.lookup root docs
      ins = restrict (Set.fromFoldable inputs) eval.inputs <#> \q -> q × (definition g q >>= (_ `Map.lookup` docs))
      shown = Set.fromFoldable (A.cons root (A.mapMaybe (definition g) (A.fromFoldable (values (fst <$> ins)))))
      ιs =
         if query then mapWithIndex (\p d -> p × Just d) (Map.filterKeys (not <<< (_ ∈ shown)) docs)
         else Map.empty

      graph = materialise g (visible eval ∪ Set.fromFoldable (values eval.inputs))
      everything = map (const true) <$> graph.vals
      ignored = unvals ins (unwrap (sel𝔹 ignoreInputs (Env (ins <#> val everything))))

      -- Over the graph as it is, and restricted to data positions less the ignored ones.
      unmasked = boolean (queries graph)
      masked = boolean $ queries $ graph # mask \p v ->
         maybe (dataPositions v) (lift2 (\b b' -> b && not b') (dataPositions v)) (Map.lookup p ignored)

      -- Positions which the output does not depend on, and which do not depend on any input.
      inert { fwd, bwd } =
         { bwd: map not <$> bwd (unval out (val everything out))
         , fwd: map not <$> fwd (Map.filterKeys (_ `elem` eval.inputs) everything)
         }
      inertMasked = inert masked
      inertUnmasked = inert unmasked

      toρ :: Labelling (Val 𝔹) -> Env (SelState 𝔹)
      toρ m = Env (ins <#> \p -> selState <$> val inertMasked.bwd p <*> val m p)

      toV :: Labelling (Val 𝔹) -> Val (SelState 𝔹)
      toV m = selState <$> val inertMasked.fwd out <*> val m out

      toι :: Labelling (Val 𝔹) -> Labelling (Val 𝔹)
      toι m = Map.filter or (ιs <#> val m)

      fromρ :: Env (SelState 𝔹) -> Labelling (Val 𝔹)
      fromρ (Env ρ) = unvals ins (map to𝔹 <$> ρ)

      fromV :: Val (SelState 𝔹) -> Labelling (Val 𝔹)
      fromV v = unval out (to𝔹 <$> v)

      linkedInputs :: SelectionType -> Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Labelling (Val 𝔹)
      linkedInputs selType ρ = (if linking then toρ (masked.bwd (fromV v)) else sel) × v × toι deps
         where
         sel = ρ <#> projSel selType
         deps = masked.fwd (fromρ sel)
         v = toV deps

      linkedOutputs :: SelectionType -> Val (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Labelling (Val 𝔹)
      linkedOutputs selType v = ρ × (if linking then toV (masked.fwd (fromρ ρ)) else sel) × toι deps
         where
         sel = v <#> projSel selType
         deps = masked.bwd (fromV sel)
         ρ = toρ deps

      linkIntermediates :: Labelling (Val (SelStates 𝔹)) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Labelling (Val 𝔹)
      linkIntermediates ι = toρ (unmasked.bwd sel) × toV (unmasked.fwd sel) × toι sel
         where
         sel = Map.unions (Map.intersectionWith unval ιs (map (projSel Transient >>> to𝔹) <$> ι))

   pure
      { spec: options
      , s
      , ρ: Env (ins <#> \p -> (\b -> selStates b false false) <$> val inertMasked.bwd p)
      , v: (\b -> selStates b false false) <$> val inertMasked.fwd out
      , ι: Map.empty
      , linkedOutputs
      , linkedInputs
      , linkIntermediates
      , dir: { persistent: LinkedOutputs, transient: LinkedOutputs }
      , in_views: ins $> Nothing
      , out_view: Nothing
      , intermediate_views: Map.empty
      , inertι: ιs <#> \p -> (&&) <$> val inertUnmasked.bwd p <*> val inertUnmasked.fwd p
      , fieldIndex: fieldIndex gconfig.classes
      }

codeMirrorDiv :: Endo String
codeMirrorDiv = ("codemirror-" <> _)

loadCode :: String -> EditorView -> Effect Unit
loadCode s ed =
   dispatch ed =<< update ed.state [ { changes: { from: 0, to: getContentsLength ed, insert: s } } ]
