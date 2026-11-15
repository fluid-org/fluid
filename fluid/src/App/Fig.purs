module App.Fig where

import Prelude hiding (absurd, compare)

import App.Util (SelState, SelStates, Selection, SelectionType(..), Selector, 𝕊, classes, pairSel, primary, primaryOrSecondary, selState, selStates, projSel, to𝔹, to𝕊)
import App.Util.Selector (objArg, envVal, ViewSetter)
import App.View (viewWithDoc)
import App.View.ViewWithDoc (drawView)
import App.View.Util (Direction(..), Fig, Filter, HTMLId, QueryResult, View)
import App.View.Util.D3 (remove, rootSelect, setAttrs, setText)
import Bind (Var)
import Control.Apply (lift2)
import Dict (Dict)
import Data.Either (Either, either)
import Data.Foldable (or)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_, sequence_)
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Class.Console (log)
import Effect.Exception (Error, message)
import DepGraph (ConjugatePair, Deriv, Labelling, Pos, VisibleGraph, dimap, mapPositions, mask, queries, selected)
import Lattice (DepKind(..), 𝔹, botOf, erase)
import Pretty (prettyP)
import Test.Util.Debug (tracing)
import Util (type (×), Endo, spyWhen, (×))
import Util.Map (get, insert, lookup, mapWithKey, values)
import Util.Set ((\\), (∈), (∪))
import Val (DerivWithDoc, EnvWithDocs(..), Val, ValWithDoc, dataPositions, unval, unvals, val)

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

selectOutput :: Selector ValWithDoc -> Endo Fig
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

selectInput :: Var -> Selector ValWithDoc -> Endo Fig
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

selectIntermediate :: Deriv -> Selector ValWithDoc -> Endo Fig
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
   { v :: ValWithDoc (SelStates 𝕊)
   , ρ :: EnvWithDocs (SelStates 𝕊)
   , ι :: Labelling (ValWithDoc (SelStates 𝔹))
   }

-- Query in the given direction, with the selection primary and what it reaches secondary.
queryResult :: Fig -> SelectionType -> Direction -> EnvWithDocs (SelState 𝕊) × ValWithDoc (SelState 𝕊) × Labelling (ValWithDoc 𝔹)
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
intermediates :: Fig -> Selection (Labelling (ValWithDoc 𝔹)) -> Labelling (ValWithDoc (SelStates 𝔹))
intermediates { inertι } ιs =
   Map.filterKeys (_ ∈ (Map.keys ιs.persistent ∪ Map.keys ιs.transient)) inertι # mapWithIndex \p inert ->
      selStates <$> inert <*> sel ιs.persistent p inert <*> sel ιs.transient p inert
   where
   sel ι p inert = fromMaybe (false <$ inert) (Map.lookup p ι)

drawFig :: HTMLId -> Fig -> Effect Unit
drawFig divId fig = do
   drawView arg { divId, suffix: str.output, view: viewWithDoc options str.output v } (selectOutput >>> redraw)
   sequence_ $ unwrap ρ # mapWithKey \x u ->
      drawView arg { divId: divId <> "-" <> str.input, suffix: x, view: viewWithDoc options x u } (selectInput x >>> redraw)
   for_ (Map.keys fig.ι \\ Map.keys ι) \p -> rootSelect ("#" <> prefix <> "-" <> show p) >>= remove
   sequence_ $ ι # mapWithIndex \p u ->
      drawView arg { divId: prefix, suffix: show p, view: viewWithDoc options str.intermediate (map to𝕊 <$> u) }
         (selectIntermediate p >>> redraw)
   where
   { v, ρ, ι } = selectionResult fig
   arg = objArg
   options = { rowFilter: fig.rowFilter }
   redraw = (_ $ fig { ι = ι }) >>> drawFig divId
   prefix = divId <> "-" <> str.intermediate

-- Replace the placeholder shown during loading by the figure or the loading error
drawLoaded :: HTMLId -> Either Error Fig -> Effect Unit
drawLoaded divId = either failed loaded
   where
   placeholder = rootSelect ("#" <> divId <> " > .fig-loading")
   failed err = log (show err) *> void (placeholder >>= setAttrs [ classes [ "fig-error" ] ] >>= setText (message err))
   loaded fig = drawFig divId fig *> (placeholder >>= remove)

-- Queries over Boolean selections.
boolean
   :: ConjugatePair (Labelling (Set Pos)) (Labelling (Val DepKind))
   -> ConjugatePair (Labelling (Val 𝔹)) (Labelling (Val 𝔹))
boolean = dimap (map selected) (map (map (_ /= Zero)))

-- Data sufficient to draw and query a figure without parser or evaluator
type FigGraph =
   { graph :: VisibleGraph Val DepKind
   , ins :: Dict DerivWithDoc -- input name ↦ vertex
   , out :: DerivWithDoc
   , ιs :: Labelling DerivWithDoc -- documented intermediates
   , ignored :: Labelling (Set Pos) -- input positions left out of linked queries
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

figure :: FigGraph -> Fig
figure { graph, ins, out, ιs, ignored, linking, rowFilter } =
   { rowFilter
   , ρ: pairSel <$> toρ nothing <*> toρ nothing
   , v: pairSel <$> toV nothing <*> toV nothing
   , ι: Map.empty
   , linkedOutputs
   , linkedInputs
   , linkIntermediates
   , dir: { persistent: LinkedOutputs, transient: LinkedOutputs }
   , in_views: ins $> Nothing
   , out_view: Nothing
   , intermediate_views: Map.empty
   , inertι: ιs <#> \p -> (&&) <$> val inertUnmasked.bwd p <*> val inertUnmasked.fwd p
   }
   where
   inputVertices = Set.fromFoldable (fst <$> values ins)
   everything = map (const true) <$> graph.vals
   nothing = map (const false) <$> graph.vals

   -- Queries over the whole graph; queries restricted to data positions other than ignored positions
   unmasked = boolean (queries graph)
   masked = boolean $ queries $ graph # mask \p v ->
      maybe (dataPositions v) (\is -> lift2 (\b b' -> b && not b') (dataPositions v) (mapPositions (_ ∈ is) v))
         (Map.lookup p ignored)

   -- Positions not reached backwards from the output; positions not reached forwards from any input
   inert
      :: ConjugatePair (Labelling (Val 𝔹)) (Labelling (Val 𝔹))
      -> { fwd :: Labelling (Val 𝔹), bwd :: Labelling (Val 𝔹) }
   inert { fwd, bwd } =
      { bwd: map not <$> bwd (unval out (val everything out))
      , fwd: map not <$> fwd (Map.filterKeys (_ ∈ inputVertices) everything)
      }
   inertMasked = inert masked
   inertUnmasked = inert unmasked

   toρ :: Labelling (Val 𝔹) -> EnvWithDocs (SelState 𝔹)
   toρ m = EnvWithDocs (ins <#> \p -> selState <$> val inertMasked.bwd p <*> val m p)

   toV :: Labelling (Val 𝔹) -> ValWithDoc (SelState 𝔹)
   toV m = selState <$> val inertMasked.fwd out <*> val m out

   toι :: Labelling (Val 𝔹) -> Labelling (ValWithDoc 𝔹)
   toι m = Map.filter or (ιs <#> val m)

   fromρ :: EnvWithDocs (SelState 𝔹) -> Labelling (Val 𝔹)
   fromρ ρ = unvals ins (to𝔹 <$> ρ)

   fromV :: ValWithDoc (SelState 𝔹) -> Labelling (Val 𝔹)
   fromV v = unval out (to𝔹 <$> v)

   linkedInputs :: SelectionType -> EnvWithDocs (SelStates 𝔹) -> QueryResult
   linkedInputs selType ρ = (if linking then toρ (masked.bwd (fromV v)) else sel) × v × toι deps
      where
      sel = ρ <#> projSel selType
      deps = masked.fwd (fromρ sel)
      v = toV deps

   linkedOutputs :: SelectionType -> ValWithDoc (SelStates 𝔹) -> QueryResult
   linkedOutputs selType v = ρ × (if linking then toV (masked.fwd (fromρ ρ)) else sel) × toι deps
      where
      sel = v <#> projSel selType
      deps = masked.bwd (fromV sel)
      ρ = toρ deps

   linkIntermediates :: Labelling (ValWithDoc (SelStates 𝔹)) -> QueryResult
   linkIntermediates ι = toρ (unmasked.bwd sel) × toV (unmasked.fwd sel) × toι sel
      where
      sel = Map.unions (Map.intersectionWith unval ιs (map (projSel Transient >>> to𝔹) <$> ι))
