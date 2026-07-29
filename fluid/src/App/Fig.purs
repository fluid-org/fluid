module App.Fig where

import Prelude hiding (absurd, compare)

import App.CodeMirror (EditorView, addEditorView, dispatch, getContentsLength, update)
import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), Selector, 𝕊, getSel, selState, selStates, to𝔹, to𝕊, primary, primaryOrSecondary)
import App.Util.Selector (envVal, ViewSetter)
import App.View (view')
import App.View.Util (Direction(..), Fig, Options, HTMLId, View, drawView)
import App.View.Util.D3 (remove, rootSelect)
import Bind (Var)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second)
import Data.Array as Array
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (for_, sequence_)
import Data.Tuple (fst, snd)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (graphEval, graphGC, withOp)
import File (class LoadFile, File(..), FileCxt)
import GaloisConnection (GaloisConnection(..), deMorgan)
import Graph (class Graph, DVertex, DVertex'(..), Vertex(..), VertexData, dvertices, runQuery, selectαs, select𝔹s, vertexData, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.Slice (bwdSlice)
import Lattice (class BoundedMeetSemilattice, Raw, 𝔹, botOf, erase, topOf)
import Module (Config, prepConfig)
import Partial.Unsafe (unsafePartial)
import Pretty (prettyP)
import Primitive.Defs (primitives)
import Test.Util.Debug (tracing)
import Util (type (×), Endo, absurd, error, spyWhen, (×), (∩))
import Util.Map (filterKeys, insert, keys, lookup, mapWithKey, restrict)
import Util.Set (empty, (\\), (∈), (∪))
import Val (Env(..), EnvStmt(..), Val(..), asVal, unrestrictGC)

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
selectOutput δv fig@{ v, dir, γ } = fig { v = v', γ = γ', dir = dir' }
   where
   v' × selType = δv v
   γ' × dir' = case selType of
      Persistent | dir.persistent /= LinkedOutputs -> botOf γ × dir { persistent = LinkedOutputs }
      Transient | dir.transient /= LinkedOutputs -> γ × dir { transient = LinkedOutputs }
      _ -> γ × dir

setOutputView :: ViewSetter Fig View
setOutputView δvw fig = fig
   { out_view = fig.out_view <#> δvw }

selectInput :: Var -> Selector Val -> Endo Fig
selectInput x δv fig@{ v, dir, γ } = fig { v = v', γ = γ', dir = dir' }
   where
   γ' × selType = envVal x δv γ
   v' × dir' = case selType of
      Persistent | dir.persistent /= LinkedInputs -> botOf v × dir { persistent = LinkedInputs }
      Transient | dir.transient /= LinkedInputs -> v × dir { transient = LinkedInputs }
      _ -> v × dir

setInputView :: Var -> ViewSetter Fig View
setInputView x δvw fig = fig
   { in_views = insert x (lookup x fig.in_views # join <#> δvw) fig.in_views
   }

selectIntermediate :: Vertex -> Selector Val -> Endo Fig
selectIntermediate (Vertex α) δv fig@{ ι, dir, γ, v } = fig { ι = ι_final, γ = γ', v = v', dir = dir' }
   where
   ι' × selType = envVal α δv ι
   γ' × v' × dir' × ι_final = case selType of
      Transient | dir.transient /= Intermediates -> γ × v × dir { transient = Intermediates } × ι'
      Transient -> γ × v × dir × ι'
      _ -> γ × v × dir × ι

setIntermediateView :: Vertex -> ViewSetter Fig View
setIntermediateView (Vertex α) δvw fig = fig
   { intermediate_views = insert α (lookup α fig.intermediate_views # join <#> δvw) fig.intermediate_views
   }

rebuildι :: Set DVertex -> Selection (Set DVertex) -> Dict (Val Vertex) -> Env (SelStates 𝔹)
rebuildι inerts αs ι =
   Env $ D.fromFoldable $ setSels <$> vs_inert <*> vs_selected
   where
   -- Consolidate with analogous calculation with γInert etc in loadFig?
   vs_inert = ι <#> \v -> select𝔹s v inerts
   vs_selected = ι <#> \v@(Val α _ _) -> α × { persistent: select𝔹s v αs.persistent, transient: select𝔹s v αs.transient }

   setSels :: Val 𝔹 -> Vertex × Selection (Val 𝔹) -> String × Val (SelStates 𝔹)
   setSels inert (Vertex α × v) = α × (selStates <$> inert <*> v.persistent <*> v.transient)

type SelectionResult =
   { v :: Val (SelStates 𝕊)
   , γ :: Env (SelStates 𝕊)
   , ι :: Env (SelStates 𝔹)
   }

selectionResult :: Fig -> SelectionResult
selectionResult fig@{ dir, v, γ, ι } =
   { v: reportOut v', γ: reportIn γ', ι: ι' }
   where
   as𝕊v :: forall a b. SelectionType -> a × Val (SelState 𝔹) × b -> a × Val (SelState 𝕊) × b
   as𝕊v selType = (second <<< first) $ primaryOrSecondary selType v

   to𝕊v :: forall a b. a × Val (SelState 𝔹) × b -> a × (Val (SelState 𝕊)) × b
   to𝕊v = second (first primary)

   as𝕊γ :: forall a. SelectionType -> Env (SelState 𝔹) × a -> Env (SelState 𝕊) × a
   as𝕊γ selType = first $ primaryOrSecondary selType γ

   to𝕊γ :: forall a. Env (SelState 𝔹) × a -> Env (SelState 𝕊) × a
   to𝕊γ = first primary

   γ1 × v1 × αs =
      case dir.persistent of
         LinkedOutputs -> to𝕊γ $ as𝕊v Persistent $ fig.linkedOutputs Persistent v
         LinkedInputs -> to𝕊v $ as𝕊γ Persistent $ fig.linkedInputs Persistent γ
         Intermediates -> error absurd
   γ2 × v2 × αs' =
      case dir.transient of
         LinkedOutputs -> to𝕊γ $ as𝕊v Transient $ fig.linkedOutputs Transient v
         LinkedInputs -> to𝕊v $ as𝕊γ Transient $ fig.linkedInputs Transient γ
         Intermediates -> to𝕊γ $ to𝕊v $ fig.linkIntermediates ι

   ι' = intermediates fig { persistent: αs, transient: αs' }

   splice :: forall a. SelState a -> SelState a -> SelStates a
   splice Inert _ = SelStates Inert
   splice _ Inert = SelStates Inert
   splice (Reactive persistent) (Reactive transient) =
      SelStates (Reactive { persistent, transient })

   v' = splice <$> v1 <*> v2
   γ' = splice <$> γ1 <*> γ2

   reportIn = spyWhen tracing.mediatingData ("Mediating inputs") (prettyP <<< erase)
   reportOut = spyWhen tracing.mediatingData ("Mediating outputs") (prettyP <<< erase)

intermediates :: Fig -> Selection (Set DVertex) -> Env (SelStates 𝔹)
intermediates { spec, in_roots, inerts } αs =
   flip (maybe empty) spec.query findIntermediates
   where
   findIntermediates :: (VertexData -> Maybe (DVertex' (Val Vertex))) -> Env (SelStates Boolean)
   findIntermediates query = rebuildι inerts αs
      $ filterKeys (\α -> not (Vertex α ∈ in_roots))
      $ runQuery query (αs.persistent ∪ αs.transient)

drawFig :: HTMLId -> Fig -> Effect Unit
drawFig divId fig@{ spec: options } = do
   drawView { divId, suffix: str.output, view: out_view } (selectOutput >>> redraw)

   sequence_ $ flip mapWithKey in_views \x view ->
      drawView { divId: divId <> "-" <> str.input, suffix: x, view } (selectInput x >>> redraw)

   for_ unused \α -> rootSelect ("#" <> prefix <> "-" <> α) >>= remove
   sequence_ $ flip mapWithKey (unwrap ι) \α v ->
      drawView { divId: prefix, suffix: α, view: unsafePartial $ view' options str.intermediate (map to𝕊 <$> v) }
         (selectIntermediate (Vertex α) >>> redraw)
   where
   { v, γ, ι } = selectionResult fig
   out_view = unsafePartial $ view' options str.output v
   in_views = γ # \(Env γ) -> unsafePartial (mapWithKey (view' options) γ)
   redraw = (_ $ fig { ι = ι }) >>> drawFig divId
   unused = keys fig.ι \\ keys ι
   prefix = divId <> "-" <> str.intermediate

drawFile :: File × String -> Effect Unit
drawFile (File fileName × src) =
   addEditorView (codeMirrorDiv fileName) >>= loadCode src

unprojStmt :: forall a. BoundedMeetSemilattice a => Raw EnvStmt -> GaloisConnection (Env a) (EnvStmt a)
unprojStmt (EnvStmt _ s) = GC
   { fwd: \γ -> EnvStmt γ (topOf s)
   , bwd: \(EnvStmt γ _) -> γ
   }

type IO a = { γ :: Env a, v :: Val a }

lift
   :: forall f f' g
    . Apply f
   => Apply f'
   => f (𝔹 -> SelState 𝔹)
   -> (f' 𝔹 -> f 𝔹 × g)
   -> f' (SelState 𝔹)
   -> f (SelState 𝔹) × g
lift selState_f f v = first (apply selState_f) (f (v <#> to𝔹))

-- Identifies @doc-annotated intermediate vertices: those whose value carries a
-- doc annotation. Shared by the web figures (App.LoadFigure) and the tests.
docQuery :: VertexData -> Maybe (DVertex' (Val Vertex))
docQuery = asVal >=> case _ of
   v@(Val α (Just _) _) -> Just (DVertex (α × v))
   _ -> Nothing

loadFig :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Options -> String -> m Fig
loadFig = loadFigWith prepConfig

loadFigWith :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => (Raw Env -> String -> m Config) -> Options -> String -> m Fig
loadFigWith prep options@{ inputs, linking } fluidSrc = do
   { s, e, gconfig } <- prep primitives fluidSrc
   eval@({ inα: EnvStmt γα _, outα, g: g0 }) <- graphEval gconfig e
   let
      opEval = withOp eval
      inputs' = Set.fromFoldable inputs
      EnvStmt γ s' = erase eval.inα
      GC focus = unrestrictGC γ inputs' >>> unprojStmt (EnvStmt γ s')
      Env γ_restricted = restrict inputs' γα
      in_roots = Set.fromFoldable $ (\(Val α _ _) -> α) <$> γ_restricted

      graphgc = graphGC eval
      graphgc_op = graphGC opEval

      gcBwd :: Val 𝔹 -> Env 𝔹 × GraphImpl
      gcBwd v = first focus.bwd (graphgc.bwd v)

      gcFwd :: Env 𝔹 -> Val 𝔹 × GraphImpl
      gcFwd γ = graphgc_op.bwd (deMorgan focus.fwd γ)

      in_views = const Nothing <$> γ_restricted
      unselected = { γ: botOf γα, v: botOf outα } :: IO 𝔹

      inertBwd = vertices g0 \\ (vertices $ snd $ gcBwd $ topOf outα)
      inertFwd = vertices $ snd $ graphgc.fwd $ focus.fwd unselected.γ

      inert = { γ: select𝔹s γα inertBwd, v: select𝔹s outα inertFwd } :: IO 𝔹
      inert' = { γ: selState <$> inert.γ, v: selState <$> inert.v } :: IO (𝔹 -> SelState 𝔹)

      demands :: Val (SelState 𝔹) -> Env (SelState 𝔹) × GraphImpl
      demands = lift inert'.γ gcBwd

      demandedBy :: Env (SelState 𝔹) -> Val (SelState 𝔹) × GraphImpl
      demandedBy = lift inert'.v gcFwd

      linkedInputs :: SelectionType -> Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkedInputs selType γ = γ'' × v × vertices g
         where
         γ' = γ <#> getSel selType
         v × g = demandedBy γ'
         γ'' = if linking then fst (demands v) else γ'

      linkedOutputs :: SelectionType -> Val (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkedOutputs selType v = γ × v'' × vertices g
         where
         v' = v <#> getSel selType
         γ × g = demands v'
         v'' = if linking then fst (demandedBy γ) else v'

      linkIntermediates :: Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkIntermediates ι =
         let
            ια = Env $ ιfromαs g0 (keys ι) :: Env Vertex
            ι' = ι <#> getSel Transient >>> to𝔹
            αs = selectαs ι' ια
            v = inert'.v <*> select𝔹s outα (vertices $ bwdSlice (αs × opEval.g))
            γ = inert'.γ <*> select𝔹s γα (vertices $ bwdSlice (αs × eval.g))
         in
            γ × v × (dvertices g0 αs)

   pure
      { spec: options
      , s
      , γ: selStates <$> inert.γ <*> unselected.γ <*> unselected.γ
      , v: selStates <$> inert.v <*> unselected.v <*> unselected.v
      , ι: empty
      , linkedOutputs
      , linkedInputs
      , linkIntermediates
      , dir: { persistent: LinkedOutputs, transient: LinkedOutputs }
      , in_views
      , out_view: Nothing
      , intermediate_views: empty
      , in_roots
      , inerts: inertFwd ∩ inertBwd
      }

ιfromαs :: forall g. Graph g => g -> Set String -> Dict (Val Vertex)
ιfromαs g = D.fromFoldable
   <<< Array.mapMaybe
      (\α -> (α × _) <$> (asVal $ vertexData g (Vertex α)))
   <<< Set.toUnfoldable

codeMirrorDiv :: Endo String
codeMirrorDiv = ("codemirror-" <> _)

loadCode :: String -> EditorView -> Effect Unit
loadCode s ed =
   dispatch ed =<< update ed.state [ { changes: { from: 0, to: getContentsLength ed, insert: s } } ]
