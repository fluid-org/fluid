module App.Fig where

import Prelude hiding (absurd, compare)

import App.CodeMirror (EditorView, addEditorView, dispatch, getContentsLength, update)
import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), Selector, 𝕊, getSel, selState, selStates, to𝔹, to𝕊, primary, primaryOrSecondary)
import App.Util.Selector (constrArg, envVal, ViewSetter)
import App.View (view')
import App.View.Util (Direction(..), Fig, Options, HTMLId, View, drawView)
import App.View.Util.D3 (remove, rootSelect)
import Bind (Var)
import DataType (class HasClasses, fieldIndex)
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
import Eval (ConjugatePair, depsOf, graphEval, withOp)
import File (class LoadFile, File(..), FileCxt)
import Graph (class Graph, DVertex, DVertex', Vertex(..), VertexData, dvertices, runQuery, selectαs, select𝔹s, vertexData, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.Slice (bwdSlice)
import Lattice (𝔹, botOf, erase, topOf)
import Module (prepConfig)
import Pretty (prettyP)
import Test.Util.Debug (tracing)
import Util (type (×), Endo, absurd, error, spyWhen, (×), (∩))
import Util.Map (filterKeys, insert, keys, lookup, mapWithKey, restrict)
import Util.Set (empty, (\\), (∈), (∪))
import Val (class HasModuleStore, Env(..), EnvStmt(..), Val(..), asVal)

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

selectIntermediate :: Vertex -> Selector Val -> Endo Fig
selectIntermediate (Vertex α) δv fig@{ ι, dir, ρ, v } = fig { ι = ι_final, ρ = ρ', v = v', dir = dir' }
   where
   ι' × selType = envVal α δv ι
   ρ' × v' × dir' × ι_final = case selType of
      Transient | dir.transient /= Intermediates -> ρ × v × dir { transient = Intermediates } × ι'
      Transient -> ρ × v × dir × ι'
      _ -> ρ × v × dir × ι

setIntermediateView :: Vertex -> ViewSetter Fig View
setIntermediateView (Vertex α) δvw fig = fig
   { intermediate_views = insert α (lookup α fig.intermediate_views # join <#> δvw) fig.intermediate_views
   }

rebuildι :: Set DVertex -> Selection (Set DVertex) -> Dict (Val Vertex) -> Env (SelStates 𝔹)
rebuildι inerts αs ι =
   Env $ D.fromFoldable $ setSels <$> vs_inert <*> vs_selected
   where
   -- Consolidate with analogous calculation with ρInert etc in loadFig?
   vs_inert = ι <#> \v -> select𝔹s v inerts
   vs_selected = ι <#> \v@(Val α _ _) -> α × { persistent: select𝔹s v αs.persistent, transient: select𝔹s v αs.transient }

   setSels :: Val 𝔹 -> Vertex × Selection (Val 𝔹) -> String × Val (SelStates 𝔹)
   setSels inert (Vertex α × v) = α × (selStates <$> inert <*> v.persistent <*> v.transient)

type SelectionResult =
   { v :: Val (SelStates 𝕊)
   , ρ :: Env (SelStates 𝕊)
   , ι :: Env (SelStates 𝔹)
   }

selectionResult :: Fig -> SelectionResult
selectionResult fig@{ dir, v, ρ, ι } =
   { v: reportOut v', ρ: reportIn ρ', ι: ι' }
   where
   as𝕊v :: forall a b. SelectionType -> a × Val (SelState 𝔹) × b -> a × Val (SelState 𝕊) × b
   as𝕊v selType = (second <<< first) $ primaryOrSecondary selType v

   to𝕊v :: forall a b. a × Val (SelState 𝔹) × b -> a × (Val (SelState 𝕊)) × b
   to𝕊v = second (first primary)

   as𝕊ρ :: forall a. SelectionType -> Env (SelState 𝔹) × a -> Env (SelState 𝕊) × a
   as𝕊ρ selType = first $ primaryOrSecondary selType ρ

   to𝕊ρ :: forall a. Env (SelState 𝔹) × a -> Env (SelState 𝕊) × a
   to𝕊ρ = first primary

   ρ1 × v1 × αs =
      case dir.persistent of
         LinkedOutputs -> to𝕊ρ $ as𝕊v Persistent $ fig.linkedOutputs Persistent v
         LinkedInputs -> to𝕊v $ as𝕊ρ Persistent $ fig.linkedInputs Persistent ρ
         Intermediates -> error absurd
   ρ2 × v2 × αs' =
      case dir.transient of
         LinkedOutputs -> to𝕊ρ $ as𝕊v Transient $ fig.linkedOutputs Transient v
         LinkedInputs -> to𝕊v $ as𝕊ρ Transient $ fig.linkedInputs Transient ρ
         Intermediates -> to𝕊ρ $ to𝕊v $ fig.linkIntermediates ι

   ι' = intermediates fig { persistent: αs, transient: αs' }

   splice :: forall a. SelState a -> SelState a -> SelStates a
   splice Inert _ = SelStates Inert
   splice _ Inert = SelStates Inert
   splice (Reactive persistent) (Reactive transient) =
      SelStates (Reactive { persistent, transient })

   v' = splice <$> v1 <*> v2
   ρ' = splice <$> ρ1 <*> ρ2

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
   drawView arg { divId, suffix: str.output, view: out_view } (selectOutput >>> redraw)

   sequence_ $ flip mapWithKey in_views \x view ->
      drawView arg { divId: divId <> "-" <> str.input, suffix: x, view } (selectInput x >>> redraw)

   for_ unused \α -> rootSelect ("#" <> prefix <> "-" <> α) >>= remove
   sequence_ $ flip mapWithKey (unwrap ι) \α v ->
      drawView arg { divId: prefix, suffix: α, view: view' fig.fieldIndex options str.intermediate (map to𝕊 <$> v) }
         (selectIntermediate (Vertex α) >>> redraw)
   where
   arg = constrArg fig.fieldIndex
   { v, ρ, ι } = selectionResult fig
   out_view = view' fig.fieldIndex options str.output v
   in_views = ρ # \(Env ρ) -> mapWithKey (view' fig.fieldIndex options) ρ
   redraw = (_ $ fig { ι = ι }) >>> drawFig divId
   unused = keys fig.ι \\ keys ι
   prefix = divId <> "-" <> str.intermediate

drawFile :: File × String -> Effect Unit
drawFile (File fileName × src) =
   addEditorView (codeMirrorDiv fileName) >>= loadCode src

type IO a = { ρ :: Env a, v :: Val a }

lift
   :: forall f f' g
    . Apply f
   => Apply f'
   => f (𝔹 -> SelState 𝔹)
   -> (f' 𝔹 -> f 𝔹 × g)
   -> f' (SelState 𝔹)
   -> f (SelState 𝔹) × g
lift selState_f f v = first (apply selState_f) (f (v <#> to𝔹))

loadFig :: forall m. HasClasses m => HasModuleStore m => MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Options -> String -> m Fig
loadFig options@{ inputs, linking } fluidSrc = do
   { s, e, gconfig } <- prepConfig fluidSrc
   eval@({ inα: EnvStmt ρα _, outα, g: g0 }) <- graphEval gconfig e
   let
      opEval = withOp eval
      inputs' = Set.fromFoldable inputs
      EnvStmt _ s' = erase eval.inα
      Env ρ_restricted = restrict inputs' ρα
      in_roots = Set.fromFoldable $ (\(Val α _ _) -> α) <$> ρ_restricted

      deps = depsOf eval

      io :: ConjugatePair GraphImpl Env Val
      io =
         { fwd: \ρ -> deps.fwd (EnvStmt ρ (botOf s'))
         , bwd: \v -> first (\(EnvStmt ρ _) -> restrict inputs' ρ) (deps.bwd v)
         }

      in_views = const Nothing <$> ρ_restricted
      unselected = { ρ: botOf ρα, v: botOf outα } :: IO 𝔹

      inertBwd = vertices g0 \\ (vertices $ snd $ io.bwd $ topOf outα)
      inertFwd = vertices g0 \\ (vertices $ snd $ deps.fwd (EnvStmt (topOf ρα) (botOf s')))

      inert = { ρ: select𝔹s ρα inertBwd, v: select𝔹s outα inertFwd } :: IO 𝔹
      inert' = { ρ: selState <$> inert.ρ, v: selState <$> inert.v } :: IO (𝔹 -> SelState 𝔹)

      demands :: Val (SelState 𝔹) -> Env (SelState 𝔹) × GraphImpl
      demands = lift inert'.ρ io.bwd

      demandedBy :: Env (SelState 𝔹) -> Val (SelState 𝔹) × GraphImpl
      demandedBy = lift inert'.v io.fwd

      linkedInputs :: SelectionType -> Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkedInputs selType ρ = ρ'' × v × vertices g
         where
         ρ' = ρ <#> getSel selType
         v × g = demandedBy ρ'
         ρ'' = if linking then fst (demands v) else ρ'

      linkedOutputs :: SelectionType -> Val (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkedOutputs selType v = ρ × v'' × vertices g
         where
         v' = v <#> getSel selType
         ρ × g = demands v'
         v'' = if linking then fst (demandedBy ρ) else v'

      linkIntermediates :: Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Set DVertex
      linkIntermediates ι =
         let
            ια = Env $ ιfromαs g0 (keys ι) :: Env Vertex
            ι' = ι <#> getSel Transient >>> to𝔹
            αs = selectαs ι' ια
            v = inert'.v <*> select𝔹s outα (vertices $ bwdSlice (αs × opEval.g))
            ρ = inert'.ρ <*> select𝔹s ρα (vertices $ bwdSlice (αs × eval.g))
         in
            ρ × v × (dvertices g0 αs)

   pure
      { spec: options
      , s
      , ρ: selStates <$> inert.ρ <*> unselected.ρ <*> unselected.ρ
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
      , fieldIndex: fieldIndex gconfig.classes
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
