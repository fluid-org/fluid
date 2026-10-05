module App.Fig where

import Prelude hiding (absurd, compare)

import App.CodeMirror (EditorView, addEditorView, dispatch, getContentsLength, update)
import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), Selector, 𝕊, getSel, selState, selStates, to𝔹, to𝕊, primary, primaryOrSecondary)
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
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second)
import Data.Set as Set
import Data.Traversable (for_, sequence_)
import Data.Tuple (Tuple(..), fst)
import Dict (Dict)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval.Dep (depEval, visible)
import File (class LoadFile, File(..), FileCxt)
import Graph.Dep (Deriv, bwd, fwd, mask, materialise, selected)
import Lattice (DepKind(..), 𝔹, botOf, erase)
import Module (prepConfig)
import Pretty (prettyP)
import Test.Util.Debug (tracing)
import Util (type (×), Endo, absurd, definitely', error, spyWhen, (×))
import Util.Map (insert, intersectionWith, lookup, mapWithKey, restrict, values)
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
   ι' × selType = first (\u -> Map.insert p u ι) (δv (definitely' (Map.lookup p ι)))
   ρ' × v' × dir' × ι_final = case selType of
      Transient | dir.transient /= Intermediates -> ρ × v × dir { transient = Intermediates } × ι'
      Transient -> ρ × v × dir × ι'
      _ -> ρ × v × dir × ι

setIntermediateView :: Deriv -> ViewSetter Fig View
setIntermediateView p δvw fig = fig
   { intermediate_views = Map.insert p (Map.lookup p fig.intermediate_views # join <#> δvw) fig.intermediate_views
   }

type SelectionResult =
   { v :: Val (SelStates 𝕊)
   , ρ :: Env (SelStates 𝕊)
   , ι :: Map Deriv (Val (SelStates 𝔹))
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

-- Intermediates reachable from either selection.
intermediates :: Fig -> Selection (Map Deriv (Val 𝔹)) -> Map Deriv (Val (SelStates 𝔹))
intermediates { inertι } ιs =
   Map.filterKeys (_ ∈ (Map.keys ιs.persistent ∪ Map.keys ιs.transient)) inertι # mapWithIndex \p inert ->
      selStates <$> inert <*> sel ιs.persistent p inert <*> sel ιs.transient p inert
   where
   sel ι p inert = fromMaybe (false <$ inert) (Map.lookup p ι)

drawFig :: HTMLId -> Fig -> Effect Unit
drawFig divId fig = do
   drawView arg { divId, suffix: str.output, view: out_view } (selectOutput >>> redraw)

   sequence_ $ flip mapWithKey in_views \x view ->
      drawView arg { divId: divId <> "-" <> str.input, suffix: x, view } (selectInput x >>> redraw)

   for_ unused \p -> rootSelect ("#" <> prefix <> "-" <> show p) >>= remove
   sequence_ $ ι # mapWithIndex \p v ->
      drawView arg { divId: prefix, suffix: show p, view: view' options str.intermediate (map to𝕊 <$> v) }
         (selectIntermediate p >>> redraw)
   where
   arg = constrArg fig.fieldIndex
   options = { fieldIndex: fig.fieldIndex, rowFilter: fig.spec.rowFilter }
   { v, ρ, ι } = selectionResult fig
   out_view = view' options str.output v
   in_views = ρ # \(Env ρ) -> mapWithKey (view' options) ρ
   redraw = (_ $ fig { ι = ι }) >>> drawFig divId
   unused = Map.keys fig.ι \\ Map.keys ι
   prefix = divId <> "-" <> str.intermediate

drawFile :: File × String -> Effect Unit
drawFile (File fileName × src) =
   addEditorView (codeMirrorDiv fileName) >>= loadCode src

loadFig :: forall m. HasClasses m => HasModuleStore m => MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Options -> String -> m Fig
loadFig options@{ inputs, linking, query, ignoreInputs } fluidSrc = do
   { s, e, gconfig } <- prepConfig fluidSrc
   eval@{ g: g@{ docs }, root } <- depEval gconfig e
   let
      -- Documented vertex defining an environment entry.
      definition q = case A.fromFoldable <<< Map.keys <$> Map.lookup q g.edges of
         Just [ p ] | Map.member p docs -> Just p
         _ -> Nothing

      -- Vertices shown as one value: a vertex and its doc.
      out = root × Map.lookup root docs
      ins = restrict (Set.fromFoldable inputs) eval.inputs <#> \q -> q × (definition q >>= (_ `Map.lookup` docs))
      shown = Set.fromFoldable (A.cons root (A.mapMaybe definition (A.fromFoldable (values (fst <$> ins)))))
      ιs = if query then mapWithIndex (\p d -> p × Just d) (Map.filterKeys (not <<< (_ ∈ shown)) docs) else Map.empty

      unmasked = materialise g (visible eval ∪ Set.fromFoldable (values eval.inputs))

      val :: forall a. Map Deriv (Val a) -> Deriv × Maybe Deriv -> Val a
      val m (p × d) = let Val α _ u = definitely' (Map.lookup p m) in Val α (d <#> \d' -> definitely' (Map.lookup d' m)) u

      unval :: forall a. Deriv × Maybe Deriv -> Val a -> Map Deriv (Val a)
      unval (p × d) (Val α doc u) = Map.fromFoldable (A.cons (p × Val α Nothing u) (A.fromFoldable (Tuple <$> d <*> doc)))

      unvals :: forall a. Dict (Deriv × Maybe Deriv) -> Dict (Val a) -> Map Deriv (Val a)
      unvals ps vs = Map.unions (values (intersectionWith unval ps vs))

      everything = map (const true) <$> unmasked.vals
      ignored = unvals ins (unwrap (sel𝔹 ignoreInputs (Env (ins <#> val everything))))
      masked = unmasked # mask \p v ->
         maybe (dataPositions v) (lift2 (\b b' -> b && not b') (dataPositions v)) (Map.lookup p ignored)

      bwd' graph sel = map (_ /= Zero) <$> bwd graph (selected <$> sel)
      fwd' graph sel = map (_ /= Zero) <$> fwd graph (selected <$> sel)

      -- Positions which the output does not depend on, and which do not depend on any input.
      inertBwd graph = map not <$> bwd' graph (unval out (val everything out))
      inertFwd graph = map not <$> fwd' graph (Map.filterKeys (_ `elem` eval.inputs) everything)
      inertρ = inertBwd masked
      inertV = inertFwd masked
      inertBwdι = inertBwd unmasked
      inertFwdι = inertFwd unmasked

      toρ :: Map Deriv (Val 𝔹) -> Env (SelState 𝔹)
      toρ m = Env (ins <#> \p -> selState <$> val inertρ p <*> val m p)

      toV :: Map Deriv (Val 𝔹) -> Val (SelState 𝔹)
      toV m = selState <$> val inertV out <*> val m out

      toι :: Map Deriv (Val 𝔹) -> Map Deriv (Val 𝔹)
      toι m = Map.filter or (ιs <#> val m)

      fromρ :: Env (SelState 𝔹) -> Map Deriv (Val 𝔹)
      fromρ (Env ρ) = unvals ins (map to𝔹 <$> ρ)

      fromV :: Val (SelState 𝔹) -> Map Deriv (Val 𝔹)
      fromV v = unval out (to𝔹 <$> v)

      linkedInputs :: SelectionType -> Env (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Map Deriv (Val 𝔹)
      linkedInputs selType ρ = ρ'' × v × toι m
         where
         ρ' = ρ <#> getSel selType
         m = fwd' masked (fromρ ρ')
         v = toV m
         ρ'' = if linking then toρ (bwd' masked (fromV v)) else ρ'

      linkedOutputs :: SelectionType -> Val (SelStates 𝔹) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Map Deriv (Val 𝔹)
      linkedOutputs selType v = ρ × v'' × toι m
         where
         v' = v <#> getSel selType
         m = bwd' masked (fromV v')
         ρ = toρ m
         v'' = if linking then toV (fwd' masked (fromρ ρ)) else v'

      linkIntermediates :: Map Deriv (Val (SelStates 𝔹)) -> Env (SelState 𝔹) × Val (SelState 𝔹) × Map Deriv (Val 𝔹)
      linkIntermediates ι = toρ (bwd' unmasked m) × toV (fwd' unmasked m) × toι m
         where
         m = Map.unions (Map.intersectionWith unval ιs (map (getSel Transient >>> to𝔹) <$> ι))

   pure
      { spec: options
      , s
      , ρ: Env (ins <#> \p -> (\inert -> selStates inert false false) <$> val inertρ p)
      , v: (\inert -> selStates inert false false) <$> val inertV out
      , ι: Map.empty
      , linkedOutputs
      , linkedInputs
      , linkIntermediates
      , dir: { persistent: LinkedOutputs, transient: LinkedOutputs }
      , in_views: ins $> Nothing
      , out_view: Nothing
      , intermediate_views: Map.empty
      , inertι: ιs <#> \p -> (&&) <$> val inertBwdι p <*> val inertFwdι p
      , fieldIndex: fieldIndex gconfig.classes
      }

codeMirrorDiv :: Endo String
codeMirrorDiv = ("codemirror-" <> _)

loadCode :: String -> EditorView -> Effect Unit
loadCode s ed =
   dispatch ed =<< update ed.state [ { changes: { from: 0, to: getContentsLength ed, insert: s } } ]
