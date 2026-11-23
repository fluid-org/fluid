module App.Fig.Build where

import Prelude

import App.Fig (figure)
import App.Fig.Graph (FigGraph, str)
import App.Util.Selector (eachElement, envVal, field, none, select, sel𝔹, valOf, (>.>))
import App.View.Util (Fig, Filter, Options)
import Data.Array as A
import Data.DateTime.Instant (unInstant)
import Data.Foldable (foldr, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (fst)
import DepGraph (selected)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Dict (fromFoldable) as D
import Eval (evalProgram, visibleGraph)
import File (Folder(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Literal (Literal(..))
import Module (prepConfig, throwParseFailure)
import Pretty (prettyP)
import Util (type (×), isEmpty, throw, (×))
import Util.Map (get)
import Util.Set ((∈))
import Val (class MonadProgram, BaseVal(..), EnvWithDocs(..), Val(..), unvals, val, valAt)

-- Options in the form decoded from JSON; delete once the options are decoded directly
type JsonOptions =
   { fluidSrcPath :: Array String
   , ignoreInputs :: Maybe (Object (Array String)) -- input ↦ columns
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

optionsFromJson :: JsonOptions -> Options
optionsFromJson spec@{ ignoreInputs, linking, rowFilter } =
   { fluidSrcPaths: Folder <$> spec.fluidSrcPath
   , ignoreInputs: foldr (>.>) none $ (maybe [] Object.toUnfoldable ignoreInputs) <#> \(x × ks) ->
        envVal x (valOf (eachElement (foldr (>.>) none (ks <#> \k -> field k select))))
   , linking
   , rowFilter
   }

-- Times in milliseconds; evaluation includes loading of modules
type Timing = { evaluate :: Number, materialise :: Number }

figGraph :: forall m. MonadProgram m => Options -> String -> m FigGraph
figGraph options fluidSrc = fst <$> figGraphTimed options fluidSrc

-- Take documented leaves of visible graph (other than output) as inputs of figure
figGraphTimed :: forall m. MonadProgram m => Options -> String -> m (FigGraph × Timing)
figGraphTimed { linking, ignoreInputs, rowFilter } fluidSrc = do
   started <- clock
   config <- throwParseFailure (prepConfig fluidSrc)
   eval@{ g, out } <- evalProgram config.inputs config.classes config.e
   evaluated <- clock
   let graph = visibleGraph eval
   materialised <- clock
   let
      leaves = Map.filterKeys (\p -> p /= out && isEmpty (get p graph.edges)) g.docs
   named :: Array _ <- for (Map.toUnfoldable leaves) \(p × d) -> case valAt g d of
      Val _ (Lit (Str x)) -> pure (x × (p × Nothing))
      v -> throw ("Doc " <> prettyP v <> " of " <> str.input <> " is not a string")
   let names = fst <$> named
   for_ (A.head (A.difference names (A.nub names))) \x ->
      throw ("More than one " <> str.input <> " documented as " <> prettyP (Str x))
   let
      ins = D.fromFoldable named
      shown = Set.insert out (Map.keys leaves)
      everything = map (const true) <$> graph.vals
   pure $
      { graph
      , ins
      , out: out × Map.lookup out g.docs
      , ιs: mapWithIndex (\p d -> p × Just d) (Map.filterKeys (not <<< (_ ∈ shown)) g.docs)
      , ignored: selected <$> unvals ins (sel𝔹 ignoreInputs (EnvWithDocs (ins <#> val everything)))
      , linking
      , rowFilter
      } × { evaluate: evaluated - started, materialise: materialised - evaluated }
   where
   clock = liftEffect (now <#> unInstant >>> unwrap)

loadFig :: forall m. MonadProgram m => Options -> String -> m Fig
loadFig options fluidSrc = figure <$> figGraph options fluidSrc
