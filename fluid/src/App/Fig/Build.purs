module App.Fig.Build where

import Prelude

import App.Fig (figure)
import App.Fig.Graph (FigGraph)
import App.Util.Selector (eachElement, envVal, field, none, select, sel𝔹, valOf, (>.>))
import App.View.Util (Fig, Filter, Options)
import Classes (class HasClasses)
import Data.Array as A
import Data.Foldable (foldr, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (fst)
import DepGraph (materialise, selected, valAt)
import Dict (fromFoldable) as D
import Eval (evalProgram, visible)
import File (class MonadLoad, Folder(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Literal (Literal(..))
import Module (prepConfig, throwParseFailure)
import Pretty (prettyP)
import Util (isEmpty, quoted, throw, (×))
import Util.Map (get)
import Util.Set ((∈))
import Val (class HasModuleStore, BaseVal(..), EnvWithDocs(..), Val(..), unvals, val, withDoc)

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

-- Take documented leaves of visible graph (other than root) as inputs of figure
figGraph :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Options -> String -> m FigGraph
figGraph { linking, ignoreInputs, rowFilter } fluidSrc = do
   config <- throwParseFailure (prepConfig fluidSrc)
   eval@{ g, root } <- evalProgram config.inputs config.classes config.e
   let
      graph = materialise g (visible eval)
      leaves = Map.filterKeys (\p -> p /= root && isEmpty (get p graph.edges)) g.docs
   named :: Array _ <- for (Map.toUnfoldable leaves) \(p × d) -> case valAt g d of
      Val _ (Lit (Str x)) -> pure (x × (p × Nothing))
      v -> throw ("Doc " <> prettyP v <> " of an input is not a string")
   let names = fst <$> named
   for_ (A.head (A.difference names (A.nub names))) \x -> throw ("Two inputs documented as " <> quoted x)
   let
      ins = D.fromFoldable named
      shown = Set.insert root (Map.keys leaves)
      everything = map (const true) <$> graph.vals
   pure
      { graph
      , ins
      , out: withDoc g root
      , ιs: mapWithIndex (\p d -> p × Just d) (Map.filterKeys (not <<< (_ ∈ shown)) g.docs)
      , ignored: selected <$> unvals ins (sel𝔹 ignoreInputs (EnvWithDocs (ins <#> val everything)))
      , linking
      , rowFilter
      }

loadFig :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Options -> String -> m Fig
loadFig options fluidSrc = figure <$> figGraph options fluidSrc
