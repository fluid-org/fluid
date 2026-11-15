module App.Fig.Build where

import Prelude

import App.Fig (FigGraph, figure)
import App.Util.Selector (eachElement, envVal, field, none, select, sel𝔹, valOf, (>.>))
import App.View.Util (Fig, Filter, Options)
import Classes (class HasClasses)
import Data.Foldable (foldr)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.Traversable (for)
import Data.Tuple (fst)
import DepGraph (materialise, selected)
import Dict (fromFoldable) as D
import Eval (documentedAs, evalProgram, visible)
import File (class MonadLoad, Folder(..))
import Foreign.Object (Object)
import Foreign.Object as Object
import Module (prepConfig, throwParseFailure)
import Util (quoted, throw, (×))
import Util.Map (values)
import Util.Set ((∈))
import Val (class HasModuleStore, EnvWithDocs(..), unvals, val, withDoc)

-- TODO: remove this extra type
type JsonOptions =
   { fluidSrcPath :: Array String
   , inputs :: Array String
   , query :: Boolean
   , ignoreInputs :: Maybe (Object (Array String)) -- input ↦ columns
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

optionsFromJson :: JsonOptions -> Options
optionsFromJson spec@{ inputs, query, ignoreInputs, linking, rowFilter } =
   { fluidSrcPaths: Folder <$> spec.fluidSrcPath
   , inputs
   , query
   , ignoreInputs: foldr (>.>) none $ (maybe [] Object.toUnfoldable ignoreInputs) <#> \(x × ks) ->
        envVal x (valOf (eachElement (foldr (>.>) none (ks <#> \k -> field k select))))
   , linking
   , rowFilter
   }

-- Build figure graph by evaluating a program
figGraph :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Options -> String -> m FigGraph
figGraph { inputs, linking, query, ignoreInputs } fluidSrc = do
   config <- throwParseFailure (prepConfig fluidSrc)
   eval@{ g, root } <- evalProgram config.inputs config.classes config.e
   -- Look up each input as the unique vertex documented with the input name; show inputs without docs
   ins <- D.fromFoldable <$> for inputs \x -> case documentedAs g x of
      [ p ] -> pure (x × (p × Nothing))
      _ -> throw ("No unique value documented " <> quoted x)
   let
      shown = Set.insert root (Set.fromFoldable (fst <$> values ins))
      graph = materialise g (visible eval)
      everything = map (const true) <$> graph.vals
   pure
      { graph
      , ins
      , out: withDoc g root
      , ιs:
           if query then mapWithIndex (\p d -> p × Just d) (Map.filterKeys (not <<< (_ ∈ shown)) g.docs)
           else Map.empty
      , ignored: selected <$> unvals ins (sel𝔹 ignoreInputs (EnvWithDocs (ins <#> val everything)))
      , linking
      }

loadFig :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Options -> String -> m Fig
loadFig options fluidSrc = figure options.rowFilter <$> figGraph options fluidSrc
