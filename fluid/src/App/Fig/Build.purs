module App.Fig.Build where

import Prelude

import App.Fig (FigGraph, figure)
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
   , query :: Boolean
   , ignoreInputs :: Maybe (Object (Array String)) -- input ↦ columns
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

optionsFromJson :: JsonOptions -> Options
optionsFromJson spec@{ query, ignoreInputs, linking, rowFilter } =
   { fluidSrcPaths: Folder <$> spec.fluidSrcPath
   , query
   , ignoreInputs: foldr (>.>) none $ (maybe [] Object.toUnfoldable ignoreInputs) <#> \(x × ks) ->
        envVal x (valOf (eachElement (foldr (>.>) none (ks <#> \k -> field k select))))
   , linking
   , rowFilter
   }

-- Build a figure graph by evaluating a program. Take as inputs the documented vertices independent of every
-- visible vertex. Never take the root as an input.
figGraph :: forall m. HasClasses m => HasModuleStore m => MonadLoad m => Options -> String -> m FigGraph
figGraph { linking, query, ignoreInputs } fluidSrc = do
   config <- throwParseFailure (prepConfig fluidSrc)
   eval@{ g, root } <- evalProgram config.inputs config.classes config.e
   let
      graph = materialise g (visible eval)
      leaves = Map.filterKeys (\p -> p /= root && isEmpty (get p graph.edges)) g.docs
   named <- for (Map.toUnfoldable leaves :: Array _) \(p × d) -> case valAt g d of
      Val _ (Lit (Str x)) -> pure (x × (p × Nothing))
      v -> throw ("Doc " <> prettyP v <> " of an input is not a string")
   for_ (A.head (A.difference (fst <$> named) (A.nub (fst <$> named)))) \x ->
      throw ("Two inputs documented as " <> quoted x)
   let
      ins = D.fromFoldable named
      shown = Set.insert root (Map.keys leaves)
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
