module App.LoadFigureGraph where

import Prelude

import App.Fig (drawLoaded, figure)
import App.Fig.Codec (decodeFigGraph)
import App.View.Util (Filter)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson, printJsonDecodeError)
import Data.Argonaut.Parser (jsonParser)
import Data.Bifunctor (lmap)
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (runAff_)
import File (File(..), loadFileFromPath)
import Util (orElse, orThrow)

loadFigureGraph :: Json -> String -> String -> Effect Unit
loadFigureGraph options divId file = runAff_ (drawLoaded divId) load
   where
   load = do
      { rowFilter } :: { rowFilter :: Maybe Filter } <- orThrow (lmap printJsonDecodeError (decodeJson options))
      loadFileFromPath (File file) >>= orElse ("File not found: " <> file)
         >>= (jsonParser >=> decodeFigGraph) >>> orThrow
         <#> figure rowFilter
