module App.LoadFigureGraph where

import Prelude

import App.Fig (drawFig, figure)
import App.Fig.Codec (decodeFigGraph)
import App.Placeholder (figureFailed, figureLoaded)
import App.View.Util (Filter)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson, printJsonDecodeError)
import Data.Argonaut.Parser (jsonParser)
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (runAff_)
import Effect.Class.Console (log)
import Effect.Exception (message)
import File (File(..), loadFileFromPath)
import Util (orElse, orThrow)

-- Draw a figure from a figure graph file
loadFigureGraph :: Json -> String -> String -> Effect Unit
loadFigureGraph options divId file = flip runAff_ load case _ of
   Left err -> log (show err) *> figureFailed divId (message err)
   Right fig -> drawFig divId fig *> figureLoaded divId
   where
   load = do
      { rowFilter } :: { rowFilter :: Maybe Filter } <- orThrow (lmap printJsonDecodeError (decodeJson options))
      loadFileFromPath (File file) >>= orElse ("File not found: " <> file)
         >>= (jsonParser >=> decodeFigGraph) >>> orThrow
         <#> figure rowFilter
