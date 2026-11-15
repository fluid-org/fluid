module App.LoadFigureGraph where

import Prelude

import App.Fig (drawLoaded, figure)
import App.Fig.Codec (decodeFigGraph)
import Data.Argonaut.Parser (jsonParser)
import Effect (Effect)
import Effect.Aff (runAff_)
import File (File(..), loadFileFromPath)
import Util (orElse, orThrow)

loadFigureGraph :: String -> String -> Effect Unit
loadFigureGraph divId file = runAff_ (drawLoaded divId) $
   loadFileFromPath (File file) >>= orElse ("File not found: " <> file)
      >>= (jsonParser >=> decodeFigGraph) >>> orThrow
      <#> figure
