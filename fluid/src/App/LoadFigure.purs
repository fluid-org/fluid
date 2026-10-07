module App.LoadFigure where

import Prelude hiding (absurd)

import App.Fig (drawFig, drawFile, loadFig)
import App.Util.Selector (dictVal, eachElement, envVal, valOf, select, none, (>.>))
import App.View.Util (Filter, Options)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson)
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Data.Array (head, last)
import Data.Either (Either(..))
import Data.Foldable (foldr)
import Data.Maybe (Maybe, maybe)
import Data.String (split, Pattern(..))
import Effect (Effect)
import Effect.Aff (launchAff_, runAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log)
import Effect.Exception (message)
import Foreign.Object (Object)
import Foreign.Object as Object
import File (File(..), Folder(..), emptyFileCxt, loadFileFromPath, withRoots)
import Module.Web (runWebT)
import Util (error, orElse, whenever, (×))

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
        envVal x (valOf (eachElement (foldr (>.>) none (ks <#> \k -> dictVal k select))))
   , linking
   , rowFilter
   }

loadFigure :: Json -> String -> String -> Effect Unit
loadFigure jsonSpec divId srcFile = launchAff_ do
   fluidSrc <- loadFileFromPath (File srcFile) >>= orElse ("File not found: " <> srcFile)
   liftEffect $ loadFigureSrc jsonSpec divId fluidSrc

loadFigureSrc :: Json -> String -> String -> Effect Unit
loadFigureSrc options divId fluidSrc = flip runAff_ load case _ of
   Left err -> log (show err) *> figureFailed divId (message err)
   Right fig -> drawFig divId fig *> figureLoaded divId
   where
   load = case decodeJson options :: Either JsonDecodeError JsonOptions of
      Left err -> error ("JSON decoding failed with " <> show err)
      Right spec -> do
         let figSpec@{ fluidSrcPaths } = optionsFromJson spec
         runWebT emptyFileCxt (withRoots fluidSrcPaths (loadFig figSpec fluidSrc))

-- Remove the placeholder shown until the figure loads; its absence tells the web tests the page has settled
foreign import figureLoaded :: String -> Effect Unit

-- Replace the placeholder by the error
foreign import figureFailed :: String -> String -> Effect Unit

loadCode :: String -> Effect Unit
loadCode file = launchAff_ do
   fluidSrc <- loadFileFromPath (File file) >>= orElse ("File not found: " <> file)
   filename <- orElse ("Empty file name: " <> file) (nonEmpty =<< head <<< split (Pattern ".") =<< last (split (Pattern "/") file))
   liftEffect $ drawFile (File filename × fluidSrc)
   where
   nonEmpty s = whenever (s /= "") s
