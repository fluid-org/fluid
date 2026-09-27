module App.LoadFigure where

import Prelude hiding (absurd)

import App.Fig (drawFig, drawFile, loadFig)
import App.Util (runAffs_)
import App.View.Util (Filter, Options)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson)
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Data.Array (head, last)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (split, Pattern(..))
import Data.Tuple (uncurry)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import File (File(..), FileCxt(..), Folder(..), loadFileFromPath, loadManifests)
import Graph (DVertex'(..))
import Module.Web (runWebT)
import Util (definitely, definitely', error, (×))
import Val (Val(..), asVal)

-- TODO: remove this extra type
type JsonOptions =
   { fluidSrcPath :: Array String
   , inputs :: Array String
   , query :: Boolean
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

optionsFromJson :: JsonOptions -> Options
optionsFromJson spec@{ inputs, query, linking, rowFilter } =
   { fluidSrcPaths: Folder <$> spec.fluidSrcPath
   , inputs
   , query:
        if query then
           Just $ asVal >=> case _ of
              v@(Val α (Just _) _) -> Just $ DVertex (α × v)
              _ -> Nothing
        else Nothing
   , linking
   , rowFilter
   }

loadFigure :: Json -> String -> String -> Effect Unit
loadFigure jsonSpec divId srcFile = launchAff_ do
   fluidSrc <- loadFileFromPath (File srcFile)
   liftEffect $ loadFigureSrc jsonSpec divId (definitely' fluidSrc)

-- TODO: runAffs_ overkill as always a singleton
loadFigureSrc :: Json -> String -> String -> Effect Unit
loadFigureSrc options divId fluidSrc = runAffs_ (uncurry drawFig)
   [ case decodeJson options :: Either JsonDecodeError JsonOptions of
        Left err -> error ("JSON decoding failed with " <> show err)
        Right spec -> do
           let figSpec@{ fluidSrcPaths } = optionsFromJson spec
           manifests <- loadManifests fluidSrcPaths
           (divId × _) <$> runWebT (FileCxt { fluidSrcPaths, manifests, classes: Map.empty }) (loadFig figSpec fluidSrc)
   ]

loadCode :: String -> Effect Unit
loadCode file = launchAff_ do
   fluidSrc <- loadFileFromPath (File file)
   liftEffect $ drawFile (File filename × definitely ("loadCode: File not found: " <> file) fluidSrc)
   where
   filename :: String
   filename = definitely ("loadCode: Filename cannot be empty: " <> file) do
      splitPath <- last (split (Pattern "/") file)
      filename_ <- head (split (Pattern ".") splitPath)
      if filename_ == "" then Nothing else pure filename_
