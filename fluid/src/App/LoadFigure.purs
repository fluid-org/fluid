module App.LoadFigure where

import Prelude hiding (absurd)

import App.CodeMirror (EditorView, addEditorView, dispatch, getContentsLength, update)
import App.Fig (drawLoaded)
import App.Fig.Build (JsonOptions, loadFig, optionsFromJson)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson)
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Data.Array (head, last)
import Data.Either (Either(..))
import Data.String (split, Pattern(..))
import Effect (Effect)
import Effect.Aff (launchAff_, runAff_)
import Effect.Class (liftEffect)
import File (File(..), emptyFileCxt, loadFileFromPath, withRoots)
import Module.Web (runWebT)
import Util (type (×), Endo, error, orElse, whenever, (×))

loadFigure :: Json -> String -> String -> Effect Unit
loadFigure jsonSpec divId srcFile = launchAff_ do
   fluidSrc <- loadFileFromPath (File srcFile) >>= orElse ("File not found: " <> srcFile)
   liftEffect $ loadFigureSrc jsonSpec divId fluidSrc

loadFigureSrc :: Json -> String -> String -> Effect Unit
loadFigureSrc options divId fluidSrc = runAff_ (drawLoaded divId) load
   where
   load = case decodeJson options :: Either JsonDecodeError JsonOptions of
      Left err -> error ("JSON decoding failed with " <> show err)
      Right spec -> do
         let figSpec@{ fluidSrcPaths } = optionsFromJson spec
         runWebT emptyFileCxt (withRoots fluidSrcPaths (loadFig figSpec fluidSrc))

loadCode :: String -> Effect Unit
loadCode file = launchAff_ do
   fluidSrc <- loadFileFromPath (File file) >>= orElse ("File not found: " <> file)
   filename <- orElse ("Empty file name: " <> file) (nonEmpty =<< head <<< split (Pattern ".") =<< last (split (Pattern "/") file))
   liftEffect $ drawFile (File filename × fluidSrc)
   where
   nonEmpty s = whenever (s /= "") s

drawFile :: File × String -> Effect Unit
drawFile (File fileName × src) =
   addEditorView (codeMirrorDiv fileName) >>= setContents src

codeMirrorDiv :: Endo String
codeMirrorDiv = ("codemirror-" <> _)

setContents :: String -> EditorView -> Effect Unit
setContents s ed =
   dispatch ed =<< update ed.state [ { changes: { from: 0, to: getContentsLength ed, insert: s } } ]
