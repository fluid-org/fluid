module File where

import Prelude

import Affjax (Error(..)) as A
import Affjax (Response)
import Affjax.ResponseFormat (json, string)
import Affjax.StatusCode (StatusCode(..))
import Affjax.Web (defaultRequest, request)
import Control.Monad.Except (class MonadError, ExceptT(..), runExceptT)
import Control.Monad.Reader (class MonadReader, ask, local)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT, lift)
import Data.Argonaut.Decode (decodeJson)
import Data.Array (catMaybes, foldM)
import Data.Either (Either(..), either, hush)
import Data.HTTP.Method (Method(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), stripPrefix)
import Data.Traversable (any, for)
import DataType (ClassTable)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class.Console (log)
import Effect.Exception (Error)
import Util (type (×), (×), debug, orElse)
import Util.Set ((∈))

-- Files under each source root that has a manifest; other roots are probed
type Manifests = Map Folder (Set File)

newtype FileCxt = FileCxt { fluidSrcPaths :: Array Folder, manifests :: Manifests, classes :: ClassTable }

withClasses :: forall m a. MonadReader FileCxt m => ClassTable -> m a -> m a
withClasses classes = local (\(FileCxt r) -> FileCxt (r { classes = classes }))

class LoadFile m where
   loadFileFromPath :: MonadError Error m => MonadAff m => File -> m (Maybe String)
   isDirectoryPath :: MonadError Error m => MonadAff m => File -> m Boolean
   loadManifest :: MonadError Error m => MonadAff m => Folder -> m (Maybe (Set File))

instance (Monoid w, MonadError Error m, MonadAff m, LoadFile m) => LoadFile (WriterT w m) where
   loadFileFromPath = lift <<< loadFileFromPath
   isDirectoryPath = lift <<< isDirectoryPath
   loadManifest = lift <<< loadManifest

instance (MonadAff m, MonadError Error m, LoadFile m) => LoadFile (StateT s m) where
   loadFileFromPath = lift <<< loadFileFromPath
   isDirectoryPath = lift <<< isDirectoryPath
   loadManifest = lift <<< loadManifest

instance LoadFile Aff where
   loadFileFromPath (File path) = do
      result <- runExceptT $ do
         resp × path' <- ExceptT $ liftAff $ requestPath
         when debug.logging $ liftAff $ log ("loadFileFromPath: resolved path: " <> path')
         pure resp.body
      pure $ either (const Nothing) Just result
      where
      requestPath :: Aff (Either A.Error (Response String × String))
      requestPath = do
         resp <- request (defaultRequest { url = path, method = Left GET, responseFormat = string })
         pure case resp of
            Right resp' | resp'.status == StatusCode 200 -> Right (resp' × path)
            Right _ -> Left A.RequestFailedError
            Left err -> Left err

   -- No reliable directory check over HTTP.
   isDirectoryPath _ = pure false

   loadManifest root = liftAff do
      resp <- request (defaultRequest { url = manifestPath, method = Left GET, responseFormat = json })
      pure case resp of
         Right resp' | resp'.status == StatusCode 200 ->
            Set.fromFoldable <<< map File <$> (hush (decodeJson resp'.body) :: Maybe (Array String))
         _ -> Nothing
      where
      File manifestPath = root </> manifestFile

newtype File = File String
newtype Folder = Folder String

derive instance Newtype File _
derive newtype instance Eq File
derive newtype instance Ord File
derive newtype instance Show File
derive newtype instance Semigroup File
derive newtype instance Monoid File
derive instance Newtype Folder _
derive newtype instance Eq Folder
derive newtype instance Ord Folder
derive newtype instance Show Folder

instance Semigroup Folder where
   append (Folder folder1) (Folder folder2) = Folder (folder1 <> "/" <> folder2)

prependFolder :: Folder -> File -> File
prependFolder (Folder folder) (File file) = File (folder <> "/" <> file)

infixr 5 prependFolder as </>

fluidExtension :: String
fluidExtension = ".fld"

-- Lists the .fld files under a source root, relative to the root
manifestFile :: File
manifestFile = File "manifest.json"

searchPaths :: Array Folder -> File -> Array File
searchPaths folders file = prependFolder <$> folders <*> [ file ]

loadManifests :: forall m. LoadFile m => MonadError Error m => MonadAff m => Array Folder -> m Manifests
loadManifests folders =
   Map.fromFoldable <<< catMaybes <$> for folders \folder -> loadManifest folder <#> map (folder × _)

withRoots :: forall m a. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> m a -> m a
withRoots roots m = do
   manifests <- loadManifests roots
   local (\(FileCxt cxt) -> FileCxt cxt { fluidSrcPaths = cxt.fluidSrcPaths <> roots, manifests = Map.union cxt.manifests manifests }) m

loadFileMaybe :: forall m. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> File -> m (Maybe String)
loadFileMaybe folders file = do
   FileCxt { manifests } <- ask
   foldM (step manifests) Nothing folders
   where
   step :: Manifests -> Maybe String -> Folder -> m (Maybe String)
   step _ (Just contents) _ = pure (Just contents)
   step manifests Nothing folder = case Map.lookup folder manifests of
      Just files | not (file ∈ files) -> pure Nothing
      _ -> loadFileFromPath (folder </> file)

loadFile :: forall m. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> File -> m String
loadFile folders file =
   loadFileMaybe folders file >>= orElse ("File not found in any path: " <> show (searchPaths folders file))

hasDirectory :: forall m. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> File -> m Boolean
hasDirectory folders (File dir) = do
   FileCxt { manifests } <- ask
   foldM (step manifests) false folders
   where
   step :: Manifests -> Boolean -> Folder -> m Boolean
   step _ true _ = pure true
   step manifests false folder = case Map.lookup folder manifests of
      Just files -> pure (any (\(File path) -> isJust (stripPrefix (Pattern (dir <> "/")) path)) files)
      Nothing -> isDirectoryPath (folder </> File dir)
