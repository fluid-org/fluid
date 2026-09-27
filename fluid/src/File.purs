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
import Data.Argonaut.Decode (JsonDecodeError, decodeJson)
import Data.Either (Either(..), either)
import Data.HTTP.Method (Method(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), stripPrefix)
import Data.Foldable (any, find)
import Data.Traversable (for)
import DataType (ClassTable)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class.Console (log)
import Effect.Exception (Error)
import Util (type (×), (×), debug, definitely, orElse, throw, throwLeft)
import Util.Set ((∈))

-- Files under each source root
type Manifests = Map Folder (Set File)

newtype FileCxt = FileCxt { fluidSrcPaths :: Array Folder, manifests :: Manifests, classes :: ClassTable }

emptyFileCxt :: FileCxt
emptyFileCxt = FileCxt { fluidSrcPaths: [], manifests: Map.empty, classes: Map.empty }

withClasses :: forall m a. MonadReader FileCxt m => ClassTable -> m a -> m a
withClasses classes = local (\(FileCxt r) -> FileCxt (r { classes = classes }))

class LoadFile m where
   loadFileFromPath :: MonadError Error m => MonadAff m => File -> m (Maybe String)
   loadManifest :: MonadError Error m => MonadAff m => Folder -> m (Set File)

instance (Monoid w, MonadError Error m, MonadAff m, LoadFile m) => LoadFile (WriterT w m) where
   loadFileFromPath = lift <<< loadFileFromPath
   loadManifest = lift <<< loadManifest

instance (MonadAff m, MonadError Error m, LoadFile m) => LoadFile (StateT s m) where
   loadFileFromPath = lift <<< loadFileFromPath
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

   loadManifest root = do
      resp <- liftAff $ request (defaultRequest { url = manifestPath, method = Left GET, responseFormat = json })
      case resp of
         Right resp' | resp'.status == StatusCode 200 -> do
            paths <- throwLeft (decodeJson resp'.body :: Either JsonDecodeError (Array String))
            pure (Set.fromFoldable (File <$> paths))
         _ -> throw ("No " <> manifestPath)
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

withRoots :: forall m a. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> m a -> m a
withRoots roots m = do
   manifests <- Map.fromFoldable <$> for roots \root -> (root × _) <$> loadManifest root
   local (\(FileCxt cxt) -> FileCxt cxt { fluidSrcPaths = cxt.fluidSrcPaths <> roots, manifests = Map.union cxt.manifests manifests }) m

manifest :: Folder -> Manifests -> Set File
manifest root = Map.lookup root >>> definitely ("Manifest for " <> show root)

loadFileMaybe :: forall m. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> File -> m (Maybe String)
loadFileMaybe folders file = do
   FileCxt { manifests } <- ask
   case find (\folder -> file ∈ manifest folder manifests) folders of
      Nothing -> pure Nothing
      Just folder -> loadFileFromPath (folder </> file)

loadFile :: forall m. LoadFile m => MonadError Error m => MonadAff m => MonadReader FileCxt m => Array Folder -> File -> m String
loadFile folders file =
   loadFileMaybe folders file >>= orElse ("File not found in any path: " <> show (searchPaths folders file))

hasDirectory :: forall m. MonadReader FileCxt m => Array Folder -> File -> m Boolean
hasDirectory folders (File dir) = ask <#> \(FileCxt { manifests }) ->
   any (\folder -> any (\(File path) -> isJust (stripPrefix (Pattern (dir <> "/")) path)) (manifest folder manifests)) folders
