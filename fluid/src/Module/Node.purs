module Module.Node where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, try)
import Control.Monad.Except (class MonadError, class MonadTrans, lift)
import Control.Monad.Reader (class MonadAsk, class MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.State (StateT, evalStateT, get, modify_)
import Data.Array (concat)
import Data.Either (Either(..), either)
import Data.Foldable (any)
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Set as Set
import Data.String (Pattern(..), stripSuffix)
import Data.Traversable (for)
import DataType (class HasClasses)
import Val (class HasModuleStore, ModuleStore, emptyModuleStore)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import File (class LoadFile, File(..), FileCxt(..), Folder(..), extensions)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile, readdir, stat)
import Node.FS.Stats (isDirectory, isFile)
import Util (throw)

instance Monad m => LoadFile (NodeT m) where
   loadFileFromPath (File path) = do
      stats <- liftAff $ try (stat path)
      case stats of
         Right s | isFile s -> Just <$> liftAff (readTextFile UTF8 path)
         _ -> pure Nothing
   loadManifest (Folder root) = liftAff do
      exists <- try (stat root) <#> either (const false) isDirectory
      unless exists $ throw ("Source root not found: " <> root)
      Set.fromFoldable <$> files Nothing
      where
      -- .fld files under the given subdirectory of root, relative to root
      files :: Maybe String -> Aff (Array File)
      files dir = do
         entries <- readdir (root <> maybe "" ("/" <> _) dir)
         concat <$> for entries \entry -> do
            let path = maybe entry (_ <> "/" <> entry) dir
            stats <- stat (root <> "/" <> path)
            if isDirectory stats then files (Just path)
            else pure (if any (\ext -> isJust (stripSuffix (Pattern ext) entry)) extensions then [ File path ] else [])

newtype NodeT m a = NodeT (ReaderT FileCxt (StateT ModuleStore m) a)

runNodeT :: forall m a. Monad m => FileCxt -> NodeT m a -> m a
runNodeT fileCxt (NodeT x) = evalStateT (runReaderT x fileCxt) emptyModuleStore

-- ======================
-- boilerplate
-- ======================

instance MonadTrans NodeT where
   lift m = NodeT (lift (lift m))

derive newtype instance Functor m => Functor (NodeT m)
derive newtype instance Monad m => Apply (NodeT m)
derive newtype instance Monad m => Applicative (NodeT m)
derive newtype instance Monad m => Bind (NodeT m)
derive newtype instance Monad m => Monad (NodeT m)
derive newtype instance MonadThrow Error m => MonadThrow Error (NodeT m)
derive newtype instance MonadError Error m => MonadError Error (NodeT m)
derive newtype instance MonadEffect m => MonadEffect (NodeT m)
derive newtype instance MonadAff m => MonadAff (NodeT m)
derive newtype instance Monad m => MonadAsk FileCxt (NodeT m)
derive newtype instance Monad m => MonadReader FileCxt (NodeT m)

instance Monad m => HasClasses (NodeT m) where
   askClasses = NodeT (ask <#> \(FileCxt { classes }) -> classes)

instance Monad m => HasModuleStore (NodeT m) where
   moduleStore = NodeT (lift get)
   modifyModuleStore f = NodeT (lift (modify_ f))
