module Module.Node where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, try)
import Control.Monad.Except (class MonadError, class MonadTrans, lift)
import Control.Monad.Reader (class MonadAsk, class MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.State (StateT, evalStateT, get, modify_)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import DataType (class HasClasses)
import Val (class HasModuleStore, ModuleStore, emptyModuleStore)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import File (class LoadFile, File(..), FileCxt(..))
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile, stat)
import Node.FS.Stats (isDirectory, isFile)

instance Monad m => LoadFile (NodeT m) where
   loadFileFromPath (File path) = do
      stats <- liftAff $ try (stat path)
      case stats of
         Right s | isFile s -> Just <$> liftAff (readTextFile UTF8 path)
         _ -> pure Nothing
   isDirectoryPath (File path) = do
      stats <- liftAff $ try (stat path)
      pure case stats of
         Right s | isDirectory s -> true
         _ -> false
   loadManifest _ = pure Nothing

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
