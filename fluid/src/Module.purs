module Module where

import Prelude

import Control.Monad.Except (class MonadError, ExceptT, except, runExceptT)
import Control.Monad.Reader (ask)
import Control.Monad.State (runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (lmap)
import Bind (dottedName, pathName, varName)
import Data.List.NonEmpty (snoc)
import Data.Either (Either(..), either)
import Data.Foldable (foldM, for_, intercalate)
import Data.List (List(..), catMaybes, elem, filter, mapMaybe, reverse, takeWhile, (:))
import Data.List as List
import Data.List.NonEmpty as NEL
import Data.String (Pattern(..), split)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (fst)
import Classes (class HasClasses, ClassTable)
import Dict (Dict)
import Effect.Exception (Error)
import Eval (evalImport, implicitMembers, load) as Dep
import Expr (Import(..)) as E
import Literal (Literal(..))
import Expr (Module, Pattern(..), Stmt, fv)
import File (class MonadLoad, File(..), FileCxt(..), hasDirectory, loadModuleSource, manifest, modulePath, withClasses)
import DepGraph (Deriv, deriv, emptyGraph)
import Module.Defs (ModuleName, containing, implicit, implicitFor, parents)
import Parse (parseModule, parseProgram)
import Primitive.Defs (predefined, predefinedClasses)
import WellFormed (CheckM, checkProgram, checkModule, mainModule, runCheckM)
import SExpr as S
import Types (Primitive(..)) as T
import Util (MayFail, type (×), orThrow, quoted, throw, whenever, (×))
import Util.Map (constMap, findWithDefault, mapWithKey, restrict)
import Val (class HasModuleStore, ModuleState(..), modifyModuleStore, Env(..))

type DependencyGraph = Map ModuleName (List ModuleName)

type Config = { s :: S.Stmt, e :: Stmt, inputs :: Dict Deriv, classes :: ClassTable }

-- Message for source of program or module that fails to parse
newtype ParseFailure = ParseFailure String

throwParseFailure :: forall m a. MonadError Error m => ExceptT ParseFailure m a -> m a
throwParseFailure m = runExceptT m >>= either (\(ParseFailure msg) -> throw msg) pure

isModule :: forall m. MonadLoad m => ModuleName -> m Boolean
isModule q = do
   FileCxt { fluidSrcPaths } <- ask
   loadModuleSource fluidSrcPaths (pathName q) >>= case _ of
      Just _ -> pure true
      Nothing -> hasDirectory fluidSrcPaths (File (pathName q))

importDeps
   :: forall m
    . MonadLoad m
   => ModuleName
   -> S.Import
   -> m { edges :: List ModuleName, load :: List ModuleName }
importDeps enclosing (S.Import q f) = do
   ps <- keepModules (parents q)
   subs <- case f of
      Nothing -> pure Nil
      Just xs -> keepModules ((snoc q) <$> xs)
   let
      prefixEdges = case f of
         Nothing -> filter (_ /= enclosing) (parents q)
         Just _ -> containing enclosing q
   pure { edges: (q : subs) <> prefixEdges, load: ps <> (q : subs) }
   where
   keepModules = map catMaybes <<< traverse (\m' -> isModule m' <#> \b -> whenever b m')

checkAcyclic :: DependencyGraph -> List ModuleName -> MayFail Unit
checkAcyclic edges roots = void (foldM (go Nil) Set.empty roots)
   where
   go :: List ModuleName -> Set ModuleName -> ModuleName -> MayFail (Set ModuleName)
   go path done q
      | Set.member q done = pure done
      | q `elem` path = Left
           ("import cycle: " <> intercalate " -> " (quoted <<< dottedName <$> (q : reverse (takeWhile (_ /= q) path)) <> (q : Nil)))
      | otherwise = Set.insert q <$> foldM (go (q : path)) done (findWithDefault Nil q edges)

-- Load modules into new dependence graph, kept in module store; return top-level environment as vertex per variable
loadTopLevel
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadLoad m
   => Map ModuleName Module
   -> List S.Import
   -> m (Dict Deriv)
loadTopLevel modules imports = do
   inputs × depGraph <- flip runStateT emptyGraph do
      predefined' <- traverse (\(_ × Env ρ) -> Loaded <$> traverse deriv ρ) predefined
      modifyModuleStore (_ { modules = Map.union predefined' (Parsed <$> modules) })
      for_ implicit Dep.load
      ρ0 <- Dep.implicitMembers
      foldM (\ρ (S.Import q f) -> Dep.evalImport mainModule ρ (E.Import q f)) ρ0 imports
   modifyModuleStore (_ { depGraph = depGraph })
   pure inputs

prepConfig
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadLoad m
   => String
   -> ExceptT ParseFailure m Config
prepConfig fluidSrc = do
   s × imports <- except (lmap ParseFailure (parseProgram fluidSrc))
   { result: e, modules: mods, classes } <- prepModules imports (checkProgram imports (named mainModule s))
   lift $ withClasses classes do
      inputs <- loadTopLevel mods imports
      pure { s, e, inputs: restrict (fv e) inputs, classes }

-- Statement preceded by declaration of module name
named :: ModuleName -> S.Stmt -> S.Stmt
named q = S.Seq (S.Def (S.VarDef (PVar varName) (Just (S.PrimitiveTy T.Str)) (S.Lit (Str (dottedName q)))))

-- Parse modules reachable through imports and run checking action over them, yielding its result, modules
-- checked, and class table.
prepModules
   :: forall m a
    . MonadLoad m
   => List S.Import
   -> CheckM a
   -> ExceptT ParseFailure m { result :: a, modules :: Map ModuleName Module, classes :: ClassTable }
prepModules imports action = do
   mods <- parseModules imports
   names <- moduleNames <$> ask
   result × { modules: checked, classes } <-
      lift (orThrow (runCheckM action mods names (fst <$> predefined) predefinedClasses))
   pure { result, modules: Map.mapMaybe _.mod checked, classes }

-- Names of modules with source under source roots, and of their containing modules
moduleNames :: FileCxt -> Set ModuleName
moduleNames (FileCxt { fluidSrcPaths, manifests }) = Set.fromFoldable (qs >>= \q -> q : parents q)
   where
   qs = List.fromFoldable (fluidSrcPaths >>= \root -> Set.toUnfoldable (manifest root manifests))
      # mapMaybe (modulePath >=> split (Pattern "/") >>> NEL.fromFoldable)

-- Module q checked as module, not program, with modules it imports.
prepModule
   :: forall m
    . MonadLoad m
   => ModuleName
   -> ExceptT ParseFailure m { modules :: Map ModuleName Module, classes :: ClassTable }
prepModule q = prepModules (S.Import q Nothing : Nil) (checkModule q) <#> \{ modules, classes } -> { modules, classes }

parseModules :: forall m. MonadLoad m => List S.Import -> ExceptT ParseFailure m (Map ModuleName S.Module)
parseModules imports = do
   deps <- lift (traverse (importDeps mainModule) imports)
   let roots = implicit <> (deps >>= _.load)
   moduleDeps × mods <- collectModules Set.empty Map.empty Map.empty roots
   lift (orThrow (checkAcyclic moduleDeps (deps >>= _.edges)))
   -- every containing module of loaded module present, and empty if without source file
   let ancestors = Set.fromFoldable ((Set.toUnfoldable (Map.keys mods) :: List ModuleName) >>= parents)
   pure (mapWithKey (\q (S.Module ιs s) -> S.Module ιs (named q s)) (mods `Map.union` constMap (S.Module Nil S.Pass) ancestors))

   where
   collectModules
      :: Set ModuleName
      -> DependencyGraph
      -> Map ModuleName S.Module
      -> List ModuleName
      -> ExceptT ParseFailure m (DependencyGraph × Map ModuleName S.Module)
   collectModules visited moduleDeps mods pending = case pending of
      Nil -> pure $ (moduleDeps × mods)
      mod : rest
         | Set.member mod visited -> collectModules visited moduleDeps mods rest
         | Map.member mod predefined -> do
              shadowed <- lift (isModule mod)
              when shadowed $ lift $ throw $ "Predefined module cannot have a source file: " <> quoted (dottedName mod)
              collectModules (Set.insert mod visited) moduleDeps mods rest
         | otherwise -> do
              mod' × edges × toLoad <- parseAndCollect mod
              collectModules
                 (Set.insert mod visited)
                 (Map.insert mod edges moduleDeps)
                 (Map.insert mod mod' mods)
                 (toLoad <> rest)

   parseAndCollect :: ModuleName -> ExceptT ParseFailure m (S.Module × List ModuleName × List ModuleName)
   parseAndCollect path = do
      FileCxt { fluidSrcPaths } <- ask
      lift (loadModuleSource fluidSrcPaths (pathName path)) >>= case _ of
         Just src -> do
            mod × _ <- except (lmap (\msg -> ParseFailure (msg <> "\nLoading module " <> quoted (dottedName path))) (parseModule src))
            deps <- lift case mod of S.Module ιs _ -> traverse (importDeps path) ιs
            pure (mod × (deps >>= _.edges) × (implicitFor path <> (deps >>= _.load)))
         Nothing -> lift (hasDirectory fluidSrcPaths (File (pathName path))) >>= case _ of
            true -> pure (S.Module Nil S.Pass × Nil × Nil)
            false -> lift (throw ("No module named " <> quoted (dottedName path)))
