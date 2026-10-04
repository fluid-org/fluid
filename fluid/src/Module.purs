module Module where

import Prelude

import Control.Monad.Except (class MonadError)
import Control.Monad.Reader (class MonadReader, ask)
import Control.Monad.State (runStateT)
import Bind (dottedName, pathName, prefixOf)
import Data.List.NonEmpty (snoc, unsnoc, fromList) as NEL
import Data.Either (Either(..))
import Data.Foldable (foldM, for_, intercalate)
import Data.List (List(..), catMaybes, elem, filter, mapMaybe, reverse, takeWhile, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (fst, snd)
import DataType (class HasClasses, ClassTable)
import Dict (Dict)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (GraphConfig, evalImport, load)
import Eval.Dep (evalImport, implicitMembers, load) as Dep
import Expr (Import(..)) as E
import Expr (Module, Stmt, fv)
import File (class LoadFile, File(..), FileCxt(..), fluidExtension, hasDirectory, loadFile, loadFileMaybe, withClasses)
import Graph (Vertex, vertices)
import Graph.Dep (Deriv, deriv, emptyGraph)
import Graph.GraphImpl (GraphImpl)
import Graph.WithGraph (AllocT, alloc, runAllocT, runWithGraphT_spy)
import Literal (Literal(..))
import ModuleGraph (DependencyGraph, ModuleName, implicit, implicitFor)
import Parse (parseModule, parseProgram)
import DefiniteAssignment (Cxt, Entry(..), erase)
import Primitive.Defs (predefined)
import WellFormed (LoadedModule, checkProgram, mainModule)
import SExpr as S
import Util (type (×), check, orThrow, throw, throwLeft, whenever, withMsg, (×))
import Util.Map (constMap, keys, findWithDefault, maplet, restrict, (<+>))
import Val (class HasModuleStore, moduleStore, modifyModuleStore, val, Env(..), Val(..))
import Val (BaseVal(..)) as V

type Config = { s :: S.Stmt, e :: Stmt, gconfig :: GraphConfig }

isModule :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => ModuleName -> m Boolean
isModule q = do
   FileCxt { fluidSrcPaths } <- ask
   loadFileMaybe fluidSrcPaths (File (pathName q <> fluidExtension)) >>= case _ of
      Just _ -> pure true
      Nothing -> hasDirectory fluidSrcPaths (File (pathName q))

parents :: ModuleName -> List ModuleName
parents q = case NEL.fromList (NEL.unsnoc q).init of
   Nothing -> Nil
   Just q' -> parents q' <> (q' : Nil)

importDeps
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => ModuleName
   -> S.Import
   -> m { edges :: List ModuleName, load :: List ModuleName }
importDeps enclosing (S.Import q f) = do
   ps <- keepModules (parents q)
   subs <- case f of
      Nothing -> pure Nil
      Just xs -> keepModules ((NEL.snoc q) <$> xs)
   let
      prefixEdges = case f of
         Nothing -> filter (_ /= enclosing) (parents q)
         Just _ -> filter (\p -> not (p `prefixOf` enclosing)) (parents q)
   pure { edges: (q : subs) <> prefixEdges, load: ps <> (q : subs) }
   where
   keepModules = map catMaybes <<< traverse (\m' -> isModule m' <#> \b -> whenever b m')

checkAcyclic :: DependencyGraph -> List ModuleName -> Either String Unit
checkAcyclic edges roots = void (foldM (go Nil) Set.empty roots)
   where
   go :: List ModuleName -> Set ModuleName -> ModuleName -> Either String (Set ModuleName)
   go path done q
      | Set.member q done = pure done
      | q `elem` path = Left
           ("import cycle: " <> intercalate " -> " (dottedName <$> (q : reverse (takeWhile (_ /= q) path)) <> (q : Nil)))
      | otherwise = Set.insert q <$> foldM (go (q : path)) done (findWithDefault Nil q edges)

classTable :: Map ModuleName Cxt -> ClassTable
classTable modCxt =
   Map.fromFoldable (map (\cls -> dottedName cls.name × cls) (Map.values modCxt >>= classValues))
   where
   classValues cxt = mapMaybe classOf (Map.values cxt)
   classOf = case _ of
      Class cls -> Just cls
      _ -> Nothing

allocTopLevel
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Map ModuleName Module
   -> List S.Import
   -> m (Int × Env Vertex)
allocTopLevel mods imports = do
   n × _ × ρ <- flip runAllocT 0 do
      predefined' <- traverse (alloc <<< snd) predefined
      let αs = Set.unions (vertices <$> Map.values predefined')
      _ × ρ <-
         runWithGraphT_spy
            ( do
                 modifyModuleStore (_ { moduleBody = mods, moduleEnvα = predefined' })
                 for_ implicit \q -> load q >>= \ρ_q -> modifyModuleStore (\s -> s { ρ0α = s.ρ0α <+> ρ_q })
                 { ρ0α } <- moduleStore
                 ρ1 <- foldM (\ρ (S.Import q f) -> evalImport mainModule ρ (E.Import q f)) ρ0α imports
                 vName <- val Nothing Set.empty (V.Lit (Str "__main__"))
                 pure (ρ1 <+> maplet "__name__" vName)
            )
            αs :: AllocT m (GraphImpl × _)
      pure ρ
   pure (n × ρ)

-- Load modules into a new dependence graph, kept in the store; return the top-level environment as a vertex per variable.
loadTopLevel
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => List S.Import
   -> m (Dict Deriv)
loadTopLevel imports = do
   inputs × depGraph <- flip runStateT emptyGraph do
      predefined' <- traverse (\(_ × Env ρ) -> traverse deriv ρ) predefined
      modifyModuleStore (_ { moduleEnv = predefined' })
      for_ implicit Dep.load
      ρ0 <- Dep.implicitMembers
      ρ1 <- foldM (\ρ (S.Import q f) -> Dep.evalImport mainModule ρ (E.Import q f)) ρ0 imports
      name <- deriv (Val unit Nothing (V.Lit (Str "__main__")))
      pure (ρ1 <+> maplet "__name__" name)
   modifyModuleStore (_ { depGraph = depGraph })
   pure inputs

prepConfig
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => String
   -> m Config
prepConfig fluidSrc = do
   s × imports <- throwLeft $ parseProgram fluidSrc
   mods <- parseModules imports
   { cxt: cxt_wf, s: e, loaded } <- orThrow (checkProgram mods (fst <$> predefined) imports s)
   let classes = classTable (_.cxt <$> loaded)
   withClasses classes do
      n × ρ <- allocTopLevel (Map.mapMaybe _.mod loaded) imports
      inputs <- loadTopLevel imports
      check (Map.keys cxt_wf == Set.fromFoldable (keys ρ)) "reduced context matches top-level environment"
      check (keys ρ == keys inputs) "top-level environment matches its derivations"
      { moduleEnvα, moduleEnv } <- moduleStore
      for_ (Map.toUnfoldable loaded :: List (ModuleName × LoadedModule)) \(q × { cxt, mod }) ->
         when (isJust mod) $ for_ (Map.lookup q moduleEnvα) \ρ_q -> do
            check (Map.keys (erase cxt) == Set.fromFoldable (keys ρ_q))
               ("module " <> dottedName q <> ": members match its environment")
            check (Just (keys ρ_q) == (keys <$> Map.lookup q moduleEnv))
               ("module " <> dottedName q <> ": members match their derivations")
      let gconfig = { n, ρ: restrict (fv e) ρ, inputs: restrict (fv e) inputs, classes }
      pure { s, e, gconfig }

parseModules
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => List S.Import
   -> m (Map ModuleName S.Module)
parseModules imports = do
   deps <- traverse (importDeps mainModule) imports
   let roots = implicit <> (deps >>= _.load)
   moduleDeps × mods <- collectModules Set.empty Map.empty Map.empty roots
   orThrow (checkAcyclic moduleDeps (deps >>= _.edges))
   -- prefix-closed: a package with no source file of its own is an empty module
   let ancestors = Set.fromFoldable ((Set.toUnfoldable (Map.keys mods) :: List ModuleName) >>= parents)
   pure (mods `Map.union` constMap (S.Module Nil Nil) ancestors)

   where

   collectModules
      :: Set ModuleName
      -> DependencyGraph
      -> Map ModuleName S.Module
      -> List ModuleName
      -> m (DependencyGraph × Map ModuleName S.Module)
   collectModules visited moduleDeps mods pending = case pending of
      Nil -> pure $ (moduleDeps × mods)
      mod : rest
         | Set.member mod visited -> collectModules visited moduleDeps mods rest
         | Map.member mod predefined -> do
              shadowed <- isModule mod
              when shadowed $ throw $ "Predefined module cannot have a source file: " <> dottedName mod
              collectModules (Set.insert mod visited) moduleDeps mods rest
         | otherwise -> do
              mod' × edges × toLoad <- parseAndCollect mod
              collectModules
                 (Set.insert mod visited)
                 (Map.insert mod edges moduleDeps)
                 (Map.insert mod mod' mods)
                 (toLoad <> rest)

   parseAndCollect :: ModuleName -> m (S.Module × List ModuleName × List ModuleName)
   parseAndCollect path = do
      FileCxt { fluidSrcPaths } <- ask
      let file = File (pathName path <> fluidExtension)
      loadFileMaybe fluidSrcPaths file >>= case _ of
         Just src -> do
            mod × _ <- throwLeft <#> withMsg ("Loading module " <> dottedName path) $ parseModule src
            deps <- case mod of S.Module is _ -> traverse (importDeps path) is
            let edges = deps >>= _.edges
            let toLoad = implicitFor path <> (deps >>= _.load)
            pure $ mod × edges × toLoad
         Nothing -> hasDirectory fluidSrcPaths (File (pathName path)) >>= case _ of
            true -> pure (S.Module Nil Nil × Nil × Nil)
            false -> loadFile fluidSrcPaths file *> pure (S.Module Nil Nil × Nil × Nil)
