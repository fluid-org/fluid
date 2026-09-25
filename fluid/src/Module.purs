module Module where

import Prelude

import Control.Monad.Except (class MonadError)
import Control.Monad.Reader (class MonadReader, ask)
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
import DataType (class HasClasses, ClassTable)
import Desugarable (desug)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (GraphConfig, evalImport, loadPredefined)
import Expr (Import(..)) as E
import Expr (Module, Stmt, fv)
import File (class LoadFile, File(..), FileCxt(..), fluidExtension, hasDirectory, loadFile, loadFileMaybe, withClasses)
import Graph (Vertex, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.WithGraph (AllocT, alloc, runAllocT, runWithGraphT_spy)
import Lattice (Raw)
import ModuleGraph (DependencyGraph, ModuleName, predefined, predefinedDeps)
import Parse (parseModule, parseProgram)
import SExpr (desugarModule)
import DefiniteAssignment (Cxt, Entry(..), WfResult(..), erase)
import WellFormed (LoadedModule, checkProgram, mainModule)
import SExpr as S
import Util (type (×), check, orThrow, throwLeft, whenever, withMsg, (×))
import Util.Map (constMap, keys, findWithDefault, maplet, restrict, (<+>))
import Util.Set (empty, (∪))
import Val (class HasModuleStore, moduleStore, modifyModuleStore, val, Env)
import Val (BaseVal(..)) as V

type Config = { s :: Raw S.Stmt, e :: Raw Stmt, gconfig :: GraphConfig }

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
   => Raw Env
   -> Map ModuleName (Raw Module)
   -> List S.Import
   -> m (Int × Env Vertex)
allocTopLevel primitives mods imports = do
   n × _ × ρ <- flip runAllocT 0 do
      primitives' <- alloc primitives
      mods' <- traverse alloc mods
      let mαs = Set.unions (vertices <$> Map.values mods')
      _ × ρ <-
         runWithGraphT_spy
            ( do
                 modifyModuleStore (_ { moduleBody = mods' })
                 ρ0 <- foldM (loadPredefined primitives') empty predefined
                 modifyModuleStore (_ { ρ0 = ρ0 })
                 ρ1 <- foldM (\ρ (S.Import q f) -> evalImport mainModule ρ (E.Import q f)) ρ0 imports
                 vName <- val Nothing Set.empty (V.Str "__main__")
                 pure (ρ1 <+> maplet "__name__" vName)
            )
            (vertices primitives' ∪ mαs) :: AllocT m (GraphImpl × _)
      pure ρ
   pure (n × ρ)

prepConfig
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Raw Env
   -> String
   -> m Config
prepConfig primitives fluidSrc = do
   s × imports <- throwLeft $ parseProgram fluidSrc
   let primitivesCxt = constMap (VarStatus true) (keys primitives)
   mods <- parseModules imports
   { cxt: cxt_wf, s: s_wf, loaded } <- orThrow (checkProgram mods primitivesCxt imports s)
   let classes = classTable (_.cxt <$> loaded)
   withClasses classes do
      desugaredMods <- traverse (\m -> (unit <$ _) <$> desugarModule (Returns <$ m)) (Map.mapMaybe _.mod loaded)
      n × ρ <- allocTopLevel primitives desugaredMods imports
      check (Map.keys cxt_wf == Set.fromFoldable (keys ρ)) "reduced context matches top-level environment"
      { moduleEnv } <- moduleStore
      for_ (Map.toUnfoldable loaded :: List (ModuleName × LoadedModule)) \(q × { cxt, mod }) ->
         when (isJust mod) $ for_ (Map.lookup q moduleEnv) \ρ_q ->
            check (Map.keys (erase cxt) == Set.fromFoldable (keys ρ_q))
               ("module " <> dottedName q <> ": members match its environment")
      e_wf <- desug s_wf
      let e = (unit <$ e_wf) :: Raw Stmt
      let gconfig = { n, ρ: restrict (fv e) ρ, classes }
      pure { s, e, gconfig }

parseModules
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => List S.Import
   -> m (Map ModuleName (Raw S.Module))
parseModules imports = do
   deps <- traverse (importDeps mainModule) imports
   let roots = predefined <> (deps >>= _.load)
   depGraph × mods <- collectModules Set.empty Map.empty Map.empty roots
   orThrow (checkAcyclic depGraph (deps >>= _.edges))
   -- prefix-closed: a package with no source file of its own is an empty module
   let ancestors = Set.fromFoldable ((Set.toUnfoldable (Map.keys mods) :: List ModuleName) >>= parents)
   pure (mods `Map.union` constMap (S.Module Nil Nil) ancestors)

   where

   collectModules
      :: Set ModuleName
      -> DependencyGraph
      -> Map ModuleName (Raw S.Module)
      -> List ModuleName
      -> m (DependencyGraph × Map ModuleName (Raw S.Module))
   collectModules visited depGraph mods pending = case pending of
      Nil -> pure $ (depGraph × mods)
      mod : rest ->
         if Set.member mod visited then
            collectModules visited depGraph mods rest
         else do
            mod' × edges × toLoad <- parseAndCollect mod
            collectModules
               (Set.insert mod visited)
               (Map.insert mod edges depGraph)
               (Map.insert mod mod' mods)
               (toLoad <> rest)

   parseAndCollect :: ModuleName -> m (Raw S.Module × List ModuleName × List ModuleName)
   parseAndCollect path = do
      FileCxt { fluidSrcPaths } <- ask
      let file = File (pathName path <> fluidExtension)
      loadFileMaybe fluidSrcPaths file >>= case _ of
         Just src -> do
            mod × _ <- throwLeft <#> withMsg ("Loading module " <> dottedName path) $ parseModule src
            deps <- case mod of S.Module is _ -> traverse (importDeps path) is
            let edges = deps >>= _.edges
            let toLoad = predefinedDeps path <> (deps >>= _.load)
            pure $ mod × edges × toLoad
         Nothing -> hasDirectory fluidSrcPaths (File (pathName path)) >>= case _ of
            true -> pure (S.Module Nil Nil × Nil × Nil)
            false -> loadFile fluidSrcPaths file *> pure (S.Module Nil Nil × Nil × Nil)
