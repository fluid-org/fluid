module Module where

import Prelude

import Control.Monad.Except (class MonadError)
import Control.Monad.Reader (class MonadReader, ask)
import Data.List (List(..), reverse, (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Desugarable (desug)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (GraphConfig, eval_primitives)
import Expr (Module, Stmt, fv, stripDocModule, stripDocStmt)
import File (class LoadFile, File(..), FileCxt(..), fluidExtension, loadFile)
import Graph (vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.WithGraph (AllocT, alloc, runAllocT, runWithGraphT_spy)
import Lattice (Raw)
import ModuleGraph (DependencyGraph, ModuleCxt, Modules, ModuleName)
import Parse (parseModule, parseProgram)
import DefiniteAssignment (TyResult(..))
import SExpr (desugarModuleFwd)
import WellFormed (checkModule, checkProgram)
import SExpr as S
import Util (type (×), error, throwLeft, withMsg, (×))
import Util.Map (keys, restrict)
import Util.Set ((∪))
import Val (Env)

type Config = { s :: Raw S.Stmt, e :: Raw Stmt, gconfig :: GraphConfig }

prelude :: ModuleName
prelude = "lib/prelude"

prepConfig :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Raw Env -> String -> m Config
prepConfig = prepConfigWith identity identity

prepConfigNoDoc :: forall m. MonadAff m => MonadError Error m => MonadReader FileCxt m => LoadFile m => Raw Env -> String -> m Config
prepConfigNoDoc = prepConfigWith stripDocModule stripDocStmt

prepConfigWith
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => (Raw Module -> Raw Module)
   -> (Raw Stmt -> Raw Stmt)
   -> Raw Env
   -> String
   -> m Config
prepConfigWith stripMod stripStmt primitives fluidSrc = do
   s × imports <- throwLeft $ parseProgram fluidSrc
   moduleCxt0 <- loadModuleGraph (prelude : imports)
   let moduleCxt = moduleCxt0 { modules = stripMod <$> moduleCxt0.modules }
   n × _ × primitives' × _ × topLevelEnv <- flip runAllocT 0 do
      primitives' <- alloc primitives
      modules' <- traverse alloc (moduleCxt.modules)
      let moduleCxt' = moduleCxt { modules = modules' }
      let mαs = Set.unions (vertices <$> Map.values modules')
      let αs = vertices primitives' ∪ mαs
      _ × γ <- runWithGraphT_spy (eval_primitives primitives' moduleCxt') αs :: AllocT m (GraphImpl × _)
      pure (primitives' × modules' × γ)
   sty <- checkProgram (keys topLevelEnv) s
   eTy <- desug sty
   let e = stripStmt ((unit <$ eTy) :: Raw Stmt)
   let gconfig = { n, primitives: primitives', γ: restrict (fv e) topLevelEnv }
   pure { s, e, gconfig }

loadModuleGraph
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => List ModuleName
   -> m (Raw ModuleCxt)
loadModuleGraph roots = do
   graph × modules <- collectModules Set.empty Map.empty Map.empty roots
   pure $ { roots, topsorted: topsort graph, graph, modules }

   where

   collectModules :: Set ModuleName -> DependencyGraph -> Raw Modules -> List ModuleName -> m (DependencyGraph × Raw Modules)
   collectModules visited graph modules imports = case imports of
      Nil -> pure $ (graph × modules)
      mod : rest ->
         if Set.member mod visited then
            collectModules visited graph modules rest
         else do
            mod' × imports' <- loadModule mod
            collectModules
               (Set.insert mod visited)
               (Map.insert mod imports' graph)
               (Map.insert mod mod' modules)
               (imports' <> rest)

   loadModule :: ModuleName -> m (Raw Module × List ModuleName)
   loadModule path = do
      FileCxt { fluidSrcPaths } <- ask
      src <- loadFile fluidSrcPaths (File (path <> fluidExtension))
      mod × imports <- throwLeft <#> withMsg ("Loading module " <> path) $ parseModule src
      checkModule mod
      modTy <- desugarModuleFwd (Returns <$ mod)
      let mod' = (unit <$ modTy) :: Raw Module
      let imports' = if path == prelude then imports else prelude : imports
      pure $ mod' × imports'

   topsort :: DependencyGraph -> List ModuleName
   topsort graph = go (List.fromFoldable $ Map.keys graph) Nil
      where
      go :: List ModuleName -> List ModuleName -> List ModuleName
      go Nil result = reverse result
      go remaining result =
         -- should always be resolvable if no cycles
         case List.find resolved remaining of
            Nothing -> error "Modules contain circular imports"
            Just next -> go (List.delete next remaining) (next : result)
         where
         -- no dependencies or dependencies all resolved
         resolved :: ModuleName -> Boolean
         resolved mod = case Map.lookup mod graph of
            Nothing -> true
            Just deps -> List.all (\dep -> not (List.elem dep remaining)) deps
