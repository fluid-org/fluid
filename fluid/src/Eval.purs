module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon)
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array ((..))
import Data.List (List(..), drop, find, foldM, foldl, length, take, unzip, zip, (:))
import Data.List.NonEmpty (NonEmptyList, last)
import Data.List.NonEmpty (head, snoc, unsnoc, fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Newtype (unwrap)
import Data.Int (toNumber)
import Data.Profunctor.Strong (first, (***))
import Data.Set (Set, insert)
import Data.Set as Set
import Data.Traversable (class Foldable, for, sequence, traverse)
import Data.Tuple (curry, fst, snd)
import DataType (class HasClasses, ClassTable, arity, askClasses, cCons, cNil, cPair, checkArity, fieldsOf, showCtr)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Def(..), Expr(..), Import(..), Module(..), RecDefs(..), Stmt(..), fv)
import File (class LoadFile, FileCxt, withClasses)
import Graph (class Graph, Vertex, op, selectαs, select𝔹s, showGraph, showVertices, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.Slice (bwdSlice)
import Graph.WithGraph (class MonadWithGraphAlloc, alloc, new, runAllocT, runWithGraphT_spy)
import Lattice (Raw, 𝔹)
import ModuleGraph (ModuleName, builtins)
import Pattern (ListRestPattern(..), Pattern(..))
import Pretty (prettyP)
import Primitive (intPair, string, unpack)
import Test.Util.Debug (checking, tracing)
import Util (type (×), Endo, absurd, check, definitely, definitely', error, orElse, singleton, spyFunWhen, throw, traceWhen, whenever, withMsg, (×), (⊆))
import Util.Map (delete, lookup, lookup', maplet, restrict, unionWith_never, (<+>))
import Util.Pair (unzip) as P
import Util.Set ((∪), empty)
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, moduleStore, modifyModuleStore, BaseVal, DictRep(..), Env(..), EnvStmt(..), ForeignOp(..), ForeignOp'(..), Fun, MatrixDim(..), MatrixRep(..), Result(..), Val(..), asReturns, forDefs, val)

-- Needs a better name.
type GraphConfig =
   { n :: Int
   , γ :: Env Vertex
   , classes :: ClassTable
   }

patternMismatch :: String -> String -> String
patternMismatch s s' = "Pattern mismatch: found " <> s <> ", expected " <> s'

-- Bindings if the pattern matches, with the vertices inspected either way.
matches :: forall m. MonadError Error m => Val Vertex -> Pattern -> m (Maybe (Env Vertex) × Set Vertex)
matches (Val α _ u) (PInt n) = literal α case u of
   V.Int n' -> n == n'
   V.Float x -> toNumber n == x
   _ -> false
matches (Val α _ u) (PFloat x) = literal α case u of
   V.Int n -> toNumber n == x
   V.Float x' -> x == x'
   _ -> false
matches (Val α _ u) (PStr s) = literal α case u of
   V.Str s' -> s == s'
   _ -> false
matches v (PVar x)
   | x == varAnon = pure (Just empty × empty)
   | otherwise = pure (Just (maplet x v) × empty)
matches _ PWild = pure (Just empty × empty)
matches v (PAs p x) = matches v p <#> first (map (_ `unionWith_never` maplet x v))
matches (Val α _ (V.Constr c' vs)) (PConstr c ps Nil)
   | c == c' = matchesMany vs ps <#> (insert α <$> _)
matches (Val α _ _) (PConstr _ _ _) = pure (Nothing × Set.singleton α)
matches (Val α _ (V.Dictionary (DictRep xvs))) (PRecord xps) =
   case traverse (\(x × p) -> lookup x (unwrap xvs) <#> \(_ × v) -> v × p) xps of
      Nothing -> pure (Nothing × Set.singleton α)
      Just vps -> matchesMany (fst <$> vps) (snd <$> vps) <#> (insert α <$> _)
matches (Val α _ _) (PRecord _) = pure (Nothing × Set.singleton α)
matches v PListEmpty = matchesTail v PListEnd
matches v (PListNonEmpty p rest) = matchesTail v (PListNext p rest)

-- Literal pattern inspects the value and binds nothing.
literal :: forall m. Monad m => Vertex -> Boolean -> m (Maybe (Env Vertex) × Set Vertex)
literal α eq = pure (whenever eq empty × Set.singleton α)

matchesTail :: forall m. MonadError Error m => Val Vertex -> ListRestPattern -> m (Maybe (Env Vertex) × Set Vertex)
matchesTail v (PListVar x) = matches v (PVar x)
matchesTail (Val α _ (V.Constr c vs)) rest
   | c == cNil = case rest of
        PListEnd -> pure (Just empty × Set.singleton α)
        _ -> pure (Nothing × Set.singleton α)
   | c == cCons, v : vs' : Nil <- vs = case rest of
        PListEnd -> pure (Nothing × Set.singleton α)
        PListNext p rest' -> do
           m × αs <- matches v p
           m' × αs' <- matchesTail vs' rest'
           pure (lift2 unionWith_never m m' × insert α (αs ∪ αs'))
        _ -> error absurd
matchesTail v@(Val _ _ (V.Constr c _)) _
   | c == cPair = throw (patternMismatch (prettyP v) "list")
matchesTail (Val α _ _) _ = pure (Nothing × Set.singleton α)

matchesMany :: forall m. MonadError Error m => List (Val Vertex) -> List Pattern -> m (Maybe (Env Vertex) × Set Vertex)
matchesMany Nil Nil = pure (Just empty × empty)
matchesMany (v : vs) (p : ps) = do
   m × αs <- matches v p
   m' × αs' <- matchesMany vs ps
   pure (lift2 unionWith_never m m' × (αs ∪ αs'))
matchesMany _ _ = error absurd

-- Bindings and body of the first case whose pattern matches, with the vertices inspected by every case tried.
dispatch
   :: forall m
    . MonadError Error m
   => Val Vertex
   -> NonEmptyList (Pattern × Stmt Vertex)
   -> m (Maybe (Env Vertex × Stmt Vertex) × Set Vertex)
dispatch v cases = go (NEL.toList cases) empty
   where
   go Nil αs = pure (Nothing × αs)
   go ((p × s) : cases') αs = do
      m × αs' <- matches v p
      case m of
         Just γ -> pure (Just (γ × s) × (αs ∪ αs'))
         Nothing -> go cases' (αs ∪ αs')

closeDefs :: forall m. HasClasses m => MonadWithGraphAlloc m => Env Vertex -> Dict (Def Vertex) -> Set Vertex -> m (Env Vertex)
closeDefs γ ρ αs =
   Env <$> for ρ \σ ->
      let
         ρ' = ρ `forDefs` σ
      in
         val Nothing αs (V.Fun (V.Closure (restrict (fv ρ' ∪ fv σ) γ) ρ' σ))

apply
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Maybe (Val Vertex)
   -> Val Vertex
   -> List (Val Vertex)
   -> m (Val Vertex)
apply doc_opt (Val α _ (V.Fun (V.Partial φ vs))) vs' = applyFun doc_opt α φ (vs <> vs')
apply doc_opt (Val α _ (V.Fun φ)) vs = applyFun doc_opt α φ vs
apply _ v _ = throw $ "Found " <> prettyP v <> ", expected function"

-- Fewer arguments than the arity is a partial application; more applies the result to the rest.
applyFun
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Maybe (Val Vertex)
   -> Vertex
   -> Fun Vertex
   -> List (Val Vertex)
   -> m (Val Vertex)
applyFun doc_opt α φ vs = do
   n <- arity'
   let k = length vs
   if k < n then val doc_opt (singleton α) (V.Fun (V.Partial φ vs))
   else if k == n then saturate doc_opt vs
   else saturate Nothing (take n vs) >>= \v -> apply doc_opt v (drop n vs)
   where
   arity' :: m Int
   arity' = case φ of
      V.Closure _ _ (Def xs _) -> pure (length xs)
      V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
      V.Type c -> askClasses >>= \λ -> maybe (throw $ "Unknown dataclass: " <> showCtr (last c)) pure (arity λ (dottedName c))
      V.Partial _ _ -> error absurd

   saturate :: Maybe (Val Vertex) -> List (Val Vertex) -> m (Val Vertex)
   saturate doc_opt' vs' = case φ of
      V.Closure γ1 ρ (Def xs s) -> do
         γ2 <- closeDefs γ1 ρ (singleton α)
         let γ3 = foldl (\γ (x × v) -> if x == varAnon then γ else γ `unionWith_never` maplet x v) empty (zip xs vs')
         asReturns <$> evalStmt doc_opt' (γ1 <+> γ2 <+> γ3) s (singleton α)
      V.Prim (ForeignOp (_ × ForeignOp' φ')) -> φ'.op doc_opt' vs'
      V.Type c -> val doc_opt' (singleton α) (V.Constr c vs')
      V.Partial _ _ -> error absurd

eval
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Maybe (Val Vertex) -- optional doc-comment context
   -> Env Vertex
   -> Expr Vertex
   -> Set Vertex
   -> m (Val Vertex)
eval doc_opt γ e0 αs = do
   αu_opt <- evalVal γ e0 αs
   case αu_opt of
      Just (α × u) ->
         new (flip Val doc_opt) (insert α αs) u
      Nothing -> case e0 of
         Var x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (variable " <> x <> ")"
            pure (definitely' (lookup x γ))
         Op op -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (operator " <> op <> ")"
            pure (definitely' (lookup op γ))
         Attribute e x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (attribute access)"
            v <- eval Nothing γ e αs
            case v of
               Val _ _ (V.Constr c vs) -> do
                  xs <- askClasses <#> \λ -> definitely' (fieldsOf λ (dottedName c))
                  find (\(k × _) -> k == x) (zip xs vs) <#> snd # orElse (dottedName c <> " has no field " <> x)
               _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected object"
         Subscript e e' -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (projection)"
            v <- eval Nothing γ e αs
            v' <- eval Nothing γ e' αs
            case v, v' of
               Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Str s) ->
                  withMsg "Dict lookup" $ snd <$> lookup s d # orElse ("Key \"" <> s <> "\" not found")
               Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP (unit <$ v') <> ", expected string"
               _, _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected dict"
         ModMember q x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (module member " <> x <> ")"
            { moduleEnv } <- moduleStore
            let γ_q = definitely "module loaded" (Map.lookup q moduleEnv)
            withMsg "Module member" $ lookup' x γ_q
         App e es -> do
            v <- eval Nothing γ e αs
            vs <- traverse (\e' -> eval Nothing γ e' αs) es
            withMsg ("In " <> funName e) $ apply doc_opt v vs
         DocExpr e e' -> do
            v <- eval Nothing γ e αs
            traceWhen (isJust doc_opt) "Outer doc trumps inner doc"
            eval (Just $ fromMaybe v doc_opt) γ e' αs
         _ -> error absurd
   where
   funName :: forall a. Expr a -> String
   funName (Var x) = x
   funName (Op op) = op
   funName (App e _) = funName e
   funName _ = "unknown"

evalStmt
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Maybe (Val Vertex)
   -> Env Vertex
   -> Stmt Vertex
   -> Set Vertex
   -> m (Result Vertex)
evalStmt doc_opt γ s αs = case s of
   Return e -> Returns <$> eval doc_opt γ e αs
   Match e cases -> do
      v <- eval Nothing γ e αs
      taken × αs' <- dispatch v cases
      case taken of
         Nothing -> pure (Assigns empty empty)
         Just (γ' × s') -> do
            r <- evalStmt doc_opt (γ <+> γ') s' (αs ∪ αs')
            case r of
               Returns _ -> pure r
               Assigns γ'' αs'' -> pure (Assigns (γ' <+> γ'') αs'')
   Assign p e -> do
      v <- eval Nothing γ e αs
      m × αs' <- matches v p
      case m of
         Nothing -> throw ("Pattern mismatch: " <> prettyP v <> " does not match " <> prettyP p)
         Just γ' -> pure (Assigns γ' αs')
   DefRec (RecDefs α ρ) -> do
      γ' <- closeDefs γ ρ (insert α αs)
      pure (Assigns γ' (insert α αs))
   Pass -> pure (Assigns empty empty)
   ExprStmt e -> do
      _ <- eval Nothing γ e αs
      pure (Assigns empty empty)
   Seq s1 s2 -> do
      r1 <- evalStmt Nothing γ s1 αs
      case r1 of
         Returns _ -> pure r1
         Assigns γ' αs' -> evalStmt doc_opt (γ <+> γ') s2 αs'

evalVal
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Env Vertex
   -> Expr Vertex
   -> Set Vertex
   -> m (Maybe (Vertex × BaseVal Vertex))
evalVal _ (Int α n) _ =
   pure $ Just (α × V.Int n)
evalVal _ (Float α n) _ =
   pure $ Just (α × V.Float n)
evalVal _ (Str α s) _ =
   pure $ Just (α × V.Str s)
evalVal γ (Dictionary α ees) αs = do
   vs × us <- traverse (traverse (flip (eval Nothing γ) αs)) ees <#> P.unzip
   let
      ss × βs = (vs <#> unpack string) # unzip
      d = D.fromFoldable $ zip ss (zip βs us)
   pure $ Just (α × V.Dictionary (DictRep d))
evalVal γ (Constr α c es) αs = do
   askClasses >>= \λ -> checkArity λ "construct" (dottedName c) (length es)
   vs <- traverse (flip (eval Nothing γ) αs) es
   pure $ Just (α × V.Constr c vs)
evalVal γ (Matrix α e (x × y) e') αs = do
   Val _ _ v <- eval Nothing γ e' αs
   let (i' × β) × (j' × β') = intPair.unpack v
   check
      (i' × j' >= 1 × 1)
      ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
   vss <- sequence do
      i <- 0 .. (i' - 1)
      singleton $ sequence do
         j <- 0 .. (j' - 1)
         let γ' = maplet x (Val β Nothing (V.Int i)) `unionWith_never` (maplet y (Val β' Nothing (V.Int j)))
         singleton (eval Nothing (γ <+> γ') e αs)
   pure $ Just (α × V.Matrix (MatrixRep (vss × MatrixDim (i' × β) × MatrixDim (j' × β'))))
evalVal γ (Lambda α σ) _ =
   pure $ Just (α × V.Fun (V.Closure (restrict (fv σ) γ) empty σ))
evalVal _ _ _ = pure Nothing

eval_module
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Env Vertex
   -> ModuleName
   -> Module Vertex
   -> Set Vertex
   -> m (Env Vertex)
eval_module γ0 q (Module is ss0) αs0 = do
   γ_imp <- foldM (evalImport q) γ0 is
   v_name <- val Nothing empty (V.Str (dottedName q))
   go γ_imp (maplet "__name__" v_name) ss0 αs0
   where
   go :: Env Vertex -> Env Vertex -> List (Stmt Vertex) -> Set Vertex -> m (Env Vertex)
   go _ γ' Nil _ = pure γ'
   go γ γ' (s : ss) αs = do
      r <- evalStmt Nothing (γ <+> γ') s αs
      case r of
         Assigns γ'' αs' -> go γ (γ' <+> γ'') ss αs'
         Returns _ -> error absurd

-- Bind imported value members; delete bindings for names that now denote modules.
evalImport
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => ModuleName
   -> Env Vertex
   -> Import
   -> m (Env Vertex)
evalImport enclosing γ = case _ of
   Import q Nothing -> do
      _ <- load q
      loadAncestors Nothing q
      pure (delete (NEL.head q) γ)
   Import q (Just xs) -> do
      γ_q <- load q
      loadAncestors (Just enclosing) q
      importsFrom q γ_q γ xs
   where
   loadAncestors bound q = case NEL.fromList (NEL.unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q γ_q = foldM step
      where
      step γ' x = case lookup x γ_q of
         Just v -> pure (γ' <+> maplet x v)
         Nothing -> do
            { moduleBody } <- moduleStore
            when (Map.member (NEL.snoc q x) moduleBody) (void (load (NEL.snoc q x)))
            pure (delete x γ')

loadPredefined
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Env Vertex
   -> Env Vertex
   -> ModuleName
   -> m (Env Vertex)
loadPredefined primitives γ q = do
   { moduleBody } <- moduleStore
   let native = if q == builtins then primitives else empty
   γ' <- maybe (pure empty) (\body -> eval_module (γ <+> native) q body empty) (Map.lookup q moduleBody)
   let members = native <+> γ'
   modifyModuleStore (\s -> s { moduleEnv = Map.insert q members s.moduleEnv })
   pure (γ <+> members)

load
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => ModuleName
   -> m (Env Vertex)
load q = do
   { moduleBody, moduleEnv, γ0 } <- moduleStore
   case Map.lookup q moduleEnv of
      Just γ -> pure γ
      Nothing -> do
         γ_q <- maybe (pure empty) (\body -> eval_module γ0 q body empty) (Map.lookup q moduleBody)
         modifyModuleStore (\s -> s { moduleEnv = Map.insert q γ_q s.moduleEnv })
         pure γ_q

type GraphEval g s t =
   { g :: g
   , graph_bwd :: Set Vertex -> Endo g
   , inα :: s Vertex
   , outα :: t Vertex
   }

withOp :: forall g s t. Graph g => GraphEval g s t -> GraphEval g t s
withOp { g, graph_bwd, inα, outα } =
   { g: op g, graph_bwd, inα: outα, outα: inα }

type ConjugatePair g s t =
   { fwd :: s 𝔹 -> t 𝔹 × g
   , bwd :: t 𝔹 -> s 𝔹 × g
   }

depsOf
   :: forall g s t
    . Graph g
   => Apply s
   => Apply t
   => Foldable s
   => Foldable t
   => GraphEval g s t
   -> ConjugatePair g s t
depsOf ge = { fwd: sliceBwd (withOp ge), bwd: sliceBwd ge }

sliceBwd
   :: forall g s t
    . Graph g
   => Apply s
   => Apply t
   => Foldable s
   => Foldable t
   => GraphEval g s t
   -> t 𝔹
   -> s 𝔹 × g
sliceBwd { g, graph_bwd, inα, outα } out𝔹 =
   let
      g' = graph_bwd (selectαs out𝔹 outα) g
   in
      select𝔹s inα (vertices g') × g'

graphEval
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadAff m
   => MonadReader FileCxt m
   => LoadFile m
   => MonadError Error m
   => GraphConfig
   -> Raw Stmt
   -> m (GraphEval GraphImpl EnvStmt Val)
graphEval { n, γ, classes } stmt =
   withClasses classes do
      { moduleBody, γ0, moduleEnv } <- moduleStore
      let mαs = Set.unions (vertices <$> Map.values moduleBody) ∪ vertices γ0 ∪ Set.unions (vertices <$> Map.values moduleEnv)
      _ × _ × g × inα × outα <- flip runAllocT n do
         sα <- alloc stmt
         let inα = EnvStmt γ sα
         g × outα <- runWithGraphT_spy (asReturns <$> evalStmt Nothing γ sα mempty) (vertices inα ∪ mαs)
         when checking.outputsInGraph $ check (vertices outα ⊆ vertices g) "outputs in graph"
         pure (g × inα × outα)
      pure { g, graph_bwd, inα, outα }
   where
   graph_bwd = curry (bwdSlice # spyFun' tracing.graphBwdSlice "bwdSlice")
   spyFun' b msg = spyFunWhen b msg (showVertices *** showGraph) showGraph
