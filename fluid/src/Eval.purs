module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon)
import Control.Alternative (guard)
import Control.Plus (empty) as Plus
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array ((..))
import Data.Foldable (oneOfMap)
import Data.List (List(..), drop, find, foldM, foldl, length, null, take, unzip, zip, (:))
import Data.List.NonEmpty (head, snoc, unsnoc, fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Newtype (unwrap)
import Data.Int (toNumber)
import Data.Profunctor.Strong (first, second, (***))
import Data.Set (Set, insert)
import Data.Set as Set
import Data.Traversable (class Foldable, for, sequence, traverse)
import Data.Tuple (curry, fst, snd)
import DataType (class HasClasses, ClassTable, askClasses, cCons, cNil, cPair, checkArity, ctrSig, fieldsOf)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Case, Def(..), Expr(..), Import(..), Module(..), Pattern(..), RecDefs(..), Stmt(..), fv)
import File (class LoadFile, FileCxt, withClasses)
import Graph (class Graph, Vertex, op, selectαs, select𝔹s, showGraph, showVertices, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.Slice (bwdSlice)
import Graph.WithGraph (class MonadWithGraphAlloc, alloc, new, runAllocT, runWithGraphT_spy)
import Lattice (Raw, 𝔹)
import ModuleGraph (ModuleName, builtins)
import Pretty (prettyP)
import Primitive (intPair, string, unpack)
import Test.Util.Debug (checking, tracing)
import Util (type (×), Endo, absurd, check, definitely, definitely', error, orElse, singleton, spyFunWhen, throw, traceWhen, withMsg, (×), (⊆))
import Util.Map (delete, lookup, lookup', maplet, restrict, unionWith_never, (<+>))
import Util.Pair (unzip) as P
import Util.Set ((∪), empty)
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, moduleStore, modifyModuleStore, BaseVal, DictRep(..), Env(..), EnvStmt(..), ForeignOp(..), ForeignOp'(..), MatrixDim(..), MatrixRep(..), Result(..), Val(..), asReturns, forDefs, val)

-- Needs a better name.
type GraphConfig =
   { n :: Int
   , ρ :: Env Vertex
   , classes :: ClassTable
   }

patternMismatch :: String -> String -> String
patternMismatch s s' = "Pattern mismatch: found " <> s <> ", expected " <> s'

-- Bindings if the pattern matches, with the vertices of the value that matching inspected.
matches :: forall m. MonadError Error m => Val Vertex -> Pattern -> MaybeT m (Env Vertex × Set Vertex)
matches (Val α _ u) (PInt n) = guard eq $> (empty × Set.singleton α)
   where
   eq = case u of
      V.Int n' -> n == n'
      V.Float x -> toNumber n == x
      _ -> false
matches (Val α _ u) (PFloat x) = guard eq $> (empty × Set.singleton α)
   where
   eq = case u of
      V.Int n -> toNumber n == x
      V.Float x' -> x == x'
      _ -> false
matches (Val α _ u) (PStr s) = guard eq $> (empty × Set.singleton α)
   where
   eq = case u of
      V.Str s' -> s == s'
      _ -> false
matches v (PVar x)
   | x == varAnon = pure (empty × empty)
   | otherwise = pure (maplet x v × empty)
matches _ PWild = pure (empty × empty)
matches v (PAs p x) = first (_ `unionWith_never` maplet x v) <$> matches v p
matches (Val α _ (V.Constr c' vs)) (PConstr c ps Nil)
   | c == c' = second (insert α) <$> matchesMany vs ps
matches _ (PConstr _ _ _) = Plus.empty
matches (Val α _ (V.Dictionary (DictRep xvs))) (PRecord xps) = do
   vps <- MaybeT $ pure $ traverse (\(x × p) -> lookup x (unwrap xvs) <#> \(_ × v) -> v × p) xps
   second (insert α) <$> matchesMany (fst <$> vps) (snd <$> vps)
matches _ (PRecord _) = Plus.empty
matches (Val α _ (V.Constr c vs)) (PList ps)
   | c == cNil = guard (null ps) $> (empty × Set.singleton α)
   | c == cCons, v : vs' : Nil <- vs = case ps of
        Nil -> Plus.empty
        p : ps' -> second (insert α) <$> matchesMany (v : vs' : Nil) (p : PList ps' : Nil)
   | c == cPair = throw (patternMismatch (prettyP (Val α Nothing (V.Constr c vs))) "list")
matches _ (PList _) = Plus.empty

matchesMany :: forall m. MonadError Error m => List (Val Vertex) -> List Pattern -> MaybeT m (Env Vertex × Set Vertex)
matchesMany Nil Nil = pure (empty × empty)
matchesMany (v : vs) (p : ps) = disjoint <$> matches v p <*> matchesMany vs ps
   where
   disjoint (ρ × αs) (ρ' × αs') = (ρ `unionWith_never` ρ') × (αs ∪ αs')
matchesMany _ _ = error absurd

-- Bindings, body and inspected vertices of the first case whose pattern matches.
dispatch :: forall m. MonadError Error m => Val Vertex -> List (Case Vertex) -> MaybeT m (Env Vertex × Stmt Vertex × Set Vertex)
dispatch v = oneOfMap \(p × s) -> (\(ρ × αs) -> ρ × s × αs) <$> matches v p

closeDefs :: forall m. HasClasses m => MonadWithGraphAlloc m => Env Vertex -> Dict (Def Vertex) -> Set Vertex -> m (Env Vertex)
closeDefs ρ ds αs =
   Env <$> for ds \d ->
      let
         ds' = ds `forDefs` d
      in
         val Nothing αs (V.Fun (V.Closure (restrict (fv ds' ∪ fv d) ρ) ds' d))

-- Fewer arguments than the arity is a partial application; more applies the result to the rest.
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
apply doc_opt (Val α _ (V.Fun (V.Partial φ vs))) vs' = apply doc_opt (Val α Nothing (V.Fun φ)) (vs <> vs')
apply doc_opt (Val α _ (V.Fun φ)) vs = do
   n <- arity'
   let k = length vs
   if k < n then val doc_opt (singleton α) (V.Fun (V.Partial φ vs))
   else if k == n then call doc_opt vs
   else call Nothing (take n vs) >>= \v -> apply doc_opt v (drop n vs)
   where
   arity' :: m Int
   arity' = case φ of
      V.Closure _ _ (Def xs _) -> pure (length xs)
      V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
      V.Type c -> askClasses >>= \λ -> ctrSig λ "construct" (dottedName c) <#> snd
      V.Partial _ _ -> error absurd

   call :: Maybe (Val Vertex) -> List (Val Vertex) -> m (Val Vertex)
   call doc_opt' vs' = case φ of
      V.Closure ρ1 ds (Def xs s) -> do
         ρ2 <- closeDefs ρ1 ds (singleton α)
         let ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip xs vs')
         asReturns <$> evalStmt doc_opt' (ρ1 <+> ρ2 <+> ρ3) s (singleton α)
      V.Prim (ForeignOp (_ × ForeignOp' φ')) -> φ'.op doc_opt' vs'
      V.Type c -> val doc_opt' (singleton α) (V.Constr c vs')
      V.Partial _ _ -> error absurd
apply _ v _ = throw $ "Found " <> prettyP v <> ", expected function"

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
eval doc_opt ρ e0 αs = do
   αu_opt <- evalVal ρ e0 αs
   case αu_opt of
      Just (α × u) ->
         new (flip Val doc_opt) (insert α αs) u
      Nothing -> case e0 of
         Var x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (variable " <> x <> ")"
            pure (definitely' (lookup x ρ))
         Op op -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (operator " <> op <> ")"
            pure (definitely' (lookup op ρ))
         Attribute e x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (attribute access)"
            v <- eval Nothing ρ e αs
            case v of
               Val _ _ (V.Constr c vs) -> do
                  xs <- askClasses <#> \λ -> definitely' (fieldsOf λ (dottedName c))
                  find (\(k × _) -> k == x) (zip xs vs) <#> snd # orElse (dottedName c <> " has no field " <> x)
               _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected object"
         Subscript e e' -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (projection)"
            v <- eval Nothing ρ e αs
            v' <- eval Nothing ρ e' αs
            case v, v' of
               Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Str s) ->
                  withMsg "Dict lookup" $ snd <$> lookup s d # orElse ("Key \"" <> s <> "\" not found")
               Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP (unit <$ v') <> ", expected string"
               _, _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected dict"
         ModMember q x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (module member " <> x <> ")"
            { moduleEnv } <- moduleStore
            let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
            withMsg "Module member" $ lookup' x ρ_q
         App e es -> do
            v <- eval Nothing ρ e αs
            vs <- traverse (\e' -> eval Nothing ρ e' αs) es
            withMsg ("In " <> funName e) $ apply doc_opt v vs
         DocExpr e e' -> do
            v <- eval Nothing ρ e αs
            traceWhen (isJust doc_opt) "Outer doc trumps inner doc"
            eval (Just $ fromMaybe v doc_opt) ρ e' αs
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
evalStmt doc_opt ρ s αs = case s of
   Return e -> Returns <$> eval doc_opt ρ e αs
   Match e bs -> do
      v <- eval Nothing ρ e αs
      runMaybeT (dispatch v (NEL.toList bs)) >>= case _ of
         Nothing -> pure (Assigns empty empty)
         Just (ρ' × s' × αs') -> do
            r <- evalStmt doc_opt (ρ <+> ρ') s' (αs ∪ αs')
            case r of
               Returns _ -> pure r
               Assigns ρ'' αs'' -> pure (Assigns (ρ' <+> ρ'') αs'')
   Assign p e -> do
      v <- eval Nothing ρ e αs
      runMaybeT (matches v p) >>= case _ of
         Nothing -> throw ("Pattern mismatch: " <> prettyP v <> " does not match " <> prettyP p)
         Just (ρ' × αs') -> pure (Assigns ρ' αs')
   DefRec (RecDefs α ds) -> do
      ρ' <- closeDefs ρ ds (insert α αs)
      pure (Assigns ρ' (insert α αs))
   Pass -> pure (Assigns empty empty)
   ExprStmt e -> do
      _ <- eval Nothing ρ e αs
      pure (Assigns empty empty)
   Seq s1 s2 -> do
      r1 <- evalStmt Nothing ρ s1 αs
      case r1 of
         Returns _ -> pure r1
         Assigns ρ' αs' -> evalStmt doc_opt (ρ <+> ρ') s2 αs'

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
evalVal ρ (Dictionary α ees) αs = do
   vs × us <- traverse (traverse (flip (eval Nothing ρ) αs)) ees <#> P.unzip
   let
      ss × βs = (vs <#> unpack string) # unzip
      d = D.fromFoldable $ zip ss (zip βs us)
   pure $ Just (α × V.Dictionary (DictRep d))
evalVal ρ (Constr α c es) αs = do
   askClasses >>= \λ -> checkArity λ "construct" (dottedName c) (length es)
   vs <- traverse (flip (eval Nothing ρ) αs) es
   pure $ Just (α × V.Constr c vs)
evalVal ρ (Matrix α e (x × y) e') αs = do
   Val _ _ v <- eval Nothing ρ e' αs
   let (i' × β) × (j' × β') = intPair.unpack v
   check
      (i' × j' >= 1 × 1)
      ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
   vss <- sequence do
      i <- 0 .. (i' - 1)
      singleton $ sequence do
         j <- 0 .. (j' - 1)
         let ρ' = maplet x (Val β Nothing (V.Int i)) `unionWith_never` (maplet y (Val β' Nothing (V.Int j)))
         singleton (eval Nothing (ρ <+> ρ') e αs)
   pure $ Just (α × V.Matrix (MatrixRep (vss × MatrixDim (i' × β) × MatrixDim (j' × β'))))
evalVal ρ (Lambda α d) _ =
   pure $ Just (α × V.Fun (V.Closure (restrict (fv d) ρ) empty d))
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
eval_module ρ0 q (Module is ss0) αs0 = do
   ρ_imp <- foldM (evalImport q) ρ0 is
   v_name <- val Nothing empty (V.Str (dottedName q))
   go ρ_imp (maplet "__name__" v_name) ss0 αs0
   where
   go :: Env Vertex -> Env Vertex -> List (Stmt Vertex) -> Set Vertex -> m (Env Vertex)
   go _ ρ' Nil _ = pure ρ'
   go ρ ρ' (s : ss) αs = do
      r <- evalStmt Nothing (ρ <+> ρ') s αs
      case r of
         Assigns ρ'' αs' -> go ρ (ρ' <+> ρ'') ss αs'
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
evalImport enclosing ρ = case _ of
   Import q Nothing -> do
      _ <- load q
      loadAncestors Nothing q
      pure (delete (NEL.head q) ρ)
   Import q (Just xs) -> do
      ρ_q <- load q
      loadAncestors (Just enclosing) q
      importsFrom q ρ_q ρ xs
   where
   loadAncestors bound q = case NEL.fromList (NEL.unsnoc q).init of
      Nothing -> pure unit
      Just q'
         | maybe false (q' `prefixOf` _) bound -> pure unit
         | otherwise -> void (load q') *> loadAncestors bound q'

   importsFrom q ρ_q = foldM step
      where
      step ρ' x = case lookup x ρ_q of
         Just v -> pure (ρ' <+> maplet x v)
         Nothing -> do
            { moduleBody } <- moduleStore
            when (Map.member (NEL.snoc q x) moduleBody) (void (load (NEL.snoc q x)))
            pure (delete x ρ')

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
loadPredefined primitives ρ q = do
   { moduleBody } <- moduleStore
   let native = if q == builtins then primitives else empty
   ρ' <- maybe (pure empty) (\body -> eval_module (ρ <+> native) q body empty) (Map.lookup q moduleBody)
   let members = native <+> ρ'
   modifyModuleStore (\s -> s { moduleEnv = Map.insert q members s.moduleEnv })
   pure (ρ <+> members)

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
   { moduleBody, moduleEnv, ρ0 } <- moduleStore
   case Map.lookup q moduleEnv of
      Just ρ -> pure ρ
      Nothing -> do
         ρ_q <- maybe (pure empty) (\body -> eval_module ρ0 q body empty) (Map.lookup q moduleBody)
         modifyModuleStore (\s -> s { moduleEnv = Map.insert q ρ_q s.moduleEnv })
         pure ρ_q

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
graphEval { n, ρ, classes } stmt =
   withClasses classes do
      { moduleBody, ρ0, moduleEnv } <- moduleStore
      let mαs = Set.unions (vertices <$> Map.values moduleBody) ∪ vertices ρ0 ∪ Set.unions (vertices <$> Map.values moduleEnv)
      _ × _ × g × inα × outα <- flip runAllocT n do
         sα <- alloc stmt
         let inα = EnvStmt ρ sα
         g × outα <- runWithGraphT_spy (asReturns <$> evalStmt Nothing ρ sα mempty) (vertices inα ∪ mαs)
         when checking.outputsInGraph $ check (vertices outα ⊆ vertices g) "outputs in graph"
         pure (g × inα × outα)
      pure { g, graph_bwd, inα, outα }
   where
   graph_bwd = curry (bwdSlice # spyFun' tracing.graphBwdSlice "bwdSlice")
   spyFun' b msg = spyFunWhen b msg (showVertices *** showGraph) showGraph
