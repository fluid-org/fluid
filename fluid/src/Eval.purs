module Eval where

import Prelude hiding (absurd, apply)

import Bind (dottedName, prefixOf, varAnon)
import Control.Alternative (guard)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array ((..))
import Data.Array as A
import Data.Foldable (elem, oneOfMap)
import Data.List (List(..), concat, drop, find, foldM, foldl, length, take, unzip, zip, (:))
import Data.List as L
import Data.List.NonEmpty (head, snoc, unsnoc, fromList, toList) as NEL
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Newtype (unwrap)
import Data.Profunctor.Strong (first, second, (***))
import Data.Set (Set, insert)
import Data.Set as Set
import Data.Traversable (class Foldable, for, sequence, traverse)
import Data.Tuple (curry, fst, snd)
import DataType (class HasClasses, ClassTable, arity, askClasses, cPair, checkArity, fieldsOf)
import DefiniteAssignment (ancestors)
import Dict (Dict)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Branch(..), Case, Def(..), Expr(..), Import(..), Module(..), Pattern(..), Qualifier(..), RecDefs(..), Stmt(..), fv, paramVar)
import File (class LoadFile, FileCxt, withClasses)
import Graph (class Graph, Vertex, op, selectαs, select𝔹s, showGraph, showVertices, vertices)
import Graph.GraphImpl (GraphImpl)
import Graph.Slice (bwdSlice)
import Graph.WithGraph (class MonadWithGraphAlloc, alloc, new, runAllocT, runWithGraphT_spy)
import Literal (Literal(..), eqLiteral)
import Lattice (Raw, 𝔹)
import ModuleGraph (ModuleName)
import Pretty (prettyP)
import Operator (binopSymbol, unopSymbol)
import Primitive (binop, boolean, intPair, string, unop, unpack)
import Test.Util.Debug (checking, tracing)
import Util (type (×), Endo, absurd, check, definitely, definitely', error, orElse, orThrow, singleton, spyFunWhen, throw, traceWhen, withMsg, (×), (⊆))
import Util.Map (delete, lookup, lookup', maplet, restrict, unionWith_never, (<+>))
import Util.Pair (unzip) as P
import Util.Set ((∪), empty)
import Val (BaseVal(..), Fun(..)) as V
import Val (class HasModuleStore, class Highlightable, moduleStore, modifyModuleStore, BaseVal, DictRep(..), Env(..), EnvStmt(..), ForeignOp(..), ForeignOp'(..), MatrixDim(..), MatrixRep(..), Result(..), Val(..), asReturns, forDefs, matrixGet, val)

-- Needs a better name.
type GraphConfig =
   { n :: Int
   , ρ :: Env Vertex
   , classes :: ClassTable
   }

patternMismatch :: String -> String -> String
patternMismatch s s' = "Pattern mismatch: found " <> s <> ", expected " <> s'

-- Bindings if the pattern matches, with the positions of the value that matching inspected.
matches :: forall a. Ord a => ClassTable -> Val a -> Pattern -> Maybe (Env a × Set a)
matches _ (Val α _ u) (PLit ℓ) = guard eq $> (empty × Set.singleton α)
   where
   eq = case u of
      V.Lit ℓ' -> eqLiteral ℓ ℓ'
      _ -> false
matches _ v (PVar x)
   | x == varAnon = pure (empty × empty)
   | otherwise = pure (maplet x v × empty)
matches _ _ PWild = pure (empty × empty)
matches classes v (PAs p x) = first (_ `unionWith_never` maplet x v) <$> matches classes v p
matches classes (Val α _ (V.Constr c' vs)) (PConstr c ps Nil) = do
   let cls' = definitely "declared class" (Map.lookup (dottedName c') classes)
   guard (c `elem` ancestors cls')
   second (insert α) <$> matchesMany classes (take (length ps) vs) ps
matches _ _ (PConstr _ _ _) = Nothing
matches classes (Val α _ (V.Dictionary (DictRep xvs))) (PRecord xps) = do
   vps <- traverse (\(x × p) -> lookup x (unwrap xvs) <#> \(_ × v) -> v × p) xps
   second (insert α) <$> matchesMany classes (fst <$> vps) (snd <$> vps)
matches _ _ (PRecord _) = Nothing
matches classes (Val α _ (V.List vs)) (PList ps)
   | A.length vs == length ps = second (insert α) <$> matchesMany classes (L.fromFoldable vs) ps
matches _ _ (PList _) = Nothing

matchesMany :: forall a. Ord a => ClassTable -> List (Val a) -> List Pattern -> Maybe (Env a × Set a)
matchesMany _ Nil Nil = pure (empty × empty)
matchesMany classes (v : vs) (p : ps) = disjoint <$> matches classes v p <*> matchesMany classes vs ps
   where
   disjoint (ρ × αs) (ρ' × αs') = (ρ `unionWith_never` ρ') × (αs ∪ αs')
matchesMany _ _ _ = error absurd

-- Bindings, body and inspected positions of the first case whose pattern matches.
dispatch :: forall a. Ord a => ClassTable -> Val a -> List (Case a) -> Maybe (Env a × Stmt a × Set a)
dispatch classes v = oneOfMap \(p × s) -> (\(ρ × αs) -> ρ × s × αs) <$> matches classes v p

-- Bindings of a pattern which must match.
assign :: forall m a. Ord a => MonadError Error m => Highlightable a => ClassTable -> Val a -> Pattern -> m (Env a × Set a)
assign classes v p = matches classes v p # orElse ("Pattern mismatch: " <> prettyP v <> " does not match " <> prettyP p)

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
      V.Closure _ _ (Def xs _ _) -> pure (length xs)
      V.Prim (ForeignOp (_ × ForeignOp' φ')) -> pure φ'.arity
      V.Type c -> askClasses >>= arity (dottedName c)
      V.Partial _ _ -> error absurd

   call :: Maybe (Val Vertex) -> List (Val Vertex) -> m (Val Vertex)
   call doc_opt' vs' = case φ of
      V.Closure ρ1 ds (Def xs _ s) -> do
         ρ2 <- closeDefs ρ1 ds (singleton α)
         let ρ3 = foldl (\ρ (x × v) -> if x == varAnon then ρ else ρ `unionWith_never` maplet x v) empty (zip (paramVar <$> xs) vs')
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
         Attribute e x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (attribute access)"
            v <- eval Nothing ρ e αs
            case v of
               Val _ _ (V.Constr c vs) -> do
                  xs <- askClasses <#> \classes -> definitely' (fieldsOf classes (dottedName c))
                  find (\(k × _) -> k == x) (zip xs vs) <#> snd # orElse (dottedName c <> " has no field " <> x)
               _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected object"
         Subscript e e' -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (projection)"
            v <- eval Nothing ρ e αs
            v' <- eval Nothing ρ e' αs
            case v, v' of
               Val _ _ (V.Dictionary (DictRep d)), Val _ _ (V.Lit (Str s)) ->
                  withMsg "Dict lookup" $ snd <$> lookup s d # orElse ("Key \"" <> s <> "\" not found")
               Val _ _ (V.Dictionary _), _ -> throw $ "Found " <> prettyP (unit <$ v') <> ", expected str"
               Val _ _ (V.List vs), Val _ _ (V.Lit (Int i)) ->
                  vs A.!! (if i < 0 then A.length vs + i else i) # orElse ("List index " <> show i <> " out of range")
               Val _ _ (V.List _), _ -> throw $ "Found " <> prettyP (unit <$ v') <> ", expected int"
               Val _ _ (V.Matrix r), Val _ _ (V.Constr c (Val _ _ (V.Lit (Int i)) : Val _ _ (V.Lit (Int j)) : Nil)) | c == cPair ->
                  pure (matrixGet i j r)
               Val _ _ (V.Matrix _), _ -> throw $ "Found " <> prettyP (unit <$ v') <> ", expected pair of int"
               _, _ -> throw $ "Found " <> prettyP (unit <$ v) <> ", expected list, dict or matrix"
         ModMember q x -> do
            traceWhen (isJust doc_opt) $ "Discarding doc (module member " <> x <> ")"
            { moduleEnv } <- moduleStore
            let ρ_q = definitely "module loaded" (Map.lookup q moduleEnv)
            withMsg "Module member" $ lookup' x ρ_q
         App e es -> do
            v <- eval Nothing ρ e αs
            vs <- traverse (\e' -> eval Nothing ρ e' αs) es
            withMsg ("In " <> funName e) $ apply doc_opt v vs
         BinOp e op e' -> do
            v <- eval Nothing ρ e αs
            v' <- eval Nothing ρ e' αs
            u × βs <- withMsg ("In " <> binopSymbol op) $ orThrow (binop op v v')
            val doc_opt βs u
         UnOp op e -> do
            v <- eval Nothing ρ e αs
            u × βs <- withMsg ("In " <> unopSymbol op) $ orThrow (unop op v)
            val doc_opt βs u
         And e e' -> do
            Val α _ u <- eval Nothing ρ e αs
            b <- orThrow (boolean.unpack u)
            if b then eval doc_opt ρ e' (insert α αs) else val doc_opt (singleton α) u
         Or e e' -> do
            Val α _ u <- eval Nothing ρ e αs
            b <- orThrow (boolean.unpack u)
            if b then val doc_opt (singleton α) u else eval doc_opt ρ e' (insert α αs)
         Cond e1 e e2 -> do
            b × α <- eval Nothing ρ e αs >>= unpack boolean >>> orThrow
            eval doc_opt ρ (if b then e1 else e2) (insert α αs)
         ListComp α e gs -> do
            ρs <- qualifiers ρ gs αs
            vs <- for ρs \(ρ' × αs') -> eval Nothing ρ' e αs'
            val doc_opt (insert α (αs ∪ Set.unions (snd <$> ρs))) (V.List (A.fromFoldable vs))
         DocExpr e e' -> do
            v <- eval Nothing ρ e αs
            traceWhen (isJust doc_opt) "Outer doc trumps inner doc"
            eval (Just $ fromMaybe v doc_opt) ρ e' αs
         _ -> error absurd
   where
   funName :: forall a. Expr a -> String
   funName (Var x) = x
   funName (App e _) = funName e
   funName _ = "unknown"

-- Environments produced by the qualifiers, each with the vertices inspected in reaching it.
qualifiers
   :: forall m
    . HasClasses m
   => HasModuleStore m
   => MonadWithGraphAlloc m
   => MonadReader FileCxt m
   => MonadAff m
   => LoadFile m
   => Env Vertex
   -> List (Qualifier Vertex)
   -> Set Vertex
   -> m (List (Env Vertex × Set Vertex))
qualifiers ρ Nil αs = pure (singleton (ρ × αs))
qualifiers ρ (Guard e : gs) αs = do
   b × α <- eval Nothing ρ e αs >>= unpack boolean >>> orThrow
   if b then qualifiers ρ gs (insert α αs) else pure Nil
qualifiers ρ (Generator p e : gs) αs = do
   Val β _ u <- eval Nothing ρ e αs
   vs <- case u of
      V.List vs -> pure vs
      _ -> throw $ "Found " <> prettyP (unit <$ u) <> ", expected list"
   concat <$> for (L.fromFoldable vs) \v ->
      askClasses <#> (\classes -> matches classes v p) >>= case _ of
         Nothing -> pure Nil
         Just (ρ' × αs') -> qualifiers (ρ <+> ρ') gs (insert β (αs ∪ αs'))
qualifiers ρ (Decl p e : gs) αs = do
   classes <- askClasses
   ρ' × αs' <- eval Nothing ρ e αs >>= \v -> assign classes v p
   qualifiers (ρ <+> ρ') gs (αs ∪ αs')

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
   If bs s_opt -> go (NEL.toList bs) αs
      where
      go Nil αs' = maybe (pure (Assigns empty empty)) (\s' -> evalStmt doc_opt ρ s' αs') s_opt
      go (Branch e s' : bs') αs' = do
         b × α <- eval Nothing ρ e αs' >>= unpack boolean >>> orThrow
         if b then evalStmt doc_opt ρ s' (insert α αs') else go bs' (insert α αs')
   Match e bs -> do
      v <- eval Nothing ρ e αs
      askClasses <#> (\classes -> dispatch classes v (NEL.toList bs)) >>= case _ of
         Nothing -> pure (Assigns empty empty)
         Just (ρ' × s' × αs') -> do
            r <- evalStmt doc_opt (ρ <+> ρ') s' (αs ∪ αs')
            case r of
               Returns _ -> pure r
               Assigns ρ'' αs'' -> pure (Assigns (ρ' <+> ρ'') αs'')
   Assign p _ e -> do
      classes <- askClasses
      ρ' × αs' <- eval Nothing ρ e αs >>= \v -> assign classes v p
      pure (Assigns ρ' αs')
   DefRec (RecDefs α ds) -> do
      ρ' <- closeDefs ρ ds (insert α αs)
      pure (Assigns ρ' (insert α αs))
   Pass -> pure (Assigns empty empty)
   ExprStmt e -> do
      _ <- eval Nothing ρ e αs
      pure (Assigns empty empty)
   Assert e e_opt -> do
      b × α <- eval Nothing ρ e αs >>= unpack boolean >>> orThrow
      if b then pure (Assigns empty empty)
      else case e_opt of
         Nothing -> throw "AssertionError"
         Just e' -> do
            Val _ _ w <- eval Nothing ρ e' (insert α αs)
            throw
               ( "AssertionError: " <> case w of
                    V.Lit (Str str) -> str
                    _ -> prettyP (unit <$ w)
               )
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
evalVal _ (Lit α ℓ) _ =
   pure $ Just (α × V.Lit ℓ)
evalVal ρ (Dictionary α ees) αs = do
   vs × us <- traverse (traverse (flip (eval Nothing ρ) αs)) ees <#> P.unzip
   ss × βs <- traverse (unpack string >>> orThrow) vs <#> unzip
   pure $ Just (α × V.Dictionary (DictRep (D.fromFoldable (zip ss (zip βs us)))))
-- Later entries overwrite earlier ones, per update in the spec.
evalVal ρ (DictComp α e e' gs) αs = do
   ρs <- qualifiers ρ gs αs
   entries <- for ρs \(ρ' × αs') -> do
      s × β <- eval Nothing ρ' e αs' >>= unpack string >>> orThrow
      u <- eval Nothing ρ' e' αs'
      pure (s × (β × u))
   pure $ Just (α × V.Dictionary (DictRep (D.fromFoldable entries)))
evalVal ρ (List α es) αs = do
   vs <- traverse (flip (eval Nothing ρ) αs) es
   pure $ Just (α × V.List (A.fromFoldable vs))
evalVal ρ (Constr α c es) αs = do
   askClasses >>= checkArity (dottedName c) (length es)
   vs <- traverse (flip (eval Nothing ρ) αs) es
   pure $ Just (α × V.Constr c vs)
evalVal ρ (Matrix α e (x × y) e') αs = do
   (i' × β) × (j' × β') <- eval Nothing ρ e' αs >>= unpack intPair >>> orThrow <#> fst
   check
      (i' × j' >= 1 × 1)
      ("array must be at least (" <> show (1 × 1) <> "); got (" <> show (i' × j') <> ")")
   vss <- sequence do
      i <- 0 .. (i' - 1)
      singleton $ sequence do
         j <- 0 .. (j' - 1)
         let ρ' = maplet x (Val β Nothing (V.Lit (Int i))) `unionWith_never` (maplet y (Val β' Nothing (V.Lit (Int j))))
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
   v_name <- val Nothing empty (V.Lit (Str (dottedName q)))
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
      Just ρ_q -> pure ρ_q
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
