module SExpr where

import Prelude hiding (absurd, top, unless)

import Bind (Bind, Name, Var, dottedName, (↦))
import Bind (keys) as B
import Data.Set (Set, empty, insert, member, singleton, unions) as Set
import Control.Monad.Error.Class (class MonadError)
import Data.Bitraversable (ltraverse, rtraverse)
import Data.Either (Either(..))
import Data.Foldable (for_, length, null)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), drop, find, sort, take, unzip, zip, zipWith, (:))
import Data.List (mapMaybe) as L
import Data.List.NonEmpty (NonEmptyList(..), foldr, groupBy, head, last, toList)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmpty ((:|))
import Data.Profunctor.Strong (second)
import Data.Show.Generic (genericShow)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (fst, snd)
import Data.Unfoldable (replicate)
import DataType (class HasClasses, ClassTable, Ctr, DataType(..), askClasses, checkArity, ctrSig, fieldsOf, cCons, cNone, cParagraph, cFalse, cNil, cTrue, dataType)
import Data.Map as Map
import DefiniteAssignment (VarCxt, WfResult(..))
import Lattice (class JoinSemilattice)
import Desugarable (class Desugarable, desug)
import Dict as D
import Effect.Exception (Error)
import Expr (class FV, Cont(..), Elim(..), asElim, fv)
import Expr (Expr(..), Import(..), Module(..), RecDefs(..), Stmt(..), VarDef(..)) as E
import Util.Set ((\\), (∪))
import Partial.Unsafe (unsafePartial)
import Pattern (ListRestPattern(..), Pattern(..), bv, pListVarAnon, pVarAnon)
import Util (type (+), type (×), Endo, absurd, appendList, assert, definitely, error, shapeMismatch, singleton, throw, unimplemented, whenever, (×), (≜))
import Util.Map (toUnfoldable)
import Util.Pair (Pair(..))

-- Surface language expressions.

data Expr a
   = Var Var
   | Op Var
   | Int a Int
   | Float a Number
   | Str a String
   | Constr a Name (List (Expr a)) (List (Bind (Expr a)))
   | Dictionary a (List (DictEntry a × Expr a))
   | Matrix a (Expr a) (Var × Var) (Expr a)
   | Lambda (LambdaClause a)
   | Attribute (Expr a) Var
   | ModMember Name Var -- member x of module q; not parseable, produced by well-formedness from Attribute
   | Subscript (Expr a) (Expr a)
   | App (Expr a) (Expr a)
   | BinaryApp (Expr a) Var (Expr a)
   | UnaryPrefixApp Var (Expr a)
   | Ternary (Expr a) (Expr a) (Expr a)
   | Paragraph (Paragraph a)
   | ListEmpty a
   | ListNonEmpty a (Expr a) (ListRest a)
   | ListEnum (Expr a) (Expr a)
   | ListComp a (Expr a) (List (Qualifier a))
   | DocExpr (Expr a) (Expr a)

data DictEntry a = ExprKey (Expr a) | VarKey a Var

data ListRest a
   = End a
   | Next a (Expr a) (ListRest a)

data ParagraphElem a = Token String | Unquote (Expr a)
type Paragraph a = List (ParagraphElem a)

showPattern :: Pattern + ListRestPattern -> String
showPattern (Left p') = show p'
showPattern (Right p') = show p'

ctrFor :: Pattern + ListRestPattern -> Maybe Ctr
ctrFor (Left (PVar _)) = Nothing
ctrFor (Left (PConstr c _ _)) = pure (dottedName c)
ctrFor (Left (PRecord _)) = Nothing
ctrFor (Left PListEmpty) = pure (dottedName cNil)
ctrFor (Left (PListNonEmpty _ _)) = pure (dottedName cCons)
ctrFor (Right (PListVar _)) = Nothing
ctrFor (Right PListEnd) = pure (dottedName cNil)
ctrFor (Right (PListNext _ _)) = pure (dottedName cCons)
ctrFor (Left _) = error absurd

subpatts :: Pattern + ListRestPattern -> List (Pattern + ListRestPattern)
subpatts (Left (PVar _)) = Nil
subpatts (Left (PConstr _ ps xps)) = Left <$> (ps <> (xps <#> snd))
subpatts (Left (PRecord xps)) = Left <$> (xps <#> snd)
subpatts (Left PListEmpty) = Nil
subpatts (Left (PListNonEmpty p o)) = Left p : Right o : Nil
subpatts (Right (PListVar _)) = Nil
subpatts (Right PListEnd) = Nil
subpatts (Right (PListNext p o)) = Left p : Right o : Nil
subpatts (Left _) = error absurd

data Stmt a
   = Return (Expr a)
   | If (NonEmptyList (Expr a × Stmt a)) (Maybe (Stmt a))
   | Match (Expr a) (NonEmptyList (Pattern × Stmt a))
   | Def (VarDef a)
   | DefRec (RecDefs a)
   | Pass
   | ExprStmt (Expr a)
   | Assert (Expr a) (Maybe (Expr a))
   | Seq (Stmt a) (Stmt a)
   | Dataclass Var (Maybe Var) (List Var)

data Import = Import Name (Maybe (List Var))

data Clause a = Clause a (NonEmptyList Pattern × Stmt a)

type Branch a = Var × Clause a
newtype Clauses a = Clauses (NonEmptyList (Clause a))

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause a = LambdaClause (NonEmptyList Pattern × Expr a)

newtype RecDef a = RecDef (NonEmptyList (Branch a))
type RecDefs a = NonEmptyList (Branch a)

-- The pattern/expr relationship is different to the one in branch (the expr is the "argument", not the "body").
data VarDef a = VarDef Pattern (Expr a)
type VarDefs a = NonEmptyList (VarDef a)

data Qualifier a
   = ListCompGuard (Expr a)
   | ListCompGen Pattern (Expr a)
   | ListCompDecl (VarDef a) -- could allow VarDefs instead

data Module a = Module (List Import) (List (Stmt a))

instance Desugarable DictEntry E.Expr where
   desug (ExprKey e) = desug e
   desug (VarKey α v) = pure (E.Str α v)

instance Desugarable Expr E.Expr where
   desug = exprFwd

instance Desugarable Stmt E.Stmt where
   desug = stmtFwd

instance Desugarable ListRest E.Expr where
   desug (End α) = pure (enil α)
   desug (Next α s l) = econs α <$> desug s <*> desug l

instance Desugarable Clauses Elim where
   desug μ = clausesStateFwd (toClausesStateFwd μ) <#> asElim

instance Desugarable LambdaClause Elim where
   desug (LambdaClause (ps × e)) = desug (Clauses (singleton (Clause (Assigns Map.empty) (ps × Return e))))

desugarModuleFwd :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
desugarModuleFwd = moduleFwd

-- helpers
enil :: forall a. a -> E.Expr a
enil α = E.Constr α cNil Nil

econs :: forall a. a -> E.Expr a -> E.Expr a -> E.Expr a
econs α e e' = E.Constr α cCons (e : e' : Nil)

elimBool :: forall a. Cont a -> Cont a -> Elim a
elimBool κ κ' = ElimConstr (D.fromFoldable [ dottedName cTrue × κ, dottedName cFalse × κ' ])

moduleFwd :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
moduleFwd (Module is ss) = E.Module (importFwd <$> is) <$> traverse stmtFwd ss
   where
   importFwd (Import q f) = E.Import q f

-- Use of eliminators to establish module bindings is a bit naff, because we don't really have a notion of
-- "rest of module" to use as continuation. So use empty dictionary (unit tuple) as continuation, and disregard
-- in evaluation.
varDefFwd :: forall m. HasClasses m => MonadError Error m => VarDef (WfResult VarCxt) -> m (E.VarDef (WfResult VarCxt))
varDefFwd (VarDef p s) =
   E.VarDef <$> desug (Clauses (singleton (Clause (Assigns Map.empty) (singleton p × Return (Dictionary Returns Nil))))) <*> desug
      s

recDefsFwd :: forall m. HasClasses m => MonadError Error m => RecDefs (WfResult VarCxt) -> m (E.RecDefs (WfResult VarCxt))
recDefsFwd xcs = do
   let xcss = map RecDef (groupBy (eq `on` fst) xcs)
   let names = (fst <<< head <<< unwrap) <$> toList xcss
   for_ (firstDuplicate names) \x ->
      throw $ "Non-contiguous clauses for: " <> x
   E.RecDefs Returns <$> D.fromFoldable <$> traverse recDefFwd xcss
   where
   firstDuplicate :: List Var -> Maybe Var
   firstDuplicate = go Set.empty
      where
      go _ Nil = Nothing
      go seen (x : xs)
         | x `Set.member` seen = Just x
         | otherwise = go (Set.insert x seen) xs

recDefFwd :: forall m. HasClasses m => MonadError Error m => RecDef (WfResult VarCxt) -> m (Bind (Elim (WfResult VarCxt)))
recDefFwd xcs = (fst (head (unwrap xcs)) ↦ _) <$> desug (Clauses (close <<< snd <$> unwrap xcs))
   where
   close (Clause Returns body) = Clause Returns body
   close (Clause (Assigns δ) (ps × s)) = Clause (Assigns δ) (ps × Seq s (Return (Constr Returns cNone Nil Nil)))

paragraphFwd
   :: forall m. HasClasses m => MonadError Error m => List (ParagraphElem (WfResult VarCxt)) -> m (E.Expr (WfResult VarCxt))
paragraphFwd elems = do
   es <- paragraphElemsFwd elems
   pure (E.Constr (Assigns Map.empty) cParagraph (es : Nil))

paragraphElemsFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => List (ParagraphElem (WfResult VarCxt))
   -> m (E.Expr (WfResult VarCxt))
paragraphElemsFwd Nil = pure (enil (Assigns Map.empty))
paragraphElemsFwd (Token s : elems) = do
   e' <- paragraphElemsFwd elems
   pure (econs (Assigns Map.empty) (E.Str (Assigns Map.empty) s) e')
paragraphElemsFwd (Unquote s : elems) = do
   e <- desug s
   e' <- paragraphElemsFwd elems
   pure (econs (Assigns Map.empty) e e')

-- Expr
exprFwd :: forall m. HasClasses m => MonadError Error m => Expr (WfResult VarCxt) -> m (E.Expr (WfResult VarCxt))
exprFwd (Var x) =
   pure $ E.Var x
exprFwd (Op op) =
   pure $ E.Op op
exprFwd (Int α n) =
   pure $ E.Int α n
exprFwd (Float α n) =
   pure $ (E.Float α n)
exprFwd (Str α s) =
   pure $ E.Str α s
exprFwd (Constr α c es Nil) = do
   λ <- askClasses
   _ <- ctrSig λ "construct" (dottedName c)
   E.Constr α c <$> traverse desug es
exprFwd (Constr α c es xes) = do
   λ <- askClasses
   _ <- ctrSig λ "construct" (dottedName c)
   reordered <- positionaliseKw λ c (length es) xes
   E.Constr α c <$> traverse desug (es <> reordered)
exprFwd (Dictionary α sss) = do
   let ks × ss = unzip sss
   ks' <- traverse desug ks
   es <- traverse desug ss
   E.Dictionary α <$> pure (zipWith Pair ks' es)
exprFwd (Matrix α s (x × y) s') =
   E.Matrix α <$> desug s <@> x × y <*> desug s'
exprFwd (Lambda μ) =
   E.Lambda Returns <$> desug μ
exprFwd (Attribute s x) =
   E.Attribute <$> desug s <@> x
exprFwd (ModMember q x) =
   pure $ E.ModMember q x
exprFwd (Subscript s x) =
   E.Subscript <$> desug s <*> desug x
exprFwd (App s1 s2) =
   E.App <$> desug s1 <*> desug s2
exprFwd (BinaryApp s1 op s2) =
   E.App <$> (E.App (E.Op op) <$> desug s1) <*> desug s2
exprFwd (UnaryPrefixApp op s) =
   E.App (E.Op op) <$> desug s
exprFwd (Ternary cond e1 e2) =
   E.App
      <$> (E.Lambda Returns <$> (elimBool <$> (ContStmt <$> E.Return <$> desug e1) <*> (ContStmt <$> E.Return <$> desug e2)))
      <*> desug cond
exprFwd (Paragraph elems) =
   paragraphFwd elems
exprFwd (ListEmpty α) =
   pure $ enil α
exprFwd (ListNonEmpty α s l) =
   econs α <$> desug s <*> desug l
exprFwd (ListEnum s1 s2) =
   E.App
      <$> (E.App (E.Var "range") <$> desug s1)
      <*> (E.App <$> (E.App (E.Op "+") <$> desug s2) <@> (E.Int Returns 1))
exprFwd (ListComp α s (ListCompGen p s' : qs)) = unsafePartial $
   listCompFwd (α × (ListCompGen p s' : qs) × s)
exprFwd (ListComp α s qs) =
   listCompFwd (α × qs × s)
exprFwd (DocExpr s s') = do
   e <- exprFwd s
   e' <- exprFwd s'
   pure $ E.DocExpr e e'

type IfElseClauses a = NonEmptyList (Expr a × Stmt a) × Stmt a

stmtFwd :: forall m. HasClasses m => MonadError Error m => Stmt (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
stmtFwd (Def vd) = E.Def <$> varDefFwd vd
stmtFwd (DefRec xcs) = E.DefRec <$> recDefsFwd xcs
stmtFwd (Match s μ) = E.Match <$> desug s <*> traverse caseFwd μ
   where
   caseFwd (p × b) = (×) <$> expandKw p <*> stmtFwd b
stmtFwd (If sss s) = ifElseFwd (sss × fromMaybe Pass s)
stmtFwd (Return e) = E.Return <$> desug e
stmtFwd Pass = pure E.Pass
stmtFwd (ExprStmt e) = E.ExprStmt <$> desug e
stmtFwd (Assert cond msg_opt) =
   stmtFwd (If (singleton (App (Var "not") cond × ExprStmt (App (Var "error") msg))) Nothing)
   where
   msg = fromMaybe (Str Returns "AssertionError") msg_opt
stmtFwd (Seq s1 s2) = E.Seq <$> stmtFwd s1 <*> stmtFwd s2
stmtFwd (Dataclass _ _ _) = pure E.Pass

ifElseFwd :: forall m. HasClasses m => MonadError Error m => IfElseClauses (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
ifElseFwd (sss × s) =
   foldr clause (stmtFwd s) sss
   where
   clause (s1 × b) e3 = do
      cond <- desug s1
      b' <- stmtFwd b
      e3' <- e3
      pure $ E.Match cond (NonEmptyList ((PConstr cTrue Nil Nil × b') :| (PConstr cFalse Nil Nil × e3') : Nil))

-- List Qualifier × Expr
listCompFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => (WfResult VarCxt) × List (Qualifier (WfResult VarCxt)) × Expr (WfResult VarCxt)
   -> m (E.Expr (WfResult VarCxt))
listCompFwd (α × Nil × s) =
   econs α <$> desug s <@> enil α
listCompFwd (α × (ListCompGuard s : qs) × s') = do
   e <- listCompFwd (α × qs × s')
   E.App (E.Lambda α (elimBool (ContStmt (E.Return e)) (ContStmt (E.Return (enil α))))) <$> desug s
listCompFwd (α × (ListCompDecl (VarDef p s) : qs) × s') = do
   σ <- clausesStateFwd (((Left p : Nil) × Nil × Return (ListComp α s' qs)) : Nil)
   E.App (E.Lambda α (asElim σ)) <$> desug s
listCompFwd (α × (ListCompGen p s : qs) × s') = do
   λ <- askClasses
   let ks = orElseFwd λ α ((Left p : Nil) × Return (ListComp α s' qs))
   σ <- clausesStateFwd (toList (ks <#> second (Nil × _)))
   E.App (E.App (E.Var "concat_map") (E.Lambda α (asElim σ))) <$> desug s

-- Clauses
toClausesStateFwd :: Clauses (WfResult VarCxt) -> ClausesState' (WfResult VarCxt)
toClausesStateFwd (Clauses μ) = toList μ <#> toClauseStateFwd
   where
   toClauseStateFwd :: Clause (WfResult VarCxt) -> ClauseState' (WfResult VarCxt)
   toClauseStateFwd (Clause _ (NonEmptyList (p :| π) × b)) = (Left p : Nil) × π × b

-- Like ClauseState but for curried functions; extra component π' stores remaining top-level patterns.
type ClauseState' a = List (Pattern + ListRestPattern) × List Pattern × Stmt a
type ClausesState' a = List (ClauseState' a)

popArgFwd
   :: forall m. HasClasses m => MonadError Error m => ClausesState' (WfResult VarCxt) -> m (ClausesState' (WfResult VarCxt))
popArgFwd ((Nil × (p : π) × s) : ks) = (((Left p : Nil) × π × s) : _) <$> popArgFwd ks
popArgFwd Nil = pure Nil
popArgFwd _ = throw (shapeMismatch unit)

popVarFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => Var
   -> ClausesState' (WfResult VarCxt)
   -> m (ClausesState' (WfResult VarCxt))
popVarFwd x (((Left (PVar x') : π) × π' × s) : ks) = ((π × π' × s) : _) <$> popVarFwd (x ≜ x') ks
popVarFwd _ Nil = pure Nil
popVarFwd _ _ = throw (shapeMismatch unit)

popListVarFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => Var
   -> ClausesState' (WfResult VarCxt)
   -> m (ClausesState' (WfResult VarCxt))
popListVarFwd x (((Right (PListVar x') : π) × π' × s) : ks) = ((π × π' × s) : _) <$> popListVarFwd (x ≜ x') ks
popListVarFwd _ Nil = pure Nil
popListVarFwd _ _ = throw (shapeMismatch unit)

popConstrFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => DataType
   -> ClausesState' (WfResult VarCxt)
   -> m (List (Ctr × ClausesState' (WfResult VarCxt)))
popConstrFwd _ ((Nil × _ × _) : _) = error absurd
popConstrFwd d (((p : π') × π'' × s) : ks) = do
   λ <- askClasses
   d' × n <- ctrSig λ "match" c
   assert (length π == n && d' == d) $
      forConstrFwd c ((π <> π') × π'' × s) <$> popConstrFwd d ks
   where
   π = subpatts p
   c = definitely ("Failed to distinguish dataclass: " <> showPattern p) (ctrFor p)
popConstrFwd _ Nil = pure Nil

forConstrFwd :: Ctr -> ClauseState' (WfResult VarCxt) -> Endo (List (Ctr × ClausesState' (WfResult VarCxt)))
forConstrFwd c k Nil = (c × (k : Nil)) : Nil
forConstrFwd c k ((c' × ks') : cks)
   | c == c' = (c' × (k : ks')) : cks
   | otherwise = (c' × ks') : forConstrFwd c k cks

popRecordFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => List Var
   -> ClausesState' (WfResult VarCxt)
   -> m (ClausesState' (WfResult VarCxt))
popRecordFwd xs (((Left (PRecord xps) : π) × π' × s) : ks) =
   assert ((xps <#> fst) == xs) $ ((((xps <#> snd >>> Left) <> π) × π' × s) : _) <$> popRecordFwd xs ks
popRecordFwd _ Nil = pure Nil
popRecordFwd _ _ = throw (shapeMismatch unit)

positionaliseKw :: forall m b. MonadError Error m => ClassTable -> Name -> Int -> List (Bind b) -> m (List b)
positionaliseKw λ c n xbs = do
   fs <- maybe (throw $ "Unknown dataclass: " <> dottedName c) pure (fieldsOf λ (dottedName c))
   let remaining = drop n fs
   let provided = xbs <#> fst
   when (sort provided /= sort remaining) $ throw $
      "Class " <> last c <> " keyword fields mismatch: expected " <> show remaining <> ", got " <> show provided
   pure $ remaining <#> \f ->
      unsafePartial $ case find (\(k ↦ _) -> k == f) xbs of
         Just (_ ↦ b) -> b

expandKw :: forall m. HasClasses m => MonadError Error m => Pattern -> m Pattern
expandKw p = do
   λ <- askClasses
   go λ p
   where
   go λ (PConstr c ps xps) = do
      reordered <- if null xps then pure Nil else positionaliseKw λ c (length ps) xps
      let ps' = ps <> reordered
      checkArity λ "match" (dottedName c) (length ps')
      (\ps'' -> PConstr c ps'' Nil) <$> traverse (go λ) ps'
   go λ (PRecord xps) = PRecord <$> traverse (traverse (go λ)) xps
   go λ (PListNonEmpty p' l) = PListNonEmpty <$> go λ p' <*> goRest λ l
   go λ (PAs p' x) = PAs <$> go λ p' <@> x
   go _ p' = pure p'

   goRest :: ClassTable -> ListRestPattern -> m ListRestPattern
   goRest λ (PListNext p' l) = PListNext <$> go λ p' <*> goRest λ l
   goRest _ p' = pure p'

-- Implementing Desugarable would require another newtype
clausesStateFwd :: forall m. HasClasses m => MonadError Error m => ClausesState' (WfResult VarCxt) -> m (Cont (WfResult VarCxt))
clausesStateFwd ks0 = do
   ks <- for ks0 \(π × π' × b) -> do
      π'' <- traverse (ltraverse (expandKw >=> eliminable)) π
      π''' <- traverse (expandKw >=> eliminable) π'
      pure (π'' × π''' × b)
   clausesStateFwd' ks

-- Patterns the eliminator compiler handles, with wildcards as anonymous variables.
eliminable :: forall m. MonadError Error m => Pattern -> m Pattern
eliminable PWild = pure pVarAnon
eliminable p@(PVar _) = pure p
eliminable PListEmpty = pure PListEmpty
eliminable (PConstr c ps Nil) = PConstr c <$> traverse eliminable ps <@> Nil
eliminable (PRecord xps) = PRecord <$> traverse (traverse eliminable) xps
eliminable (PListNonEmpty p rest) = PListNonEmpty <$> eliminable p <*> eliminableRest rest
   where
   eliminableRest (PListNext p' rest') = PListNext <$> eliminable p' <*> eliminableRest rest'
   eliminableRest rest' = pure rest'
eliminable p = throw ("Pattern supported only in match: " <> show p)

clausesStateFwd' :: forall m. HasClasses m => MonadError Error m => ClausesState' (WfResult VarCxt) -> m (Cont (WfResult VarCxt))
clausesStateFwd' ks = case ks of
   Nil -> error absurd
   (Nil × Nil × b) : Nil ->
      ContStmt <$> stmtFwd b
   (Nil × _) : _ ->
      ContStmt <$> E.Return <$> E.Lambda Returns <$> asElim <$> (clausesStateFwd' =<< popArgFwd ks)
   ((Left (PVar x) : _) × _) : _ ->
      ContElim <$> ElimVar x <$> (clausesStateFwd' =<< popVarFwd x ks)
   ((Left (PRecord xps) : _) × _) : _ ->
      ContElim <$> ElimDict (B.keys xps) <$> (clausesStateFwd' =<< popRecordFwd (xps <#> fst) ks)
   ((Right (PListVar x) : _) × _) : _ ->
      ContElim <$> ElimVar x <$> (clausesStateFwd' =<< popListVarFwd x ks)
   ((p : _) × _) : _ -> do
      λ <- askClasses
      let c = definitely ("clausesStateFwd ctrFor failed for: " <> showPattern p) (ctrFor p)
      d <- maybe (throw $ "Unknown dataclass: " <> c) pure (dataType λ c)
      kss <- popConstrFwd d ks
      ContElim <$> ElimConstr <$> D.fromFoldable <$> sequence (rtraverse clausesStateFwd <$> kss)

-- First component π is stack of subpatterns active during processing of a single top-level pattern p,
-- initially containing only p and empty when the recursion terminates.
type ClauseState a = List (Pattern + ListRestPattern) × Stmt a

unless :: ClassTable -> Pattern + ListRestPattern -> List (Pattern + ListRestPattern)
unless _ (Left (PVar _)) = Nil
unless _ (Left (PRecord _)) = Nil
unless λ (Left (PConstr c _ _)) =
   let
      c0 = dottedName c
      DataType _ sigs = case dataType λ c0 of
         Just d -> d
         Nothing -> error $ "Unknown dataclass: " <> c0
   in
      (toUnfoldable sigs :: List _) # L.mapMaybe
         \(c' × n) -> whenever (c' /= c0) (Left (PConstr (singleton c') (replicate n pVarAnon) Nil))
unless _ (Left PListEmpty) = Left (PConstr cCons (replicate 2 pVarAnon) Nil) : Nil
unless _ (Left (PListNonEmpty _ _)) = Left PListEmpty : Nil
unless _ (Right (PListVar _)) = Nil
unless _ (Right (PListNext _ _)) = Right PListEnd : Nil
unless _ (Right PListEnd) = Right (PListNext pVarAnon pListVarAnon) : Nil
unless _ (Left _) = error absurd

orElseFwd :: forall a. ClassTable -> a -> ClauseState a -> NonEmptyList (ClauseState a)
orElseFwd λ α = case _ of
   Nil × s -> singleton (Nil × s)
   (p : π) × s ->
      (orElseFwd λ α ((π' <> π) × s) <#> popPatts (length π') <#> pushPattFor p)
         `appendList`
            (unless λ p <#> \p' -> ((π <#> anon) × Return (ListEmpty α)) # pushPatt p')
      where
      π' = subpatts p
   where
   pushPatt :: Pattern + ListRestPattern -> Endo (ClauseState a)
   pushPatt p (π × s) = (p : π) × s

   popPatts :: Int -> ClauseState a -> List (Pattern + ListRestPattern) × ClauseState a
   popPatts n (π' × s) = take n π' × drop n π' × s

   pushPattFor :: Pattern + ListRestPattern -> List (Pattern + ListRestPattern) × ClauseState a -> ClauseState a
   pushPattFor (Left (PVar x)) = \(_ × k) ->
      pushPatt (Left (PVar x)) k
   pushPattFor (Left (PRecord xps)) = \(π × k) ->
      pushPatt (Left (PRecord (zip (fst <$> xps) (unsafePartial (\(Left p) -> p) <$> π)))) k
   pushPattFor (Left (PConstr c _ _)) = \(π × k) ->
      pushPatt (Left (PConstr c (unsafePartial (\(Left p) -> p) <$> π) Nil)) k
   pushPattFor (Left PListEmpty) = \(_ × k) ->
      pushPatt (Left PListEmpty) k
   pushPattFor (Left (PListNonEmpty _ _)) = unsafePartial \((Left p : Right o : Nil) × k) ->
      pushPatt (Left (PListNonEmpty p o)) k
   pushPattFor (Right (PListVar x)) = \(_ × k) ->
      pushPatt (Right (PListVar x)) k
   pushPattFor (Right (PListNext _ _)) = unsafePartial \((Left p : Right o : Nil) × k) ->
      pushPatt (Right (PListNext p o)) k
   pushPattFor (Right PListEnd) = \(_ × k) ->
      pushPatt (Right PListEnd) k
   pushPattFor (Left _) = error absurd

anon :: Pattern + ListRestPattern -> Pattern + ListRestPattern
anon (Left _) = Left pVarAnon
anon (Right _) = Right pListVarAnon

-- ======================
-- boilerplate
-- ======================
derive instance Newtype (Clauses a) _
derive instance Newtype (LambdaClause a) _
derive instance Newtype (RecDef a) _
derive instance Functor Stmt
derive instance Functor Clause
derive instance Functor Clauses
derive instance Functor LambdaClause
derive instance Functor DictEntry
derive instance Functor ListRest
derive instance Functor VarDef
derive instance Functor Qualifier
derive instance Functor ParagraphElem
derive instance Functor Expr

instance Functor Module where
   map f (Module is ss) = Module is (map f <$> ss)

instance JoinSemilattice a => JoinSemilattice (Expr a) where
   join _ = error unimplemented

derive instance Eq a => Eq (DictEntry a)
derive instance Generic (DictEntry a) _
instance Show a => Show (DictEntry a) where
   show c = genericShow c

derive instance Eq a => Eq (Expr a)
derive instance Generic (Expr a) _
instance Show a => Show (Expr a) where
   show c = genericShow c

derive instance Eq a => Eq (ListRest a)
derive instance Generic (ListRest a) _
instance Show a => Show (ListRest a) where
   show c = genericShow c

derive instance Eq a => Eq (Stmt a)
derive instance Generic (Stmt a) _
instance Show a => Show (Stmt a) where
   show c = genericShow c

derive instance Eq Import
derive instance Generic Import _
instance Show Import where
   show c = genericShow c

derive instance Eq a => Eq (Clause a)
derive instance Generic (Clause a) _
instance Show a => Show (Clause a) where
   show c = genericShow c

derive instance Eq a => Eq (Clauses a)
derive instance Generic (Clauses a) _
instance Show a => Show (Clauses a) where
   show c = genericShow c

derive instance Eq a => Eq (LambdaClause a)
derive instance Generic (LambdaClause a) _
instance Show a => Show (LambdaClause a) where
   show c = genericShow c

derive instance Eq a => Eq (VarDef a)
derive instance Generic (VarDef a) _
instance Show a => Show (VarDef a) where
   show c = genericShow c

derive instance Eq a => Eq (Qualifier a)
derive instance Generic (Qualifier a) _
instance Show a => Show (Qualifier a) where
   show c = genericShow c

derive instance Eq a => Eq (ParagraphElem a)
derive instance Generic (ParagraphElem a) _
instance Show a => Show (ParagraphElem a) where
   show c = genericShow c

-- ======================
-- Free / bound variables
-- ======================

instance FV (Expr a) where
   fv (Var x) = Set.singleton x
   fv (Op op) = Set.singleton op
   fv (Int _ _) = Set.empty
   fv (Float _ _) = Set.empty
   fv (Str _ _) = Set.empty
   fv (Constr _ c es xes) = Set.singleton (head c) ∪ Set.unions (fv <$> es) ∪ Set.unions ((fv <<< snd) <$> xes)
   fv (Dictionary _ entries) = Set.unions ((\(k × v) -> fv k ∪ fv v) <$> entries)
   fv (Matrix _ body (x × y) source) = (fv body \\ (Set.singleton x ∪ Set.singleton y)) ∪ fv source
   fv (Lambda clause) = fv clause
   fv (Attribute e _) = fv e
   fv (ModMember _ _) = Set.empty
   fv (Subscript e e') = fv e ∪ fv e'
   fv (App e e') = fv e ∪ fv e'
   fv (BinaryApp e op e') = fv e ∪ Set.singleton op ∪ fv e'
   fv (UnaryPrefixApp op e) = Set.singleton op ∪ fv e
   fv (Ternary cond e1 e2) = fv cond ∪ fv e1 ∪ fv e2
   fv (Paragraph elems) = Set.unions (fv <$> elems)
   fv (ListEmpty _) = Set.empty
   fv (ListNonEmpty _ e l) = fv e ∪ fv l
   fv (ListEnum e1 e2) = fv e1 ∪ fv e2
   fv (ListComp _ e quals) = qualsFv quals e
   fv (DocExpr e e') = fv e ∪ fv e'

instance FV (Stmt a) where
   fv (Return e) = fv e
   fv (If clauses elseBody) =
      Set.unions ((\(c × b) -> fv c ∪ fv b) <$> clauses) ∪ fv elseBody
   fv (Match scrut branches) =
      fv scrut ∪ Set.unions ((\(p × b) -> fv b \\ bv p) <$> branches)
   fv (Def vd) = fv vd
   fv (DefRec rs) = fvRecDefs rs
   fv Pass = Set.empty
   fv (ExprStmt e) = fv e
   fv (Assert cond msg) = fv cond ∪ maybe Set.empty fv msg
   fv (Seq s1 s2) = fv s1 ∪ fv s2
   fv (Dataclass _ _ _) = Set.empty

instance FV (VarDef a) where
   fv (VarDef _ e) = fv e

instance FV (LambdaClause a) where
   fv (LambdaClause (ps × e)) = fv e \\ Set.unions (bv <$> ps)

instance FV (Clause a) where
   fv (Clause _ (ps × b)) = fv b \\ Set.unions (bv <$> ps)

instance FV (DictEntry a) where
   fv (ExprKey e) = fv e
   fv (VarKey _ _) = Set.empty

instance FV (ListRest a) where
   fv (End _) = Set.empty
   fv (Next _ e l) = fv e ∪ fv l

instance FV (ParagraphElem a) where
   fv (Token _) = Set.empty
   fv (Unquote e) = fv e

fvRecDefs :: forall a. RecDefs a -> Set.Set Var
fvRecDefs rs =
   Set.unions (fv <$> (snd <$> rs)) \\ Set.unions (Set.singleton <<< fst <$> rs)

-- List-comprehension qualifiers bind their variables for subsequent qualifiers
-- (and the producing expression). Process right-to-left.
qualsFv :: forall a. List (Qualifier a) -> Expr a -> Set.Set Var
qualsFv Nil e = fv e
qualsFv (q : qs) e = case q of
   ListCompGuard cond -> fv cond ∪ qualsFv qs e
   ListCompGen p src -> fv src ∪ (qualsFv qs e \\ bv p)
   ListCompDecl (VarDef p src) -> fv src ∪ (qualsFv qs e \\ bv p)
