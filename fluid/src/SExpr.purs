module SExpr where

import Prelude hiding (absurd, top)

import Bind (Bind, Name, Var, dottedName, (↦))
import Data.Set (Set, empty, insert, member, singleton, unions) as Set
import Control.Monad.Error.Class (class MonadError)
import Data.Foldable (all, for_, length, null)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, find, mapMaybe, sort, transpose, unzip, zipWith, (:))
import Data.List.NonEmpty (NonEmptyList(..), foldr, groupBy, head, last, toList)
import Data.List.NonEmpty (zipWith) as NonEmptyList
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmpty ((:|))
import Data.Show.Generic (genericShow)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (fst, snd)
import DataType (class HasClasses, ClassTable, askClasses, checkArity, ctrSig, fieldsOf, cCons, cNone, cPair, cParagraph, cFalse, cNil, cTrue)
import Data.Map as Map
import DefiniteAssignment (VarCxt, WfResult(..))
import Lattice (class JoinSemilattice)
import Desugarable (class Desugarable, desug)
import Dict as D
import Effect.Exception (Error)
import Expr (class FV, Pattern(..), bv, fv)
import Expr (Case, Def(..), Expr(..), Import(..), Module(..), RecDefs(..), Stmt(..)) as E
import Util.Set ((\\), (∪))
import Partial.Unsafe (unsafePartial)
import Util (type (×), absurd, error, nonEmpty, singleton, throw, unimplemented, (×))
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
   | App (Expr a) (List (Expr a))
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

data Stmt a
   = Return (Expr a)
   | If (NonEmptyList (Expr a × Stmt a)) (Maybe (Stmt a))
   | Match (Expr a) (NonEmptyList (Case a))
   | Def (VarDef a)
   | DefRec (RecDefs a)
   | Pass
   | ExprStmt (Expr a)
   | Assert (Expr a) (Maybe (Expr a))
   | Seq (Stmt a) (Stmt a)
   | Dataclass Var (Maybe Var) (List Var)

data Import = Import Name (Maybe (List Var))

-- Case of a match statement.
type Case a = Pattern × Stmt a

data Clause a = Clause a (List Pattern × Stmt a)

type Branch a = Var × Clause a
newtype Clauses a = Clauses (NonEmptyList (Clause a))

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause a = LambdaClause (List Pattern × Expr a)

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

instance Desugarable Clauses E.Def where
   desug (Clauses μ) = clausesFwd (μ <#> \(Clause _ clause) -> clause)

instance Desugarable LambdaClause E.Def where
   desug (LambdaClause (ps × e)) = clausesFwd (singleton (ps × Return e))

desugarModuleFwd :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
desugarModuleFwd = moduleFwd

-- helpers
enil :: forall a. a -> E.Expr a
enil α = E.Constr α cNil Nil

econs :: forall a. a -> E.Expr a -> E.Expr a -> E.Expr a
econs α e e' = E.Constr α cCons (e : e' : Nil)

-- Parameter names for desugared functions, kept apart from source identifiers by the leading $.
param :: Int -> Var
param i = "$" <> show i

-- Cases branching on a Boolean.
boolCases :: forall a. E.Stmt a -> E.Stmt a -> NonEmptyList (E.Case a)
boolCases s s' = NonEmptyList ((PConstr cTrue Nil Nil × s) :| (PConstr cFalse Nil Nil × s') : Nil)

-- Unary function matching its argument against the cases.
matchFun :: forall a. a -> NonEmptyList (E.Case a) -> E.Expr a
matchFun α bs = E.Lambda α (E.Def (param 1 : Nil) (E.Match (E.Var (param 1)) bs))

matchWith :: forall a. a -> E.Expr a -> NonEmptyList (E.Case a) -> E.Expr a
matchWith α e bs = E.App (matchFun α bs) (e : Nil)

moduleFwd :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
moduleFwd (Module is ss) = E.Module (importFwd <$> is) <$> traverse stmtFwd ss
   where
   importFwd (Import q f) = E.Import q f

varDefFwd :: forall m. HasClasses m => MonadError Error m => VarDef (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
varDefFwd (VarDef p s) = E.Assign <$> expandKw p <*> desug s

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

recDefFwd :: forall m. HasClasses m => MonadError Error m => RecDef (WfResult VarCxt) -> m (Bind (E.Def (WfResult VarCxt)))
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
exprFwd (App s ss) =
   E.App <$> desug s <*> traverse desug ss
exprFwd (BinaryApp s1 op s2) =
   E.App (E.Op op) <$> traverse desug (s1 : s2 : Nil)
exprFwd (UnaryPrefixApp op s) =
   E.App (E.Op op) <$> traverse desug (s : Nil)
exprFwd (Ternary cond e1 e2) =
   matchWith Returns <$> desug cond <*> (boolCases <$> (E.Return <$> desug e1) <*> (E.Return <$> desug e2))
exprFwd (Paragraph elems) =
   paragraphFwd elems
exprFwd (ListEmpty α) =
   pure $ enil α
exprFwd (ListNonEmpty α s l) =
   econs α <$> desug s <*> desug l
exprFwd (ListEnum s1 s2) =
   E.App (E.Var "range") <$> sequence (desug s1 : (E.App (E.Op "+") <<< (_ : E.Int Returns 1 : Nil) <$> desug s2) : Nil)
exprFwd (ListComp α s qs) =
   listCompFwd (α × qs × s)
exprFwd (DocExpr s s') = do
   e <- exprFwd s
   e' <- exprFwd s'
   pure $ E.DocExpr e e'

type IfElseClauses a = NonEmptyList (Expr a × Stmt a) × Stmt a

stmtFwd :: forall m. HasClasses m => MonadError Error m => Stmt (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
stmtFwd (Def vd) = varDefFwd vd
stmtFwd (DefRec xcs) = E.DefRec <$> recDefsFwd xcs
stmtFwd (Match s bs) = E.Match <$> desug s <*> traverse caseFwd bs
   where
   caseFwd (p × s') = (×) <$> expandKw p <*> stmtFwd s'
stmtFwd (If sss s) = ifElseFwd (sss × fromMaybe Pass s)
stmtFwd (Return e) = E.Return <$> desug e
stmtFwd Pass = pure E.Pass
stmtFwd (ExprStmt e) = E.ExprStmt <$> desug e
stmtFwd (Assert cond msg_opt) =
   (\c msg -> E.Match c (boolCases E.Pass (E.ExprStmt (E.App (E.Var "error") (msg : Nil)))))
      <$> desug cond
      <*> maybe (pure (E.Str Returns "AssertionError")) desug msg_opt
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
      pure $ E.Match cond (boolCases b' e3')

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
   matchWith α <$> desug s <@> boolCases (E.Return e) (E.Return (enil α))
listCompFwd (α × (ListCompDecl (VarDef p s) : qs) × s') = do
   e <- listCompFwd (α × qs × s')
   p' <- expandKw p
   matchWith α <$> desug s <@> singleton (p' × E.Return e)
-- Elements not matching the pattern contribute nothing.
listCompFwd (α × (ListCompGen p s : qs) × s') = do
   e <- listCompFwd (α × qs × s')
   p' <- expandKw p
   let
      bs = case p' of
         PVar _ -> singleton (p' × E.Return e)
         PWild -> singleton (p' × E.Return e)
         _ -> NonEmptyList ((p' × E.Return e) :| (PWild × E.Return (enil α)) : Nil)
   e' <- desug s
   pure $ E.App (E.Var "concat_map") (matchFun α bs : e' : Nil)

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

-- Keyword sub-patterns positionalised; constructor patterns checked against the class.
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
   go λ (PList ps) = PList <$> traverse (go λ) ps
   go λ (PAs p' x) = PAs <$> go λ p' <@> x
   go _ p' = pure p'

-- Clauses over k parameters as a function of k parameters. A parameter column that is the same variable in
-- every clause is a parameter of that name; the remaining columns are matched together, as nested pairs when
-- there are several.
clausesFwd
   :: forall m
    . HasClasses m
   => MonadError Error m
   => NonEmptyList (List Pattern × Stmt (WfResult VarCxt))
   -> m (E.Def (WfResult VarCxt))
clausesFwd clauses = do
   let k = length (fst (head clauses)) :: Int
   for_ clauses \(ps × _) ->
      when (length ps /= k) $ throw "Clauses differ in number of parameters"
   let
      columns = transpose (toList (fst <$> clauses))
      params = columns # mapWithIndex \i column -> case sharedVar column of
         Just x -> x × Nothing
         Nothing -> param (i + 1) × Just column
      matched = params # mapMaybe \(x × column) -> (x × _) <$> column
   bodies <- for clauses \(_ × s) -> stmtFwd s
   body <- case matched of
      Nil -> pure (head bodies)
      _ -> do
         rows <- traverse (traverse expandKw) (transpose (snd <$> matched))
         let bs = NonEmptyList.zipWith (\ps s -> patterns ps × s) (nonEmpty rows) bodies
         pure (E.Match (scrutinee (fst <$> matched)) bs)
   pure (E.Def (fst <$> params) body)
   where
   sharedVar :: List Pattern -> Maybe Var
   sharedVar column = case column of
      PVar x : ps | all (_ == PVar x) ps -> Just x
      _ -> Nothing

   scrutinee :: List Var -> E.Expr (WfResult VarCxt)
   scrutinee Nil = error absurd
   scrutinee (x : Nil) = E.Var x
   scrutinee (x : xs) = E.Constr Returns cPair (E.Var x : scrutinee xs : Nil)

   patterns :: List Pattern -> Pattern
   patterns Nil = error absurd
   patterns (p : Nil) = p
   patterns (p : ps) = PConstr cPair (p : patterns ps : Nil) Nil

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
   fv (App e es) = fv e ∪ Set.unions (fv <$> es)
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
