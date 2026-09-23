module SExpr where

import Prelude hiding (top)

import Bind (Bind, Name, Var, dottedName, (↦))
import Data.Set (Set, empty, singleton, unions) as Set
import Control.Monad.Error.Class (class MonadError)
import Data.Bitraversable (bitraverse)
import Data.Foldable (all, for_, length, null)
import Data.Function (on)
import Data.Generic.Rep (class Generic)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), drop, find, mapMaybe, sort, transpose, unzip, zipWith, (:))
import Data.List.NonEmpty (NonEmptyList(..), foldr, groupBy, head, last, toList)
import Data.Semigroup.Foldable (foldr1)
import Data.List.NonEmpty (zipWith) as NonEmptyList
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmpty ((:|))
import Data.Show.Generic (genericShow)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DataType (class HasClasses, ClassTable, askClasses, classEntry, ctrSig, cCons, cNone, cPair, cParagraph, cFalse, cNil, cTrue)
import Data.Map as Map
import DefiniteAssignment (VarCxt, WfResult(..), fields)
import Lattice (class JoinSemilattice)
import Desugarable (class Desugarable, desug)
import Dict as D
import Effect.Exception (Error)
import Expr (class FV, Pattern(..), bv, fv)
import Expr (Case, Def(..), Expr(..), Import(..), Module(..), RecDefs(..), Stmt(..)) as E
import Util.Set ((\\), (∪))
import Partial.Unsafe (unsafePartial)
import Util (type (×), checkDistinct, error, nonEmpty, singleton, throw, unimplemented, (×))
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

moduleFwd :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
moduleFwd (Module is ss) = E.Module (importFwd <$> is) <$> traverse stmtFwd ss
   where
   importFwd (Import q f) = E.Import q f

varDefFwd :: forall m. HasClasses m => MonadError Error m => VarDef (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
varDefFwd (VarDef p s) = E.Assign <$> patternFwd p <*> desug s

recDefsFwd :: forall m. HasClasses m => MonadError Error m => RecDefs (WfResult VarCxt) -> m (E.RecDefs (WfResult VarCxt))
recDefsFwd xcs = do
   let xcss = map RecDef (groupBy (eq `on` fst) xcs)
   let names = (fst <<< head <<< unwrap) <$> toList xcss
   checkDistinct (error <<< ("Non-contiguous clauses for: " <> _)) names
   E.RecDefs Returns <$> D.fromFoldable <$> traverse recDefFwd xcss

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
   classes <- askClasses
   _ <- ctrSig classes "construct" (dottedName c)
   E.Constr α c <$> traverse desug es
exprFwd (Constr α c es xes) = do
   classes <- askClasses
   _ <- ctrSig classes "construct" (dottedName c)
   reordered <- positionaliseKw classes c (length es) xes
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
   E.App <$> branch <*> ((_ : Nil) <$> desug cond)
   where
   branch = matchFun Returns <$> (boolCases <$> (E.Return <$> desug e1) <*> (E.Return <$> desug e2))
exprFwd (Paragraph elems) =
   paragraphFwd elems
exprFwd (ListEmpty α) =
   pure $ enil α
exprFwd (ListNonEmpty α s l) =
   econs α <$> desug s <*> desug l
exprFwd (ListEnum s1 s2) =
   (\e1 e2 -> E.App (E.Var "range") (e1 : E.App (E.Op "+") (e2 : E.Int Returns 1 : Nil) : Nil)) <$> desug s1 <*> desug s2
exprFwd (ListComp α s gs) =
   listCompFwd (α × gs × s)
exprFwd (DocExpr s s') = do
   e <- exprFwd s
   e' <- exprFwd s'
   pure $ E.DocExpr e e'

type IfElseClauses a = NonEmptyList (Expr a × Stmt a) × Stmt a

stmtFwd :: forall m. HasClasses m => MonadError Error m => Stmt (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
stmtFwd (Def vd) = varDefFwd vd
stmtFwd (DefRec xcs) = E.DefRec <$> recDefsFwd xcs
stmtFwd (Match s bs) = E.Match <$> desug s <*> traverse (bitraverse patternFwd stmtFwd) bs
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
listCompFwd (α × (ListCompGuard s : gs) × s') = do
   e <- listCompFwd (α × gs × s')
   E.App (matchFun α (boolCases (E.Return e) (E.Return (enil α)))) <$> ((_ : Nil) <$> desug s)
listCompFwd (α × (ListCompDecl (VarDef p s) : gs) × s') = do
   e <- listCompFwd (α × gs × s')
   p' <- patternFwd p
   E.App (matchFun α (singleton (p' × E.Return e))) <$> ((_ : Nil) <$> desug s)
-- Elements not matching the pattern contribute nothing.
listCompFwd (α × (ListCompGen p s : gs) × s') = do
   e <- listCompFwd (α × gs × s')
   p' <- patternFwd p
   let
      bs = case p' of
         PVar _ -> singleton (p' × E.Return e)
         PWild -> singleton (p' × E.Return e)
         _ -> NonEmptyList ((p' × E.Return e) :| (PWild × E.Return (enil α)) : Nil)
   e' <- desug s
   pure $ E.App (E.Var "concat_map") (matchFun α bs : e' : Nil)

positionaliseKw :: forall m b. MonadError Error m => ClassTable -> Name -> Int -> List (Bind b) -> m (List b)
positionaliseKw classes c n xbs = do
   fs <- fields <$> classEntry classes (dottedName c)
   let remaining = drop n fs
   let provided = xbs <#> fst
   when (sort provided /= sort remaining) $ throw $
      "Class " <> last c <> " keyword fields mismatch: expected " <> show remaining <> ", got " <> show provided
   pure $ remaining <#> \f ->
      unsafePartial $ case find (\(k ↦ _) -> k == f) xbs of
         Just (_ ↦ b) -> b

-- Keyword sub-patterns positionalised; list patterns as Nil and Cons.
patternFwd :: forall m. HasClasses m => MonadError Error m => Pattern -> m Pattern
patternFwd (PConstr c ps xps) = do
   classes <- askClasses
   reordered <- if null xps then pure Nil else positionaliseKw classes c (length ps) xps
   _ <- ctrSig classes "match" (dottedName c)
   PConstr c <$> traverse patternFwd (ps <> reordered) <@> Nil
patternFwd (PRecord xps) = PRecord <$> traverse (traverse patternFwd) xps
patternFwd (PList ps) = foldr (\p ps' -> PConstr cCons (p : ps' : Nil) Nil) (PConstr cNil Nil Nil) <$> traverse patternFwd ps
patternFwd (PAs p x) = PAs <$> patternFwd p <@> x
patternFwd p = pure p

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
   let n = length (fst (head clauses)) :: Int
   for_ clauses \(ps × _) ->
      when (length ps /= n) $ throw "Clauses differ in number of parameters"
   let
      columns = transpose (toList (fst <$> clauses))
      named = columns # mapWithIndex \i ps -> case sharedVar ps of
         Just x -> x × Nothing
         Nothing -> param (i + 1) × Just ps
      matched = named # mapMaybe \(x × ps_opt) -> (x × _) <$> ps_opt
   ss <- for clauses (stmtFwd <<< snd)
   body <- case matched of
      Nil -> pure (head ss)
      _ -> do
         pss <- traverse (traverse patternFwd) (transpose (snd <$> matched))
         let
            e = foldr1 (\e1 e2 -> E.Constr Returns cPair (e1 : e2 : Nil)) (E.Var <<< fst <$> nonEmpty matched)
            bs = NonEmptyList.zipWith (\ps s -> foldr1 (\p p' -> PConstr cPair (p : p' : Nil) Nil) (nonEmpty ps) × s) (nonEmpty pss) ss
         pure (E.Match e bs)
   pure (E.Def (fst <$> named) body)
   where
   sharedVar :: List Pattern -> Maybe Var
   sharedVar (PVar x : ps) | all (_ == PVar x) ps = Just x
   sharedVar _ = Nothing

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
   fv (ListComp _ e gs) = qualifiersFv gs e
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
qualifiersFv :: forall a. List (Qualifier a) -> Expr a -> Set.Set Var
qualifiersFv Nil e = fv e
qualifiersFv (g : gs) e = case g of
   ListCompGuard e' -> fv e' ∪ qualifiersFv gs e
   ListCompGen p e' -> fv e' ∪ (qualifiersFv gs e \\ bv p)
   ListCompDecl (VarDef p e') -> fv e' ∪ (qualifiersFv gs e \\ bv p)
