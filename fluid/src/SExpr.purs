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
import Data.List.NonEmpty (NonEmptyList(..), foldr, groupBy, head, last, tail, toList)
import Data.Semigroup.Foldable (foldr1)
import Data.List.NonEmpty (zipWith) as NonEmptyList
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmpty ((:|))
import Data.Show.Generic (genericShow)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DataType (class HasClasses, ClassTable, askClasses, classEntry, ctrSig, cCons, cPair, cParagraph, cNil)
import Data.Map as Map
import DefiniteAssignment (VarCxt, WfResult(..), fields)
import Lattice (class JoinSemilattice)
import Literal (Literal(..))
import Desugarable (class Desugarable, desug)
import Dict as D
import Effect.Exception (Error)
import Expr (class BV, class FV, Pattern(..), bv, fv)
import Expr (Branch(..), Case, Def(..), Expr(..), Import(..), Module(..), Param(..), RecDefs(..), Stmt(..)) as E
import Type as T
import Util.Set ((\\), (∪))
import Partial.Unsafe (unsafePartial)
import Util (type (×), checkDistinct, error, nonEmpty, singleton, throw, unimplemented, (×))
import Util.Pair (Pair(..))

-- Surface language expressions.

data Expr a
   = Var Var
   | Op Var
   | Lit a Literal
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
   | Cond (Expr a) (Expr a) (Expr a) -- e1 if e else e2
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
   | Dataclass Var (Maybe Var) (List (Var × T.TypeExpr Name))

data Import = Import Name (Maybe (List Var))

-- Case of a match statement.
type Case a = Pattern × Stmt a

data Param = Param Pattern (Maybe (T.TypeExpr Name))

data Clause a = Clause a (List Param × Maybe (T.TypeExpr Name) × Stmt a)

type Branch a = Var × Clause a
newtype Clauses a = Clauses (NonEmptyList (Clause a))

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause a = LambdaClause (List Pattern × Expr a)

newtype RecDef a = RecDef (NonEmptyList (Branch a))
type RecDefs a = NonEmptyList (Branch a)

-- The pattern/expr relationship is different to the one in branch (the expr is the "argument", not the "body").
data VarDef a = VarDef Pattern (Maybe (T.TypeExpr Name)) (Expr a)
type VarDefs a = NonEmptyList (VarDef a)

data Qualifier a
   = ListCompGuard (Expr a)
   | ListCompGen Pattern (Expr a)
   | ListCompDecl (VarDef a) -- could allow VarDefs instead

data Module a = Module (List Import) (List (Stmt a))

instance Desugarable DictEntry E.Expr where
   desug (ExprKey e) = desug e
   desug (VarKey α v) = pure (E.Lit α (Str v))

instance Desugarable Expr E.Expr where
   desug = expr

instance Desugarable Stmt E.Stmt where
   desug = stmt

instance Desugarable ListRest E.Expr where
   desug (End α) = pure (enil α)
   desug (Next α s l) = econs α <$> desug s <*> desug l

instance Desugarable Clauses E.Def where
   desug (Clauses μ) = clauses (μ <#> \(Clause _ clause) -> clause)

instance Desugarable LambdaClause E.Def where
   desug (LambdaClause (ps × e)) = clauses (singleton ((ps <#> \p -> Param p Nothing) × Nothing × Return e))

-- helpers
enil :: forall a. a -> E.Expr a
enil α = E.Constr α cNil Nil

econs :: forall a. a -> E.Expr a -> E.Expr a -> E.Expr a
econs α e e' = E.Constr α cCons (e : e' : Nil)

-- Parameter names for desugared functions, kept apart from source identifiers by the leading $.
param :: Int -> Var
param i = "$" <> show i

-- Unary function matching its argument against the cases.
matchFun :: forall a. a -> NonEmptyList (E.Case a) -> E.Expr a
matchFun α bs = E.Lambda α (E.Def (E.Param (param 1) Nothing : Nil) Nothing (E.Match (E.Var (param 1)) bs))

desugarModule :: forall m. HasClasses m => MonadError Error m => Module (WfResult VarCxt) -> m (E.Module (WfResult VarCxt))
desugarModule (Module is ss) = E.Module (is <#> \(Import q f) -> E.Import q f) <$> traverse stmt ss

varDef :: forall m. HasClasses m => MonadError Error m => VarDef (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
varDef (VarDef p ψ s) = E.Assign <$> pattern p <@> (typeExpr <$> ψ) <*> desug s

recDefs :: forall m. HasClasses m => MonadError Error m => RecDefs (WfResult VarCxt) -> m (E.RecDefs (WfResult VarCxt))
recDefs xcs = do
   let xcss = map RecDef (groupBy (eq `on` fst) xcs)
   let names = (fst <<< head <<< unwrap) <$> toList xcss
   checkDistinct (error <<< ("Non-contiguous clauses for: " <> _)) names
   E.RecDefs Returns <$> D.fromFoldable <$> traverse recDef xcss

recDef :: forall m. HasClasses m => MonadError Error m => RecDef (WfResult VarCxt) -> m (Bind (E.Def (WfResult VarCxt)))
recDef xcs = (fst (head (unwrap xcs)) ↦ _) <$> desug (Clauses (close <<< snd <$> unwrap xcs))
   where
   close (Clause Returns body) = Clause Returns body
   close (Clause (Assigns δ) (ps × ψ × s)) = Clause (Assigns δ) (ps × ψ × Seq s (Return (Lit Returns None)))

paragraph
   :: forall m. HasClasses m => MonadError Error m => List (ParagraphElem (WfResult VarCxt)) -> m (E.Expr (WfResult VarCxt))
paragraph elems = do
   es <- paragraphElems elems
   pure (E.Constr (Assigns Map.empty) cParagraph (es : Nil))

paragraphElems
   :: forall m
    . HasClasses m
   => MonadError Error m
   => List (ParagraphElem (WfResult VarCxt))
   -> m (E.Expr (WfResult VarCxt))
paragraphElems Nil = pure (enil (Assigns Map.empty))
paragraphElems (Token s : elems) = do
   e' <- paragraphElems elems
   pure (econs (Assigns Map.empty) (E.Lit (Assigns Map.empty) (Str s)) e')
paragraphElems (Unquote s : elems) = do
   e <- desug s
   e' <- paragraphElems elems
   pure (econs (Assigns Map.empty) e e')

-- Expr
expr :: forall m. HasClasses m => MonadError Error m => Expr (WfResult VarCxt) -> m (E.Expr (WfResult VarCxt))
expr (Var x) =
   pure $ E.Var x
expr (Op op) =
   pure $ E.Op op
expr (Lit α ℓ) =
   pure $ E.Lit α ℓ
expr (Constr α c es Nil) = do
   classes <- askClasses
   _ <- ctrSig classes "construct" (dottedName c)
   E.Constr α c <$> traverse desug es
expr (Constr α c es xes) = do
   classes <- askClasses
   _ <- ctrSig classes "construct" (dottedName c)
   reordered <- positionaliseKw classes c (length es) xes
   E.Constr α c <$> traverse desug (es <> reordered)
expr (Dictionary α sss) = do
   let ks × ss = unzip sss
   ks' <- traverse desug ks
   es <- traverse desug ss
   E.Dictionary α <$> pure (zipWith Pair ks' es)
expr (Matrix α s (x × y) s') =
   E.Matrix α <$> desug s <@> x × y <*> desug s'
expr (Lambda μ) =
   E.Lambda Returns <$> desug μ
expr (Attribute s x) =
   E.Attribute <$> desug s <@> x
expr (ModMember q x) =
   pure $ E.ModMember q x
expr (Subscript s x) =
   E.Subscript <$> desug s <*> desug x
expr (App s ss) =
   E.App <$> desug s <*> traverse desug ss
expr (BinaryApp s1 op s2) =
   E.App (E.Op op) <$> traverse desug (s1 : s2 : Nil)
expr (UnaryPrefixApp op s) =
   E.App (E.Op op) <$> traverse desug (s : Nil)
expr (Cond e1 e e2) =
   E.Cond <$> desug e1 <*> desug e <*> desug e2
expr (Paragraph elems) =
   paragraph elems
expr (ListEmpty α) =
   pure $ enil α
expr (ListNonEmpty α s l) =
   econs α <$> desug s <*> desug l
expr (ListEnum s1 s2) =
   (\e1 e2 -> E.App (E.Var "range") (e1 : E.App (E.Op "+") (e2 : E.Lit Returns (Int 1) : Nil) : Nil)) <$> desug s1 <*> desug s2
expr (ListComp α s gs) =
   listComp (α × gs × s)
expr (DocExpr s s') = do
   e <- expr s
   e' <- expr s'
   pure $ E.DocExpr e e'

stmt :: forall m. HasClasses m => MonadError Error m => Stmt (WfResult VarCxt) -> m (E.Stmt (WfResult VarCxt))
stmt (Def vd) = varDef vd
stmt (DefRec xcs) = E.DefRec <$> recDefs xcs
stmt (Match s bs) = E.Match <$> desug s <*> traverse (bitraverse pattern stmt) bs
stmt (If ess s_opt) = E.If <$> traverse (\(e × s) -> E.Branch <$> desug e <*> stmt s) ess <*> traverse stmt s_opt
stmt (Return e) = E.Return <$> desug e
stmt Pass = pure E.Pass
stmt (ExprStmt e) = E.ExprStmt <$> desug e
stmt (Assert e e_opt) = E.Assert <$> desug e <*> traverse desug e_opt
stmt (Seq s1 s2) = E.Seq <$> stmt s1 <*> stmt s2
stmt (Dataclass _ _ _) = pure E.Pass

-- List Qualifier × Expr
listComp
   :: forall m
    . HasClasses m
   => MonadError Error m
   => (WfResult VarCxt) × List (Qualifier (WfResult VarCxt)) × Expr (WfResult VarCxt)
   -> m (E.Expr (WfResult VarCxt))
listComp (α × Nil × s) =
   econs α <$> desug s <@> enil α
listComp (α × (ListCompGuard s : gs) × s') = do
   e <- listComp (α × gs × s')
   E.Cond e <$> desug s <@> enil α
listComp (α × (ListCompDecl (VarDef p _ s) : gs) × s') = do
   e <- listComp (α × gs × s')
   p' <- pattern p
   E.App (matchFun α (singleton (p' × E.Return e))) <$> ((_ : Nil) <$> desug s)
-- Elements not matching the pattern contribute nothing.
listComp (α × (ListCompGen p s : gs) × s') = do
   e <- listComp (α × gs × s')
   p' <- pattern p
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

typeExpr :: T.TypeExpr Name -> T.Type
typeExpr = map T.Class

-- Keyword sub-patterns positionalised; list patterns as Nil and Cons.
pattern :: forall m. HasClasses m => MonadError Error m => Pattern -> m Pattern
pattern (PConstr c ps xps) = do
   classes <- askClasses
   reordered <- if null xps then pure Nil else positionaliseKw classes c (length ps) xps
   _ <- ctrSig classes "match" (dottedName c)
   PConstr c <$> traverse pattern (ps <> reordered) <@> Nil
pattern (PRecord xps) = PRecord <$> traverse (traverse pattern) xps
pattern (PList ps) = foldr (\p ps' -> PConstr cCons (p : ps' : Nil) Nil) (PConstr cNil Nil Nil) <$> traverse pattern ps
pattern (PAs p x) = PAs <$> pattern p <@> x
pattern p = pure p

-- Clauses over k parameters as a function of k parameters. A parameter column that is the same variable in
-- every clause is a parameter of that name; the remaining columns are matched together, as nested pairs when
-- there are several.
clauses
   :: forall m
    . HasClasses m
   => MonadError Error m
   => NonEmptyList (List Param × Maybe (T.TypeExpr Name) × Stmt (WfResult VarCxt))
   -> m (E.Def (WfResult VarCxt))
clauses cs = do
   let n = length (fst (head cs)) :: Int
   for_ cs \(ps × _) ->
      when (length ps /= n) $ throw "Clauses differ in number of parameters"
   ψs <- traverse (signature "parameter annotations" <<< nonEmpty) (transpose (toList (cs <#> \(ps × _) -> ps <#> \(Param _ ψ) -> ψ)))
   ψ <- signature "return annotation" (cs <#> \(_ × ψ × _) -> ψ)
   let
      columns = transpose (toList (cs <#> \(ps × _) -> ps <#> \(Param p _) -> p))
      named = columns # mapWithIndex \i ps -> case sharedVar ps of
         Just x -> x × Nothing
         Nothing -> param (i + 1) × Just ps
      matched = named # mapMaybe \(x × ps_opt) -> (x × _) <$> ps_opt
   ss <- for cs \(_ × _ × s) -> stmt s
   body <- case matched of
      Nil -> pure (head ss)
      _ -> do
         pss <- traverse (traverse pattern) (transpose (snd <$> matched))
         let
            e = foldr1 (\e1 e2 -> E.Constr Returns cPair (e1 : e2 : Nil)) (E.Var <<< fst <$> nonEmpty matched)
            bs = NonEmptyList.zipWith (\ps s -> foldr1 (\p p' -> PConstr cPair (p : p' : Nil) Nil) (nonEmpty ps) × s) (nonEmpty pss) ss
         pure (E.Match e bs)
   pure (E.Def (zipWith E.Param (fst <$> named) (map typeExpr <$> ψs)) (typeExpr <$> ψ) body)
   where
   sharedVar :: List Pattern -> Maybe Var
   sharedVar (PVar x : ps) | all (_ == PVar x) ps = Just x
   sharedVar _ = Nothing

   signature :: String -> NonEmptyList (Maybe (T.TypeExpr Name)) -> m (Maybe (T.TypeExpr Name))
   signature what ψs
      | all (\ψ -> ψ == Nothing || ψ == head ψs) (tail ψs) = pure (head ψs)
      | otherwise = throw ("Clauses differ in " <> what)

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

derive instance Eq Param
derive instance Generic Param _
instance Show Param where
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
   fv (Lit _ _) = Set.empty
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
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (Paragraph elems) = Set.unions (fv <$> elems)
   fv (ListEmpty _) = Set.empty
   fv (ListNonEmpty _ e l) = fv e ∪ fv l
   fv (ListEnum e1 e2) = fv e1 ∪ fv e2
   fv (ListComp _ e gs) = qualifiersFv gs e
   fv (DocExpr e e') = fv e ∪ fv e'

instance FV (Stmt a) where
   fv (Return e) = fv e
   fv (If ess s_opt) =
      Set.unions ((\(e × s) -> fv e ∪ fv s) <$> ess) ∪ fv s_opt
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
   fv (VarDef _ _ e) = fv e

instance FV (LambdaClause a) where
   fv (LambdaClause (ps × e)) = fv e \\ Set.unions (bv <$> ps)

instance FV (Clause a) where
   fv (Clause _ (ps × _ × b)) = fv b \\ Set.unions (bv <$> ps)

instance BV Param where
   bv (Param p _) = bv p

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
   ListCompDecl (VarDef p _ e') -> fv e' ∪ (qualifiersFv gs e \\ bv p)
