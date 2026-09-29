module SExpr where

import Prelude hiding (top)

import Bind (Bind, Name, Var)
import Data.Set (Set, empty, singleton, unions) as Set
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List.NonEmpty (NonEmptyList, head)
import Data.Maybe (Maybe, maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (fst, snd)
import Lattice (class JoinSemilattice)
import Literal (Literal)
import Expr (class BV, class FV, Binop, Pattern, Unop, bv, fv)
import Type as T
import Util.Set ((\\), (∪))
import Util (type (×), error, unimplemented, (×))

-- Surface language expressions.

data Expr a
   = Var Var
   | Lit a Literal
   | Constr a Name (List (Expr a)) (List (Bind (Expr a)))
   | Dictionary a (List (DictEntry a × Expr a))
   | Matrix a (Expr a) (Var × Var) (Expr a)
   | Lambda (LambdaClause a)
   | Attribute (Expr a) Var
   | Subscript (Expr a) (Expr a)
   | App (Expr a) (List (Expr a))
   | BinOp (Expr a) Binop (Expr a)
   | UnOp Unop (Expr a)
   | And (Expr a) (Expr a)
   | Or (Expr a) (Expr a)
   | InfixApp (Expr a) Var (Expr a) -- e |f| e', sugar for f(e, e')
   | Cond (Expr a) (Expr a) (Expr a) -- e1 if e else e2
   | Paragraph (Paragraph a)
   | List a (List (Expr a))
   | ListComp a (Expr a) (List (Qualifier a))
   | DictComp a (DictEntry a) (Expr a) (List (Qualifier a))
   | DocExpr (Expr a) (Expr a)

data DictEntry a = ExprKey (Expr a) | VarKey a Var

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

data Clause a = Clause (List Param × Maybe (T.TypeExpr Name) × Stmt a)

type Branch a = Var × Clause a

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause a = LambdaClause (List Pattern × Expr a)

type RecDefs a = NonEmptyList (Branch a)

-- The pattern/expr relationship is different to the one in branch (the expr is the "argument", not the "body").
data VarDef a = VarDef Pattern (Maybe (T.TypeExpr Name)) (Expr a)
type VarDefs a = NonEmptyList (VarDef a)

data Qualifier a
   = Guard (Expr a)
   | Generator Pattern (Expr a)
   | Decl (VarDef a)

data Module a = Module (List Import) (List (Stmt a))

-- ======================
-- boilerplate
-- ======================
derive instance Functor Stmt
derive instance Functor Clause
derive instance Functor LambdaClause
derive instance Functor DictEntry
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
   fv (Lit _ _) = Set.empty
   fv (Constr _ c es xes) = Set.singleton (head c) ∪ Set.unions (fv <$> es) ∪ Set.unions ((fv <<< snd) <$> xes)
   fv (Dictionary _ entries) = Set.unions ((\(k × v) -> fv k ∪ fv v) <$> entries)
   fv (Matrix _ body (x × y) source) = (fv body \\ (Set.singleton x ∪ Set.singleton y)) ∪ fv source
   fv (Lambda clause) = fv clause
   fv (Attribute e _) = fv e
   fv (Subscript e e') = fv e ∪ fv e'
   fv (App e es) = fv e ∪ Set.unions (fv <$> es)
   fv (BinOp e _ e') = fv e ∪ fv e'
   fv (UnOp _ e) = fv e
   fv (And e e') = fv e ∪ fv e'
   fv (Or e e') = fv e ∪ fv e'
   fv (InfixApp e f e') = fv e ∪ Set.singleton f ∪ fv e'
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (Paragraph elems) = Set.unions (fv <$> elems)
   fv (List _ es) = Set.unions (fv <$> es)
   fv (ListComp _ e gs) = fvQualifiers gs ∪ (fv e \\ bv gs)
   fv (DictComp _ k e gs) = fvQualifiers gs ∪ ((fv k ∪ fv e) \\ bv gs)
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
   fv (Clause (ps × _ × b)) = fv b \\ Set.unions (bv <$> ps)

instance BV Param where
   bv (Param p _) = bv p

instance FV (DictEntry a) where
   fv (ExprKey e) = fv e
   fv (VarKey _ _) = Set.empty

instance FV (ParagraphElem a) where
   fv (Token _) = Set.empty
   fv (Unquote e) = fv e

fvRecDefs :: forall a. RecDefs a -> Set.Set Var
fvRecDefs rs =
   Set.unions (fv <$> (snd <$> rs)) \\ Set.unions (Set.singleton <<< fst <$> rs)

fvQualifiers :: forall a. List (Qualifier a) -> Set.Set Var
fvQualifiers Nil = Set.empty
fvQualifiers (Guard e : gs) = fv e ∪ fvQualifiers gs
fvQualifiers (Generator p e : gs) = fv e ∪ (fvQualifiers gs \\ bv p)
fvQualifiers (Decl (VarDef p _ e) : gs) = fv e ∪ (fvQualifiers gs \\ bv p)

instance BV (Qualifier a) where
   bv (Guard _) = Set.empty
   bv (Generator p _) = bv p
   bv (Decl (VarDef p _ _)) = bv p
