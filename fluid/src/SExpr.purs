module SExpr where

import Prelude hiding (top)

import Bind (Bind, Name, Var, varThis)
import Data.Set (Set, empty, singleton, unions) as Set
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List.NonEmpty (NonEmptyList)
import Data.Maybe (Maybe, maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (fst, snd)
import Literal (Literal)
import Expr (class BV, class FV, Binop, Pattern, Unop, bv, fv)
import Type as T
import Util.Set ((\\), (∪))
import Util (type (×), (×))

-- Surface language expressions.

data Expr
   = Var Var
   | Lit Literal
   | Call Expr (List Expr) (List (Bind Expr)) -- constructor call when head names a class
   | Dictionary (List (Expr × Expr))
   | Matrix Expr (Var × Var) Expr
   | Lambda LambdaClause
   | Attribute Expr Var
   | Subscript Expr Expr
   | BinOp Expr Binop Expr
   | UnOp Unop Expr
   | And Expr Expr
   | Or Expr Expr
   | InfixApp Expr Var Expr -- e |f| e', sugar for f(e, e')
   | Cond Expr Expr Expr -- e1 if e else e2
   | Paragraph Paragraph
   | List (List Expr)
   | Tuple (List Expr)
   | ListComp Expr (List Qualifier)
   | DictComp Expr Expr (List Qualifier)
   | DocExpr Expr Expr

data ParagraphElem = Token String | Unquote Expr
type Paragraph = List ParagraphElem

data Stmt
   = Return Expr
   | If (NonEmptyList (Expr × Stmt)) (Maybe Stmt)
   | Match Expr (NonEmptyList Case)
   | Def VarDef
   | DefRec RecDefs
   | Pass
   | ExprStmt Expr
   | Assert Expr (Maybe Expr)
   | Seq Stmt Stmt
   | Dataclass Var (Maybe Var) (List (Var × T.TypeExpr Name))

data Import = Import Name (Maybe (List Var))

-- Case of a match statement.
type Case = Pattern × Stmt

data Param = Param Pattern (Maybe (T.TypeExpr Name))

data Clause = Clause (List Param × Maybe (T.TypeExpr Name) × Stmt)

type Branch = Var × Clause

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause = LambdaClause (List Pattern × Expr)

type RecDefs = NonEmptyList Branch

data VarDef = VarDef Pattern (Maybe (T.TypeExpr Name)) Expr
type VarDefs = NonEmptyList VarDef

data Qualifier
   = Guard Expr
   | Generator Pattern Expr
   | Decl VarDef

data Module = Module (List Import) (List Stmt)

-- ======================
-- boilerplate
-- ======================
derive instance Eq Expr
derive instance Generic Expr _
instance Show Expr where
   show c = genericShow c

derive instance Eq Stmt
derive instance Generic Stmt _
instance Show Stmt where
   show c = genericShow c

derive instance Eq Import
derive instance Generic Import _
instance Show Import where
   show c = genericShow c

derive instance Eq Param
derive instance Generic Param _
instance Show Param where
   show c = genericShow c

derive instance Eq Clause
derive instance Generic Clause _
instance Show Clause where
   show c = genericShow c

derive instance Eq LambdaClause
derive instance Generic LambdaClause _
instance Show LambdaClause where
   show c = genericShow c

derive instance Eq VarDef
derive instance Generic VarDef _
instance Show VarDef where
   show c = genericShow c

derive instance Eq Qualifier
derive instance Generic Qualifier _
instance Show Qualifier where
   show c = genericShow c

derive instance Eq ParagraphElem
derive instance Generic ParagraphElem _
instance Show ParagraphElem where
   show c = genericShow c

-- ======================
-- Free / bound variables
-- ======================

instance FV Expr where
   fv (Var x) = Set.singleton x
   fv (Lit _) = Set.empty
   fv (Call e es xes) = fv e ∪ Set.unions (fv <$> es) ∪ Set.unions ((fv <<< snd) <$> xes)
   fv (Dictionary entries) = Set.unions ((\(k × v) -> fv k ∪ fv v) <$> entries)
   fv (Matrix body (x × y) source) = (fv body \\ (Set.singleton x ∪ Set.singleton y)) ∪ fv source
   fv (Lambda clause) = fv clause
   fv (Attribute e _) = fv e
   fv (Subscript e e') = fv e ∪ fv e'
   fv (BinOp e _ e') = fv e ∪ fv e'
   fv (UnOp _ e) = fv e
   fv (And e e') = fv e ∪ fv e'
   fv (Or e e') = fv e ∪ fv e'
   fv (InfixApp e f e') = fv e ∪ Set.singleton f ∪ fv e'
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (Paragraph elems) = Set.unions (fv <$> elems)
   fv (List es) = Set.unions (fv <$> es)
   fv (Tuple es) = Set.unions (fv <$> es)
   fv (ListComp e gs) = fvQualifiers gs ∪ (fv e \\ bv gs)
   fv (DictComp k e gs) = fvQualifiers gs ∪ ((fv k ∪ fv e) \\ bv gs)
   fv (DocExpr e e') = (fv e \\ Set.singleton varThis) ∪ fv e'

instance FV Stmt where
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

instance FV VarDef where
   fv (VarDef _ _ e) = fv e

instance FV LambdaClause where
   fv (LambdaClause (ps × e)) = fv e \\ Set.unions (bv <$> ps)

instance FV Clause where
   fv (Clause (ps × _ × b)) = fv b \\ Set.unions (bv <$> ps)

instance BV Param where
   bv (Param p _) = bv p

instance FV ParagraphElem where
   fv (Token _) = Set.empty
   fv (Unquote e) = fv e

fvRecDefs :: RecDefs -> Set.Set Var
fvRecDefs rs =
   Set.unions (fv <$> (snd <$> rs)) \\ Set.unions (Set.singleton <<< fst <$> rs)

fvQualifiers :: List Qualifier -> Set.Set Var
fvQualifiers Nil = Set.empty
fvQualifiers (Guard e : gs) = fv e ∪ fvQualifiers gs
fvQualifiers (Generator p e : gs) = fv e ∪ (fvQualifiers gs \\ bv p)
fvQualifiers (Decl (VarDef p _ e) : gs) = fv e ∪ (fvQualifiers gs \\ bv p)

instance BV Qualifier where
   bv (Guard _) = Set.empty
   bv (Generator p _) = bv p
   bv (Decl (VarDef p _ _)) = bv p
