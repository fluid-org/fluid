module SExpr where

import Prelude hiding (top)

import Bind (Bind, Name, Var, varThis)
import Data.Set (Set, empty, unions)
import Data.Set as Set
import Data.Generic.Rep (class Generic)
import Data.List (List(..), nub, (:))
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..), maybe)
import Data.Show.Generic (genericShow)
import Data.Tuple (fst, snd)
import Literal (Literal)
import Expr (class BV, class FV, Binop, Pattern, Unop, bv, fv)
import Types as T
import Util.Set ((\\), (∪))
import Util (type (×), singleton, (×))

-- Surface language expressions.

data Expr
   = Var Var
   | Lit Literal
   | Imaginary Number
   | Call Expr (List TypeExpr) (List Expr) (List (Bind Expr)) -- constructor call when head names a class
   | Dictionary (List (Expr × Expr))
   | Matrix Expr (Var × Var) Expr
   | Lambda LambdaClause
   | Attribute Expr Var
   | Subscript Expr Expr
   | BinOp Expr Binop Expr
   | UnOp Unop Expr
   | And Expr Expr
   | Or Expr Expr
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
   = Return (Maybe Expr)
   | If (NonEmptyList (Expr × Stmt)) (Maybe Stmt)
   | Match Expr (NonEmptyList Case)
   | Declare Var TypeExpr
   | Def VarDef
   | DefRegion (NonEmptyList Branch)
   | Pass
   | ExprStmt Expr
   | Assert Expr (Maybe Expr)
   | Seq Stmt Stmt
   | TypeRegion (NonEmptyList TypeDef)

data TypeDef
   = Dataclass Var (List Var) (Maybe TypeExpr) (List (Var × TypeExpr))
   | TypeAlias Var (List Var) TypeExpr

typeDefName :: TypeDef -> Var
typeDefName (Dataclass x _ _ _) = x
typeDefName (TypeAlias x _ _) = x

simpleNames :: TypeExpr -> List Var
simpleNames (NameTy q ψs) = (if NEL.length q == 1 then NEL.head q : Nil else Nil) <> (ψs >>= simpleNames)
simpleNames (ListTy ψ) = simpleNames ψ
simpleNames (TupleTy ψs) = ψs >>= simpleNames
simpleNames (DictTy ψ) = simpleNames ψ
simpleNames (CallableTy ψs ψ) = (ψs >>= simpleNames) <> simpleNames ψ
simpleNames (TypeTy ψ) = simpleNames ψ
simpleNames (UnionTy ψ ψ') = simpleNames ψ <> simpleNames ψ'
simpleNames (PrimitiveTy _) = Nil
simpleNames (LitTy _) = Nil

data Import = Import Name (Maybe (List Var))

type Case = Pattern × Stmt

data Param = Param Pattern TypeExpr

-- Type parameters, parameters, return annotation and body.
data Clause = Clause (List Var × List Param × TypeExpr × Stmt)

type Branch = Var × Clause

-- Lambdas accept exactly one clause whose body is an expression (no defs / return-keyword).
newtype LambdaClause = LambdaClause (List Pattern × Expr)

data VarDef = VarDef Pattern (Maybe TypeExpr) Expr
type VarDefs = NonEmptyList VarDef

data Qualifier
   = Guard Expr
   | Generator Pattern Expr
   | Decl VarDef

data Module = Module (List Import) Stmt

data TypeExpr
   = PrimitiveTy T.Primitive
   | ListTy TypeExpr
   | TupleTy (List TypeExpr)
   | DictTy TypeExpr
   | CallableTy (List TypeExpr) TypeExpr
   | LitTy Literal
   | NameTy Name (List TypeExpr) -- class, alias or type parameter, with type arguments
   | TypeTy TypeExpr -- class as value
   | UnionTy TypeExpr TypeExpr

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

derive instance Eq TypeDef
derive instance Generic TypeDef _
instance Show TypeDef where
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

derive instance Eq TypeExpr
derive instance Generic TypeExpr _
instance Show TypeExpr where
   show c = genericShow c

derive instance Eq ParagraphElem
derive instance Generic ParagraphElem _
instance Show ParagraphElem where
   show c = genericShow c

-- ======================
-- Free / bound variables
-- ======================

instance FV Expr where
   fv (Var x) = singleton x
   fv (Lit _) = empty
   fv (Imaginary _) = empty
   fv (Call e _ es xes) = fv e ∪ unions (fv <$> es) ∪ unions ((fv <<< snd) <$> xes)
   fv (Dictionary entries) = unions ((\(k × v) -> fv k ∪ fv v) <$> entries)
   fv (Matrix body (x × y) source) = (fv body \\ (singleton x ∪ singleton y)) ∪ fv source
   fv (Lambda clause) = fv clause
   fv (Attribute e _) = fv e
   fv (Subscript e e') = fv e ∪ fv e'
   fv (BinOp e _ e') = fv e ∪ fv e'
   fv (UnOp _ e) = fv e
   fv (And e e') = fv e ∪ fv e'
   fv (Or e e') = fv e ∪ fv e'
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (Paragraph elems) = unions (fv <$> elems)
   fv (List es) = unions (fv <$> es)
   fv (Tuple es) = unions (fv <$> es)
   fv (ListComp e gs) = fvQualifiers gs ∪ (fv e \\ bv gs)
   fv (DictComp k e gs) = fvQualifiers gs ∪ ((fv k ∪ fv e) \\ bv gs)
   fv (DocExpr e e') = (fv e \\ singleton varThis) ∪ fv e'

instance FV Stmt where
   fv (Return e) = fv e
   fv (If ess s_opt) =
      unions ((\(e × s) -> fv e ∪ fv s) <$> ess) ∪ fv s_opt
   fv (Match scrut branches) =
      fv scrut ∪ unions ((\(p × b) -> fv b \\ bv p) <$> branches)
   fv (Declare _ _) = empty
   fv (Def vd) = fv vd
   fv (DefRegion rs) = unions (fv <<< snd <$> rs) \\ Set.fromFoldable (fst <$> rs)
   fv Pass = empty
   fv (ExprStmt e) = fv e
   fv (Assert cond msg) = fv cond ∪ maybe empty fv msg
   fv (Seq s1 s2) = fv s1 ∪ fv s2
   fv (TypeRegion _) = empty

instance FV VarDef where
   fv (VarDef _ _ e) = fv e

instance FV LambdaClause where
   fv (LambdaClause (ps × e)) = fv e \\ unions (bv <$> ps)

instance FV Clause where
   fv (Clause (_ × ps × _ × b)) = (fv b \\ unions (bv <$> ps)) \\ assigns b

-- Variables assigned by a statement.
assigns :: Stmt -> Set Var
assigns Pass = empty
assigns (Declare x _) = singleton x
assigns (Def (VarDef p _ _)) = bv p
assigns (ExprStmt _) = empty
assigns (Assert _ _) = empty
assigns (Return _) = empty
assigns (If es s) = unions (assigns <$> (snd <$> es)) ∪ maybe empty assigns s
assigns (Match _ ps) = unions ((\(p × s) -> bv p ∪ assigns s) <$> ps)
assigns (DefRegion ds) = unions (singleton <<< fst <$> ds)
assigns (Seq s1 s2) = assigns s1 ∪ assigns s2
assigns (TypeRegion χs) = Set.fromFoldable (typeDefName <$> χs)

declares :: Stmt -> List Var
declares (Declare x _) = singleton x
declares (Def (VarDef p (Just _) _)) = Set.toUnfoldable (bv p)
declares (DefRegion ds) = nub (NEL.toList (fst <$> ds))
declares (If es s) = (NEL.toList es >>= declares <<< snd) <> maybe Nil declares s
declares (Match _ ps) = NEL.toList ps >>= declares <<< snd
declares (Seq s1 s2) = declares s1 <> declares s2
declares (TypeRegion χs) = NEL.toList (typeDefName <$> χs)
declares _ = Nil

binds :: Stmt -> Set Var
binds (If es s) = unions (binds <<< snd <$> es) ∪ maybe empty binds s
binds (Match _ ps) = unions ((\(p × s) -> bv p ∪ binds s) <$> ps)
binds (Seq s1 s2) = binds s1 ∪ binds s2
binds _ = empty

instance BV Param where
   bv (Param p _) = bv p

instance FV ParagraphElem where
   fv (Token _) = empty
   fv (Unquote e) = fv e

fvQualifiers :: List Qualifier -> Set Var
fvQualifiers Nil = empty
fvQualifiers (Guard e : gs) = fv e ∪ fvQualifiers gs
fvQualifiers (Generator p e : gs) = fv e ∪ (fvQualifiers gs \\ bv p)
fvQualifiers (Decl (VarDef p _ e) : gs) = fv e ∪ (fvQualifiers gs \\ bv p)

instance BV Qualifier where
   bv (Guard _) = empty
   bv (Generator p _) = bv p
   bv (Decl (VarDef p _ _)) = bv p
