module Expr where

import Prelude hiding (absurd, top)

import Bind (Bind, Name, Var, varThis)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List.NonEmpty (NonEmptyList, last)
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set, empty, unions)
import Data.Set (fromFoldable) as S
import Data.Show.Generic (genericShow)
import Data.Tuple (snd)
import Dict (Dict)
import Literal (Literal)
import Util (type (×), singleton, (×))
import Util.Map (keys)
import Util.Pair (Pair(..))
import Util.Set ((\\), (∪))

data Binop = Eq | Ne | Lt | Le | Gt | Ge | In | NotIn | Add | Sub | Mul | Div | FloorDiv | Mod | Pow

data Unop = Not | Pos | Neg

data Expr
   = Var Var
   | Lit Literal
   | Dictionary (List (Pair Expr)) -- constructor name Dict borks (import of same name)
   | Constr Name (List Expr)
   | List (List Expr)
   | Tuple (List Expr)
   | Matrix Expr (Var × Var) Expr
   | Lambda Def
   | Attribute Expr Var -- attribute x of a dataclass instance
   | Subscript Expr Expr
   | ModMember Name Var -- member x of module q; only arises during desugaring
   | App Expr (List Expr)
   | BinOp Expr Binop Expr
   | UnOp Unop Expr
   | And Expr Expr
   | Or Expr Expr
   | Cond Expr Expr Expr -- e1 if e else e2
   | ListComp Expr (List Qualifier)
   | DictComp Expr Expr (List Qualifier)
   | DocExpr Expr Expr

-- Comprehension qualifiers; the spec has only guards and generators over variables.
data Qualifier
   = Guard Expr
   | Generator Pattern Expr
   | Decl Pattern Expr

data Pattern
   = PLit Literal
   | PVar Var
   | PWild
   | PConstr Name (List Pattern) (List (Bind Pattern))
   | PRecord (List (Bind Pattern))
   | PList (List Pattern)
   | PTuple (List Pattern)
   | PAs Pattern Var

-- Parameters and body of a function.
data Def = Def (List Var) Stmt

-- Mutually recursive function definitions.
newtype RecDefs = RecDefs (Dict Def)

-- Case of a match statement.
type Case = Pattern × Stmt

-- Condition and body of an if or elif clause.
data Branch = Branch Expr Stmt

data Stmt
   = Return Expr
   | If (NonEmptyList Branch) (Maybe Stmt)
   | Match Expr (NonEmptyList Case)
   | Assign Pattern Expr -- assignment to a pattern; the spec has only variables
   | DefRec RecDefs
   | Pass
   | ExprStmt Expr
   | Assert Expr (Maybe Expr)
   | Dataclass Name -- class declaration, by fully-qualified name
   | Seq Stmt Stmt

data Import = Import Name (Maybe (List Var))

data Module = Module (List Import) (List Stmt)

class FV a where
   fv :: a -> Set Var

instance FV Expr where
   fv (Var x) = singleton x
   fv (Lit _) = empty
   fv (Dictionary ees) = unions ((\(Pair e e') -> fv e ∪ fv e') <$> ees)
   fv (Constr _ es) = unions (fv <$> es)
   fv (List es) = unions (fv <$> es)
   fv (Tuple es) = unions (fv <$> es)
   fv (Matrix e1 _ e2) = fv e1 ∪ fv e2
   fv (Lambda d) = fv d
   fv (Attribute e _) = fv e
   fv (Subscript e x) = fv e ∪ fv x
   fv (ModMember _ _) = empty
   fv (App e es) = fv e ∪ unions (fv <$> es)
   fv (BinOp e _ e') = fv e ∪ fv e'
   fv (UnOp _ e) = fv e
   fv (And e e') = fv e ∪ fv e'
   fv (Or e e') = fv e ∪ fv e'
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (ListComp e gs) = fvQualifiers gs ∪ (fv e \\ bv gs)
   fv (DictComp e e' gs) = fvQualifiers gs ∪ ((fv e ∪ fv e') \\ bv gs)
   fv (DocExpr doc e) = (fv doc \\ singleton varThis) ∪ fv e

fvQualifiers :: List Qualifier -> Set Var
fvQualifiers Nil = empty
fvQualifiers (Guard e : gs) = fv e ∪ fvQualifiers gs
fvQualifiers (Generator p e : gs) = fv e ∪ (fvQualifiers gs \\ bv p)
fvQualifiers (Decl p e : gs) = fv e ∪ (fvQualifiers gs \\ bv p)

instance FV Def where
   fv (Def xs s) = fv s \\ S.fromFoldable xs

instance FV RecDefs where
   fv (RecDefs ds) = fv ds

instance FV Branch where
   fv (Branch e s) = fv e ∪ fv s

instance FV Stmt where
   fv (Return e) = fv e
   fv (If bs s_opt) = unions (fv <$> bs) ∪ fv s_opt
   fv (Match e bs) = fv e ∪ unions ((\(p × s) -> fv s \\ bv p) <$> bs)
   fv (Assign _ e) = fv e
   fv (DefRec ds) = fv ds
   fv Pass = empty
   fv (ExprStmt e) = fv e
   fv (Assert e e_opt) = fv e ∪ fv e_opt
   fv (Dataclass _) = empty
   fv (Seq s s') = fv s ∪ fv s'

instance FV a => FV (Dict a) where
   fv ds = unions (fv <$> ds) \\ S.fromFoldable (keys ds)

instance (FV a, FV b) => FV (a × b) where
   fv (x × y) = fv x ∪ fv y

instance FV a => FV (Maybe a) where
   fv Nothing = empty
   fv (Just x) = fv x

instance (FV a) => FV (List a) where
   fv xs = unions (fv <$> xs)

class BV a where
   bv :: a -> Set Var

instance BV Pattern where
   bv (PLit _) = empty
   bv (PVar x) = singleton x
   bv PWild = empty
   bv (PConstr _ ps xps) = unions (bv <$> ps) ∪ unions ((bv <<< snd) <$> xps)
   bv (PRecord xps) = unions ((bv <<< snd) <$> xps)
   bv (PList ps) = unions (bv <$> ps)
   bv (PTuple ps) = unions (bv <$> ps)
   bv (PAs p x) = bv p ∪ singleton x

instance BV Qualifier where
   bv (Guard _) = empty
   bv (Generator p _) = bv p
   bv (Decl p _) = bv p

instance BV a => BV (List a) where
   bv xs = unions (bv <$> xs)

assigns :: Stmt -> Set Var
assigns (Return _) = empty
assigns (If bs s_opt) = unions ((\(Branch _ s) -> assigns s) <$> bs) ∪ maybe empty assigns s_opt
assigns (Match _ bs) = unions ((\(p × s) -> bv p ∪ assigns s) <$> bs)
assigns (Assign p _) = bv p
assigns (DefRec (RecDefs ds)) = S.fromFoldable (keys ds)
assigns Pass = empty
assigns (ExprStmt _) = empty
assigns (Assert _ _) = empty
assigns (Dataclass c) = singleton (last c)
assigns (Seq s s') = assigns s ∪ assigns s'

-- ======================
-- boilerplate
-- ======================
derive instance Eq Expr
derive instance Eq Qualifier
derive instance Eq Binop
derive instance Generic Binop _
instance Show Binop where
   show = genericShow

derive instance Eq Unop
derive instance Generic Unop _
instance Show Unop where
   show = genericShow

derive instance Eq Def
derive instance Eq Pattern
derive instance Generic Pattern _
instance Show Pattern where
   show c = genericShow c

derive instance Eq RecDefs
derive instance Eq Branch
derive instance Eq Stmt
