module Expr where

import Prelude hiding (absurd, top)

import Bind (Bind, Name, Var)
import Control.Apply (lift2)
import Data.Foldable (class Foldable, foldl, foldrDefault, foldMapDefaultL)
import Data.Generic.Rep (class Generic)
import Data.List (List, zipWith)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty (zipWith) as NEL
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set, empty, unions)
import Data.Set (fromFoldable) as S
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (snd)
import Dict (Dict)
import Graph (class TypeName, class Vertices, DVertex'(..), Vertex, pack, vertices)
import Lattice (class BoundedJoinSemilattice, class Expandable, class JoinSemilattice, class MeetSemilattice, Raw, expand, (∧), (∨))
import Literal (Literal)
import Type as T
import Util (type (×), shapeMismatch, singleton, (×), (≜))
import Util.Map (keys)
import Util.Pair (Pair(..))
import Util.Set ((\\), (∪))

data Binop = Eq | Ne | Lt | Le | Gt | Ge | In | NotIn | Add | Sub | Mul | Div | FloorDiv | Mod | Pow

data Unop = Not | Pos | Neg

data Expr a
   = Var Var
   | Lit a Literal
   | Dictionary a (List (Pair (Expr a))) -- constructor name Dict borks (import of same name)
   | Constr a Name (List (Expr a))
   | Matrix a (Expr a) (Var × Var) (Expr a)
   | Lambda a (Def a)
   | Attribute (Expr a) Var -- attribute x of a dataclass instance
   | Subscript (Expr a) (Expr a)
   | ModMember Name Var -- member x of module q; only arises during desugaring
   | App (Expr a) (List (Expr a))
   | BinOp (Expr a) Binop (Expr a)
   | UnOp Unop (Expr a)
   | And (Expr a) (Expr a)
   | Or (Expr a) (Expr a)
   | Cond (Expr a) (Expr a) (Expr a) -- e1 if e else e2
   | DocExpr (Expr a) (Expr a)

data Pattern
   = PLit Literal
   | PVar Var
   | PWild
   | PConstr Name (List Pattern) (List (Bind Pattern))
   | PRecord (List (Bind Pattern))
   | PList (List Pattern)
   | PAs Pattern Var

data Param = Param Var (Maybe T.Type)

-- Parameters, return annotation and body of a function.
data Def a = Def (List Param) (Maybe T.Type) (Stmt a)

paramVar :: Param -> Var
paramVar (Param x _) = x

-- Mutually recursive function definitions.
data RecDefs a = RecDefs a (Dict (Def a))

-- Case of a match statement.
type Case a = Pattern × Stmt a

-- Condition and body of an if or elif clause.
data Branch a = Branch (Expr a) (Stmt a)

data Stmt a
   = Return (Expr a)
   | If (NonEmptyList (Branch a)) (Maybe (Stmt a))
   | Match (Expr a) (NonEmptyList (Case a))
   | Assign Pattern (Maybe T.Type) (Expr a) -- assignment to a pattern; the spec has only variables
   | DefRec (RecDefs a)
   | Pass
   | ExprStmt (Expr a)
   | Assert (Expr a) (Maybe (Expr a))
   | Seq (Stmt a) (Stmt a)

data Import = Import Name (Maybe (List Var))

data Module a = Module (List Import) (List (Stmt a))

class FV a where
   fv :: a -> Set Var

instance FV (Expr a) where
   fv (Var x) = singleton x
   fv (Lit _ _) = empty
   fv (Dictionary _ ees) = unions ((\(Pair e e') -> fv e ∪ fv e') <$> ees)
   fv (Constr _ _ es) = unions (fv <$> es)
   fv (Matrix _ e1 _ e2) = fv e1 ∪ fv e2
   fv (Lambda _ d) = fv d
   fv (Attribute e _) = fv e
   fv (Subscript e x) = fv e ∪ fv x
   fv (ModMember _ _) = empty
   fv (App e es) = fv e ∪ unions (fv <$> es)
   fv (BinOp e _ e') = fv e ∪ fv e'
   fv (UnOp _ e) = fv e
   fv (And e e') = fv e ∪ fv e'
   fv (Or e e') = fv e ∪ fv e'
   fv (Cond e1 e e2) = fv e1 ∪ fv e ∪ fv e2
   fv (DocExpr doc e) = fv doc ∪ fv e

instance FV (Def a) where
   fv (Def xs _ s) = fv s \\ S.fromFoldable (paramVar <$> xs)

instance FV (RecDefs a) where
   fv (RecDefs _ ds) = fv ds

instance FV (Branch a) where
   fv (Branch e s) = fv e ∪ fv s

instance FV (Stmt a) where
   fv (Return e) = fv e
   fv (If bs s_opt) = unions (fv <$> bs) ∪ fv s_opt
   fv (Match e bs) = fv e ∪ unions ((\(p × s) -> fv s \\ bv p) <$> bs)
   fv (Assign _ _ e) = fv e
   fv (DefRec ds) = fv ds
   fv Pass = empty
   fv (ExprStmt e) = fv e
   fv (Assert e e_opt) = fv e ∪ fv e_opt
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
   bv (PAs p x) = bv p ∪ singleton x

instance JoinSemilattice a => JoinSemilattice (Def a) where
   join (Def xs ψ s) (Def xs' ψ' s') = Def (xs ≜ xs') (ψ ≜ ψ') (s ∨ s')

instance BoundedJoinSemilattice a => Expandable (Def a) (Raw Def) where
   expand (Def xs ψ s) (Def xs' ψ' s') = Def (xs ≜ xs') (ψ ≜ ψ') (expand s s')

instance JoinSemilattice a => JoinSemilattice (RecDefs a) where
   join (RecDefs α ds) (RecDefs α' ds') = RecDefs (α ∨ α') (ds ∨ ds')

instance BoundedJoinSemilattice a => Expandable (RecDefs a) (Raw RecDefs) where
   expand (RecDefs α ds) (RecDefs _ ds') = RecDefs α (expand ds ds')

instance JoinSemilattice a => JoinSemilattice (Branch a) where
   join (Branch e s) (Branch e' s') = Branch (e ∨ e') (s ∨ s')

instance BoundedJoinSemilattice a => Expandable (Branch a) (Raw Branch) where
   expand (Branch e s) (Branch e' s') = Branch (expand e e') (expand s s')

instance JoinSemilattice a => JoinSemilattice (Stmt a) where
   join (Return e) (Return e') = Return (e ∨ e')
   join (If bs s_opt) (If bs' s_opt') = If (NEL.zipWith (∨) bs bs') (s_opt ∨ s_opt')
   join (Match e bs) (Match e' bs') = Match (e ∨ e') (NEL.zipWith joinCase bs bs')
      where
      joinCase (p × s) (p' × s') = (p ≜ p') × (s ∨ s')
   join (Assign p ψ e) (Assign p' ψ' e') = Assign (p ≜ p') (ψ ≜ ψ') (e ∨ e')
   join (DefRec ds) (DefRec ds') = DefRec (ds ∨ ds')
   join Pass Pass = Pass
   join (ExprStmt e) (ExprStmt e') = ExprStmt (e ∨ e')
   join (Assert e e_opt) (Assert e' e_opt') = Assert (e ∨ e') (e_opt ∨ e_opt')
   join (Seq s1 s2) (Seq s1' s2') = Seq (s1 ∨ s1') (s2 ∨ s2')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Stmt a) (Raw Stmt) where
   expand (Return e) (Return e') = Return (expand e e')
   expand (If bs s_opt) (If bs' s_opt') = If (NEL.zipWith expand bs bs') (expand s_opt s_opt')
   expand (Match e bs) (Match e' bs') = Match (expand e e') (NEL.zipWith expandCase bs bs')
      where
      expandCase (p × s) (p' × s') = (p ≜ p') × expand s s'
   expand (Assign p ψ e) (Assign p' ψ' e') = Assign (p ≜ p') (ψ ≜ ψ') (expand e e')
   expand (DefRec ds) (DefRec ds') = DefRec (expand ds ds')
   expand Pass Pass = Pass
   expand (ExprStmt e) (ExprStmt e') = ExprStmt (expand e e')
   expand (Assert e e_opt) (Assert e' e_opt') = Assert (expand e e') (expand e_opt e_opt')
   expand (Seq s1 s2) (Seq s1' s2') = Seq (expand s1 s1') (expand s2 s2')
   expand _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (Expr a) where
   join (Var x) (Var x') = Var (x ≜ x')
   join (Lit α ℓ) (Lit α' ℓ') = Lit (α ∨ α') (ℓ ≜ ℓ')
   join (Dictionary α ees) (Dictionary α' ees') = Dictionary (α ∨ α') (ees ∨ ees')
   join (Constr α c es) (Constr α' c' es') = Constr (α ∨ α') (c ≜ c') (es ∨ es')
   join (Matrix α e1 (x × y) e2) (Matrix α' e1' (x' × y') e2') =
      Matrix (α ∨ α') (e1 ∨ e1') ((x ≜ x') × (y ≜ y')) (e2 ∨ e2')
   join (Lambda α d) (Lambda α' d') = Lambda (α ∨ α') (d ∨ d')
   join (Attribute e x) (Attribute e' x') = Attribute (e ∨ e') (x ≜ x')
   join (Subscript e1 e2) (Subscript e1' e2') = Subscript (e1 ∨ e1') (e2 ∨ e2')
   join (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   join (App e es) (App e' es') = App (e ∨ e') (es ∨ es')
   join (BinOp e1 op e2) (BinOp e1' op' e2') = BinOp (e1 ∨ e1') (op ≜ op') (e2 ∨ e2')
   join (UnOp op e) (UnOp op' e') = UnOp (op ≜ op') (e ∨ e')
   join (And e1 e2) (And e1' e2') = And (e1 ∨ e1') (e2 ∨ e2')
   join (Or e1 e2) (Or e1' e2') = Or (e1 ∨ e1') (e2 ∨ e2')
   join (Cond e1 e e2) (Cond e1' e' e2') = Cond (e1 ∨ e1') (e ∨ e') (e2 ∨ e2')
   join (DocExpr doc e) (DocExpr doc' e') = DocExpr (doc ∨ doc') (e ∨ e')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Expr a) (Raw Expr) where
   expand (Var x) (Var x') = Var (x ≜ x')
   expand (Lit α ℓ) (Lit _ ℓ') = Lit α (ℓ ≜ ℓ')
   expand (Dictionary α ees) (Dictionary _ ees') = Dictionary α (expand ees ees')
   expand (Constr α c es) (Constr _ c' es') = Constr α (c ≜ c') (expand es es')
   expand (Matrix α e1 (x × y) e2) (Matrix _ e1' (x' × y') e2') =
      Matrix α (expand e1 e1') ((x ≜ x') × (y ≜ y')) (expand e2 e2')
   expand (Lambda α d) (Lambda _ d') = Lambda α (expand d d')
   expand (Attribute e x) (Attribute e' x') = Attribute (expand e e') (x ≜ x')
   expand (Subscript e1 e2) (Subscript e1' e2') = Subscript (expand e1 e1') (expand e2 e2')
   expand (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   expand (App e es) (App e' es') = App (expand e e') (expand es es')
   expand (BinOp e1 op e2) (BinOp e1' op' e2') = BinOp (expand e1 e1') (op ≜ op') (expand e2 e2')
   expand (UnOp op e) (UnOp op' e') = UnOp (op ≜ op') (expand e e')
   expand (And e1 e2) (And e1' e2') = And (expand e1 e1') (expand e2 e2')
   expand (Or e1 e2) (Or e1' e2') = Or (expand e1 e1') (expand e2 e2')
   expand (Cond e1 e e2) (Cond e1' e' e2') = Cond (expand e1 e1') (expand e e') (expand e2 e2')
   expand (DocExpr doc e) (DocExpr doc' e') = DocExpr (expand doc doc') (expand e e')
   expand _ _ = shapeMismatch unit

instance MeetSemilattice a => MeetSemilattice (Expr a) where
   meet = lift2 (∧)

instance Vertices (Expr Vertex) where
   vertices (Var _) = empty
   vertices e@(Lit α _) = singleton (DVertex (α × pack e))
   vertices d@(Dictionary α ees) = singleton (DVertex (α × pack d)) ∪ unions (go <$> ees)
      where
      go (Pair e e') = vertices e ∪ vertices e'
   vertices e@(Constr α _ es) = singleton (DVertex (α × pack e)) ∪ unions (vertices <$> es)
   vertices e@(Matrix α e1 _ e2) = singleton (DVertex (α × pack e)) ∪ vertices e1 ∪ vertices e2
   vertices e@(Lambda α d) = singleton (DVertex (α × pack e)) ∪ vertices d
   vertices (Attribute e _) = vertices e
   vertices (Subscript e e') = vertices e ∪ vertices e'
   vertices (ModMember _ _) = empty
   vertices (App e es) = vertices e ∪ unions (vertices <$> es)
   vertices (BinOp e _ e') = vertices e ∪ vertices e'
   vertices (UnOp _ e) = vertices e
   vertices (And e e') = vertices e ∪ vertices e'
   vertices (Or e e') = vertices e ∪ vertices e'
   vertices (Cond e1 e e2) = vertices e1 ∪ vertices e ∪ vertices e2
   vertices (DocExpr e e') = vertices e ∪ vertices e'

instance Vertices (Def Vertex) where
   vertices (Def _ _ s) = vertices s

instance Vertices (RecDefs Vertex) where
   vertices defs@(RecDefs α ds) = singleton (DVertex (α × pack defs)) ∪ vertices ds

instance Vertices (Branch Vertex) where
   vertices (Branch e s) = vertices e ∪ vertices s

instance Vertices (Stmt Vertex) where
   vertices (Return e) = vertices e
   vertices (If bs s_opt) = unions (vertices <$> bs) ∪ maybe empty vertices s_opt
   vertices (Match e bs) = vertices e ∪ unions ((vertices <<< snd) <$> bs)
   vertices (Assign _ _ e) = vertices e
   vertices (DefRec ds) = vertices ds
   vertices Pass = empty
   vertices (ExprStmt e) = vertices e
   vertices (Assert e e_opt) = vertices e ∪ maybe empty vertices e_opt
   vertices (Seq s1 s2) = vertices s1 ∪ vertices s2

instance Vertices (Module Vertex) where
   vertices (Module _ ss) = unions (vertices <$> ss)

-- ======================
-- boilerplate
-- ======================
derive instance Functor Def
derive instance Foldable Def
derive instance Traversable Def
derive instance Functor Expr
derive instance Foldable Expr
derive instance Traversable Expr
derive instance Functor RecDefs
derive instance Foldable RecDefs
derive instance Traversable RecDefs
derive instance Functor Branch
derive instance Foldable Branch
derive instance Traversable Branch
derive instance Functor Stmt
derive instance Foldable Stmt
derive instance Traversable Stmt
derive instance Functor Module

-- For terms of a fixed shape.
instance Apply Expr where
   apply (Var x) (Var x') = Var (x ≜ x')
   apply (Lit fα ℓ) (Lit α ℓ') = Lit (fα α) (ℓ ≜ ℓ')
   apply (Dictionary fα fxes) (Dictionary α xes) = Dictionary (fα α) (zipWith (lift2 (<*>)) fxes xes)
   apply (Constr fα c fes) (Constr α c' es) = Constr (fα α) (c ≜ c') (zipWith (<*>) fes es)
   apply (Matrix fα fe1 (x × y) fe2) (Matrix α e1 (x' × y') e2) =
      Matrix (fα α) (fe1 <*> e1) ((x ≜ x') × (y ≜ y')) (fe2 <*> e2)
   apply (Lambda fα fd) (Lambda α d) = Lambda (fα α) (fd <*> d)
   apply (Attribute fe x) (Attribute e x') = Attribute (fe <*> e) (x ≜ x')
   apply (Subscript fd fk) (Subscript d k) = Subscript (fd <*> d) (fk <*> k)
   apply (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   apply (App fe fes) (App e es) = App (fe <*> e) (zipWith (<*>) fes es)
   apply (BinOp fe1 op fe2) (BinOp e1 op' e2) = BinOp (fe1 <*> e1) (op ≜ op') (fe2 <*> e2)
   apply (UnOp op fe) (UnOp op' e) = UnOp (op ≜ op') (fe <*> e)
   apply (And fe1 fe2) (And e1 e2) = And (fe1 <*> e1) (fe2 <*> e2)
   apply (Or fe1 fe2) (Or e1 e2) = Or (fe1 <*> e1) (fe2 <*> e2)
   apply (Cond fe1 fe fe2) (Cond e1 e e2) = Cond (fe1 <*> e1) (fe <*> e) (fe2 <*> e2)
   apply (DocExpr fe fe') (DocExpr e e') = DocExpr (fe <*> e) (fe' <*> e')
   apply _ _ = shapeMismatch unit

instance Apply Def where
   apply (Def xs ψ fs) (Def _ _ s) = Def xs ψ (fs <*> s)

instance Apply RecDefs where
   apply (RecDefs fα fds) (RecDefs α ds) = RecDefs (fα α) (((<*>) <$> fds) <*> ds)

instance Apply Branch where
   apply (Branch fe fs) (Branch e s) = Branch (fe <*> e) (fs <*> s)

instance Apply Stmt where
   apply (Return fe) (Return e) = Return (fe <*> e)
   apply (If fbs fs_opt) (If bs s_opt) = If (NEL.zipWith (<*>) fbs bs) (lift2 (<*>) fs_opt s_opt)
   apply (Match fe fbs) (Match e bs) = Match (fe <*> e) (NEL.zipWith applyCase fbs bs)
      where
      applyCase (p × fs) (_ × s) = p × (fs <*> s)
   apply (Assign p ψ fe) (Assign _ _ e) = Assign p ψ (fe <*> e)
   apply (DefRec fds) (DefRec ds) = DefRec (fds <*> ds)
   apply Pass Pass = Pass
   apply (ExprStmt fe) (ExprStmt e) = ExprStmt (fe <*> e)
   apply (Assert fe fe_opt) (Assert e e_opt) = Assert (fe <*> e) (lift2 (<*>) fe_opt e_opt)
   apply (Seq fs1 fs2) (Seq s1 s2) = Seq (fs1 <*> s1) (fs2 <*> s2)
   apply _ _ = shapeMismatch unit

instance Apply Module where
   apply (Module fis fss) (Module _ ss) = Module fis (zipWith (<*>) fss ss)

instance Foldable Module where
   foldl f acc (Module _ ss) = foldl (foldl f) acc ss
   foldr f = foldrDefault f
   foldMap f = foldMapDefaultL f

instance Traversable Module where
   traverse f (Module is ss) = Module is <$> traverse (traverse f) ss
   sequence = sequenceDefault

derive instance Eq a => Eq (Expr a)
derive instance Eq Binop
derive instance Generic Binop _
instance Show Binop where
   show = genericShow

derive instance Eq Unop
derive instance Generic Unop _
instance Show Unop where
   show = genericShow

derive instance Eq Param
derive instance Generic Param _
instance Show Param where
   show c = genericShow c

derive instance Eq a => Eq (Def a)
derive instance Eq Pattern
derive instance Generic Pattern _
instance Show Pattern where
   show c = genericShow c

derive instance Eq a => Eq (RecDefs a)
derive instance Eq a => Eq (Branch a)
derive instance Eq a => Eq (Stmt a)

instance TypeName (RecDefs a) where
   typeName _ = "RecDefs"

instance TypeName (Expr a) where
   typeName _ = "Expr"
