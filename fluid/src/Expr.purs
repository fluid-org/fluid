module Expr where

import Prelude hiding (absurd, top)

import Bind (Name, Var)
import Control.Apply (lift2)
import Data.Foldable (class Foldable, foldl, foldrDefault, foldMapDefaultL)
import Data.List (List, zipWith)
import Data.List.NonEmpty (NonEmptyList)
import Data.List.NonEmpty (zipWith) as NEL
import Data.Maybe (Maybe(..))
import Data.Set (Set, empty, unions)
import Data.Set (fromFoldable) as S
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (snd)
import Dict (Dict)
import Graph (class TypeName, class Vertices, DVertex'(..), Vertex, pack, vertices)
import Lattice (class BoundedJoinSemilattice, class Expandable, class JoinSemilattice, class MeetSemilattice, Raw, expand, (∧), (∨))
import Pattern (class BV, Pattern, bv)
import Util (type (×), error, shapeMismatch, singleton, (×), (≜))
import Util.Map (keys, asMaplet)
import Util.Pair (Pair(..))
import Util.Set ((\\), (∪))

-- Deviate from POPL paper by having closures depend on originating lambda or letrec
data Expr a
   = Var Var
   | Op Var
   | Int a Int
   | Float a Number
   | Str a String
   | Dictionary a (List (Pair (Expr a))) -- constructor name Dict borks (import of same name)
   | Constr a Name (List (Expr a))
   | Matrix a (Expr a) (Var × Var) (Expr a)
   | Lambda a (Elim a)
   | Attribute (Expr a) Var -- attribute x of a dataclass instance
   | Subscript (Expr a) (Expr a)
   | ModMember Name Var -- member x of module q; only arises during desugaring
   | App (Expr a) (Expr a)
   | DocExpr (Expr a) (Expr a)

-- eliminator here is a singleton with null terminal continuation
data VarDef a = VarDef (Elim a) (Expr a)
data RecDefs a = RecDefs a (Dict (Elim a))

data Elim a
   = ElimVar Var (Cont a)
   | ElimConstr (Dict (Cont a))
   | ElimDict (Set Var) (Cont a)

-- Continuation of an eliminator branch.
data Cont a
   = ContElim (Elim a)
   | ContStmt (Stmt a)

asElim :: forall a. Cont a -> Elim a
asElim (ContElim σ) = σ
asElim _ = error "Eliminator expected"

asStmt :: forall a. Cont a -> Stmt a
asStmt (ContStmt s) = s
asStmt _ = error "Statement expected"

data Stmt a
   = Return (Expr a)
   | Match (Expr a) (NonEmptyList (Pattern × Stmt a))
   | Def (VarDef a)
   | DefRec (RecDefs a)
   | Pass
   | ExprStmt (Expr a)
   | Seq (Stmt a) (Stmt a)

data Import = Import Name (Maybe (List Var))

data Module a = Module (List Import) (List (Stmt a))

class FV a where
   fv :: a -> Set Var

instance FV (Expr a) where
   fv (Var x) = singleton x
   fv (Op op) = singleton op
   fv (Int _ _) = empty
   fv (Float _ _) = empty
   fv (Str _ _) = empty
   fv (Dictionary _ ees) = unions ((\(Pair e e') -> fv e ∪ fv e') <$> ees)
   fv (Constr _ _ es) = unions (fv <$> es)
   fv (Matrix _ e1 _ e2) = fv e1 ∪ fv e2
   fv (Lambda _ σ) = fv σ
   fv (Attribute e _) = fv e
   fv (Subscript e x) = fv e ∪ fv x
   fv (ModMember _ _) = empty
   fv (App e1 e2) = fv e1 ∪ fv e2
   fv (DocExpr doc e) = fv doc ∪ fv e

instance FV (Elim a) where
   fv (ElimVar x κ) = fv κ \\ singleton x
   fv (ElimConstr m) = unions (fv <$> m)
   fv (ElimDict _ κ) = fv κ

instance FV (Cont a) where
   fv (ContElim σ) = fv σ
   fv (ContStmt s) = fv s

instance FV (VarDef a) where
   fv (VarDef _ e) = fv e

instance FV (RecDefs a) where
   fv (RecDefs _ ρ) = fv ρ

instance FV (Stmt a) where
   fv (Return e) = fv e
   fv (Match e cases) = fv e ∪ unions ((\(p × s) -> fv s \\ bv p) <$> cases)
   fv (Def vd) = fv vd
   fv (DefRec ρ) = fv ρ
   fv Pass = empty
   fv (ExprStmt e) = fv e
   fv (Seq s s') = fv s ∪ fv s'

instance FV a => FV (Dict a) where
   fv ρ = unions (fv <$> ρ) \\ S.fromFoldable (keys ρ)

instance (FV a, FV b) => FV (a × b) where
   fv (x × y) = fv x ∪ fv y

instance FV a => FV (Maybe a) where
   fv Nothing = empty
   fv (Just x) = fv x

instance (FV a) => FV (List a) where
   fv xs = unions (fv <$> xs)

-- Bound variables, defined only for singleton eliminators.
instance BV (Elim a) where
   bv (ElimVar x κ) = singleton x ∪ bv κ
   bv (ElimConstr m) = bv (snd (asMaplet m))
   bv (ElimDict _ κ) = bv κ

instance BV (VarDef a) where
   bv (VarDef σ _) = bv σ

instance BV (Cont a) where
   bv (ContElim σ) = bv σ
   bv (ContStmt _) = empty

instance JoinSemilattice a => JoinSemilattice (Elim a) where
   join (ElimVar x κ) (ElimVar x' κ') = ElimVar (x ≜ x') (κ ∨ κ')
   join (ElimConstr cκs) (ElimConstr cκs') = ElimConstr (cκs ∨ cκs')
   join (ElimDict xs κ) (ElimDict ys κ') = ElimDict (xs ≜ ys) (κ ∨ κ')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Elim a) (Raw Elim) where
   expand (ElimVar x κ) (ElimVar x' κ') = ElimVar (x ≜ x') (expand κ κ')
   expand (ElimConstr cκs) (ElimConstr cκs') = ElimConstr (expand cκs cκs')
   expand (ElimDict xs κ) (ElimDict ys κ') = ElimDict (xs ≜ ys) (expand κ κ')
   expand _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (Cont a) where
   join (ContElim σ) (ContElim σ') = ContElim (σ ∨ σ')
   join (ContStmt s) (ContStmt s') = ContStmt (s ∨ s')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Cont a) (Raw Cont) where
   expand (ContElim σ) (ContElim σ') = ContElim (expand σ σ')
   expand (ContStmt s) (ContStmt s') = ContStmt (expand s s')
   expand _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (VarDef a) where
   join (VarDef σ e) (VarDef σ' e') = VarDef (σ ∨ σ') (e ∨ e')

instance BoundedJoinSemilattice a => Expandable (VarDef a) (Raw VarDef) where
   expand (VarDef σ e) (VarDef σ' e') = VarDef (expand σ σ') (expand e e')

instance JoinSemilattice a => JoinSemilattice (RecDefs a) where
   join (RecDefs α ρ) (RecDefs α' ρ') = RecDefs (α ∨ α') (ρ ∨ ρ')

instance BoundedJoinSemilattice a => Expandable (RecDefs a) (Raw RecDefs) where
   expand (RecDefs α ρ) (RecDefs _ ρ') = RecDefs α (expand ρ ρ')

instance JoinSemilattice a => JoinSemilattice (Stmt a) where
   join (Return e) (Return e') = Return (e ∨ e')
   join (Match e cases) (Match e' cases') = Match (e ∨ e') (NEL.zipWith joinCase cases cases')
      where
      joinCase (p × s) (p' × s') = (p ≜ p') × (s ∨ s')
   join (Def vd) (Def vd') = Def (vd ∨ vd')
   join (DefRec ρ) (DefRec ρ') = DefRec (ρ ∨ ρ')
   join Pass Pass = Pass
   join (ExprStmt e) (ExprStmt e') = ExprStmt (e ∨ e')
   join (Seq s1 s2) (Seq s1' s2') = Seq (s1 ∨ s1') (s2 ∨ s2')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Stmt a) (Raw Stmt) where
   expand (Return e) (Return e') = Return (expand e e')
   expand (Match e cases) (Match e' cases') = Match (expand e e') (NEL.zipWith expandCase cases cases')
      where
      expandCase (p × s) (p' × s') = (p ≜ p') × expand s s'
   expand (Def vd) (Def vd') = Def (expand vd vd')
   expand (DefRec ρ) (DefRec ρ') = DefRec (expand ρ ρ')
   expand Pass Pass = Pass
   expand (ExprStmt e) (ExprStmt e') = ExprStmt (expand e e')
   expand (Seq s1 s2) (Seq s1' s2') = Seq (expand s1 s1') (expand s2 s2')
   expand _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (Expr a) where
   join (Var x) (Var x') = Var (x ≜ x')
   join (Op op) (Op op') = Op (op ≜ op')
   join (Int α n) (Int α' n') = Int (α ∨ α') (n ≜ n')
   join (Str α str) (Str α' str') = Str (α ∨ α') (str ≜ str')
   join (Float α n) (Float α' n') = Float (α ∨ α') (n ≜ n')
   join (Dictionary α ees) (Dictionary α' ees') = Dictionary (α ∨ α') (ees ∨ ees')
   join (Constr α c es) (Constr α' c' es') = Constr (α ∨ α') (c ≜ c') (es ∨ es')
   join (Matrix α e1 (x × y) e2) (Matrix α' e1' (x' × y') e2') =
      Matrix (α ∨ α') (e1 ∨ e1') ((x ≜ x') × (y ≜ y')) (e2 ∨ e2')
   join (Lambda α σ) (Lambda α' σ') = Lambda (α ∨ α') (σ ∨ σ')
   join (Attribute e x) (Attribute e' x') = Attribute (e ∨ e') (x ≜ x')
   join (Subscript e1 e2) (Subscript e1' e2') = Subscript (e1 ∨ e1') (e2 ∨ e2')
   join (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   join (App e1 e2) (App e1' e2') = App (e1 ∨ e1') (e2 ∨ e2')
   join (DocExpr doc e) (DocExpr doc' e') = DocExpr (doc ∨ doc') (e ∨ e')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Expr a) (Raw Expr) where
   expand (Var x) (Var x') = Var (x ≜ x')
   expand (Op op) (Op op') = Op (op ≜ op')
   expand (Int α n) (Int _ n') = Int α (n ≜ n')
   expand (Str α str) (Str _ str') = Str α (str ≜ str')
   expand (Float α n) (Float _ n') = Float α (n ≜ n')
   expand (Dictionary α ees) (Dictionary _ ees') = Dictionary α (expand ees ees')
   expand (Constr α c es) (Constr _ c' es') = Constr α (c ≜ c') (expand es es')
   expand (Matrix α e1 (x × y) e2) (Matrix _ e1' (x' × y') e2') =
      Matrix α (expand e1 e1') ((x ≜ x') × (y ≜ y')) (expand e2 e2')
   expand (Lambda α σ) (Lambda _ σ') = Lambda α (expand σ σ')
   expand (Attribute e x) (Attribute e' x') = Attribute (expand e e') (x ≜ x')
   expand (Subscript e1 e2) (Subscript e1' e2') = Subscript (expand e1 e1') (expand e2 e2')
   expand (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   expand (App e1 e2) (App e1' e2') = App (expand e1 e1') (expand e2 e2')
   expand (DocExpr doc e) (DocExpr doc' e') = DocExpr (expand doc doc') (expand e e')
   expand _ _ = shapeMismatch unit

instance MeetSemilattice a => MeetSemilattice (Expr a) where
   meet = lift2 (∧)

instance Vertices (Expr Vertex) where
   vertices (Var _) = empty
   vertices (Op _) = empty
   vertices e@(Int α _) = singleton (DVertex (α × pack e))
   vertices e@(Float α _) = singleton (DVertex (α × pack e))
   vertices e@(Str α _) = singleton (DVertex (α × pack e))
   vertices d@(Dictionary α ees) = singleton (DVertex (α × pack d)) ∪ unions (go <$> ees)
      where
      go (Pair e e') = vertices e ∪ vertices e'
   vertices e@(Constr α _ es) = singleton (DVertex (α × pack e)) ∪ unions (vertices <$> es)
   vertices e@(Matrix α e1 _ e2) = singleton (DVertex (α × pack e)) ∪ vertices e1 ∪ vertices e2
   vertices e@(Lambda α σ) = singleton (DVertex (α × pack e)) ∪ vertices σ
   vertices (Attribute e _) = vertices e
   vertices (Subscript e e') = vertices e ∪ vertices e'
   vertices (ModMember _ _) = empty
   vertices (App e1 e2) = vertices e1 ∪ vertices e2
   vertices (DocExpr e e') = vertices e ∪ vertices e'

instance Vertices (Elim Vertex) where
   vertices (ElimVar _ κ) = vertices κ
   vertices (ElimConstr m) = vertices m
   vertices (ElimDict _ κ) = vertices κ

instance Vertices (VarDef Vertex) where
   vertices (VarDef σ e) = vertices σ ∪ vertices e

instance Vertices (Cont Vertex) where
   vertices (ContElim σ) = vertices σ
   vertices (ContStmt s) = vertices s

instance Vertices (RecDefs Vertex) where
   vertices defs@(RecDefs α ρ) = singleton (DVertex (α × pack defs)) ∪ vertices ρ

instance Vertices (Stmt Vertex) where
   vertices (Return e) = vertices e
   vertices (Match e cases) = vertices e ∪ unions ((vertices <<< snd) <$> cases)
   vertices (Def vd) = vertices vd
   vertices (DefRec ρ) = vertices ρ
   vertices Pass = empty
   vertices (ExprStmt e) = vertices e
   vertices (Seq s1 s2) = vertices s1 ∪ vertices s2

instance Vertices (Module Vertex) where
   vertices (Module _ ss) = unions (vertices <$> ss)

-- ======================
-- boilerplate
-- ======================
derive instance Functor VarDef
derive instance Foldable VarDef
derive instance Traversable VarDef
derive instance Functor Cont
derive instance Foldable Cont
derive instance Traversable Cont
derive instance Functor Elim
derive instance Foldable Elim
derive instance Traversable Elim
derive instance Functor Expr
derive instance Foldable Expr
derive instance Traversable Expr
derive instance Functor RecDefs
derive instance Foldable RecDefs
derive instance Traversable RecDefs
derive instance Functor Stmt
derive instance Foldable Stmt
derive instance Traversable Stmt
derive instance Functor Module

-- For terms of a fixed shape.
instance Apply Expr where
   apply (Var x) (Var x') = Var (x ≜ x')
   apply (Op op) (Op _) = Op op
   apply (Int fα n) (Int α n') = Int (fα α) (n ≜ n')
   apply (Float fα n) (Float α n') = Float (fα α) (n ≜ n')
   apply (Str fα s) (Str α s') = Str (fα α) (s ≜ s')
   apply (Dictionary fα fxes) (Dictionary α xes) = Dictionary (fα α) (zipWith (lift2 (<*>)) fxes xes)
   apply (Constr fα c fes) (Constr α c' es) = Constr (fα α) (c ≜ c') (zipWith (<*>) fes es)
   apply (Matrix fα fe1 (x × y) fe2) (Matrix α e1 (x' × y') e2) =
      Matrix (fα α) (fe1 <*> e1) ((x ≜ x') × (y ≜ y')) (fe2 <*> e2)
   apply (Lambda fα fσ) (Lambda α σ) = Lambda (fα α) (fσ <*> σ)
   apply (Attribute fe x) (Attribute e x') = Attribute (fe <*> e) (x ≜ x')
   apply (Subscript fd fk) (Subscript d k) = Subscript (fd <*> d) (fk <*> k)
   apply (ModMember q x) (ModMember q' x') = ModMember (q ≜ q') (x ≜ x')
   apply (App fe1 fe2) (App e1 e2) = App (fe1 <*> e1) (fe2 <*> e2)
   apply (DocExpr fe fe') (DocExpr e e') = DocExpr (fe <*> e) (fe' <*> e')
   apply _ _ = shapeMismatch unit

instance Apply Elim where
   apply (ElimVar x fk) (ElimVar _ k) = ElimVar x (fk <*> k)
   apply (ElimConstr fk) (ElimConstr k) = ElimConstr (((<*>) <$> fk) <*> k)
   apply (ElimDict xs fk) (ElimDict _ k) = ElimDict xs (fk <*> k)
   apply _ _ = shapeMismatch unit

instance Apply Cont where
   apply (ContElim fσ) (ContElim σ) = ContElim (fσ <*> σ)
   apply (ContStmt fs) (ContStmt s) = ContStmt (fs <*> s)
   apply _ _ = shapeMismatch unit

instance Apply VarDef where
   apply (VarDef fσ fe) (VarDef σ e) = VarDef (fσ <*> σ) (fe <*> e)

instance Apply RecDefs where
   apply (RecDefs fα fρ) (RecDefs α ρ) = RecDefs (fα α) (((<*>) <$> fρ) <*> ρ)

instance Apply Stmt where
   apply (Return fe) (Return e) = Return (fe <*> e)
   apply (Match fe fcases) (Match e cases) = Match (fe <*> e) (NEL.zipWith applyCase fcases cases)
      where
      applyCase (p × fs) (_ × s) = p × (fs <*> s)
   apply (Def fvd) (Def vd) = Def (fvd <*> vd)
   apply (DefRec fρ) (DefRec ρ) = DefRec (fρ <*> ρ)
   apply Pass Pass = Pass
   apply (ExprStmt fe) (ExprStmt e) = ExprStmt (fe <*> e)
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
derive instance Eq a => Eq (Elim a)
derive instance Eq a => Eq (Cont a)
derive instance Eq a => Eq (VarDef a)
derive instance Eq a => Eq (RecDefs a)
derive instance Eq a => Eq (Stmt a)

instance TypeName (RecDefs a) where
   typeName _ = "RecDefs"

instance TypeName (Expr a) where
   typeName _ = "Expr"
