module Expr where

import Prelude hiding (absurd, top)

import Bind (Var)
import Control.Apply (lift2)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldl, foldrDefault, foldMapDefaultL)
import Data.List (List(..), (:), zipWith)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set, empty, unions)
import Data.Set (fromFoldable) as S
import Data.Traversable (class Traversable, sequenceDefault, traverse)
import Data.Tuple (snd)
import DataType (Ctr)
import Dict (Dict)
import Graph (class TypeName, class Vertices, DVertex'(..), Vertex, pack, vertices)
import Lattice (class BoundedJoinSemilattice, class Expandable, class JoinSemilattice, class MeetSemilattice, Raw, expand, (∧), (∨))
import Util (type (+), type (×), error, shapeMismatch, singleton, (×), (≜))
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
   | Constr a Ctr (List (Expr a))
   | Matrix a (Expr a) (Var × Var) (Expr a)
   | Lambda a (Elim a)
   | DProject (Expr a) (Expr a)
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
   | Match (Expr a) (Elim a)
   | Def (VarDef a)
   | DefRec (RecDefs a)
   | Pass
   | ExprStmt (Expr a)
   | Seq (Stmt a) (Stmt a)

newtype Module a = Module (List (VarDef a + RecDefs a))

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
   fv (DProject e x) = fv e ∪ fv x
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
   fv (Match e σ) = fv e ∪ fv σ
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

class BV a where
   bv :: a -> Set Var

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
   join (Match e σ) (Match e' σ') = Match (e ∨ e') (σ ∨ σ')
   join (Def vd) (Def vd') = Def (vd ∨ vd')
   join (DefRec ρ) (DefRec ρ') = DefRec (ρ ∨ ρ')
   join Pass Pass = Pass
   join (ExprStmt e) (ExprStmt e') = ExprStmt (e ∨ e')
   join (Seq s1 s2) (Seq s1' s2') = Seq (s1 ∨ s1') (s2 ∨ s2')
   join _ _ = shapeMismatch unit

instance BoundedJoinSemilattice a => Expandable (Stmt a) (Raw Stmt) where
   expand (Return e) (Return e') = Return (expand e e')
   expand (Match e σ) (Match e' σ') = Match (expand e e') (expand σ σ')
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
   join (DProject e1 e2) (DProject e1' e2') = DProject (e1 ∨ e1') (e2 ∨ e2')
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
   expand (DProject e1 e2) (DProject e1' e2') = DProject (expand e1 e1') (expand e2 e2')
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
   vertices (DProject e e') = vertices e ∪ vertices e'
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
   vertices (Match e σ) = vertices e ∪ vertices σ
   vertices (Def vd) = vertices vd
   vertices (DefRec ρ) = vertices ρ
   vertices Pass = empty
   vertices (ExprStmt e) = vertices e
   vertices (Seq s1 s2) = vertices s1 ∪ vertices s2

instance Vertices (Module Vertex) where
   vertices (Module defs) = unions (go <$> defs)
      where
      go (Left vardef) = vertices vardef
      go (Right recdefs) = vertices recdefs

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
derive instance Newtype (Module a) _
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
   apply (DProject fd fk) (DProject d k) = DProject (fd <*> d) (fk <*> k)
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
   apply (Match fe fσ) (Match e σ) = Match (fe <*> e) (fσ <*> σ)
   apply (Def fvd) (Def vd) = Def (fvd <*> vd)
   apply (DefRec fρ) (DefRec ρ) = DefRec (fρ <*> ρ)
   apply Pass Pass = Pass
   apply (ExprStmt fe) (ExprStmt e) = ExprStmt (fe <*> e)
   apply (Seq fs1 fs2) (Seq s1 s2) = Seq (fs1 <*> s1) (fs2 <*> s2)
   apply _ _ = shapeMismatch unit

-- Apply instance for Either no good here as doesn't assume fixed shape.
instance Apply Module where
   apply (Module Nil) (Module Nil) = Module Nil
   apply (Module (Left fdef : fdefs)) (Module (Left def : defs)) =
      Module (Left (fdef <*> def) : unwrap (apply (Module fdefs) (Module defs)))
   apply (Module (Right fdef : fdefs)) (Module (Right def : defs)) =
      Module (Right (fdef <*> def) : unwrap (apply (Module fdefs) (Module defs)))
   apply _ _ = shapeMismatch unit

-- Foldable instance for Either only considers Right case.
foldlModuleDef :: forall a b. (b -> a -> b) -> b -> VarDef a + RecDefs a -> b
foldlModuleDef f acc (Left def) = foldl f acc def
foldlModuleDef f acc (Right def) = foldl f acc def

instance Foldable Module where
   foldl _ acc (Module Nil) = acc
   foldl f acc (Module (Left def : defs)) =
      foldl (foldlModuleDef f) (foldl f acc def) defs
   foldl f acc (Module (Right def : defs)) =
      foldl (foldlModuleDef f) (foldl f acc def) defs

   foldr f = foldrDefault f
   foldMap f = foldMapDefaultL f

instance Traversable Module where
   traverse _ (Module Nil) = pure (Module Nil)
   traverse f (Module (Left def : ds)) =
      Module <$> ((Left <$> traverse f def) `lift2 (:)` (unwrap <$> traverse f (Module ds)))
   traverse f (Module (Right def : ds)) =
      Module <$> ((Right <$> traverse f def) `lift2 (:)` (unwrap <$> traverse f (Module ds)))

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

stripDocStmt :: forall a. Stmt a -> Stmt a
stripDocStmt (Return e) = Return (stripDocE e)
stripDocStmt (Match e σ) = Match (stripDocE e) (stripDocEl σ)
stripDocStmt (Def vd) = Def (stripDocVD vd)
stripDocStmt (DefRec ρ) = DefRec (stripDocRD ρ)
stripDocStmt Pass = Pass
stripDocStmt (ExprStmt e) = ExprStmt (stripDocE e)
stripDocStmt (Seq s1 s2) = Seq (stripDocStmt s1) (stripDocStmt s2)

stripDocE :: forall a. Expr a -> Expr a
stripDocE (Var x) = Var x
stripDocE (Op op) = Op op
stripDocE (Int α n) = Int α n
stripDocE (Float α n) = Float α n
stripDocE (Str α s) = Str α s
stripDocE (Dictionary α ees) = Dictionary α (map (\(Pair e e') -> Pair (stripDocE e) (stripDocE e')) ees)
stripDocE (Constr α c es) = Constr α c (map stripDocE es)
stripDocE (Matrix α e1 xy e2) = Matrix α (stripDocE e1) xy (stripDocE e2)
stripDocE (Lambda α σ) = Lambda α (stripDocEl σ)
stripDocE (DProject e1 e2) = DProject (stripDocE e1) (stripDocE e2)
stripDocE (App e1 e2) = App (stripDocE e1) (stripDocE e2)
stripDocE (DocExpr _ e) = stripDocE e

stripDocEl :: forall a. Elim a -> Elim a
stripDocEl (ElimVar x κ) = ElimVar x (stripDocC κ)
stripDocEl (ElimConstr m) = ElimConstr (map stripDocC m)
stripDocEl (ElimDict xs κ) = ElimDict xs (stripDocC κ)

stripDocC :: forall a. Cont a -> Cont a
stripDocC (ContElim σ) = ContElim (stripDocEl σ)
stripDocC (ContStmt s) = ContStmt (stripDocStmt s)

stripDocVD :: forall a. VarDef a -> VarDef a
stripDocVD (VarDef σ e) = VarDef (stripDocEl σ) (stripDocE e)

stripDocRD :: forall a. RecDefs a -> RecDefs a
stripDocRD (RecDefs α ρ) = RecDefs α (map stripDocEl ρ)
