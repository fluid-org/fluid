module Types where

import Prelude
import Prim hiding (Type)

import Bind (Name, Var)
import Data.Bounded.Generic (genericBottom, genericTop)
import Data.Enum (class Enum, upFromIncluding)
import Data.Enum.Generic (genericPred, genericSucc)
import Data.Generic.Rep (class Generic)
import Data.List (List, length, zip, (:))
import Data.List.NonEmpty (NonEmptyList)
import Data.Map (Map, fromFoldable, lookup)
import Data.Maybe (fromMaybe)
import Data.Set (Set, empty, singleton, union, unions)
import Data.Show.Generic (genericShow)
import Literal (Literal)
import Literal as L
import Util (assert, (×))

data Primitive
   = Object
   | Never
   | None
   | Bool
   | Int
   | Float
   | Str
   | Sized

data Type
   = PrimitiveTy Primitive
   | ListTy Type
   | TupleTy (List Type)
   | DictTy Type
   | CallableTy (List Type) Type
   | LitTy Literal
   | VarTy Var
   | ClassTy Name (List Type) -- class by fully-qualified name, with type arguments
   | TypeTy Type -- class as value
   | UnionTy Type Type

data Scheme = Forall (NonEmptyList Var) Type

primitiveName :: Primitive -> String
primitiveName Object = "object"
primitiveName Never = "Never"
primitiveName None = "None"
primitiveName Bool = "bool"
primitiveName Int = "int"
primitiveName Float = "float"
primitiveName Str = "str"
primitiveName Sized = "Sized"

-- Primitive types by name
primitives :: Map String Primitive
primitives = fromFoldable ((\π -> primitiveName π × π) <$> (upFromIncluding bottom :: List Primitive))

data TypeCtr
   = ListCtr
   | DictCtr
   | TupleCtr
   | CallableCtr
   | TypeTyCtr
   | LiteralCtr

typeCtrName :: TypeCtr -> String
typeCtrName ListCtr = "list"
typeCtrName DictCtr = "dict"
typeCtrName TupleCtr = "tuple"
typeCtrName CallableCtr = "Callable"
typeCtrName TypeTyCtr = "type"
typeCtrName LiteralCtr = "Literal"

-- Type constructors by name
typeCtrs :: Map String TypeCtr
typeCtrs = fromFoldable ((\c -> typeCtrName c × c) <$> (upFromIncluding bottom :: List TypeCtr))

baseType :: Type -> Type
baseType (LitTy (L.Int _)) = PrimitiveTy Int
baseType (LitTy (L.Float _)) = PrimitiveTy Float
baseType (LitTy (L.Str _)) = PrimitiveTy Str
baseType (LitTy (L.Bool _)) = PrimitiveTy Bool
baseType (LitTy L.None) = PrimitiveTy None
baseType τ = τ

subst :: List Type -> List Var -> Type -> Type
subst τs αs = assert (length τs == length αs) go
   where
   σs = fromFoldable (zip αs τs)

   go (VarTy α) = fromMaybe (VarTy α) (lookup α σs)
   go (ListTy τ) = ListTy (go τ)
   go (TupleTy τs') = TupleTy (go <$> τs')
   go (DictTy τ) = DictTy (go τ)
   go (CallableTy τs' τ) = CallableTy (go <$> τs') (go τ)
   go (ClassTy c τs') = ClassTy c (go <$> τs')
   go (TypeTy τ) = TypeTy (go τ)
   go (UnionTy σ τ) = UnionTy (go σ) (go τ)
   go τ = τ

fv :: Type -> Set Var
fv (VarTy α) = singleton α
fv (ListTy τ) = fv τ
fv (TupleTy τs) = unions (fv <$> τs)
fv (DictTy τ) = fv τ
fv (CallableTy τs τ) = unions (fv <$> τs) `union` fv τ
fv (ClassTy _ τs) = unions (fv <$> τs)
fv (TypeTy τ) = fv τ
fv (UnionTy σ τ) = fv σ `union` fv τ
fv _ = empty

subterms :: Type -> List Type
subterms (UnionTy σ τ) = subterms σ <> subterms τ
subterms τ@(ListTy σ) = τ : subterms σ
subterms τ@(DictTy σ) = τ : subterms σ
subterms τ@(TupleTy σs) = τ : (σs >>= subterms)
subterms τ@(ClassTy _ σs) = τ : (σs >>= subterms)
subterms τ@(CallableTy σs σ) = τ : ((σ : σs) >>= subterms)
subterms τ = pure τ

disjuncts :: Type -> List Type
disjuncts (UnionTy σ τ) = disjuncts σ <> disjuncts τ
disjuncts τ = pure τ

derive instance Eq Primitive
derive instance Ord Primitive
derive instance Generic Primitive _

instance Bounded Primitive where
   bottom = genericBottom
   top = genericTop

instance Enum Primitive where
   succ = genericSucc
   pred = genericPred

derive instance Eq TypeCtr
derive instance Ord TypeCtr
derive instance Generic TypeCtr _

instance Bounded TypeCtr where
   bottom = genericBottom
   top = genericTop

instance Enum TypeCtr where
   succ = genericSucc
   pred = genericPred

instance Show Primitive where
   show = genericShow

derive instance Eq Type
derive instance Generic Type _
instance Show Type where
   show x = genericShow x

derive instance Eq Scheme
derive instance Generic Scheme _
instance Show Scheme where
   show = genericShow
