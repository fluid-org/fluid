module Type where

import Prelude
import Prim hiding (Type)

import Bind (Name, Var)
import Data.Generic.Rep (class Generic)
import Data.List (List, length, zip)
import Data.Map (fromFoldable, lookup)
import Data.Maybe (fromMaybe)
import Data.Show.Generic (genericShow)
import Literal (Literal)
import Literal as L
import Util (assert)

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
   | UnionTy Type Type

primitiveName :: Primitive -> String
primitiveName Object = "object"
primitiveName Never = "Never"
primitiveName None = "None"
primitiveName Bool = "bool"
primitiveName Int = "int"
primitiveName Float = "float"
primitiveName Str = "str"
primitiveName Sized = "Sized"

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
   go (UnionTy σ τ) = UnionTy (go σ) (go τ)
   go τ = τ

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Eq Type
derive instance Generic Type _
instance Show Type where
   show x = genericShow x
