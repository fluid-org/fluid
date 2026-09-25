module Type where

import Prelude
import Prim hiding (Type)

import Bind (Name)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Show.Generic (genericShow)
import Literal (Literal)

-- Primitive types ν.
data Primitive
   = Object
   | Never
   | None
   | Bool
   | Int
   | Float
   | Str
   | Sized

-- Type expressions ψ. A type is a type expression whose class names are resolved to classes.
data Type
   = Primitive Primitive
   | List Type
   | Tuple (List Type)
   | Dict Type
   | Callable (List Type) Type
   | Lit Literal
   | ClassName Name
   | Class Name -- class by fully qualified name; doesn't occur in source text
   | Union Type Type

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Eq Type
derive instance Generic Type _
instance Show Type where
   show x = genericShow x
