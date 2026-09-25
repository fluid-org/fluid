module TypeExpr where

import Prelude

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
data TypeExpr
   = Primitive Primitive
   | List TypeExpr
   | Tuple (List TypeExpr)
   | Dict TypeExpr
   | Callable (List TypeExpr) TypeExpr
   | Lit Literal
   | ClassName Name
   | Class Name -- class by fully qualified name; doesn't occur in source text
   | Union TypeExpr TypeExpr

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Eq TypeExpr
derive instance Generic TypeExpr _
instance Show TypeExpr where
   show x = genericShow x
