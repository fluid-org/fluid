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

-- Type expressions ψ, carried but not consulted. Marked names don't occur in source.
data TypeExpr
   = Primitive Primitive
   | List TypeExpr
   | Tuple (List TypeExpr)
   | Dict TypeExpr
   | Callable (List TypeExpr) TypeExpr
   | Lit Literal
   | ClassName Name
   | Union TypeExpr TypeExpr

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Eq TypeExpr
derive instance Generic TypeExpr _
instance Show TypeExpr where
   show x = genericShow x
