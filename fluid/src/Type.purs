module Type where

import Prelude hiding (join)
import Prim hiding (Type)

import Bind (Name, dottedName)
import Data.Foldable (and, elem, foldr)
import Data.Generic.Rep (class Generic)
import Data.List (List, length, zipWith)
import Data.Map (lookup)
import Data.Maybe (maybe)
import Data.Newtype (class Newtype)
import Data.Show.Generic (genericShow)
import DataType (ClassTable)
import DefiniteAssignment (ancestors)
import Literal (Literal)
import Literal as L

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

-- Type expressions ψ over class references c: a name in source, a class once resolved.
data TypeExpr c
   = Primitive Primitive
   | List (TypeExpr c)
   | Tuple (List (TypeExpr c))
   | Dict (TypeExpr c)
   | Callable (List (TypeExpr c)) (TypeExpr c)
   | Lit Literal
   | ClassName c
   | Union (TypeExpr c) (TypeExpr c)

newtype Class = Class Name

type Type = TypeExpr Class

baseType :: Type -> Type
baseType (Lit (L.Int _)) = Primitive Int
baseType (Lit (L.Float _)) = Primitive Float
baseType (Lit (L.Str _)) = Primitive Str
baseType (Lit (L.Bool _)) = Primitive Bool
baseType (Lit L.None) = Primitive None
baseType τ = τ

subtype :: ClassTable -> Type -> Type -> Boolean
subtype classes σ τ
   | σ == τ = true
   | otherwise =
        case σ, τ of
           Primitive Never, _ -> true
           _, Primitive Object -> true
           Union σ1 σ2, _ -> subtype classes σ1 τ && subtype classes σ2 τ
           _, Union τ1 τ2 -> subtype classes σ τ1 || subtype classes σ τ2
           Lit _, _ -> subtype classes (baseType σ) τ
           Primitive Int, Primitive Float -> true
           ClassName (Class c), ClassName (Class d) -> maybe false (elem d <<< ancestors) (lookup (dottedName c) classes)
           _, Primitive Sized -> sized σ
           List σ', List τ' -> equiv classes σ' τ'
           Dict σ', Dict τ' -> equiv classes σ' τ'
           Tuple σs, Tuple τs -> length σs == length τs && and (zipWith (subtype classes) σs τs)
           Callable σs σ', Callable τs τ' ->
              length σs == length τs && and (zipWith (subtype classes) τs σs) && subtype classes σ' τ'
           _, _ -> false
        where
        sized (List _) = true
        sized (Dict _) = true
        sized (Primitive Str) = true
        sized (Tuple _) = true
        sized _ = false

equiv :: ClassTable -> Type -> Type -> Boolean
equiv classes σ τ = subtype classes σ τ && subtype classes τ σ

join :: ClassTable -> Type -> Type -> Type
join classes σ τ
   | subtype classes σ τ = τ
   | subtype classes τ σ = σ
   | otherwise = Union σ τ

joins :: ClassTable -> List (Type) -> Type
joins classes = foldr (join classes) (Primitive Never)

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Functor TypeExpr
derive instance Eq c => Eq (TypeExpr c)
derive instance Generic (TypeExpr c) _
instance Show c => Show (TypeExpr c) where
   show x = genericShow x

derive instance Newtype Class _
derive instance Eq Class
derive instance Generic Class _
instance Show Class where
   show = genericShow
