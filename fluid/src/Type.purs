module Type where

import Prelude hiding (join)
import Prim hiding (Type)

import Bind (Name, dottedName)
import Data.Foldable (and, elem, foldr)
import Data.Generic.Rep (class Generic)
import Data.List (List, length, zipWith)
import Data.Map (lookup)
import Data.Maybe (maybe)
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
           Class c, Class d -> maybe false (elem d <<< ancestors) (lookup (dottedName c) classes)
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

joins :: ClassTable -> List Type -> Type
joins classes = foldr (join classes) (Primitive Never)

derive instance Eq Primitive
derive instance Generic Primitive _
instance Show Primitive where
   show = genericShow

derive instance Eq Type
derive instance Generic Type _
instance Show Type where
   show x = genericShow x
