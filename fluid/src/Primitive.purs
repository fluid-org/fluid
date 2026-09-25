module Primitive where

import Prelude hiding (absurd, apply, div, top)

import Bind (Bind)
import Data.Either (Either(..), either)
import Data.Int (toNumber)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Profunctor.Choice ((|||))
import Data.Set (insert)
import DataType (cPair)
import Dict (Dict)
import Lattice (class BoundedJoinSemilattice, bot, erase)
import Literal (Literal(..))
import Partial.Unsafe (unsafePartial)
import Pretty (prettyP)
import Util (type (+), type (×), error, orThrow, singleton, (×))
import Val (BaseVal(..), DictRep(..), ForeignOp(..), ForeignOp'(..), Fun(..), MatrixRep, Op, Val(..), val)

-- Mediate between wrapped values and underlying datatype d. Wasn't able to make a typeclass version
-- work with required higher-rank polymorphism.
type ToFrom d a =
   { pack :: d -> BaseVal a
   , unpack :: BaseVal a -> Either String d
   }

unpack :: forall d a. ToFrom d a -> Val a -> Either String (d × a)
unpack toFrom (Val α _ v) = toFrom.unpack v <#> (_ × α)

-- For values whose shape is known.
unpack' :: forall d a. ToFrom d a -> Val a -> d × a
unpack' toFrom = unpack toFrom >>> either error identity

pack :: forall d a. ToFrom d a -> d × a -> Val a
pack toFrom (v × α) = Val α Nothing (toFrom.pack v)

typeMismatch :: forall a. BaseVal a -> String -> String
typeMismatch v typeName = "Found " <> prettyP (erase v) <> ", expected " <> typeName

typeError :: forall a b. BaseVal a -> String -> b
typeError v typeName = error (typeMismatch v typeName)

int :: forall a. ToFrom Int a
int =
   { pack: Lit <<< Int
   , unpack: case _ of
        Lit (Int n) -> Right n
        v -> Left (typeMismatch v "int")
   }

number :: forall a. ToFrom Number a
number =
   { pack: Lit <<< Float
   , unpack: case _ of
        Lit (Float n) -> Right n
        v -> Left (typeMismatch v "float")
   }

string :: forall a. ToFrom String a
string =
   { pack: Lit <<< Str
   , unpack: case _ of
        Lit (Str str) -> Right str
        v -> Left (typeMismatch v "str")
   }

intOrNumber :: forall a. ToFrom (Int + Number) a
intOrNumber =
   { pack: case _ of
        Left n -> Lit (Int n)
        Right n -> Lit (Float n)
   , unpack: case _ of
        Lit (Int n) -> Right (Left n)
        Lit (Float n) -> Right (Right n)
        v -> Left (typeMismatch v "int or float")
   }

intOrNumberOrString :: forall a. ToFrom (Int + Number + String) a
intOrNumberOrString =
   { pack: case _ of
        Left n -> Lit (Int n)
        Right (Left n) -> Lit (Float n)
        Right (Right str) -> Lit (Str str)
   , unpack: case _ of
        Lit (Int n) -> Right (Left n)
        Lit (Float n) -> Right (Right (Left n))
        Lit (Str str) -> Right (Right (Right str))
        v -> Left (typeMismatch v "int, float or str")
   }

intPair :: forall a. ToFrom ((Int × a) × (Int × a)) a
intPair =
   { pack: \(nβ × mβ') -> Constr cPair (pack int nβ : pack int mβ' : Nil)
   , unpack: case _ of
        Constr c (v : v' : Nil) | c == cPair -> (×) <$> unpack int v <*> unpack int v'
        v -> Left (typeMismatch v "Pair")
   }

matrixRep :: forall a. ToFrom (MatrixRep a) a
matrixRep =
   { pack: Matrix
   , unpack: case _ of
        Matrix m -> Right m
        v -> Left (typeMismatch v "matrix")
   }

dict :: forall a. ToFrom (Dict (a × Val a)) a
dict =
   { pack: Dictionary <<< DictRep
   , unpack: case _ of
        Dictionary (DictRep d) -> Right d
        v -> Left (typeMismatch v "dict")
   }

boolean :: forall a. ToFrom Boolean a
boolean =
   { pack: Lit <<< Bool
   , unpack: case _ of
        Lit (Bool b) -> Right b
        v -> Left (typeMismatch v "bool")
   }

class IsZero a where
   isZero :: a -> Boolean

instance IsZero Int where
   isZero = ((==) 0)

instance IsZero Number where
   isZero = ((==) 0.0)

instance (IsZero a, IsZero b) => IsZero (a + b) where
   isZero = isZero ||| isZero

-- Need to be careful about type variables escaping higher-rank quantification.
type Unary i o a =
   { i :: ToFrom i a
   , o :: ToFrom o a
   , fwd :: i -> o
   }

type Binary i1 i2 o a =
   { i1 :: ToFrom i1 a
   , i2 :: ToFrom i2 a
   , o :: ToFrom o a
   , fwd :: i1 -> i2 -> o
   }

type BinaryZero i o a =
   { i :: ToFrom i a
   , o :: ToFrom o a
   , fwd :: i -> i -> o
   }

unary :: forall i o a'. BoundedJoinSemilattice a' => String -> (forall a. Unary i o a) -> Bind (Val a')
unary id f =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × op))))
   where
   op :: ForeignOp'
   op = ForeignOp' { arity: 1, op: unsafePartial op' }

   op' :: Partial => Op
   op' doc_opt (Val α _ v : Nil) = do
      x <- orThrow (f.i.unpack v)
      val doc_opt (singleton α) (f.o.pack (f.fwd x))

binary :: forall i1 i2 o a'. BoundedJoinSemilattice a' => String -> (forall a. Binary i1 i2 o a) -> Bind (Val a')
binary id f =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × op))))
   where
   op :: ForeignOp'
   op = ForeignOp' { arity: 2, op: unsafePartial op' }

   op' :: Partial => Op
   op' doc_opt (Val α _ v1 : Val β _ v2 : Nil) = do
      x <- orThrow (f.i1.unpack v1)
      y <- orThrow (f.i2.unpack v2)
      val doc_opt (singleton α # insert β) (f.o.pack (f.fwd x y))

-- If both are zero, depend only on the first.
binaryZero :: forall i o a'. BoundedJoinSemilattice a' => IsZero i => String -> (forall a. BinaryZero i o a) -> Bind (Val a')
binaryZero id f =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × op))))
   where
   op :: ForeignOp'
   op = ForeignOp' { arity: 2, op: unsafePartial op' }

   op' :: Partial => Op
   op' doc_opt (Val α _ v1 : Val β _ v2 : Nil) = do
      x <- orThrow (f.i.unpack v1)
      y <- orThrow (f.i.unpack v2)
      let
         αs =
            if isZero x then singleton α
            else if isZero y then singleton β
            else singleton α # insert β
      val doc_opt αs (f.o.pack (f.fwd x y))

class As a b where
   as :: a -> b

union1 :: forall a1 b. (a1 -> b) -> (Number -> b) -> a1 + Number -> b
union1 f _ (Left x) = f x
union1 _ g (Right x) = g x

-- Biased towards g: if arguments are of mixed types, we try to coerce to an application of g.
union
   :: forall a1 b1 c1 a2 b2 c2 c
    . As c1 c
   => As c2 c
   => As a1 a2
   => As b1 b2
   => (a1 -> b1 -> c1)
   -> (a2 -> b2 -> c2)
   -> a1 + a2
   -> b1 + b2
   -> c
union f _ (Left x) (Left y) = as (f x y)
union _ g (Left x) (Right y) = as (g (as x) y)
union _ g (Right x) (Right y) = as (g x y)
union _ g (Right x) (Left y) = as (g x (as y))

-- Helper to avoid some explicit type annotations when defining primitives.
unionStr
   :: forall a b
    . As a a
   => As b String
   => (b -> b -> a)
   -> (String -> String -> a)
   -> b + String
   -> b + String
   -> a
unionStr = union

instance asIntIntOrNumber :: As Int (Int + a) where
   as = Left

instance asNumberIntOrNumber :: As Number (a + Number) where
   as = Right

instance asIntNumber :: As Int Number where
   as = toNumber

instance asBooleanBoolean :: As Boolean Boolean where
   as = identity

instance asNumberString :: As Number String where
   as _ = error "Non-uniform argument types"

instance asIntNumberOrString :: As Int (Number + a) where
   as = toNumber >>> Left

instance asIntorNumberNumber :: As (Int + Number) Number where
   as (Left n) = as n
   as (Right n) = n
