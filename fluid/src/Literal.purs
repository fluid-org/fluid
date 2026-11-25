module Literal where

import Prelude hiding (absurd)

import Data.Generic.Rep (class Generic)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Number (isFinite, isNaN)
import Data.Number.Format (precision, toStringWith)
import Data.Show.Generic (genericShow)
import Data.String (Pattern(..), contains, split, stripSuffix)
import Util (type (×), absurd, error, (×))

data Literal
   = Int Int
   | Float Number
   | Complex Number Number
   | Str String
   | Bool Boolean
   | None

-- Equality of the values denoted, so NaN differs from itself.
eqLiteral :: Literal -> Literal -> Boolean
eqLiteral (Int n) (Float x) = toNumber n == x
eqLiteral (Float x) (Int n) = x == toNumber n
eqLiteral (Float x) (Float y) = x == y
eqLiteral (Complex x y) (Complex x' y') = x == x' && y == y'
eqLiteral (Complex x y) ℓ = y == 0.0 && eqLiteral (Float x) ℓ
eqLiteral ℓ (Complex x y) = y == 0.0 && eqLiteral ℓ (Float x)
eqLiteral ℓ ℓ' = ℓ == ℓ'

-- Number as real and imaginary part
complex :: Literal -> Maybe (Number × Number)
complex (Int n) = Just (toNumber n × 0.0)
complex (Float x) = Just (x × 0.0)
complex (Complex x y) = Just (x × y)
complex _ = Nothing

-- Real or imaginary part of number, by attribute name
numberPart :: String -> Literal -> Maybe Literal
numberPart "real" (Complex x _) = Just (Float x)
numberPart "imag" (Complex _ y) = Just (Float y)
numberPart "real" ℓ@(Int _) = Just ℓ
numberPart "imag" (Int _) = Just (Int 0)
numberPart "real" ℓ@(Float _) = Just ℓ
numberPart "imag" (Float _) = Just (Float 0.0)
numberPart _ _ = Nothing

-- Equality of literals as written, so NaN equals itself.
instance Eq Literal where
   eq (Int n) (Int n') = n == n'
   eq (Float x) (Float y) = x == y || (isNaN x && isNaN y)
   eq (Complex x y) (Complex x' y') = Float x == Float x' && Float y == Float y'
   eq (Str s) (Str s') = s == s'
   eq (Bool b) (Bool b') = b == b'
   eq None None = true
   eq _ _ = false

derive instance Generic Literal _
instance Show Literal where
   show = genericShow

-- Float to 12 significant digits, with trailing zeros dropped, ".0" on an integral value and an exponent for a
-- very large or small magnitude
showFloat :: Number -> String
showFloat x
   | not (isFinite x) = show x
   | otherwise =
        case split (Pattern "e") (toStringWith (precision 12) x) of
           [ m ] -> withPoint (trim m)
           [ m, e ] -> trim m <> "e" <> e
           _ -> error absurd
        where
        trim m
           | contains (Pattern ".") m = dropPoint (dropZeros m)
           | otherwise = m
        dropZeros m = maybe m dropZeros (stripSuffix (Pattern "0") m)
        dropPoint m = fromMaybe m (stripSuffix (Pattern ".") m)
        withPoint m
           | contains (Pattern ".") m = m
           | otherwise = m <> ".0"

-- Complex number in parentheses as real part and signed imaginary part; imaginary part alone when real part zero
showComplex :: Number -> Number -> String
showComplex x y =
   if x == 0.0 then part y <> "j"
   else "(" <> part x <> (if y < 0.0 then "" else "+") <> part y <> "j)"
   where
   part z = fromMaybe (showFloat z) (stripSuffix (Pattern ".0") (showFloat z))
