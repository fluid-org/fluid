module Literal where

import Prelude hiding (absurd)

import Data.Generic.Rep (class Generic)
import Data.Int (toNumber)
import Data.Maybe (fromMaybe, maybe)
import Data.Number (isFinite, isNaN)
import Data.Number.Format (precision, toStringWith)
import Data.Show.Generic (genericShow)
import Data.String (Pattern(..), contains, split, stripSuffix)
import Util (absurd, error)

data Literal
   = Int Int
   | Float Number
   | Str String
   | Bool Boolean
   | None

-- Equality of the values denoted, so NaN differs from itself.
eqLiteral :: Literal -> Literal -> Boolean
eqLiteral (Int n) (Float x) = toNumber n == x
eqLiteral (Float x) (Int n) = x == toNumber n
eqLiteral (Float x) (Float y) = x == y
eqLiteral ℓ ℓ' = ℓ == ℓ'

-- Equality of literals as written, so NaN equals itself.
instance Eq Literal where
   eq (Int n) (Int n') = n == n'
   eq (Float x) (Float y) = x == y || (isNaN x && isNaN y)
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
