module Literal where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Int (toNumber)
import Data.Number (isNaN)
import Data.Show.Generic (genericShow)

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
