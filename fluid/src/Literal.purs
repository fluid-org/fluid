module Literal where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Int (toNumber)
import Data.Show.Generic (genericShow)

data Literal
   = Int Int
   | Float Number
   | Str String
   | Bool Boolean
   | None

eqLiteral :: Literal -> Literal -> Boolean
eqLiteral (Int n) (Float x) = toNumber n == x
eqLiteral (Float x) (Int n) = x == toNumber n
eqLiteral ℓ ℓ' = ℓ == ℓ'

derive instance Eq Literal
derive instance Generic Literal _
instance Show Literal where
   show = genericShow
