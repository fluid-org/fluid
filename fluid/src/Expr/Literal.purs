module Expr.Literal where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- Literals ℓ; numbers may be negative, covering negative literal types.
data Literal
   = Int Int
   | Float Number
   | Str String
   | Bool Boolean
   | None

derive instance Eq Literal
derive instance Generic Literal _
instance Show Literal where
   show = genericShow
