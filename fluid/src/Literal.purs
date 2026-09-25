module Literal where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- Literals ℓ; a negative number is a literal, so the spec's negative-literal pattern and type need no separate form.
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
