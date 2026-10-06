module Util.Set where

import Prelude hiding (append)

import Data.Foldable (class Foldable, foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set as Set
import Foreign.Object (Object)
import Foreign.Object as Object
import Util (class IsEmpty, Endo)

-- Generalises Set but also supports a fixed element type. Doesn't support transforming element type.
class IsEmpty a <= Set a b | a -> b where
   empty :: a
   filter :: (b -> Boolean) -> Endo a
   size :: a -> Int
   difference :: a -> Endo a
   member :: b -> a -> Boolean
   union :: a -> Endo a

infix 5 difference as \\
infix 5 member as ∈
infixr 6 union as ∪

instance Ord a => Set (Set a) a where
   empty = Set.empty
   filter = Set.filter
   size = Set.size
   difference = Set.difference
   member = Set.member
   union = Set.union

instance Ord k => Set (Map k v) k where
   empty = Map.empty
   filter = Map.filterKeys
   size = Map.size
   difference = Map.difference
   member = Map.member
   union = Map.union

instance Set (Object a) String where
   empty = Object.empty
   filter = Object.filterKeys
   size = Object.size
   difference x y = foldl (flip Object.delete) x (Object.keys y)
   member = Object.member
   union = Object.union

unions ∷ ∀ f a b. Foldable f ⇒ Set a b ⇒ f a → a
unions = foldl union empty
