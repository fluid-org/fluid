module Util.Map where

import Prelude hiding (append)

import Control.Monad.Error.Class (class MonadThrow)
import Data.Foldable (foldl)
import Data.List (List, head)
import Data.List as List
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Unfoldable (class Unfoldable)
import Effect.Exception (Error)
import Foreign.Object (Object)
import Foreign.Object as Object
import Util (type (×), Endo, assert, definitely, definitely', error, orElse, (×))
import Util.Set (class Set, (∈), size)
import Data.Map as M
import Data.Set as DSet

-- Generalises Map but also supports a fixed key type, like Dict. Doesn't support transforming element type.
class Set a k <= Map a k b | a -> k, a -> b where
   maplet :: k -> b -> a
   keys :: a -> Set k
   values :: a -> List b
   filterKeys :: (k -> Boolean) -> Endo a
   unionWith :: (b -> Endo b) -> a -> Endo a
   lookup :: k -> a -> Maybe b
   delete :: k -> a -> a
   insert :: k -> b -> Endo a
   toUnfoldable :: forall f. Unfoldable f => a -> f (k × b)

-- Can't be provided by Map because of non-uniform type.
class MapF (f :: Type -> Type) k | f -> k where
   intersectionWith :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
   difference :: forall a b. f a -> f b -> f a
   mapWithKey :: forall a b. (k -> a -> b) -> f a -> f b

instance Map (Object a) String a where
   maplet = Object.singleton
   keys = Object.keys >>> Set.fromFoldable
   values = Object.values >>> List.fromFoldable
   filterKeys = Object.filterKeys
   unionWith = Object.unionWith
   lookup = Object.lookup
   delete = Object.delete
   insert = Object.insert
   toUnfoldable = Object.toAscUnfoldable

instance Ord k => Map (M.Map k v) k v where
   maplet = M.singleton
   keys = M.keys
   values = M.values
   filterKeys = M.filterKeys
   unionWith = M.unionWith
   lookup = M.lookup
   delete = M.delete
   insert = M.insert
   toUnfoldable = M.toUnfoldable

instance MapF Object String where
   intersectionWith = intersectionWith_Object
   difference m1 m2 = foldl (flip delete) m1 (Object.keys m2)
   mapWithKey = Object.mapWithKey

infixr 7 intersection as ∩
infix 5 difference as \\

foreign import intersectionWith_Object :: forall a b c. (a -> b -> c) -> Object a -> Object b -> Object c

constMap :: forall k v. v -> Set k -> M.Map k v
constMap v ks = v <$ DSet.toMap ks

restrict :: forall a k b. Ord k => Map a k b => Set k -> Endo a
restrict xs = filterKeys (_ ∈ xs)

intersection :: forall f a k b. MapF f k => f a -> f b -> f a
intersection = intersectionWith const

unionWith_never :: forall a k b. Map a k b => a -> Endo a
unionWith_never = unionWith (\_ _ -> error "not disjoint")

disjointUnion_inv :: forall a k b. Ord k => Map a k b => Set k -> a -> a × a
disjointUnion_inv ks m = filterKeys (_ ∈ ks) m × filterKeys (_ `not <<< (∈)` ks) m

lookup' :: forall m a k b. MonadThrow Error m => Show k => Map a k b => k -> a -> m b
lookup' k = lookup k >>> orElse (keyNotFound k)

keyNotFound :: forall k. Show k => k -> String
keyNotFound k = "Key " <> show k <> " not found"

get :: forall a k b. Show k => Map a k b => k -> a -> b
get k = lookup k >>> definitely (keyNotFound k)

findWithDefault :: forall k v. Ord k => v -> k -> M.Map k v -> v
findWithDefault d k = maybe d identity <<< M.lookup k

-- Maybe push a semigroup requirement onto Map
append :: forall a k b. Map a k b => a -> Endo a
append = unionWith (const identity)

infixl 5 append as <+>

append_inv :: forall a k b. Ord k => Map a k b => Set k -> a -> a × a
append_inv xs m = filterKeys (_ `not <<< (∈)` xs) m × restrict xs m

alter :: forall a k b. Map a k b => (Endo (Maybe b)) -> k -> Endo a
alter f k m = case f (lookup k m) of
   Nothing -> delete k m
   Just v -> insert k v m

update :: forall a k b. Show k => Map a k b => Endo b -> k -> Endo a
update f k = alter (definitely (keyNotFound k) >>> f >>> Just) k

insertWith :: forall a k b. Map a k b => (b -> Endo b) -> k -> b -> Endo a
insertWith f k v = alter (Just <<< maybe v (flip f v)) k

asMaplet :: forall a k b. Map a k b => a -> k × b
asMaplet m =
   assert (size m == 1) (definitely' (head (toUnfoldable m)))
