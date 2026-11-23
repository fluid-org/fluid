-- Paths into values, and sets of paths with one representation per set
module Path
   ( Path
   , PathSet
   , Step(..)
   , Vertex(..)
   , members
   , pathSet
   , sourceAt
   , sourceRoot
   , ε
   ) where

import Prelude

import Bind (Var)
import Data.FoldableWithIndex (foldMapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import Util (class IsEmpty, type (×), singleton, (×))
import Util.Map (get, lookup, maplet)
import Util.Set (empty, size, (∪))

newtype Vertex = Vertex Int

-- Step to part of value; values include families of values such as environments
data Step
   = Source Vertex -- of edge
   | InputsEnv
   | InputsCtl
   | Binding Var
   | Field Var
   | Element Int -- of list or tuple
   | DictKey String
   | DictVal String
   | MatrixElement Int Int
   | MatrixRows
   | MatrixCols
   | ClosureEnv
   | PartialFun
   | PartialArg Int

type Path = List Step

ε :: Path
ε = Nil

-- Position p of source vertex a
sourceAt :: Vertex -> Path -> Path
sourceAt a p = Source a : p

sourceRoot :: Vertex -> Path
sourceRoot a = sourceAt a ε

-- Set of paths; equal sets have equal identities
newtype PathSet = PathSet Int

-- Whether the empty path is a member, then non-empty set of remaining paths after each first step
data Trie = Trie Boolean (Map Step PathSet)

-- Every path set and union computed so far
type Interned =
   { ids :: Map Trie PathSet
   , tries :: Map PathSet Trie
   , unions :: Map (PathSet × PathSet) PathSet
   }

interned :: Ref Interned
interned = unsafePerformEffect (Ref.new { ids: empty, tries: empty, unions: empty })

intern :: Trie -> PathSet
intern t = unsafePerformEffect do
   { ids } <- Ref.read interned
   case lookup t ids of
      Just ps -> pure ps
      Nothing -> do
         let ps = PathSet (size ids)
         Ref.modify_ (\r -> r { ids = Map.insert t ps r.ids, tries = Map.insert ps t r.tries }) interned
         pure ps

trie :: PathSet -> Trie
trie ps = get ps (unsafePerformEffect (Ref.read interned)).tries

pathSet :: Path -> PathSet
pathSet Nil = intern (Trie true empty)
pathSet (step : p) = intern (Trie false (maplet step (pathSet p)))

members :: PathSet -> Set Path
members ps = case trie ps of
   Trie b children -> (if b then singleton Nil else empty) ∪ foldMapWithIndex (\step -> Set.map (step : _) <<< members) children

-- Union computed once for each pair of sets
instance Semigroup PathSet where
   append ps ps'
      | ps == ps' = ps
      | ps > ps' = append ps' ps
      | otherwise = unsafePerformEffect do
           { unions } <- Ref.read interned
           case lookup (ps × ps') unions of
              Just ps'' -> pure ps''
              Nothing -> do
                 let
                    Trie b children = trie ps
                    Trie b' children' = trie ps'
                    ps'' = intern (Trie (b || b') (Map.unionWith append children children'))
                 Ref.modify_ (\r -> r { unions = Map.insert (ps × ps') ps'' r.unions }) interned
                 pure ps''

instance Monoid PathSet where
   mempty = intern (Trie false empty)

instance IsEmpty PathSet where
   isEmpty ps = ps == mempty

-- ======================
-- boilerplate
-- ======================
derive instance Eq Vertex
derive instance Ord Vertex
derive instance Newtype Vertex _
derive newtype instance Show Vertex
derive instance Eq Step
derive instance Ord Step
derive instance Generic Step _

instance Show Step where
   show = genericShow

derive instance Eq PathSet
derive instance Ord PathSet
derive newtype instance Show PathSet
derive instance Eq Trie
derive instance Ord Trie
