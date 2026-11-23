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
   , sourceVertex
   , ε
   ) where

import Prelude hiding (absurd)

import Bind (Var)
import Data.Foldable (foldMap)
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
import Util (class IsEmpty, type (×), absurd, error, singleton, (×))
import Util.Map (get, lookup, maplet)
import Util.Set (class Set, empty, filter, size, union, (∈), (∪))

newtype Vertex = Vertex Int

-- Step to child of value; values include families of values such as environments
data Step
   = EdgeSrc Vertex
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
sourceAt a p = EdgeSrc a : p

sourceRoot :: Vertex -> Path
sourceRoot a = sourceAt a ε

sourceVertex :: Path -> Vertex
sourceVertex (EdgeSrc a : _) = a
sourceVertex _ = error absurd

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

instance IsEmpty PathSet where
   isEmpty ps = ps == empty

instance Set PathSet (List Step) where
   empty = intern (Trie false empty)
   filter p ps = foldMap pathSet (Set.filter p (members ps))
   size ps = size (members ps)
   difference ps ps' = filter (not <<< (_ ∈ members ps')) ps
   member p ps = p ∈ members ps
   -- Computed once for each pair of sets
   union ps ps'
      | ps == ps' = ps
      | ps > ps' = union ps' ps
      | otherwise = unsafePerformEffect do
           { unions } <- Ref.read interned
           case lookup (ps × ps') unions of
              Just ps'' -> pure ps''
              Nothing -> do
                 let
                    Trie b children = trie ps
                    Trie b' children' = trie ps'
                    ps'' = intern (Trie (b || b') (Map.unionWith union children children'))
                 Ref.modify_ (\r -> r { unions = Map.insert (ps × ps') ps'' r.unions }) interned
                 pure ps''

instance Semigroup PathSet where
   append = union

instance Monoid PathSet where
   mempty = empty

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
