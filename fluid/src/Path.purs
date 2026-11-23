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
import Control.Monad.ST.Global (Global, toEffect)
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial (peek) as STAP
import Data.FoldableWithIndex (foldMapWithIndex, foldlWithIndex)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (length)
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Partial.Unsafe (unsafePartial)
import Util (class IsEmpty, absurd, error, singleton, (×))
import Util.Map (maplet)
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

-- Every path set and union computed so far; path sets by identity, then identities by key
type Interned =
   { tries :: STArray Global Trie
   , ids :: STObject Global PathSet
   , unions :: STObject Global PathSet
   }

interned :: Interned
interned = unsafePerformEffect $ toEffect do
   tries <- STA.new
   ids <- STO.new
   unions <- STO.new
   pure { tries, ids, unions }

-- Equal exactly for equal steps
stepKey :: Step -> String
stepKey (EdgeSrc (Vertex a)) = "v" <> show a
stepKey InputsEnv = "e"
stepKey InputsCtl = "c"
stepKey (Binding x) = "b" <> sized x
stepKey (Field x) = "f" <> sized x
stepKey (Element i) = "i" <> show i
stepKey (DictKey k) = "k" <> sized k
stepKey (DictVal k) = "d" <> sized k
stepKey (MatrixElement i j) = "m" <> show i <> "," <> show j
stepKey MatrixRows = "r"
stepKey MatrixCols = "n"
stepKey ClosureEnv = "u"
stepKey PartialFun = "p"
stepKey (PartialArg i) = "a" <> show i

-- String after its length, since text which follows could otherwise be read as part of the string
sized :: String -> String
sized x = show (length x) <> "." <> x

-- Equal exactly for equal tries
trieKey :: Trie -> String
trieKey (Trie b children) =
   foldlWithIndex (\step k (PathSet i) -> k <> stepKey step <> "=" <> show i <> ";") (if b then "1" else "0") children

intern :: Trie -> PathSet
intern t = unsafePerformEffect $ toEffect do
   STO.peek k interned.ids >>= case _ of
      Just ps -> pure ps
      Nothing -> do
         ps <- STA.push t interned.tries <#> \n -> PathSet (n - 1)
         STO.poke k ps interned.ids $> ps
   where
   k = trieKey t

trie :: PathSet -> Trie
trie (PathSet i) = unsafePerformEffect (toEffect (unsafePartial (STAP.peek i interned.tries)))

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
   union ps@(PathSet i) ps'@(PathSet j)
      | ps == ps' = ps
      | ps > ps' = union ps' ps
      | otherwise =
           unsafePerformEffect $ toEffect do
              STO.peek k interned.unions >>= case _ of
                 Just ps'' -> pure ps''
                 Nothing -> STO.poke k unioned interned.unions $> unioned
           where
           k = show i <> "," <> show j
           unioned = case trie ps × trie ps' of
              Trie b children × Trie b' children' -> intern (Trie (b || b') (Map.unionWith union children children'))

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
