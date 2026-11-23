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
import Data.Generic.Rep (class Generic)
import Data.Int.Bits (complement, zshr, (.&.), (.^.), (.|.))
import Data.List (List(..), (:))
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
import Util (class IsEmpty, absurd, error, singleton)
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

-- Members by number; branch has common prefix of members, bit at which they differ, then members with 0 and 1 at that bit
data Tree = Empty | Leaf Int | Branch Int Int PathSet PathSet

-- Paths numbered in order of first use; then every path set and union computed so far
type Interned =
   { numbers :: STObject Global Int
   , paths :: STArray Global Path
   , trees :: STArray Global Tree
   , ids :: STObject Global PathSet
   , unions :: STObject Global PathSet
   }

interned :: Interned
interned = unsafePerformEffect $ toEffect do
   numbers <- STO.new
   paths <- STA.new
   trees <- STA.new
   ids <- STO.new
   unions <- STO.new
   pure { numbers, paths, trees, ids, unions }

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

-- Equal exactly for equal trees
treeKey :: Tree -> String
treeKey Empty = "e"
treeKey (Leaf n) = "l" <> show n
treeKey (Branch prefix bit (PathSet i) (PathSet j)) = show prefix <> "," <> show bit <> "," <> show i <> "," <> show j

number :: Path -> Int
number p = unsafePerformEffect $ toEffect do
   STO.peek k interned.numbers >>= case _ of
      Just n -> pure n
      Nothing -> do
         n <- STA.push p interned.paths <#> (_ - 1)
         STO.poke k n interned.numbers $> n
   where
   k = foldMap stepKey p

intern :: Tree -> PathSet
intern t = unsafePerformEffect $ toEffect do
   STO.peek k interned.ids >>= case _ of
      Just ps -> pure ps
      Nothing -> do
         ps <- STA.push t interned.trees <#> \n -> PathSet (n - 1)
         STO.poke k ps interned.ids $> ps
   where
   k = treeKey t

tree :: PathSet -> Tree
tree (PathSet i) = unsafePerformEffect (toEffect (unsafePartial (STAP.peek i interned.trees)))

pathSet :: Path -> PathSet
pathSet p = intern (Leaf (number p))

members :: PathSet -> Set Path
members ps = case tree ps of
   Empty -> empty
   Leaf n -> singleton (unsafePerformEffect (toEffect (unsafePartial (STAP.peek n interned.paths))))
   Branch _ _ ps0 ps1 -> members ps0 ∪ members ps1

-- Whether n has 0 at the given bit
zeroAt :: Int -> Int -> Boolean
zeroAt bit n = n .&. bit == 0

-- Bits of n above the given bit
prefixAbove :: Int -> Int -> Int
prefixAbove bit n = n .&. (complement (bit - 1) .^. bit)

-- Highest bit at which m and n differ
branchingBit :: Int -> Int -> Int
branchingBit m n = k5 .^. (k5 `zshr` 1)
   where
   k1 = (m .^. n) .|. ((m .^. n) `zshr` 1)
   k2 = k1 .|. (k1 `zshr` 2)
   k3 = k2 .|. (k2 `zshr` 4)
   k4 = k3 .|. (k3 `zshr` 8)
   k5 = k4 .|. (k4 `zshr` 16)

-- Branch over two path sets with members which differ in prefix
branchOver :: Int -> PathSet -> Int -> PathSet -> PathSet
branchOver m ps n ps' = intern (if zeroAt bit m then Branch prefix bit ps ps' else Branch prefix bit ps' ps)
   where
   bit = branchingBit m n
   prefix = prefixAbove bit m

instance IsEmpty PathSet where
   isEmpty ps = ps == empty

instance Set PathSet (List Step) where
   empty = intern Empty
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
                 Nothing -> do
                    let ps'' = unionTrees ps (tree ps) ps' (tree ps')
                    STO.poke k ps'' interned.unions $> ps''
           where
           k = show i <> "," <> show j

unionTrees :: PathSet -> Tree -> PathSet -> Tree -> PathSet
unionTrees _ Empty ps' _ = ps'
unionTrees ps _ _ Empty = ps
unionTrees ps (Leaf m) ps' (Leaf n) = branchOver m ps n ps'
unionTrees ps (Leaf m) ps' (Branch prefix bit ps0 ps1) = into m ps prefix bit ps0 ps1 ps'
unionTrees ps (Branch prefix bit ps0 ps1) ps' (Leaf n) = into n ps' prefix bit ps0 ps1 ps
unionTrees ps (Branch prefix bit ps0 ps1) ps' (Branch prefix' bit' ps0' ps1')
   | bit > bit' = into prefix' ps' prefix bit ps0 ps1 ps
   | bit' > bit = into prefix ps prefix' bit' ps0' ps1' ps'
   | prefix == prefix' = intern (Branch prefix bit (ps0 ∪ ps0') (ps1 ∪ ps1'))
   | otherwise = branchOver prefix ps prefix' ps'

-- Union of ps with the branch ps' over ps0 and ps1; ps branches below the given bit and has n as member or prefix
into :: Int -> PathSet -> Int -> Int -> PathSet -> PathSet -> PathSet -> PathSet
into n ps prefix bit ps0 ps1 ps'
   | prefixAbove bit n /= prefix = branchOver n ps prefix ps'
   | zeroAt bit n = intern (Branch prefix bit (ps ∪ ps0) ps1)
   | otherwise = intern (Branch prefix bit ps0 (ps ∪ ps1))

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
