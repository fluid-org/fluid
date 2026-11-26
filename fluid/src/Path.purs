-- Paths into values, positions in the values of vertices, and sets of positions with one representation per set
module Path
   ( Path
   , Position
   , PositionSet
   , Step(..)
   , Vertex(..)
   , followedBy
   , members
   , positionSet
   , ε
   ) where

import Prelude

import Bind (Var)
import Data.Foldable (foldMap)
import Control.Monad.ST.Global (Global, toEffect)
import Data.Array.ST (STArray)
import Data.Array.ST as STA
import Data.Array.ST.Partial (peek) as STAP
import Data.Generic.Rep (class Generic)
import Data.Int.Bits (complement, zshr, (.&.), (.^.), (.|.))
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (length)
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Object.ST (STObject)
import Foreign.Object.ST as STO
import Partial.Unsafe (unsafePartial)
import Util (class IsEmpty, type (×), singleton, (×))
import Util.Set (class Set, empty, filter, size, union, (∈), (∪))

newtype Vertex = Vertex Int

-- Step to child of value; values include families of values such as environments
data Step
   = InputsEnv
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

-- Path into the value of a vertex
type Position = Vertex × Path

-- Position with its path followed by p
followedBy :: Position -> Path -> Position
followedBy (a × q) p = a × (q <> p)

-- Set of positions; equal sets have equal identities
newtype PositionSet = PositionSet Int

-- Members by number; branch has common prefix of members, bit at which they differ, then members with 0 and 1 at that bit
data Tree = Empty | Leaf Int | Branch Int Int PositionSet PositionSet

-- Positions numbered in order of first use; then every position set and union computed so far
type Interned =
   { numbers :: STObject Global Int
   , positions :: STArray Global Position
   , trees :: STArray Global Tree
   , ids :: STObject Global PositionSet
   , unions :: STObject Global PositionSet
   }

interned :: Interned
interned = unsafePerformEffect $ toEffect do
   numbers <- STO.new
   positions <- STA.new
   trees <- STA.new
   ids <- STO.new
   unions <- STO.new
   pure { numbers, positions, trees, ids, unions }

-- Equal exactly for equal steps
stepKey :: Step -> String
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
treeKey (Branch prefix bit (PositionSet i) (PositionSet j)) = show prefix <> "," <> show bit <> "," <> show i <> "," <> show j

number :: Position -> Int
number q@(Vertex a × p) = unsafePerformEffect $ toEffect do
   STO.peek k interned.numbers >>= case _ of
      Just n -> pure n
      Nothing -> do
         n <- STA.push q interned.positions <#> (_ - 1)
         STO.poke k n interned.numbers $> n
   where
   k = "v" <> show a <> foldMap stepKey p

intern :: Tree -> PositionSet
intern t = unsafePerformEffect $ toEffect do
   STO.peek k interned.ids >>= case _ of
      Just ps -> pure ps
      Nothing -> do
         ps <- STA.push t interned.trees <#> \n -> PositionSet (n - 1)
         STO.poke k ps interned.ids $> ps
   where
   k = treeKey t

tree :: PositionSet -> Tree
tree (PositionSet i) = unsafePerformEffect (toEffect (unsafePartial (STAP.peek i interned.trees)))

positionSet :: Position -> PositionSet
positionSet p = intern (Leaf (number p))

members :: PositionSet -> Set Position
members ps = case tree ps of
   Empty -> empty
   Leaf n -> singleton (unsafePerformEffect (toEffect (unsafePartial (STAP.peek n interned.positions))))
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

-- Branch over two position sets with members which differ in prefix
branchOver :: Int -> PositionSet -> Int -> PositionSet -> PositionSet
branchOver m ps n ps' = intern (if zeroAt bit m then Branch prefix bit ps ps' else Branch prefix bit ps' ps)
   where
   bit = branchingBit m n
   prefix = prefixAbove bit m

instance IsEmpty PositionSet where
   isEmpty ps = ps == empty

instance Set PositionSet (Tuple Vertex (List Step)) where
   empty = intern Empty
   filter p ps = foldMap positionSet (Set.filter p (members ps))
   size ps = size (members ps)
   difference ps ps' = filter (not <<< (_ ∈ members ps')) ps
   member p ps = p ∈ members ps
   -- Computed once for each pair of sets
   union ps@(PositionSet i) ps'@(PositionSet j)
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

unionTrees :: PositionSet -> Tree -> PositionSet -> Tree -> PositionSet
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
into :: Int -> PositionSet -> Int -> Int -> PositionSet -> PositionSet -> PositionSet -> PositionSet
into n ps prefix bit ps0 ps1 ps'
   | prefixAbove bit n /= prefix = branchOver n ps prefix ps'
   | zeroAt bit n = intern (Branch prefix bit (ps ∪ ps0) ps1)
   | otherwise = intern (Branch prefix bit ps0 (ps ∪ ps1))

instance Semigroup PositionSet where
   append = union

instance Monoid PositionSet where
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

derive instance Eq PositionSet
derive instance Ord PositionSet
derive newtype instance Show PositionSet
