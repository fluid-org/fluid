module Test.Benchmark.Util where

import Prelude

import Control.Monad.Writer.Class (class MonadWriter, tell)
import Data.Array (intersperse, fromFoldable) as A
import Data.Array.NonEmpty (NonEmptyArray, head, toArray)
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.List (List(..), fold, length)
import Data.Map (Map, unionWith, keys, values)
import Data.Map (empty, singleton) as Map
import Data.Newtype (class Newtype, over2)
import Data.Number (pow, sqrt)
import Data.Tuple (snd)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Class.Console (log)
import Graph (class Graph, size)
import Util (type (×), EffectError, Thunk, debug, force, (×), singleton)

logAs :: forall m. MonadEffect m => String -> String -> m Unit
logAs tag s = log $ tag <> ": " <> s

newtype BenchAcc = BenchAcc (NonEmptyArray (String × BenchRow))

instance Show BenchAcc where
   show (BenchAcc rows) =
      fold $ A.intersperse "\n" ([ showHeader ] <> (toArray $ showRow <$> rows))
      where
      BenchRow firstRow = head rows # snd

      showHeader :: String
      showHeader =
         fold $ A.intersperse "," ([ "Test-Name" ] <> A.fromFoldable (keys firstRow))

      showRow :: String × BenchRow -> String
      showRow (test_name × (BenchRow row)) =
         fold $ A.intersperse "," ([ test_name ] <> (show <$> A.fromFoldable (values row)))

newtype BenchRow = BenchRow (Map String (List Number))

derive instance Newtype BenchRow _

instance Semigroup BenchRow where
   append = unionWith (<>) `flip over2` BenchRow

instance Monoid BenchRow where
   mempty = BenchRow Map.empty

foreign import microtime :: Effect Number

microtime' :: forall m. MonadEffect m => m Number
microtime' = liftEffect microtime

time :: forall m a. MonadEffect m => Thunk (m a) -> m (Number × a)
time m = do
   t1 <- microtime'
   x <- force m
   t2 <- microtime'
   pure (t2 `sub` t1 × x)

logTimeWhen :: forall m a. MonadEffect m => Boolean -> String -> Thunk (m a) -> m a
logTimeWhen false _ m = force m
logTimeWhen true msg m = do
   t × x <- time m
   logAs msg (show t)
   pure x

benchmark :: forall m a. MonadWriter BenchRow m => String -> Thunk (m a) -> EffectError m a
benchmark name = benchmark' name

benchmark' :: forall m a. MonadWriter BenchRow m => String -> Thunk (m a) -> EffectError m a
benchmark' name m = do
   when debug.logging $ log ("**** " <> name)
   t × x <- time m
   tell (BenchRow $ Map.singleton name (singleton t))
   pure x

-- Record a single named metric into the BenchRow.
record :: forall m. MonadWriter BenchRow m => String -> Number -> m Unit
record name x = tell (BenchRow $ Map.singleton name (singleton x))

recordGraphSize :: forall g m. Graph g => MonadWriter BenchRow m => g -> m Unit
recordGraphSize g = record "Graph-Nodes" (toNumber $ size g)

divRow :: BenchRow -> Int -> BenchRow
divRow (BenchRow row) n =
   BenchRow $ (\x -> Cons (sum x `div` toNumber n) (singleton (stdErr x))) <$> row

stdDev :: List Number -> Number
stdDev ns' = sqrt $ mean deviation
   where
   deviation = map (\x -> pow (x - mean ns') 2.0) ns'

   mean :: List Number -> Number
   mean ns = sum ns `div` (toNumber $ length ns)

stdErr :: List Number -> Number
stdErr nums = stdDev nums / sqrt (toNumber $ length nums)
