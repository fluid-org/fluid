module Test.Benchmark.Intermediate where

import Prelude

import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Reader (class MonadReader)
import Data.Array (concatMap, drop, elem, filter, head, zip)
import Data.Array.NonEmpty (fromArray) as NEA
import Data.Map (fromFoldable, lookup) as Map
import Data.Maybe (fromMaybe, maybe)
import Data.Number (fromString) as Number
import Data.Number.Format (fixed, toStringWith)
import Data.String (Pattern(..), contains, joinWith, split, trim)
import Data.String.CodeUnits (dropWhile, takeWhile) as CU
import Data.Traversable (for)
import Effect.Aff (Error)
import Effect.Aff.Class (class MonadAff)
import Effect.Class.Console (log)
import File (class LoadFile, FileCxt)
import Test.Benchmark.Util (BenchAcc(..))
import Test.Util.Suite (TestBwdIntermediateSpec, intermediateTest)
import Util (AffError, (×))

benchmarkIntermediates
   :: forall m
    . MonadAff m
   => MonadError Error m
   => MonadReader FileCxt m
   => LoadFile m
   => Int
   -> Array TestBwdIntermediateSpec
   -> AffError m Unit
benchmarkIntermediates n specs = do
   rows <- for specs \s -> (s.file × _) <$> intermediateTest n s
   maybe (log "no intermediate benchmark files") emit (NEA.fromArray rows)
   where
   emit rows' = log csv *> log (latexFromCsv csv)
      where
      csv = show (BenchAcc rows')

latexFromCsv :: String -> String
latexFromCsv csv =
   joinWith "\n" ([ headerLine ] <> map rowLine dataRows)
   where
   rows = filter (_ /= "") (map trim (split (Pattern "\n") csv))
   header = maybe [] (split (Pattern ",")) (head rows)
   dataRows = drop 1 rows
   bases = filter (\c -> not (contains (Pattern "°") c) && (c <> "°") `elem` header) header

   headerLine =
      joinWith " & " ([ "File" ] <> concatMap (\b -> [ b, b <> "°", b <> " ratio" ]) bases) <> " \\\\"

   rowLine line = joinWith " & " ([ name ] <> concatMap cellsFor bases) <> " \\\\"
      where
      cells = split (Pattern ",") line
      dict = Map.fromFoldable (zip header cells)
      name = fromMaybe "?" (head cells)
      col c = mean (fromMaybe "" (Map.lookup c dict))
      cellsFor b = [ fmt (col b), fmt (col (b <> "°")), ratio (col b) (col (b <> "°")) ]

mean :: String -> Number
mean s = fromMaybe 0.0 (Number.fromString (CU.takeWhile numeric (CU.dropWhile (not <<< numeric) s)))
   where
   numeric c = (c >= '0' && c <= '9') || c == '.' || c == '-'

fmt :: Number -> String
fmt = toStringWith (fixed 1)

ratio :: Number -> Number -> String
ratio a b
   | b == 0.0 = "--"
   | otherwise = toStringWith (fixed 3) (a / b)
