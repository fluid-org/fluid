module Test.Benchmark.Intermediate where

-- Paired performance harness comparing backward slicing with vs. without
-- `@doc`-annotated intermediate values. The "without" variant is obtained by
-- applying `stripDocStmt` to the desugared program, which structurally removes
-- every `DocExpr` wrapper. See docs/reports/intermediate-perf.tex for the
-- table this populates.

import Prelude

import Control.Monad.Error.Class (catchError)
import Control.Monad.Reader (class MonadReader)
import Data.Array (head, length, range)
import Data.Foldable (for_, sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Number.Format (fixed, toStringWith)
import Data.Set (size) as Set
import Data.Traversable (for, traverse)
import Effect.Class.Console (log)
import Effect.Exception (message)
import Eval (GraphConfig, graphEval, graphGC)
import Expr (Stmt)
import File (class LoadFile, File(..), FileCxt, Folder(..), loadFile)
import Graph (size, vertices)
import Lattice (Raw, erase, topOf, 𝔹)
import Module (prepConfig, prepConfigNoDoc)
import Pretty (prettyP)
import Primitive.Defs (primitives)
import Test.Benchmark.Util (time)
import Util (AffError, check, throw, (×))
import Val (Val, intermediateVertices)

type VariantResult =
   { evalMs :: Number -- graph evaluation time
   , bwdMs :: Number -- backward slice time (whole output selected)
   , verts :: Int -- total graph vertices
   , interm :: Int -- number of @doc-annotated intermediate vertices
   , out :: Raw Val -- evaluated output (annotations erased), for equivalence checks
   }

type PerfRow =
   { file :: String
   , withDoc :: VariantResult
   , without :: VariantResult
   }

fluidSrcPaths :: Array Folder
fluidSrcPaths = [ Folder "fluid", Folder "test/fluid" ]

runVariant
   :: forall m
    . MonadReader FileCxt m
   => LoadFile m
   => GraphConfig
   -> Raw Stmt
   -> AffError m VariantResult
runVariant gconfig s' = do
   evalMs × graphed <- time \_ -> graphEval gconfig s'
   let { g, outα } = graphed
   let { bwd } = graphGC graphed
   let out_top = topOf outα :: Val 𝔹
   -- Force the slice by demanding the resulting graph's size.
   bwdMs × _ <- time \_ -> pure (let _ × g' = bwd out_top in size g')
   pure
      { evalMs
      , bwdMs
      , verts: size g
      , interm: Set.size (intermediateVertices (vertices g))
      , out: erase outα
      }

benchFile
   :: forall m
    . MonadReader FileCxt m
   => LoadFile m
   => Int
   -> File
   -> AffError m PerfRow
benchFile n file = do
   fluidSrc <- loadFile fluidSrcPaths file
   withCfg <- prepConfig primitives fluidSrc
   noDocCfg <- prepConfigNoDoc primitives fluidSrc

   runs <- for (range 1 n) \_ -> do
      w <- runVariant withCfg.gconfig withCfg.e
      wo <- runVariant noDocCfg.gconfig noDocCfg.e
      pure (w × wo)

   withDoc <- averageVariant (map (\(w × _) -> w) runs)
   without <- averageVariant (map (\(_ × wo) -> wo) runs)

   check (withDoc.interm > 0)
      ("stripDocStmt check: expected intermediate vertices in " <> show file <> ", found none")
   check (without.interm == 0)
      ( "stripDocStmt check: stripped " <> show file <> " still has "
           <> show without.interm
           <> " intermediate vertices"
      )
   check (prettyP withDoc.out == prettyP without.out)
      ( "stripDocStmt check: output changed for " <> show file
           <> "\nwith @doc:\n"
           <> prettyP withDoc.out
           <> "\nwithout:\n"
           <> prettyP without.out
      )

   pure { file: unwrap file, withDoc, without }

averageVariant :: forall m. Array VariantResult -> AffError m VariantResult
averageVariant rs = case head rs of
   Nothing -> throw "averageVariant: no runs (n must be >= 1)"
   Just first ->
      pure $ first
         { evalMs = sum (map _.evalMs rs) / n
         , bwdMs = sum (map _.bwdMs rs) / n
         }
   where
   n = toNumber (length rs)

benchmarkIntermediates
   :: forall m
    . MonadReader FileCxt m
   => LoadFile m
   => Int
   -> Array String
   -> AffError m Unit
benchmarkIntermediates n files = do
   rows <- traverse (\file -> benchFile n (File file)) files
   log "\n% --- intermediate-perf.tex table body (with @doc | without | ratio) ---"
   for_ rows \row -> log (latexRow row)
   log "% --- end table body ---\n"
   for_ rows \row -> log (summaryLine row)

probeIntermediates
   :: forall m
    . MonadReader FileCxt m
   => LoadFile m
   => Array String
   -> AffError m Unit
probeIntermediates files = do
   log "\n-- intermediate-vertex probe (intermediate / total vertices) --"
   for_ files \path ->
      catchError (probeFile path) \err ->
         log (path <> ": ERROR " <> message err)
   where
   probeFile path = do
      fluidSrc <- loadFile fluidSrcPaths (File path)
      { e, gconfig } <- prepConfig primitives fluidSrc
      r <- runVariant gconfig e
      log (path <> ": intermediate=" <> show r.interm <> " total=" <> show r.verts)

latexRow :: PerfRow -> String
latexRow { file, withDoc, without } =
   file
      <> " & "
      <> ms withDoc.evalMs
      <> " & "
      <> ms withDoc.bwdMs
      <> " & "
      <> show withDoc.verts
      <> " & "
      <> ms without.evalMs
      <> " & "
      <> ms without.bwdMs
      <> " & "
      <> show without.verts
      <> " & "
      <> ratio withDoc.evalMs without.evalMs
      <> " & "
      <> ratio withDoc.bwdMs without.bwdMs
      <> " & "
      <> ratio (toNumber withDoc.verts) (toNumber without.verts)
      <> " \\\\"

summaryLine :: PerfRow -> String
summaryLine { file, withDoc, without } =
   file <> ": intermediate vertices with=" <> show withDoc.interm
      <> " without="
      <> show without.interm
      <> " (eval "
      <> ms withDoc.evalMs
      <> "/"
      <> ms without.evalMs
      <> " ms,"
      <> " bwd "
      <> ms withDoc.bwdMs
      <> "/"
      <> ms without.bwdMs
      <> " ms)"

ms :: Number -> String
ms = toStringWith (fixed 1)

ratio :: Number -> Number -> String
ratio a b
   | b == 0.0 = "--"
   | otherwise = toStringWith (fixed 3) (a / b)
