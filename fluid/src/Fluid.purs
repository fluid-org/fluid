module Fluid where

import Prelude hiding (between)

import Bind (Bind, (↦))
import Data.Array (filter)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split, stripPrefix, stripSuffix, trim)
import Data.String as String
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Aff (Aff, Error, runAff_)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Eval (graphEval)
import File (File(..), FileCxt(..), Folder(..), loadFile)
import Lattice (erase)
import Module (prepConfig)
import Module.Node (runNodeT)
import Options.Applicative (Parser, command, execParser, fullDesc, header, help, helper, long, progDesc, short, strOption, subparser, switch, (<**>))
import Options.Applicative.Builder (info)
import Parse (parseProgram)
import Pretty (prettyP)
import Util (Endo)
import Val (Val)

data EvalArgs = EvalArgs
   { local :: Boolean
   , fileName :: String
   , fluidSrcPath :: Folder
   }

data Command = Evaluate EvalArgs | Parse_ EvalArgs

between :: forall a. Pattern -> Pattern -> Endo (String -> Either String a)
between p1 p2 f s =
   case (stripPrefix p1) s >>= stripSuffix p2 of
      Just rest -> f rest
      Nothing -> Left ("Expected " <> show p1 <> "..." <> show p2 <> " but got ...")

parsePair :: String -> Either String (Bind String)
parsePair = between (Pattern "(") (Pattern ")") $ \s ->
   case split (Pattern ",") s of
      [ k, v ] -> Right (trim k ↦ trim v)
      _ -> Left $ "Expected a pair but got " <> s

parseImports' :: Pattern -> Pattern -> (String -> Either String (Array String))
parseImports' open close = between open close $ \s -> do
   Right (map trim $ filter (not <<< String.null) $ split (Pattern ",") s)

parseLocal :: Parser Boolean
parseLocal = switch (long "local" <> short 'l' <> help "Are you running fluid as a library?")

parseEvaluate :: Parser EvalArgs
parseEvaluate = ado
   local <- parseLocal
   fileName <- strOption (long "file" <> short 'f' <> help "The file to parse")
   fluidSrcPath <- Folder <$> strOption (long "fluid-src-path" <> short 'p' <> help "The path containing the program files")
   in EvalArgs { local, fileName, fluidSrcPath }

commands :: { evaluate :: Parser Command, parse :: Parser Command }
commands =
   { evaluate: Evaluate <$> parseEvaluate
   , parse: Parse_ <$> parseEvaluate
   }

commandParser :: Parser Command
commandParser = subparser
   ( command "evaluate" (info commands.evaluate (progDesc "Evaluate a file"))
        <> command "parse" (info commands.parse (progDesc "Parse a file"))
   )

dispatchCommand ∷ Command → Aff Unit
dispatchCommand (Evaluate p) = do
   v <- evaluate p
   log (prettyP v)
dispatchCommand (Parse_ p) = do
   r <- parse p
   log r

main :: Effect Unit
main = runAff_ callback (dispatchCommand =<< liftEffect (execParser opts))
   where
   opts = info (commandParser <**> helper) (fullDesc <> progDesc "Parse a file" <> header "parse - a simple parser")

callback :: Either Error Unit -> Effect Unit
callback = case _ of
   Left err -> logShow err
   Right _ -> pure unit

fluidLibraryPath :: String
fluidLibraryPath = "node_modules/@fluid-org/fluid"

evaluate :: EvalArgs -> Aff (Val Unit)
evaluate (EvalArgs { local, fileName, fluidSrcPath }) = do
   let fluidSrcPaths = [ fluidSrcPath ] <> if local then [ Folder (fluidLibraryPath <> "/dist/fluid/fluid") ] else []
   runNodeT (FileCxt { fluidSrcPaths, classes: Map.empty }) $ do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      { e, gconfig } <- prepConfig fluidSrc
      { outα } <- graphEval gconfig e
      pure (erase outα)

parse :: EvalArgs -> Aff String
parse (EvalArgs { local, fileName, fluidSrcPath }) = do
   let fluidSrcPaths = [ fluidSrcPath ] <> if local then [ Folder (fluidLibraryPath <> "/dist/fluid/fluid") ] else []
   runNodeT (FileCxt { fluidSrcPaths, classes: Map.empty }) $ do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      case (parseProgram fluidSrc) of
         Left err -> pure err
         Right expr -> pure $ prettyP (fst expr)
