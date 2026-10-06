module Fluid where

import Prelude hiding (between)

import Bind (Bind, (↦))
import Data.Argonaut.Core (stringifyWithIndent)
import Data.Argonaut.Encode (encodeJson)
import Data.Array (filter)
import Data.Array as Array
import Data.Foldable (for_)
import Data.List.Types (NonEmptyList)
import Data.Set as Set
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (Pattern(..), joinWith, split, stripPrefix, stripSuffix, trim)
import Data.String as String
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Aff (Aff, Error, message, runAff_, try)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Eval.Dep (depEval)
import File (File(..), Folder(..), emptyFileCxt, fluidExtension, loadFile, loadManifest, withClasses, withRoots)
import Module (loadTopLevel, prepConfig, prepModule)
import Module.Node (runNodeT)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (writeTextFile)
import Node.Process (exit')
import Options.Applicative (Parser, command, execParser, fullDesc, header, help, helper, long, metavar, progDesc, short, some, strArgument, strOption, subparser, switch, (<**>))
import Options.Applicative.Builder (info)
import Parse (parseModule, parseProgram)
import Pretty (prettyP)
import SExpr (Import(..)) as S
import Util (Endo, definitely)
import Graph.Dep (valAt)
import Val (Val)

data EvalArgs = EvalArgs
   { local :: Boolean
   , fileName :: String
   , fluidSrcPaths :: Array Folder
   , asModule :: Boolean -- check the file as a module rather than a program
   }

data Command = Evaluate EvalArgs | Parse_ EvalArgs | Check EvalArgs | Manifest (NonEmptyList String)

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
   fluidSrcPaths <- Array.fromFoldable <$> some (Folder <$> strOption (long "fluid-src-path" <> short 'p' <> help "A path containing program or library files"))
   asModule <- switch (long "module" <> short 'm' <> help "Check the file as a module rather than a program")
   in EvalArgs { local, fileName, fluidSrcPaths, asModule }

parseManifest :: Parser (NonEmptyList String)
parseManifest = some (strArgument (metavar "DIR" <> help "Directory to write manifests under"))

commands :: { evaluate :: Parser Command, parse :: Parser Command, check :: Parser Command, manifest :: Parser Command }
commands =
   { evaluate: Evaluate <$> parseEvaluate
   , parse: Parse_ <$> parseEvaluate
   , check: Check <$> parseEvaluate
   , manifest: Manifest <$> parseManifest
   }

commandParser :: Parser Command
commandParser = subparser
   ( command "evaluate" (info commands.evaluate (progDesc "Evaluate a file"))
        <> command "parse" (info commands.parse (progDesc "Parse a file"))
        <> command "check" (info commands.check (progDesc "Check and run a file; exit 1 if rejected by the parser, 3 if ill-formed, 5 if evaluation fails"))
        <> command "manifest" (info commands.manifest (progDesc "Write manifest.json into each directory with .fld files beneath it"))
   )

dispatchCommand ∷ Command → Aff Unit
dispatchCommand (Evaluate p) = do
   v <- evaluate p
   log (prettyP v)
dispatchCommand (Parse_ p) = do
   r <- parse p
   log r
dispatchCommand (Check p) = check p >>= liftEffect <<< exit'
dispatchCommand (Manifest dirs) = for_ dirs (writeManifests <<< Folder)

main :: Effect Unit
main = runAff_ callback (dispatchCommand =<< liftEffect (execParser opts))
   where
   opts = info (commandParser <**> helper) (fullDesc <> progDesc "Parse a file" <> header "parse - a simple parser")

callback :: Either Error Unit -> Effect Unit
callback = case _ of
   Left err -> logShow err *> exit' 1
   Right _ -> pure unit

-- Source roots: the given one, plus the installed library when running locally.
srcPaths :: Boolean -> Array Folder -> Array Folder
srcPaths local fluidSrcPaths = fluidSrcPaths <> if local then [ Folder "node_modules/@fluid-org/fluid/dist/fluid/lib" ] else []

evaluate :: EvalArgs -> Aff (Val Unit)
evaluate (EvalArgs { local, fileName, fluidSrcPaths: roots }) = do
   let fluidSrcPaths = srcPaths local roots
   runNodeT emptyFileCxt $ withRoots fluidSrcPaths do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      { e, inputs, classes } <- prepConfig fluidSrc
      { g, root } <- depEval inputs classes e
      pure (valAt g root)

-- Manifest for dir and for each subdirectory with .fld files beneath it
writeManifests :: Folder -> Aff Unit
writeManifests root@(Folder dir) = do
   files <- runNodeT emptyFileCxt (loadManifest root)
   for_ (Set.insert Nothing (Set.fromFoldable (Set.toUnfoldable files >>= directories))) \sub -> do
      let
         strip (File path) = maybe (Just path) (\sub' -> stripPrefix (Pattern (sub' <> "/")) path) sub
         paths = Array.mapMaybe strip (Set.toUnfoldable files)
      writeTextFile UTF8 (dir <> maybe "" ("/" <> _) sub <> "/manifest.json") (stringifyWithIndent 2 (encodeJson paths) <> "\n")
   where
   -- proper prefixes of a path
   directories :: File -> Array (Maybe String)
   directories (File path) = Array.range 1 (Array.length segments - 1) <#> \n -> Just (joinWith "/" (Array.take n segments))
      where
      segments = split (Pattern "/") path

-- Exit code for the stage at which the program is rejected, if any: 1 syntax, 3 well-formedness, 5 evaluation.
check :: EvalArgs -> Aff Int
check (EvalArgs { local, fileName, fluidSrcPaths: roots, asModule }) = do
   let fluidSrcPaths = srcPaths local roots
   runNodeT emptyFileCxt $ withRoots fluidSrcPaths do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      if asModule then
         case parseModule fluidSrc of
            Left err -> rejected 1 err
            Right _ -> try (prepModule q) >>= case _ of
               Left err -> rejected 3 (message err)
               Right { modules, classes } -> try (withClasses classes (loadTopLevel modules (S.Import q Nothing : Nil))) >>= case _ of
                  Left err -> rejected 5 (message err)
                  Right _ -> pure 0
      else
         case parseProgram fluidSrc of
            Left err -> rejected 1 err
            Right _ -> try (prepConfig fluidSrc) >>= case _ of
               Left err -> rejected 3 (message err)
               Right { e, inputs, classes } -> try (depEval inputs classes e) >>= case _ of
                  Left err -> rejected 5 (message err)
                  Right _ -> pure 0
   where
   rejected code msg = log msg $> code
   -- module name of the file, relative to its root
   q = definitely "module name" (NEL.fromFoldable (split (Pattern "/") (fromMaybe fileName (stripSuffix (Pattern fluidExtension) fileName))))

parse :: EvalArgs -> Aff String
parse (EvalArgs { local, fileName, fluidSrcPaths: roots }) = do
   let fluidSrcPaths = srcPaths local roots
   runNodeT emptyFileCxt $ withRoots fluidSrcPaths do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      case (parseProgram fluidSrc) of
         Left err -> pure err
         Right expr -> pure $ prettyP (fst expr)
