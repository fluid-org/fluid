module Fluid where

import Prelude hiding (between)

import Bind (Bind, (↦))
import Data.Argonaut.Core (stringifyWithIndent)
import Data.Argonaut.Encode (encodeJson)
import Data.Array (filter)
import Data.Array as Array
import Data.Foldable (foldl, for_)
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
import Data.Traversable (for)
import Effect.Class.Console (log, logShow)
import Eval.Dep (depEval)
import File (File(..), Folder(..), emptyFileCxt, loadFile, loadManifest, modulePath, withClasses, withRoots)
import Module (loadTopLevel, prepConfig, prepModule)
import Module.Node (NodeT, runNodeT)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (writeTextFile)
import Node.Process (exit')
import Options.Applicative (Parser, command, execParser, fullDesc, header, help, helper, long, metavar, progDesc, short, some, strArgument, strOption, subparser, switch, (<**>))
import Options.Applicative.Builder (info)
import Parse (parseModule, parseProgram)
import Pretty (prettyP)
import SExpr (Import(..)) as S
import Util (type (×), Endo, definitely, (×))
import Graph.Dep (valAt)
import Val (Val)

data EvalArgs = EvalArgs
   { local :: Boolean
   , fileName :: String
   , fluidSrcPaths :: Array Folder
   }

data CheckArgs = CheckArgs
   { local :: Boolean
   , fileNames :: NonEmptyList String
   , fluidSrcPaths :: Array Folder
   , asModule :: Boolean -- check each file as module rather than program
   }

data Command = Evaluate EvalArgs | Parse_ EvalArgs | Check CheckArgs | Manifest (NonEmptyList String)

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

parseSrcPaths :: Parser (Array Folder)
parseSrcPaths = Array.fromFoldable <$> some (Folder <$> strOption (long "fluid-src-path" <> short 'p' <> help "A path containing program or library files"))

parseEvaluate :: Parser EvalArgs
parseEvaluate = ado
   local <- parseLocal
   fileName <- strOption (long "file" <> short 'f' <> help "The file to parse")
   fluidSrcPaths <- parseSrcPaths
   in EvalArgs { local, fileName, fluidSrcPaths }

parseCheck :: Parser CheckArgs
parseCheck = ado
   local <- parseLocal
   fileNames <- some (strOption (long "file" <> short 'f' <> help "A file to check"))
   fluidSrcPaths <- parseSrcPaths
   asModule <- switch (long "module" <> short 'm' <> help "Check each file as a module rather than a program")
   in CheckArgs { local, fileNames, fluidSrcPaths, asModule }

parseManifest :: Parser (NonEmptyList String)
parseManifest = some (strArgument (metavar "DIR" <> help "Directory to write manifests under"))

commands :: { evaluate :: Parser Command, parse :: Parser Command, check :: Parser Command, manifest :: Parser Command }
commands =
   { evaluate: Evaluate <$> parseEvaluate
   , parse: Parse_ <$> parseEvaluate
   , check: Check <$> parseCheck
   , manifest: Manifest <$> parseManifest
   }

commandParser :: Parser Command
commandParser = subparser
   ( command "evaluate" (info commands.evaluate (progDesc "Evaluate a file"))
        <> command "parse" (info commands.parse (progDesc "Parse a file"))
        <> command "check" (info commands.check (progDesc "Check and run files, reporting each as <code> <file>[: <message>] with the exit codes of a pure-py-spec checker, and exit with the largest code"))
        <> command "manifest" (info commands.manifest (progDesc "Write manifest.json into each directory with .fld files beneath it"))
   )

dispatchCommand ∷ Command → Aff Unit
dispatchCommand (Evaluate p) = do
   v <- evaluate p
   log (prettyP v)
dispatchCommand (Parse_ p) = do
   r <- parse p
   log r
dispatchCommand (Check (CheckArgs { local, fileNames, fluidSrcPaths, asModule })) = do
   codes <- for fileNames \fileName -> do
      code × msg <- check (srcPaths local fluidSrcPaths) asModule fileName
      log (show code <> " " <> fileName <> maybe "" (": " <> _) msg)
      pure code
   liftEffect (exit' (foldl max 0 codes))
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

-- Exit codes required of checker by pure-py-spec test runner, plus evaluationFailed for file that checks but fails
-- to run.
exitCode :: { accepted :: Int, prohibited :: Int, illFormed :: Int, evaluationFailed :: Int }
exitCode = { accepted: 0, prohibited: 1, illFormed: 3, evaluationFailed: 5 }

check :: Array Folder -> Boolean -> String -> Aff (Int × Maybe String)
check fluidSrcPaths asModule fileName =
   runNodeT emptyFileCxt $ withRoots fluidSrcPaths do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      if asModule then
         stages (void (parseModule fluidSrc)) (prepModule q) \{ modules, classes } ->
            withClasses classes (void (loadTopLevel modules (S.Import q Nothing : Nil)))
      else
         stages (void (parseProgram fluidSrc)) (prepConfig fluidSrc) \{ e, inputs, classes } ->
            void (depEval inputs classes e)
   where
   -- module name of file, relative to its root
   q = definitely "module name" (NEL.fromFoldable (split (Pattern "/") (definitely "source file" (modulePath (File fileName)))))

-- Parse, check, run; stop at first failure with its code and first line of its message.
stages :: forall a. Either String Unit -> NodeT Aff a -> (a -> NodeT Aff Unit) -> NodeT Aff (Int × Maybe String)
stages parsed prepare run = case parsed of
   Left err -> rejected exitCode.prohibited err
   Right _ -> try prepare >>= case _ of
      Left err -> rejected exitCode.illFormed (message err)
      Right prepared -> try (run prepared) >>= case _ of
         Left err -> rejected exitCode.evaluationFailed (message err)
         Right _ -> pure (exitCode.accepted × Nothing)
   where
   rejected code msg = pure (code × Just (fromMaybe msg (Array.head (split (Pattern "\n") msg))))

parse :: EvalArgs -> Aff String
parse (EvalArgs { local, fileName, fluidSrcPaths: roots }) = do
   let fluidSrcPaths = srcPaths local roots
   runNodeT emptyFileCxt $ withRoots fluidSrcPaths do
      fluidSrc <- loadFile fluidSrcPaths (File fileName)
      case (parseProgram fluidSrc) of
         Left err -> pure err
         Right expr -> pure $ prettyP (fst expr)
