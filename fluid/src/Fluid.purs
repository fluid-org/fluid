module Fluid where

import Prelude

import App.Fig.Build (JsonOptions, figGraphTimed, optionsFromJson)
import App.Fig.Graph (encodeFigGraph)
import Control.Monad.Except (runExceptT)
import Control.Monad.Trans.Class (lift)
import Data.Argonaut.Core (Json, stringify, stringifyWithIndent)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError)
import Data.Argonaut.Encode (encodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Foldable (for_)
import Data.List.Types (NonEmptyList)
import Data.Set as Set
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.List.NonEmpty as NEL
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (Pattern(..), joinWith, split, stripPrefix)
import Data.Tuple (fst)
import Effect (Effect)
import Effect.Aff (Aff, Error, message, runAff_, try)
import Effect.Class (liftEffect)
import Effect.Class.Console (log, logShow)
import Eval (evalProgram)
import File (File(..), Folder(..), emptyFileCxt, fileCxtIn, loadFile, loadManifest, modulePath, withClasses, withRoots)
import Classes (ClassTable)
import Data.Map (Map)
import Module (Config, ParseFailure(..), loadTopLevel, prepConfig, prepModule)
import Module.Defs (ModuleName)
import Module.Node (NodeT, runNodeT)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (mkdir', readTextFile, writeTextFile)
import Node.FS.Perms (permsAll)
import Node.Path (basenameWithoutExt, concat, dirname)
import Node.Process (exit')
import Options.Applicative (Parser, command, execParser, fullDesc, header, help, helper, long, metavar, progDesc, short, some, strArgument, strOption, subparser, switch, (<**>))
import Options.Applicative.Builder (info)
import Parse (parseModule, parseProgram)
import Pretty (prettyP)
import Pretty.Trace (renderTrace)
import Expr (Module) as E
import SExpr (Import(..)) as S
import Util (type (×), orElse, orThrow, throw, withMsg, (×))
import Val (valAt)

type FileArgs =
   { local :: Boolean
   , fileName :: String
   , fluidSrcPaths :: Array Folder
   , asModule :: Boolean -- as module rather than program
   }

type BuildArgs =
   { specs :: NonEmptyList String -- JSON files of figure options
   , out :: String -- directory for figure graphs
   , timing :: Boolean
   }

data Command = Parse_ FileArgs | Check FileArgs | Evaluate FileArgs | Trace FileArgs | Build BuildArgs | Manifest (NonEmptyList String)

parseFileArgs :: Parser FileArgs
parseFileArgs = ado
   local <- switch (long "local" <> short 'l' <> help "Are you running Fluid as a library?")
   fileName <- strOption (long "file" <> short 'f' <> help "The file")
   fluidSrcPaths <- Array.fromFoldable <$> some (Folder <$> strOption (long "fluid-src-path" <> short 'p' <> help "A path containing program or library files"))
   asModule <- switch (long "module" <> short 'm' <> help "Treat the file as a module rather than a program")
   in { local, fileName, fluidSrcPaths, asModule }

parseBuildArgs :: Parser BuildArgs
parseBuildArgs = ado
   out <- strOption (long "out" <> short 'o' <> help "Directory for figure graphs")
   timing <- switch (long "timing" <> help "Print times of evaluation and materialisation")
   specs <- some (strArgument (metavar "SPEC" <> help "JSON file of figure options"))
   in { specs, out, timing }

parseManifest :: Parser (NonEmptyList String)
parseManifest = some (strArgument (metavar "DIR" <> help "Directory to write manifests under"))

commandParser :: Parser Command
commandParser = subparser
   ( command "parse" (info (Parse_ <$> parseFileArgs) (progDesc "Parse a file and print it back"))
        <> command "check" (info (Check <$> parseFileArgs) (progDesc "Check a file statically, with the exit codes of a PurePy checker"))
        <> command "evaluate" (info (Evaluate <$> parseFileArgs) (progDesc "Check and evaluate a file, printing its value; exit 1 on failure"))
        <> command "trace" (info ((Trace <$> parseFileArgs) <**> helper) (progDesc "Evaluate a program and print its recorded rule graph"))
        <> command "build" (info (Build <$> parseBuildArgs) (progDesc "Write the figure graph of each figure"))
        <> command "manifest" (info (Manifest <$> parseManifest) (progDesc "Write manifest.json into each directory with .fld files beneath it"))
   )

dispatchCommand ∷ Command → Aff Unit
dispatchCommand (Parse_ args) = report args do
   fluidSrc <- loadFile (srcPaths args.local args.fluidSrcPaths) (File args.fileName)
   pure case (if args.asModule then prettyP <<< fst <$> parseModule fluidSrc else prettyP <<< fst <$> parseProgram fluidSrc) of
      Left err -> exitCode.prohibited × Just err
      Right src -> exitCode.accepted × Just src
dispatchCommand (Check args) = report args (stages args (const (pure Nothing)))
dispatchCommand (Evaluate args) = report args $ stages args case _ of
   AsProgram { e, inputs, classes } -> evalProgram inputs classes e <#> \{ g, out } -> Just (prettyP (valAt g out))
   AsModule q { modules, classes } -> withClasses classes (loadTopLevel modules (S.Import q Nothing : Nil)) $> Nothing

dispatchCommand (Trace args) = report args $ stages args case _ of
   AsProgram { e, inputs, classes } -> do
      ev <- evalProgram inputs classes e
      pure (Just (renderTrace ev))
   AsModule _ _ -> throw "Tracing modules is not supported"
dispatchCommand (Build { specs, out, timing }) = do
   mkdir' out { recursive: true, mode: permsAll }
   for_ specs \spec -> withMsg spec do
      json <- readTextFile UTF8 spec >>= jsonParser >>> orThrow
      { program } :: { program :: String } <- decode json
      options :: JsonOptions <- decode json
      fluidSrc <- readTextFile UTF8 program
      let options'@{ fluidSrcPaths } = optionsFromJson options
      graph × times <- runNodeT (fileCxtIn (Folder (dirname program))) $ withRoots fluidSrcPaths do
         fig × times <- figGraphTimed options' fluidSrc
         (_ × times) <$> orThrow (encodeFigGraph fig)
      writeTextFile UTF8 (concat [ out, basenameWithoutExt spec ".json" <> ".json" ]) (stringify graph)
      when timing $ log $
         spec <> ": evaluate " <> show times.evaluate <> " ms, materialise " <> show times.materialise <> " ms"
   where
   decode :: forall a. DecodeJson a => Json -> Aff a
   decode = decodeJson >>> lmap printJsonDecodeError >>> orThrow
dispatchCommand (Manifest dirs) = for_ dirs (writeManifests <<< Folder)

-- Print message, if any, and exit with code.
report :: FileArgs -> NodeT Aff (Int × Maybe String) -> Aff Unit
report { local, fluidSrcPaths } action = do
   code × msg <- runNodeT emptyFileCxt $ withRoots (srcPaths local fluidSrcPaths) action
   for_ msg log
   liftEffect (exit' code)

main :: Effect Unit
main = runAff_ callback (dispatchCommand =<< liftEffect (execParser opts))
   where
   opts = info (commandParser <**> helper) (fullDesc <> progDesc "Parse a file" <> header "parse - a simple parser")

callback :: Either Error Unit -> Effect Unit
callback = case _ of
   Left err -> logShow err *> exit' 1
   Right _ -> pure unit

-- Add installed library when running as library.
srcPaths :: Boolean -> Array Folder -> Array Folder
srcPaths local fluidSrcPaths = fluidSrcPaths <> if local then [ Folder "node_modules/@fluid-org/fluid/dist/fluid/lib" ] else []

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
   directories (File path) = Array.range 1 (Array.length segments) # Array.dropEnd 1 <#> \n -> Just (joinWith "/" (Array.take n segments))
      where
      segments = split (Pattern "/") path

-- Exit codes required of checker by PurePy test runner.
exitCode :: { accepted :: Int, prohibited :: Int, illFormed :: Int }
exitCode = { accepted: 0, prohibited: 1, illFormed: 3 }

-- File parsed and checked as program or module.
data Prepared = AsProgram Config | AsModule ModuleName { modules :: Map ModuleName E.Module, classes :: ClassTable }

-- Parse and check, then run; stop at first failure with its code and first line of its message, or finish with
-- the run's message. A run failure exits 1.
stages :: FileArgs -> (Prepared -> NodeT Aff (Maybe String)) -> NodeT Aff (Int × Maybe String)
stages { local, fileName, fluidSrcPaths, asModule } run = do
   fluidSrc <- loadFile (srcPaths local fluidSrcPaths) (File fileName)
   try (runExceptT (prepare fluidSrc)) >>= case _ of
      Left err -> rejected exitCode.illFormed (message err)
      Right (Left (ParseFailure msg)) -> rejected exitCode.prohibited msg
      Right (Right prepared) -> try (run prepared) >>= case _ of
         Left err -> rejected 1 (message err)
         Right msg -> pure (exitCode.accepted × msg)
   where
   prepare fluidSrc
      | asModule = lift moduleName >>= \q -> AsModule q <$> prepModule q
      | otherwise = AsProgram <$> prepConfig fluidSrc

   -- module name of file, relative to its root
   moduleName = do
      path <- modulePath (File fileName) # orElse ("Not a source file: " <> fileName)
      NEL.fromFoldable (split (Pattern "/") path) # orElse "Empty module name"

   rejected code msg = pure (code × Just (fromMaybe msg (Array.head (split (Pattern "\n") msg))))
