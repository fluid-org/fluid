module Fluid where

import Prelude

import Data.Argonaut.Core (stringifyWithIndent)
import Data.Argonaut.Encode (encodeJson)
import Data.Array as Array
import Data.Foldable (foldl, for_)
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
import Data.Traversable (for)
import Effect.Class.Console (log, logShow)
import Eval (evalProgram)
import File (File(..), Folder(..), emptyFileCxt, loadFile, loadManifest, modulePath, withClasses, withRoots)
import DataType (ClassTable)
import Data.Map (Map)
import Module (Config, loadTopLevel, prepConfig, prepModule)
import ModuleGraph (ModuleName)
import Module.Node (NodeT, runNodeT)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (writeTextFile)
import Node.Process (exit')
import Options.Applicative (Parser, command, execParser, fullDesc, header, help, helper, long, metavar, progDesc, short, some, strArgument, strOption, subparser, switch, (<**>))
import Options.Applicative.Builder (info)
import Parse (parseModule, parseProgram)
import Pretty (prettyP)
import Expr (Module) as E
import SExpr (Import(..)) as S
import Util (type (×), orElse, (×))
import DepGraph (valAt)

type FileArgs =
   { local :: Boolean
   , fileNames :: NonEmptyList String
   , fluidSrcPaths :: Array Folder
   , asModule :: Boolean -- each file as module rather than program
   }

data Command = Parse_ FileArgs | Check FileArgs | Evaluate FileArgs | Manifest (NonEmptyList String)

parseFileArgs :: Parser FileArgs
parseFileArgs = ado
   local <- switch (long "local" <> short 'l' <> help "Are you running fluid as a library?")
   fileNames <- some (strOption (long "file" <> short 'f' <> help "A file"))
   fluidSrcPaths <- Array.fromFoldable <$> some (Folder <$> strOption (long "fluid-src-path" <> short 'p' <> help "A path containing program or library files"))
   asModule <- switch (long "module" <> short 'm' <> help "Treat each file as a module rather than a program")
   in { local, fileNames, fluidSrcPaths, asModule }

parseManifest :: Parser (NonEmptyList String)
parseManifest = some (strArgument (metavar "DIR" <> help "Directory to write manifests under"))

commandParser :: Parser Command
commandParser = subparser
   ( command "parse" (info (Parse_ <$> parseFileArgs) (progDesc "Parse files and print them back"))
        <> command "check" (info (Check <$> parseFileArgs) (progDesc "Check files statically, reporting each as <code> <file>[: <message>] with the exit codes of a PurePy checker, and exit with the largest code"))
        <> command "evaluate" (info (Evaluate <$> parseFileArgs) (progDesc "Check and evaluate files, reporting each as <code> <file>[: <message or value>], and exit with the largest code"))
        <> command "manifest" (info (Manifest <$> parseManifest) (progDesc "Write manifest.json into each directory with .fld files beneath it"))
   )

dispatchCommand ∷ Command → Aff Unit
dispatchCommand (Parse_ args) = report args \fileName -> do
   fluidSrc <- loadFile (srcPaths args.local args.fluidSrcPaths) (File fileName)
   pure case (if args.asModule then prettyP <<< fst <$> parseModule fluidSrc else prettyP <<< fst <$> parseProgram fluidSrc) of
      Left err -> exitCode.prohibited × Just err
      Right src -> exitCode.accepted × Just src
dispatchCommand (Check args) = report args \fileName -> stages args fileName (const (pure Nothing))
dispatchCommand (Evaluate args) = report args \fileName -> stages args fileName case _ of
   AsProgram { e, inputs, classes } -> evalProgram inputs classes e <#> \{ g, root } -> Just (prettyP (valAt g root))
   AsModule q { modules, classes } -> withClasses classes (loadTopLevel modules (S.Import q Nothing : Nil)) $> Nothing
dispatchCommand (Manifest dirs) = for_ dirs (writeManifests <<< Folder)

-- Run action over each file, printing its code and message, and exit with the largest code.
report :: FileArgs -> (String -> NodeT Aff (Int × Maybe String)) -> Aff Unit
report { local, fileNames, fluidSrcPaths } action = do
   codes <- for fileNames \fileName -> do
      code × msg <- runNodeT emptyFileCxt $ withRoots (srcPaths local fluidSrcPaths) (action fileName)
      log (show code <> " " <> fileName <> maybe "" (": " <> _) msg)
      pure code
   liftEffect (exit' (foldl max 0 codes))

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
   directories (File path) = Array.range 1 (Array.length segments - 1) <#> \n -> Just (joinWith "/" (Array.take n segments))
      where
      segments = split (Pattern "/") path

-- Exit codes required of checker by PurePy test runner.
exitCode :: { accepted :: Int, prohibited :: Int, illFormed :: Int }
exitCode = { accepted: 0, prohibited: 1, illFormed: 3 }

-- File parsed and checked as program or module.
data Prepared = AsProgram Config | AsModule ModuleName { modules :: Map ModuleName E.Module, classes :: ClassTable }

-- Parse and check, then run; stop at first failure with its code and first line of its message, or finish with
-- the run's message. A run failure exits 1.
stages :: FileArgs -> String -> (Prepared -> NodeT Aff (Maybe String)) -> NodeT Aff (Int × Maybe String)
stages { local, fluidSrcPaths, asModule } fileName run = do
   fluidSrc <- loadFile (srcPaths local fluidSrcPaths) (File fileName)
   let
      parsed = if asModule then void (parseModule fluidSrc) else void (parseProgram fluidSrc)
      prepare =
         if asModule then do
            q <- moduleName
            AsModule q <$> prepModule q
         else AsProgram <$> prepConfig fluidSrc
   case parsed of
      Left err -> rejected exitCode.prohibited err
      Right _ -> try prepare >>= case _ of
         Left err -> rejected exitCode.illFormed (message err)
         Right prepared -> try (run prepared) >>= case _ of
            Left err -> rejected 1 (message err)
            Right msg -> pure (exitCode.accepted × msg)
   where
   -- module name of file, relative to its root
   moduleName = do
      path <- modulePath (File fileName) # orElse ("Not a source file: " <> fileName)
      NEL.fromFoldable (split (Pattern "/") path) # orElse "Empty module name"

   rejected code msg = pure (code × Just (fromMaybe msg (Array.head (split (Pattern "\n") msg))))
