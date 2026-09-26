module ModuleGraph where

import Prelude

import Data.List (List(..), takeWhile, (:))
import Data.List.NonEmpty (NonEmptyList(..))
import Data.Map (Map)
import Data.NonEmpty ((:|))
import Bind (Name)

type ModuleName = Name

builtins :: ModuleName
builtins = pure "builtins"

math :: ModuleName
math = pure "math"

typing :: ModuleName
typing = pure "typing"

dataclasses :: ModuleName
dataclasses = pure "dataclasses"

prelude :: ModuleName
prelude = NonEmptyList ("fluid" :| "prelude" : Nil)

-- Modules in scope without import, each under the members of those before it.
implicit :: List ModuleName
implicit = builtins : prelude : Nil

implicitFor :: ModuleName -> List ModuleName
implicitFor q = takeWhile (_ /= q) implicit

type DependencyGraph = Map ModuleName (List ModuleName)
