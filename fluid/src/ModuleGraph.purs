module ModuleGraph where

import Prelude

import Data.List (List(..), mapMaybe, takeWhile, (:))
import Data.List.NonEmpty (NonEmptyList(..), unsnoc)
import Data.List.NonEmpty (fromList) as NEL
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Set (Set)
import Data.Set as Set
import Bind (Name, Var)
import Util (type (×), whenever, (×))

type ModuleName = Name

builtins :: ModuleName
builtins = pure "builtins"

math :: ModuleName
math = pure "math"

typing :: ModuleName
typing = pure "typing"

dataclasses :: ModuleName
dataclasses = pure "dataclasses"

sys :: ModuleName
sys = pure "sys"

prelude :: ModuleName
prelude = NonEmptyList ("fluid" :| "prelude" : Nil)

-- Modules in scope without import, each under members of those before it
implicit :: List ModuleName
implicit = builtins : prelude : Nil

implicitFor :: ModuleName -> List ModuleName
implicitFor q = takeWhile (_ /= q) implicit

-- Immediate submodules of q in the module table, by unqualified name.
submodules :: Set ModuleName -> ModuleName -> List (Var × ModuleName)
submodules modules q = mapMaybe sub (Set.toUnfoldable modules)
   where
   sub m = let { init, last: x } = unsnoc m in whenever (NEL.fromList init == Just q) (x × m)

type DependencyGraph = Map ModuleName (List ModuleName)
