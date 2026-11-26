module Module.Defs where

import Prelude

import Data.List (List(..), filter, mapMaybe, (:))
import Data.List.NonEmpty (NonEmptyList(..), unsnoc)
import Data.List.NonEmpty (fromList) as NEL
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Set (Set)
import Data.Set as Set
import Bind (Name, Var, prefixOf)
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

view :: ModuleName
view = NonEmptyList ("fluid" :| "view" : Nil)

-- Immediate submodules of q in the module table, by simple name.
submods :: Set ModuleName -> ModuleName -> List (Var × ModuleName)
submods modules q = mapMaybe sub (Set.toUnfoldable modules)
   where
   sub m = let { init, last: x } = unsnoc m in whenever (NEL.fromList init == Just q) (x × m)

parents :: ModuleName -> List ModuleName
parents q = case NEL.fromList (unsnoc q).init of
   Nothing -> Nil
   Just q' -> parents q' <> (q' : Nil)

containing :: ModuleName -> ModuleName -> List ModuleName
containing q q' = filter (not <<< (_ `prefixOf` q)) (parents q')
