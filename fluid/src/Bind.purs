module Bind where

import Prelude
import Data.Foldable (intercalate)
import Data.List (List(..), Pattern(..), stripPrefix, (:))
import Data.List.NonEmpty (NonEmptyList, snoc, toList, uncons)
import Data.Maybe (Maybe(..), isJust)
import Data.Set (Set, empty)
import Data.Tuple (Tuple(..), fst, snd)
import Util (type (×), definitely, singleton, whenever)
import Util.Set ((∪))

-- Not easy as a newtype as there is no Coercible instance for Set.
type Var = String

type Name = NonEmptyList Var

dottedName :: Name -> String
dottedName = intercalate "."

qual :: Name -> Var -> Name
qual = snoc

prefixOf :: Name -> Name -> Boolean
prefixOf q q' = isJust (stripPrefix (Pattern (toList q)) (toList q'))

properPrefixOf :: Name -> Name -> Boolean
properPrefixOf q q' = q `prefixOf` q' && q /= q'

pathName :: Name -> String
pathName = intercalate "/"

simple :: Name -> Maybe Var
simple n = case uncons n of
   { head: x, tail: Nil } -> Just x
   _ -> Nothing

varAnon = "_" :: Var

-- Discrete partial order for variables.
mustGeq :: Var -> Var -> Var
mustGeq x y = definitely "greater" (whenever (x == y) x)

type Bind a = Var × a

key :: forall a. Bind a -> Var
key = fst

val :: forall a. Bind a -> a
val = snd

keys :: forall a. List (Bind a) -> Set Var
keys Nil = empty
keys ((x ↦ _) : xvs) = singleton x ∪ keys xvs

showBind :: forall a. Show a => Var -> a -> Bind String
showBind x = show >>> (x ↦ _)

infix 4 Tuple as ↦
infix 4 showBind as ⟼
infixl 4 mustGeq as ⪂
