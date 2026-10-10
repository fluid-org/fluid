module DefiniteAssignment where

import Prelude

import Bind (Name, Var, dottedName)
import Control.Monad.Error.Class (throwError)
import Data.List.NonEmpty (unsnoc)
import Data.List.NonEmpty as NEL
import Data.Foldable (lookup)
import Data.List (List(..), elemIndex, index, length, (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Types (Type) as T
import Util (MayFail, type (×), definitely')

type ClassEntry =
   { cxt :: Cxt -- declaring context (resolves the base class)
   , name :: Name -- fully-qualified name, the class's identity
   , typeParams :: List Var
   , base :: Maybe Var -- base class, if any
   , fields :: List Var -- own field names, distinct
   }

-- Variable entries carry no type until checking and synthesis, as unannotated assignments have none.
data Entry
   = Unbound -- declared later in scope
   | Declared -- definitely unassigned
   | PossiblyUnassigned
   | Assigned
   | Class ClassEntry
   | Mod Name
   | ModChecked Name Cxt
   | PredefName
   | TypeVar -- type parameter
   | TypeAlias (List Var) T.Type

type Cxt = Map Var Entry

data WfResult a = Returns | Assigns a

extend :: Cxt -> Cxt -> Cxt
extend cxt cxt' = Map.unionWith extendEntry cxt cxt'

extendEntry :: Entry -> Entry -> Entry
extendEntry (ModChecked q cxt) (ModChecked q' cxt') | q == q' = ModChecked q (cxt `extend` cxt')
extendEntry (Mod q) θ'@(ModChecked q' _) | q == q' = θ'
extendEntry θ@(ModChecked q _) (Mod q') | q == q' = θ
extendEntry _ θ' = θ'

override :: Cxt -> Cxt -> Cxt
override = flip Map.union

merge :: Cxt -> Cxt -> Cxt
merge cxt cxt' = Map.intersectionWith mergeEntry cxt cxt' `Map.union` (PossiblyUnassigned <$ Map.union cxt cxt')
   where
   mergeEntry θ θ' = if θ == θ' then θ else PossiblyUnassigned

overrideRes :: WfResult Cxt -> WfResult Cxt -> WfResult Cxt
overrideRes _ Returns = Returns
overrideRes Returns _ = Returns
overrideRes (Assigns cxt) (Assigns cxt') = Assigns (cxt `override` cxt')

mergeRes :: WfResult Cxt -> WfResult Cxt -> WfResult Cxt
mergeRes Returns r = r
mergeRes r Returns = r
mergeRes (Assigns cxt) (Assigns cxt') = Assigns (cxt `merge` cxt')

classFor :: Cxt -> Var -> Maybe ClassEntry
classFor cxt c = case Map.lookup c cxt of
   Just (Class cls) -> Just cls
   _ -> Nothing

classOf :: Cxt -> Name -> MayFail ClassEntry
classOf cxt c = case resolveName cxt c of
   Just (Class cls) -> pure cls
   _ -> throwError $ "Unknown dataclass: " <> dottedName c

resolveName :: Cxt -> Name -> Maybe Entry
resolveName cxt name = case NEL.fromList init of
   Nothing -> simpleEntry cxt x
   Just q -> case resolveName cxt q of
      Just (ModChecked _ cxt') -> simpleEntry cxt' x
      _ -> Nothing
   where
   { init, last: x } = unsnoc name
   simpleEntry g y = case Map.lookup y g of
      Just e@Assigned -> Just e
      Just e@(ModChecked _ _) -> Just e
      Just e@(Class _) -> Just e
      Just e@TypeVar -> Just e
      Just e@(TypeAlias _ _) -> Just e
      _ -> Nothing

fields :: ClassEntry -> List Var
fields cls = case cls.base of
   Nothing -> cls.fields
   Just b -> fields (definitely' (classFor cls.cxt b)) <> cls.fields

ancestors :: ClassEntry -> List Name
ancestors cls = cls.name : maybe Nil ancestors (cls.base >>= classFor cls.cxt)

-- Argument for a field, positional then keyword.
fieldMap :: forall a. ClassEntry -> List a -> List (Var × a) -> Var -> Maybe a
fieldMap cls xs xys x = case elemIndex x (fields cls) of
   Just i | i < length xs -> index xs i
   _ -> lookup x xys

-- ======================
-- boilerplate
-- ======================
derive instance Functor WfResult
derive instance Eq a => Eq (WfResult a)
derive instance Eq Entry

