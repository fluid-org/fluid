module DefiniteAssignment where

import Prelude

import Bind (Name, Var, dottedName)
import Control.Monad.Error.Class (throwError)
import Data.Either (Either)
import Data.List.NonEmpty as NEL
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set (Set)
import Data.Set as Set
import Util (definitely')

type VarCxt = Map Var Boolean

type ClassEntry =
   { cxt :: Cxt -- declaring context (resolves the base class)
   , name :: Name -- fully-qualified name, the class's identity
   , base :: Maybe Var -- base class, if any
   , fields :: List Var -- own field names, distinct
   }

data Entry
   = VarStatus Boolean -- definite-assignment status
   | Class ClassEntry
   | Mod Name
   | ModLoaded Name Cxt

type Cxt = Map Var Entry

data WfResult a = Returns | Assigns a

extendCxtWith :: Cxt -> Cxt -> Cxt
extendCxtWith cxt cxt' = Map.unionWith extendEntry cxt cxt'

extendEntry :: Entry -> Entry -> Entry
extendEntry (ModLoaded q cxt) (ModLoaded q' cxt') | q == q' = ModLoaded q (cxt `extendCxtWith` cxt')
extendEntry (Mod q) θ'@(ModLoaded q' _) | q == q' = θ'
extendEntry θ@(ModLoaded q _) (Mod q') | q == q' = θ
extendEntry _ θ' = θ'

overrideVarCxt :: VarCxt -> VarCxt -> VarCxt
overrideVarCxt = flip Map.union

mergeVarCxt :: VarCxt -> VarCxt -> VarCxt
mergeVarCxt cxt1 cxt2 =
   foldl (\acc k -> Map.insert k (mergedAt k) acc) Map.empty allKeys
   where
   allKeys :: Set Var
   allKeys = Set.fromFoldable (Map.keys cxt1) `Set.union` Set.fromFoldable (Map.keys cxt2)
   mergedAt k = case Map.lookup k cxt1, Map.lookup k cxt2 of
      Just a, Just b -> a && b
      _, _ -> false

overrideRes :: WfResult VarCxt -> WfResult VarCxt -> WfResult VarCxt
overrideRes _ Returns = Returns
overrideRes Returns _ = Returns
overrideRes (Assigns a) (Assigns b) = Assigns (overrideVarCxt a b)

mergeRes :: WfResult VarCxt -> WfResult VarCxt -> WfResult VarCxt
mergeRes Returns r = r
mergeRes r Returns = r
mergeRes (Assigns a) (Assigns b) = Assigns (mergeVarCxt a b)

-- The desugared program's context: module and class entries resolved away.
erase :: Cxt -> VarCxt
erase = Map.mapMaybe case _ of
   VarStatus b -> Just b
   _ -> Nothing

classFor :: Cxt -> Var -> Maybe ClassEntry
classFor cxt c = case Map.lookup c cxt of
   Just (Class cls) -> Just cls
   _ -> Nothing

classOf :: Cxt -> Name -> Either String ClassEntry
classOf cxt c = case resolveName cxt c of
   Just (Class cls) -> pure cls
   _ -> throwError $ "Unknown dataclass: " <> dottedName c

resolveName :: Cxt -> Name -> Maybe Entry
resolveName cxt name = case NEL.fromList init of
   Nothing -> simpleEntry cxt x
   Just q -> case resolveName cxt q of
      Just (ModLoaded _ cxt') -> simpleEntry cxt' x
      _ -> Nothing
   where
   { init, last: x } = NEL.unsnoc name
   simpleEntry g y = case Map.lookup y g of
      Just e@(VarStatus true) -> Just e
      Just e@(ModLoaded _ _) -> Just e
      Just e@(Class _) -> Just e
      _ -> Nothing

extendCxt :: Cxt -> VarCxt -> Cxt
extendCxt cxt δ = Map.union (VarStatus <$> δ) cxt

fields :: ClassEntry -> List Var
fields cls = case cls.base of
   Nothing -> cls.fields
   Just b -> fields (definitely' (classFor cls.cxt b)) <> cls.fields

ancestors :: ClassEntry -> List Name
ancestors cls = cls.name : maybe Nil ancestors (cls.base >>= classFor cls.cxt)

-- ======================
-- boilerplate
-- ======================
derive instance Functor WfResult
derive instance Eq a => Eq (WfResult a)
derive instance Eq Entry

