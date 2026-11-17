module Cxt where

import Prelude hiding (absurd)

import Bind (Name, Var, dottedName)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Data.List.NonEmpty (unsnoc)
import Data.List.NonEmpty as NEL
import Data.List (List)
import Data.Map (Map)
import Data.Map (unionWith) as M
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), maybe)
import Types (Scheme(..), Type, fv) as T
import Util (type (+), absurd, error, quoted)
import Util.Map (intersectionWith, lookup)
import Util.Set ((∪))

data CxtEntry
   = Unbound -- declared later in scope
   | Declared T.Type -- definitely unassigned
   | PossiblyUnassigned (T.Type + T.Scheme)
   | Assigned T.Type
   | TypeScheme T.Scheme
   | Type Name -- class, by fully-qualified name
   | Mod Name
   | ModChecked Name Cxt
   | PredefName
   | TypeVar -- type parameter
   | TypeAlias (List Var) T.Type

type Cxt = Map Var CxtEntry

generalise :: T.Type -> CxtEntry
generalise τ = maybe (Assigned τ) (TypeScheme <<< flip T.Forall τ) (NEL.fromFoldable (T.fv τ))

data WfResult = Returns | Assigns Cxt

class Extend a where
   extend :: a -> a -> a

instance Extend CxtEntry where
   extend (ModChecked q cxt) (ModChecked q' cxt') | q == q' = ModChecked q (cxt `extend` cxt')
   extend (Mod q) θ'@(ModChecked q' _) | q == q' = θ'
   extend θ@(ModChecked q _) (Mod q') | q == q' = θ
   extend _ θ' = θ'

instance (Ord k, Extend a) => Extend (Map k a) where
   extend = M.unionWith extend

class Override a where
   override :: a -> a -> a

instance Override CxtEntry where
   override _ θ' = θ'

instance (Ord k, Override a) => Override (Map k a) where
   override = M.unionWith override

instance Override WfResult where
   override _ Returns = Returns
   override Returns _ = Returns
   override (Assigns cxt) (Assigns cxt') = Assigns (cxt `override` cxt')

class Merge a where
   merge :: a -> a -> a

instance Merge CxtEntry where
   merge θ θ' = if θ == θ' then θ else possiblyUnassigned θ

instance Merge (Map Var CxtEntry) where
   merge cxt cxt' = intersectionWith merge cxt cxt' ∪ (possiblyUnassigned <$> (cxt ∪ cxt'))

possiblyUnassigned :: CxtEntry -> CxtEntry
possiblyUnassigned (Declared τ) = PossiblyUnassigned (Left τ)
possiblyUnassigned (PossiblyUnassigned π) = PossiblyUnassigned π
possiblyUnassigned (Assigned τ) = PossiblyUnassigned (Left τ)
possiblyUnassigned (TypeScheme π) = PossiblyUnassigned (Right π)
possiblyUnassigned _ = error absurd

instance Merge WfResult where
   merge Returns r = r
   merge r Returns = r
   merge (Assigns cxt) (Assigns cxt') = Assigns (cxt `merge` cxt')

classOf :: forall m. MonadThrow String m => Cxt -> Name -> m Name
classOf cxt c = case resolveName cxt c of
   Just (Type c') -> pure c'
   _ -> throwError $ "Unknown dataclass: " <> quoted (dottedName c)

resolveName :: Cxt -> Name -> Maybe CxtEntry
resolveName cxt name = case NEL.fromList init of
   Nothing -> simpleEntry cxt x
   Just q -> case resolveName cxt q of
      Just (ModChecked _ cxt') -> simpleEntry cxt' x
      _ -> Nothing
   where
   { init, last: x } = unsnoc name
   simpleEntry g y = case lookup y g of
      Just e@(Assigned _) -> Just e
      Just e@(TypeScheme _) -> Just e
      Just e@(ModChecked _ _) -> Just e
      Just e@(Type _) -> Just e
      Just e@TypeVar -> Just e
      Just e@(TypeAlias _ _) -> Just e
      _ -> Nothing

-- ======================
-- boilerplate
-- ======================
derive instance Eq WfResult
derive instance Eq CxtEntry
