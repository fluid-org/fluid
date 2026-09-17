module Pattern where

import Prelude

import Bind (Bind, Name, Var, varAnon)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Set (Set, empty, singleton, unions)
import Data.Show.Generic (genericShow)
import Data.Tuple (snd)
import Util.Set ((∪))

data Pattern
   = PVar Var
   | PConstr Name (List Pattern) (List (Bind Pattern))
   | PRecord (List (Bind Pattern))
   | PListEmpty
   | PListNonEmpty Pattern ListRestPattern

data ListRestPattern
   = PListVar Var -- currently unsupported in parser; only arise during desugaring
   | PListEnd
   | PListNext Pattern ListRestPattern

pVarAnon :: Pattern
pVarAnon = PVar varAnon

pListVarAnon :: ListRestPattern
pListVarAnon = PListVar varAnon

class BV a where
   bv :: a -> Set Var

instance BV Pattern where
   bv (PVar x) = singleton x
   bv (PConstr _ ps xps) = unions (bv <$> ps) ∪ unions ((bv <<< snd) <$> xps)
   bv (PRecord xps) = unions ((bv <<< snd) <$> xps)
   bv PListEmpty = empty
   bv (PListNonEmpty p lr) = bv p ∪ bv lr

instance BV ListRestPattern where
   bv (PListNext p lr) = bv p ∪ bv lr
   bv (PListVar x) = singleton x
   bv PListEnd = empty

-- ======================
-- boilerplate
-- ======================
derive instance Eq Pattern
derive instance Generic Pattern _
instance Show Pattern where
   show c = genericShow c

derive instance Eq ListRestPattern
derive instance Generic ListRestPattern _
instance Show ListRestPattern where
   show c = genericShow c
