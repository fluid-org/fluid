module Pattern where

import Prelude

import Bind (Bind, Name, Var)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Set (Set, empty, singleton, unions)
import Data.Show.Generic (genericShow)
import Data.Tuple (snd)
import Util.Set ((∪))

data Pattern
   = PInt Int
   | PFloat Number
   | PStr String
   | PVar Var
   | PWild
   | PConstr Name (List Pattern) (List (Bind Pattern))
   | PRecord (List (Bind Pattern))
   | PList (List Pattern)
   | PAs Pattern Var

class BV a where
   bv :: a -> Set Var

instance BV Pattern where
   bv (PInt _) = empty
   bv (PFloat _) = empty
   bv (PStr _) = empty
   bv (PVar x) = singleton x
   bv PWild = empty
   bv (PConstr _ ps xps) = unions (bv <$> ps) ∪ unions ((bv <<< snd) <$> xps)
   bv (PRecord xps) = unions ((bv <<< snd) <$> xps)
   bv (PList ps) = unions (bv <$> ps)
   bv (PAs p x) = bv p ∪ singleton x

-- ======================
-- boilerplate
-- ======================
derive instance Eq Pattern
derive instance Generic Pattern _
instance Show Pattern where
   show c = genericShow c

