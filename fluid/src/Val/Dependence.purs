module Val.Dependence where

import Prelude hiding (absurd)

import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable) as A
import Data.Foldable (foldMap, foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List ((!!), range, take) as L
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (fst, snd)
import DepGraph (bindings, construct, controlDep, dataDep, DepGraph, newVertex, paths, positions, Rel(..), Restructuring(..), reuse, Support(..), tupling, withCtrl, ι)
import Dict (Dict)
import Dict as D
import Lattice (class DepSemiring, Lineage(..), Raw, erase)
import Literal (Literal(..))
import Path (Path, Position, Step(..), followedBy, ε)
import Types.Defs (cRange)
import Util (type (×), Endo, MayFail, absurd, definitely', definitelyRight, error, singleton, (×))
import Util.Map (mapWithKey, toUnfoldable)
import Val (BaseVal(..), DepFun, DictRep(..), Env(..), GVal, Label(..), ValAt, Val(..), child, element, elementCount)

positionsIn :: ValAt -> Set Position
positionsIn (q × v) = Set.fromFoldable ((q `followedBy` _) <<< fst <$> positions (paths v))

-- Positions which determine length of the sequence at a position
lengthPositions :: ValAt -> Set Position
lengthPositions (q × Val _ (Obj c xvs)) | c == cRange =
   Set.fromFoldable (q : (xvs <#> \(x × _) -> q `followedBy` singleton (Field x)))
lengthPositions (q × _) = singleton q

childAt :: Step -> Endo ValAt
childAt step (p × v) = (p `followedBy` singleton step) × child step v

-- Elements of the list or tuple at a position
elementsAt :: ValAt -> List ValAt
elementsAt pv = (\i -> childAt (Element i) pv) <$> L.take n (L.range 0 n)
   where
   n = definitely' (elementCount (snd pv))

reuseAt :: forall s. Semiring s => ValAt -> GVal s
reuseAt (p × v) = v × reuse p

-- Add control dependence on given positions to every position outside a function value
deliver :: forall s. Set Position -> Endo (GVal s)
deliver ps (v × θ × r) = v × withCtrl ps θ × r

newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m ValAt
newValue (v × δ) = newVertex (Value v) δ <#> \a -> (a × ε) × v

-- Allocate vertex for environment independent of other vertices
newEnv :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Raw Env -> m (Dict ValAt)
newEnv γ@(Env ρ) = newVertex (Environment γ) (tupling (bindings (ρ <#> const (construct mempty Map.empty))))
   <#> \a -> bindingsAt (a × ε) γ

-- Each binding of environment at given position
bindingsAt :: Position -> Raw Env -> Dict ValAt
bindingsAt p (Env ρ) = mapWithKey (\x v -> (p `followedBy` singleton (Binding x)) × v) ρ

-- Apply function to compute the support of each result position. Every result position also depends on ps.
-- Result positions with empty support depend on ps'.
applyDepFun :: forall s. DepSemiring s => DepFun -> Set Position -> Set Position -> List ValAt -> MayFail (GVal s)
applyDepFun f ps ps' pvs = f (arg <$> pvs) <#> \v ->
   erase v × NoReuse ps × foldl addSupport mempty (positions (paths v))
   where
   arg :: ValAt -> Val (Lineage Position s)
   arg (q × v) = paths v <#> \(p × _) -> Lineage (zero × Map.singleton (q `followedBy` p) one)

   addSupport :: Rel (Set Position) s -> Path × Lineage Position s -> Rel (Set Position) s
   addSupport r (p × Lineage (_ × ws)) =
      r <> ι p (Rel (if Map.isEmpty ws then controlDep ps' else Support Set.empty ws) Map.empty)

-- Step to given element of sequence if that element is a child
elementStep :: Int -> Raw Val -> Maybe Step
elementStep i (Val _ (List _)) = Just (Element i)
elementStep i (Val _ (Tuple _)) = Just (Element i)
elementStep i (Val _ (Dictionary (DictRep d))) = Just (DictKey (fst (definitely' (toUnfoldable d L.!! i))))
elementStep _ _ = Nothing

elementAt :: forall s. DepSemiring s => Int -> ValAt -> GVal s
elementAt i pv = case elementStep i (snd pv) of
   Just step -> reuseAt (childAt step pv)
   Nothing -> definitelyRight (applyDepFun elementOf Set.empty Set.empty (singleton pv))
   where
   elementOf :: forall a. List (Val a) -> MayFail (Val a)
   elementOf (v : Nil) = pure (element i v)
   elementOf _ = error absurd

-- String or range as list of elements
explode :: forall s. DepSemiring s => ValAt -> GVal s
explode pv = sequenceOf List (foldMap dataDep (lengthPositions pv)) (flip elementAt pv <$> L.take n (L.range 0 n))
   where
   n = definitely' (elementCount (snd pv))

-- Sequence with root dependent on support
sequenceOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List (GVal s) -> GVal s
sequenceOf mk support vs =
   Val unit (mk (A.fromFoldable (fst <$> vs))) × construct support (Map.fromFoldable (mapWithIndex (\i (_ × δ) -> Element i × δ) vs))

-- Concatenate sequences; root depends on support and each sequence
concatOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List ValAt -> GVal s
concatOf mk support pvs = sequenceOf mk (support <> foldMap (fst >>> dataDep) pvs) $
   pvs >>= \pv@(p × _) -> deliver (singleton p) <<< reuseAt <$> elementsAt pv

-- Dictionary with root dependent on support
dictionary :: forall s. Semiring s => Support (Set Position) s -> List (GVal s × GVal s) -> GVal s
dictionary support kvs =
   Val unit (Dictionary (DictRep (D.fromFoldable (kvs <#> \((k × _) × v × _) -> key k × unit × v)))) ×
      construct support (Map.fromFoldable (kvs >>= \((k × δ) × _ × δ') -> (DictKey (key k) × δ) : (DictVal (key k) × δ') : Nil))
   where
   key :: Raw Val -> String
   key (Val _ (Lit (Str k))) = k
   key _ = error absurd
