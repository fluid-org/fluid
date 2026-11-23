module Val.Dependence where

import Prelude hiding (absurd)

import Control.Monad.State (class MonadState)
import Data.Array (fromFoldable) as A
import Data.Foldable (foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List ((!!), range, take) as L
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (fst, snd)
import DepGraph (Dependence, DepGraph, Rel(..), Restructuring(..), Support(..), bindings, construct, newVertex, paths, positions, reuse, tupling, withCtrl, ι)
import Dict (Dict)
import Dict as D
import Lattice (class DepSemiring, Lineage(..), Raw, erase)
import Literal (Literal(..))
import Path (Path, Step(..), Vertex, sourceAt, sourceRoot)
import Types.Defs (cRange)
import Util (type (×), Endo, MayFail, absurd, definitely', definitelyRight, error, orThrow, singleton, (×))
import Util.Map (mapWithKey, toUnfoldable)
import Val (BaseVal(..), DepOp, DictRep(..), Env(..), GVal, Label(..), Position, Val(..), child, element, elementCount)

-- Every position within the value at a position
positionsIn :: Position -> Set Path
positionsIn (q × v) = Set.fromFoldable ((q <> _) <<< fst <$> positions (paths v))

-- Positions which determine length of sequence at a position; for a range, its root with start and stop
lengthPositions :: Position -> Set Path
lengthPositions (q × Val _ (Obj c xvs)) | c == cRange = Set.fromFoldable (q : (xvs <#> \(x × _) -> q <> singleton (Field x)))
lengthPositions (q × _) = singleton q

-- Child at step of the value at a position
childAt :: Step -> Endo Position
childAt step (p × v) = (p <> singleton step) × child step v

-- Elements of the list or tuple at a position
elementsAt :: Position -> List Position
elementsAt u = (\i -> childAt (Element i) u) <$> L.take n (L.range 0 n)
   where
   n = definitely' (elementCount (snd u))

-- Value at a position, as a value which reuses that position
reuseAt :: forall s. Semiring s => Position -> GVal s
reuseAt (p × v) = v × reuse p

-- Add control dependence on each of ps to every position outside a function value
deliver :: forall s. Set Path -> Endo (GVal s)
deliver ps (v × θ × r) = v × withCtrl ps θ × r

-- Allocate vertex for given value; return root position with raw value
newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m Position
newValue (v × δ) = newVertex (Value v) δ <#> \a -> sourceRoot a × v

-- Position of the environment at inputs vertex b
envAt :: Vertex -> Path
envAt b = sourceAt b (singleton InputsEnv)

-- Control position at inputs vertex b
ctlAt :: Vertex -> Path
ctlAt b = sourceAt b (singleton InputsCtl)

-- Allocate inputs vertex for environment ρ with dependence δ; control position has dependence δ'
newInputs
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Semiring s
   => Dict (Raw Val)
   -> Dependence (Set Path) s
   -> Dependence (Set Path) s
   -> m Vertex
newInputs ρ δ δ' = newVertex (Inputs unit (Env ρ)) (tupling (Map.fromFoldable [ InputsEnv × δ, InputsCtl × δ' ]))

-- Allocate vertex for bindings ρ; return each binding as reuse of its position
newBindings :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Dict (GVal s) -> m (Dict (GVal s))
newBindings ρ = newVertex (Bindings (Env (fst <$> ρ))) (tupling (bindings (snd <$> ρ))) <#> \a ->
   mapWithKey (\x (v × _) -> v × reuse (sourceAt a (singleton (Binding x)))) ρ

-- Result of f at the values at rs, if any; dependence is the derivative of f, plus control dependence on ctl
derivative
   :: forall s
    . DepSemiring s
   => (forall a. DepSemiring a => List (Val a) -> MayFail (Val a))
   -> Set Path
   -> List Position
   -> MayFail (GVal s)
derivative f ctl rs = f (arg <$> rs) <#> \v ->
   erase v × NoReuse ctl × foldl row mempty (positions (paths v))
   where
   arg :: Position -> Val (Lineage Path s)
   arg (q × v) = paths v <#> \(p × _) -> Lineage (zero × Map.singleton (q <> p) one)

   row :: Rel (Set Path) s -> Path × Lineage Path s -> Rel (Set Path) s
   row r (p × Lineage (_ × ws))
      | Map.isEmpty ws = r
      | otherwise = r <> ι p (Rel (Support Set.empty ws) Map.empty)

-- Step to element i of sequence if that element is a child
elementStep :: Int -> Raw Val -> Maybe Step
elementStep i (Val _ (List _)) = Just (Element i)
elementStep i (Val _ (Tuple _)) = Just (Element i)
elementStep i (Val _ (Dictionary (DictRep d))) = Just (DictKey (fst (definitely' (toUnfoldable d L.!! i))))
elementStep _ _ = Nothing

-- Element i computed from the sequence at a position
computedElement :: forall s. DepSemiring s => Int -> Position -> GVal s
computedElement i r = definitelyRight (derivative elementOf Set.empty (singleton r))
   where
   elementOf :: forall a. List (Val a) -> MayFail (Val a)
   elementOf (v : Nil) = pure (element i v)
   elementOf _ = error absurd

-- Element i of the sequence at a position
elementAt :: forall s. DepSemiring s => Int -> Position -> GVal s
elementAt i r = case elementStep i (snd r) of
   Just step -> reuseAt (childAt step r)
   Nothing -> computedElement i r

-- List or tuple of vs, as mk determines; root depends on support
sequenceOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Path) s -> List (GVal s) -> GVal s
sequenceOf mk support vs =
   Val unit (mk (A.fromFoldable (fst <$> vs))) × construct support (Map.fromFoldable (mapWithIndex (\i (_ × δ) -> Element i × δ) vs))

-- Dictionary with the given entries; root depends on support
dictionary :: forall s. Semiring s => Support (Set Path) s -> List (GVal s × GVal s) -> GVal s
dictionary support kvs =
   Val unit (Dictionary (DictRep (D.fromFoldable (kvs <#> \((k × _) × v × _) -> key k × unit × v)))) ×
      construct support (Map.fromFoldable (kvs >>= \((k × δ) × _ × δ') -> (DictKey (key k) × δ) : (DictVal (key k) × δ') : Nil))
   where
   key :: Raw Val -> String
   key (Val _ (Lit (Str k))) = k
   key _ = error absurd

-- Foreign function with derivative given by f; application of f may fail
fromRel :: (forall a. DepSemiring a => List (Val a) -> MayFail (Val a)) -> DepOp
fromRel f _ ctl rs = orThrow (derivative f (singleton ctl) rs)
