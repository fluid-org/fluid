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
import DepGraph (bindings, construct, controlDep, dataDep, DepGraph, extend, newVertex, paths, positions, Rel(..), Restructuring(..), reuse, Support(..), tupling, withCtrl, ι)
import Dict (Dict)
import Dict as D
import Lattice (class DepSemiring, Lineage(..), Raw, erase)
import Literal (Literal(..))
import Path (Path, Position, Step(..), Vertex, followedBy, ε)
import Types.Defs (cRange)
import Util (type (×), Endo, MayFail, absurd, definitely', definitelyRight, error, singleton, (×))
import Util.Map (mapWithKey, toUnfoldable, (<+>))
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
elementsAt u = (\i -> childAt (Element i) u) <$> L.take n (L.range 0 n)
   where
   n = definitely' (elementCount (snd u))

reuseAt :: forall s. Semiring s => ValAt -> GVal s
reuseAt (p × v) = v × reuse p

-- Add control dependence on each of ps to every position outside a function value
deliver :: forall s. Set Position -> Endo (GVal s)
deliver ps (v × θ × r) = v × withCtrl ps θ × r

newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m ValAt
newValue (v × δ) = newVertex (Value v) δ <#> \a -> (a × ε) × v

-- Allocate fresh vertex for environment ρ; return each binding as reuse of its position
newEnv :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Dict (GVal s) -> m (Vertex × Dict (GVal s))
newEnv ρ = newVertex (Environment (Env (fst <$> ρ))) (tupling (bindings (snd <$> ρ))) <#> \a ->
   a × mapWithKey (\x (v × _) -> v × reuse (a × singleton (Binding x))) ρ

-- Allocate fresh vertex for extension by ρ' of environment ρ at position p
newExtendEnv
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Semiring s
   => Dict (Raw Val)
   -> Position
   -> Dict (GVal s)
   -> m (Dict (Raw Val) × Vertex)
newExtendEnv ρ p ρ' = (ρ'' × _) <$> newVertex (Environment (Env ρ'')) (extend p (snd <$> ρ'))
   where
   ρ'' = ρ <+> (fst <$> ρ')

-- Apply f to the values at rs to compute the support of each result position. Every result position also
-- depends on ps. Result positions with empty support depend on ps'.
applyDepFun :: forall s. DepSemiring s => DepFun -> Set Position -> Set Position -> List ValAt -> MayFail (GVal s)
applyDepFun f ps ps' rs = f (arg <$> rs) <#> \v ->
   erase v × NoReuse ps × foldl addSupport mempty (positions (paths v))
   where
   arg :: ValAt -> Val (Lineage Position s)
   arg (q × v) = paths v <#> \(p × _) -> Lineage (zero × Map.singleton (q `followedBy` p) one)

   addSupport :: Rel (Set Position) s -> Path × Lineage Position s -> Rel (Set Position) s
   addSupport r (p × Lineage (_ × ws)) =
      r <> ι p (Rel (if Map.isEmpty ws then controlDep ps' else Support Set.empty ws) Map.empty)

-- Step to element i of sequence if that element is a child
elementStep :: Int -> Raw Val -> Maybe Step
elementStep i (Val _ (List _)) = Just (Element i)
elementStep i (Val _ (Tuple _)) = Just (Element i)
elementStep i (Val _ (Dictionary (DictRep d))) = Just (DictKey (fst (definitely' (toUnfoldable d L.!! i))))
elementStep _ _ = Nothing

elementAt :: forall s. DepSemiring s => Int -> ValAt -> GVal s
elementAt i r = case elementStep i (snd r) of
   Just step -> reuseAt (childAt step r)
   Nothing -> definitelyRight (applyDepFun elementOf Set.empty Set.empty (singleton r))
   where
   elementOf :: forall a. List (Val a) -> MayFail (Val a)
   elementOf (v : Nil) = pure (element i v)
   elementOf _ = error absurd

-- String or range at position r as list of elements
explode :: forall s. DepSemiring s => ValAt -> GVal s
explode r = sequenceOf List (foldMap dataDep (lengthPositions r)) (flip elementAt r <$> L.take n (L.range 0 n))
   where
   n = definitely' (elementCount (snd r))

-- Sequence of vs with root dependent on support
sequenceOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List (GVal s) -> GVal s
sequenceOf mk support vs =
   Val unit (mk (A.fromFoldable (fst <$> vs))) × construct support (Map.fromFoldable (mapWithIndex (\i (_ × δ) -> Element i × δ) vs))

-- Concatenate sequences at rs; root depends on support and each sequence
concatOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List ValAt -> GVal s
concatOf mk support rs = sequenceOf mk (support <> foldMap (fst >>> dataDep) rs) $
   rs >>= \r -> deliver (singleton (fst r)) <<< reuseAt <$> elementsAt r

-- Dictionary of entries kvs with root dependent on support
dictionary :: forall s. Semiring s => Support (Set Position) s -> List (GVal s × GVal s) -> GVal s
dictionary support kvs =
   Val unit (Dictionary (DictRep (D.fromFoldable (kvs <#> \((k × _) × v × _) -> key k × unit × v)))) ×
      construct support (Map.fromFoldable (kvs >>= \((k × δ) × _ × δ') -> (DictKey (key k) × δ) : (DictVal (key k) × δ') : Nil))
   where
   key :: Raw Val -> String
   key (Val _ (Lit (Str k))) = k
   key _ = error absurd
