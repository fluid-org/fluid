module Val.Dependence where

import Prelude hiding (absurd)

import Bind (Var)
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
import Path (Path, Position, Step(..), followedBy, ε)
import Types.Defs (cRange)
import Util (type (×), Endo, MayFail, absurd, definitely', definitelyRight, error, singleton, (×))
import Util.Map (get, mapWithKey, toUnfoldable, (<+>))
import Val (BaseVal(..), DepFun, DictRep(..), Env(..), EnvAt, GVal, Label(..), ValAt, Val(..), child, element, elementCount)

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

-- Add control dependence on each of ps to every position outside a function value
deliver :: forall s. Set Position -> Endo (GVal s)
deliver ps (v × θ × r) = v × withCtrl ps θ × r

newValue :: forall m s. MonadState (DepGraph Label s) m => GVal s -> m ValAt
newValue (v × δ) = newVertex (Value v) δ <#> \a -> (a × ε) × v

-- Allocate fresh vertex for bindings ρ
newEnv :: forall m s. MonadState (DepGraph Label s) m => Semiring s => Dict (GVal s) -> m EnvAt
newEnv ρ = newVertex (Environment ρ') (tupling (bindings (snd <$> ρ))) <#> \a -> (a × ε) × ρ'
   where
   ρ' = Env (fst <$> ρ)

-- Extend environment ρ at position p with bindings ρ' at fresh vertex
newExtendEnv :: forall m s. MonadState (DepGraph Label s) m => Semiring s => EnvAt -> Dict (GVal s) -> m EnvAt
newExtendEnv (p × Env ρ) ρ' = newVertex (Environment ρ'') (extend p (snd <$> ρ')) <#> \a -> (a × ε) × ρ''
   where
   ρ'' = Env (ρ <+> (fst <$> ρ'))

-- Binding of x in the environment at a position
bindingAt :: Var -> EnvAt -> ValAt
bindingAt x (p × Env ρ) = (p `followedBy` singleton (Binding x)) × get x ρ

-- Each binding of the environment at a position, as a value which reuses the position of that binding
bindingsAt :: forall s. Semiring s => EnvAt -> Dict (GVal s)
bindingsAt pρ@(_ × Env ρ) = mapWithKey (\x _ -> reuseAt (bindingAt x pρ)) ρ

-- Apply f to pvs to compute the support of each result position. Every result position also
-- depends on ps. Result positions with empty support depend on ps'.
applyDepFun :: forall s. DepSemiring s => DepFun -> Set Position -> Set Position -> List ValAt -> MayFail (GVal s)
applyDepFun f ps ps' pvs = f (arg <$> pvs) <#> \v ->
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
elementAt i pv = case elementStep i (snd pv) of
   Just step -> reuseAt (childAt step pv)
   Nothing -> definitelyRight (applyDepFun elementOf Set.empty Set.empty (singleton pv))
   where
   elementOf :: forall a. List (Val a) -> MayFail (Val a)
   elementOf (v : Nil) = pure (element i v)
   elementOf _ = error absurd

-- String or range pv as list of elements
explode :: forall s. DepSemiring s => ValAt -> GVal s
explode pv = sequenceOf List (foldMap dataDep (lengthPositions pv)) (flip elementAt pv <$> L.take n (L.range 0 n))
   where
   n = definitely' (elementCount (snd pv))

-- Sequence of vs with root dependent on support
sequenceOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List (GVal s) -> GVal s
sequenceOf mk support vs =
   Val unit (mk (A.fromFoldable (fst <$> vs))) × construct support (Map.fromFoldable (mapWithIndex (\i (_ × δ) -> Element i × δ) vs))

-- Concatenate sequences pvs; root depends on support and each sequence
concatOf :: forall s. Semiring s => (Array (Raw Val) -> Raw BaseVal) -> Support (Set Position) s -> List ValAt -> GVal s
concatOf mk support pvs = sequenceOf mk (support <> foldMap (fst >>> dataDep) pvs) $
   pvs >>= \pv -> deliver (singleton (fst pv)) <<< reuseAt <$> elementsAt pv

-- Dictionary of entries kvs with root dependent on support
dictionary :: forall s. Semiring s => Support (Set Position) s -> List (GVal s × GVal s) -> GVal s
dictionary support kvs =
   Val unit (Dictionary (DictRep (D.fromFoldable (kvs <#> \((k × _) × v × _) -> key k × unit × v)))) ×
      construct support (Map.fromFoldable (kvs >>= \((k × δ) × _ × δ') -> (DictKey (key k) × δ) : (DictVal (key k) × δ') : Nil))
   where
   key :: Raw Val -> String
   key (Val _ (Lit (Str k))) = k
   key _ = error absurd
