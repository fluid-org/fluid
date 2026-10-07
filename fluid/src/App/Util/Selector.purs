module App.Util.Selector where

import Prelude hiding (absurd)

import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), SetSel, getPersistent, selStates)
import Bind (Name, Var)
import Data.List.NonEmpty (last)
import Data.Newtype (over)
import Data.Profunctor.Strong (first, second)
import Data.Tuple (fst) as T
import DataType (FieldIndex, FieldName, cSegment, cStackedBar, f_segments, f_z)
import Lattice (class Neg, 𝔹, neg)
import Partial.Unsafe (unsafePartial)
import Util (Endo, absurd, assert, error, unsafeUpdateAt, (!), (×))
import Util.Map (get, insert, update)
import Util.Set ((∈))
import Val (BaseVal(..), DictRep(..), Env, MatrixRep(..), Val(..), matrixGet, matrixPut)

type SelSetter f g = Setter (f (SelStates 𝔹)) (g (SelStates 𝔹))

sel𝔹 :: forall f a. Functor f => SetSel (f (SelStates 𝔹)) -> f a -> f 𝔹
sel𝔹 sel template = getPersistent <$> ρ'
   where
   ρ' × _ = sel (const (selStates false false false) <$> template)

type Setter b a = SetSel a -> SetSel b

type ViewSetter f g = Endo g -> Endo f -- Only used in unexercised view setters
type ViewSelSetter a = a -> SelSetter Val Val

select :: forall f a. Neg a => Functor f => SetSel (f (SelStates a))
select b = (setSel <$> b) × Persistent
   where
   setSel :: Endo (SelStates a)
   setSel (SelStates Inert) = SelStates Inert
   setSel (SelStates (Reactive sel')) = SelStates (Reactive (sel' { persistent = neg sel'.persistent }))

select' :: forall a. Neg a => SetSel a
select' x = neg x × Persistent

persist :: forall a. Setter (SelStates a) a
persist δα = \v -> (over SelStates ((<$>) mapδ) v) × Persistent
   where
   mapδ :: Endo (Selection a)
   mapδ s = s { persistent = (T.fst <<< δα) s.persistent }

type ConstrArg = Name -> FieldName -> SelSetter Val Val

barSegment :: ConstrArg -> Int -> Int -> SelSetter Val Val
barSegment arg i j =
   nthSegment arg j >>> arg cStackedBar f_segments >>> listElement i

nthSegment :: ConstrArg -> Int -> SelSetter Val Val
nthSegment arg n = arg cSegment f_z >>> listElement n

matrixElement :: Int -> Int -> SelSetter Val Val
matrixElement i j δv (Val α doc (Matrix r)) =
   first (\r' -> Val α doc $ Matrix $ matrixPut i j (const r') r) (δv (matrixGet i j r))
matrixElement _ _ _ _ = error absurd

listElement :: Int -> SelSetter Val Val
listElement n δv = unsafePartial $ case _ of
   Val α doc (List vs) -> first (\v' -> Val α doc (List (unsafeUpdateAt n v' vs))) (δv (vs ! n))

tupleElement :: Int -> SelSetter Val Val
tupleElement n δv = unsafePartial $ case _ of
   Val α doc (Tuple vs) -> first (\v' -> Val α doc (Tuple (unsafeUpdateAt n v' vs))) (δv (vs ! n))

eachElement :: SelSetter Val Val
eachElement δv = unsafePartial $ case _ of
   Val α doc (List vs) -> Val α doc (List (T.fst <<< δv <$> vs)) × Persistent

none :: forall a. SetSel a
none = (_ × Persistent)

constrArg :: FieldIndex -> ConstrArg
constrArg fieldIndex c f δv = unsafePartial $ case _ of
   Val α doc (Constr c' us) | last c == last c' ->
      first (\u' -> Val α doc (Constr c' $ unsafeUpdateAt n u' us)) (δv (us ! n))
   where
   n = fieldIndex c f

constr :: Var -> Setter (Val (SelStates 𝔹)) 𝔹
constr c δα = unsafePartial $ case _ of
   Val α doc (Constr c' vs) | c == last c' -> first (\α' -> Val α' doc (Constr c' vs)) (persist δα α)

dict :: Setter (Val (SelStates 𝔹)) 𝔹
dict δα = unsafePartial $ case _ of
   Val α doc (Dictionary d) -> first (\α' -> Val α' doc (Dictionary d)) (persist δα α)

matrix :: Setter (Val (SelStates 𝔹)) 𝔹
matrix δα = unsafePartial $ case _ of
   Val α doc (Matrix r) -> first (\α' -> Val α' doc (Matrix r)) (persist δα α)

matrixDims :: Setter (Val (SelStates 𝔹)) 𝔹
matrixDims δα = unsafePartial $ case _ of
   Val α doc (Matrix (MatrixRep (vss × i × j))) ->
      Val α doc (Matrix (MatrixRep (vss × i' × j'))) × s
      where
      i' × _ = topα δα i
      j' × s = topα δα j

-- Flip only the outer Val annotation, regardless of payload (closure, etc.).
topα :: Setter (Val (SelStates 𝔹)) 𝔹
topα δα (Val α doc baseVal) = first (\α' -> Val α' doc baseVal) (persist δα α)

dictKey :: String -> Setter (Val (SelStates 𝔹)) 𝔹
dictKey s δα = unsafePartial $ case _ of
   Val α doc (Dictionary (DictRep d)) ->
      first (\β' -> Val α doc $ Dictionary $ DictRep $ insert s (β' × v) d) (persist δα β)
      where
      β × v = get s d

dictVal :: String -> SelSetter Val Val
dictVal s δv = unsafePartial $ case _ of
   Val α doc (Dictionary (DictRep d)) ->
      first (\v' -> Val α doc $ Dictionary $ DictRep $ update (second (const v')) s d) (δv v)
      where
      _ × v = get s d

envVal :: Var -> Setter (Env (SelStates 𝔹)) (Val (SelStates 𝔹))
envVal x δv ρ =
   assert (x ∈ ρ) $ first (\v' -> update (const v') x ρ) (δv (get x ρ))

list :: Setter (Val (SelStates 𝔹)) 𝔹
list δα = unsafePartial $ case _ of
   Val α doc (List vs) -> first (\α' -> Val α' doc (List vs)) (persist δα α)

composeSetSel :: forall a. SetSel a -> SetSel a -> SetSel a
composeSetSel f g = \x -> let x' × _ = f x in g x'

infixr 9 composeSetSel as >.>
