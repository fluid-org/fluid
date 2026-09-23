module App.Util.Selector where

import Prelude hiding (absurd)

import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), SetSel, getPersistent, selStates)
import Bind (Name, Var)
import Data.List (List(..), (:))
import Data.List.NonEmpty (last)
import Data.Newtype (over)
import Data.Profunctor.Strong (first, second)
import Data.Tuple (fst) as T
import DataType (FieldIndex, FieldName, cCons, cJust, cNil, f_segments, f_z)
import Lattice (class Neg, 𝔹, neg)
import Partial.Unsafe (unsafePartial)
import Util (Endo, absurd, assert, error, unsafeUpdateAt, (!), (×))
import Util.Map (get, insert, update)
import Util.Set ((∈))
import Val (BaseVal(..), DictRep(..), Env, MatrixDim(..), MatrixRep(..), Val(..), matrixGet, matrixPut)

type SelSetter f g = Setter (f (SelStates 𝔹)) (g (SelStates 𝔹))

sel𝔹 :: forall f a. Functor f => SetSel (f (SelStates 𝔹)) -> f a -> f 𝔹
sel𝔹 sel template = getPersistent <$> ρ'
   where
   ρ' × _ = sel (const (selStates false false false) <$> template)

type Setter b a = SetSel a -> SetSel b

type ViewSetter f g = Endo g -> Endo f -- Only used in unexercised view setters
type ViewSelSetter a = a -> SelSetter Val Val

-- Both of these functions could be reimplemented with const instead of neg
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

just :: Setter (Val (SelStates 𝔹)) 𝔹
just = constr (last cJust)

type ConstrArg = Name -> FieldName -> SelSetter Val Val

barSegment :: Int -> Int -> SelSetter Val Val
barSegment i j =
   nthSegment j >>> dictVal f_segments >>> listElement i

nthSegment :: Int -> SelSetter Val Val
nthSegment n = dictVal f_z >>> listElement n

matrixElement :: Int -> Int -> SelSetter Val Val
matrixElement i j δv (Val α doc (Matrix r)) =
   first (\r' -> Val α doc $ Matrix $ matrixPut i j (const r') r) (δv (matrixGet i j r))
matrixElement _ _ _ _ = error absurd

listElement :: Int -> SelSetter Val Val
listElement n δv = unsafePartial $ case _ of
   Val α doc (Constr c (v : u : Nil)) | n == 0 && c == cCons ->
      first (\v' -> Val α doc (Constr c (v' : u : Nil))) (δv v)
   Val α doc (Constr c (v : u : Nil)) | c == cCons ->
      first (\u' -> Val α doc (Constr c (v : u' : Nil))) (listElement (n - 1) δv u)

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
   Val α doc (Matrix (MatrixRep (vss × MatrixDim (i × βi) × MatrixDim (j × βj)))) ->
      Val α doc (Matrix (MatrixRep (vss × MatrixDim (i × βi') × MatrixDim (j × βj')))) × s
      where
      βi' × _ = persist δα βi
      βj' × s = persist δα βj

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

listCell :: Int -> Setter (Val (SelStates 𝔹)) 𝔹
listCell n δα = unsafePartial $ case _ of
   Val α doc (Constr c Nil) | n == 0 && c == cNil ->
      first (\α' -> Val α' doc (Constr c Nil)) (persist δα α)
   Val α doc (Constr c (v : u : Nil)) | c == cCons ->
      if n == 0 then first (\α' -> Val α' doc (Constr c (v : u : Nil))) (persist δα α)
      else first (\u' -> Val α doc (Constr c (v : u' : Nil))) (listCell (n - 1) δα u)

composeSetSel :: forall a. SetSel a -> SetSel a -> SetSel a
composeSetSel f g = \x -> let x' × _ = f x in g x'

infixr 9 composeSetSel as >.>
