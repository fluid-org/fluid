module App.Util.Selector where

import Prelude hiding (absurd)

import App.Util (SelState(..), SelStates(..), Selection, SelectionType(..), SetSel, getPersistent, selStates)
import Bind (Var)
import Data.List (List(..), updateAt, (!!), (:))
import Data.Maybe (fromJust)
import Data.Newtype (over)
import Data.Profunctor.Strong (first, second)
import Data.Tuple (fst) as T
import DataType (Ctr, cBarChart, cCons, cLineChart, cLinePlot, cMultiView, cNil, cPair, cParagraph, cScatterPlot, cJust, f_points, f_segments, f_stackedBars, f_z)
import Dict (Dict)
import Lattice (class Neg, 𝔹, neg)
import Partial.Unsafe (unsafePartial)
import Util (Endo, absurd, assert, definitely, error, (×))
import Util.Map (get, insert, update)
import Util.Set ((∈))
import Val (BaseVal(..), DictRep(..), Env, Val(..), matrixGet, matrixPut)

type SelSetter f g = Setter (f (SelStates 𝔹)) (g (SelStates 𝔹))
type IntermediateVals a = Dict (Val a)

sel𝔹 :: forall f a. Functor f => SetSel (f (SelStates 𝔹)) -> f a -> f 𝔹
sel𝔹 sel template = getPersistent <$> γ'
   where
   γ' × _ = sel (const (selStates false false false) <$> template)

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

fst :: SelSetter Val Val
fst = constrArg cPair 0

snd :: SelSetter Val Val
snd = constrArg cPair 1

just :: Setter (Val (SelStates 𝔹)) 𝔹
just = constr cJust

multiView :: SelSetter Val Val
multiView = constrArg cMultiView 0

multiViewEntry :: Int -> SelSetter Val Val
multiViewEntry n = listElement n >>> multiView

lineChart :: SelSetter Val Val
lineChart = constrArg cLineChart 0

linePoint :: Int -> SelSetter Val Val
linePoint i = listElement i >>> dictVal f_points >>> constrArg cLinePlot 0

barChart :: SelSetter Val Val
barChart = constrArg cBarChart 0

scatterPlot :: SelSetter Val Val
scatterPlot = constrArg cScatterPlot 0

scatterPoint :: Int -> Setter (Val (SelStates 𝔹)) (Val (SelStates 𝔹))
scatterPoint i = listElement i >>> dictVal f_points

barSegment :: Int -> Int -> SelSetter Val Val
barSegment i j =
   nthSegment j >>> dictVal f_segments >>> listElement i >>> dictVal f_stackedBars

nthSegment :: Int -> SelSetter Val Val
nthSegment n = dictVal f_z >>> listElement n

paragraph :: SelSetter Val Val
paragraph = constrArg cParagraph 0

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

constrArg :: Ctr -> Int -> SelSetter Val Val
constrArg c n δv = unsafePartial $ case _ of
   Val α doc (Constr c' us) | c == c' ->
      first (\u' -> Val α doc (Constr c' $ fromJust (updateAt n u' us)))
         $ definitely "constrArg out of bounds"
         $ δv <$> (us !! n)

constr :: Ctr -> Setter (Val (SelStates 𝔹)) 𝔹
constr c' δα = unsafePartial $ case _ of
   Val α doc (Constr c vs) | c == c' -> first (\α' -> Val α' doc (Constr c vs)) (persist δα α)

dict :: Setter (Val (SelStates 𝔹)) 𝔹
dict δα = unsafePartial $ case _ of
   Val α doc (Dictionary d) -> first (\α' -> Val α' doc (Dictionary d)) (persist δα α)

matrix :: Setter (Val (SelStates 𝔹)) 𝔹
matrix δα = unsafePartial $ case _ of
   Val α doc (Matrix r) -> first (\α' -> Val α' doc (Matrix r)) (persist δα α)

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
envVal x δv γ =
   assert (x ∈ γ) $ first (\v' -> update (const v') x γ) (δv (get x γ))

intermediateDoc :: String -> Setter (Dict (Val (SelStates 𝔹))) (Val (SelStates 𝔹))
intermediateDoc doc δv d =
   first (\v' -> update (const v') doc d) (δv (get doc d))

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
