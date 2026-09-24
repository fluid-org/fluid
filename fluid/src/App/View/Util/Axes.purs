module App.View.Util.Axes where

import Prelude

import App.Util (classes)
import App.View.Util.D3 (ElementType(..), create, rotate, selectAll, setAttrs, setStyles, translate, xAxis, yAxis)
import App.View.Util.D3 as D3
import Bind ((↦))
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.List (List(..))
import DataType (cDefault, cRotated)
import Effect (Effect)
import Primitive (ToFrom, typeMismatch)
import Val (BaseVal(..))

data Orientation
   = Default
   | Rotated

-- ======================
-- boilerplate
-- ======================

derive instance Eq Orientation

-- Hefty amount of boilerplate just for a type isomorphic to Bool :-o
orientation :: forall a. ToFrom Orientation a
orientation =
   { pack: case _ of
        Default -> Constr cDefault Nil
        Rotated -> Constr cRotated Nil
   , unpack: case _ of
        Constr c Nil
           | c == cDefault -> Right Default
           | c == cRotated -> Right Rotated
        v -> Left (typeMismatch v "Orientation")
   }

create_xAxis :: forall a r. D3.Selection -> { x :: a -> Number | r } -> NonEmptyArray a -> Int -> Orientation -> Effect D3.Selection
create_xAxis parent' to ticks y orient = do
   x <- xAxis to ticks =<<
      (parent' # create G [ classes [ "x-axis" ], translate { x: 0, y } ])
   when (orient == Rotated) do
      labels <- x # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "start" ]
   pure x

-- numTicks is a "hint" only
create_yAxis :: forall a r. D3.Selection -> { y :: a -> Number | r } -> Number -> Int -> Orientation -> Effect D3.Selection
create_yAxis parent' to nTicks decPlaces orient = do
   y <- yAxis to nTicks decPlaces =<<
      (parent' # create G [ classes [ "y-axis" ] ])
   when (orient == Rotated) do
      labels <- y # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "end" ]
   pure y
