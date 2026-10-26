module App.View.Util.Axes where

import Prelude

import App.Util (classes)
import App.View.Util.D3 (ElementType(..), create, rotate, selectAll, setAttrs, setStyles, translate, xAxis, yAxis)
import App.View.Util.D3 as D3
import App.View.Util.Scale (Interval)
import Bind ((↦))
import Data.Array (range)
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Int (ceil, floor, toNumber)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (toNullable)
import Types.Defs (cDefault, cRotated)
import Effect (Effect)
import Primitive (ToFrom, typeMismatch)
import Val (BaseVal(..))

data Orientation
   = Default
   | Rotated

data TickSpacing
   = AutoTicks
   | Count Int
   | Every Number

data LabelFormat
   = AutoFormat
   | Decimals Int

newtype AxisTicks = AxisTicks { spacing :: TickSpacing, format :: LabelFormat }

newtype Ticks = Ticks { x :: AxisTicks, y :: AxisTicks }

-- Tick values within domain, for spacing by a fixed step
tickValues :: TickSpacing -> Interval -> Maybe (Array Number)
tickValues (Every step) { min, max } = Just (if first > last then [] else range first last <#> toNumber >>> (_ * step))
   where
   first = ceil (min / step - tolerance)
   last = floor (max / step + tolerance)
   -- Round-off in quotient
   tolerance = 1e-9
tickValues _ _ = Nothing

-- Count hint for d3, given default
tickCount :: TickSpacing -> Number -> Number
tickCount (Count n) _ = toNumber n
tickCount _ default = default

decimalPlaces :: LabelFormat -> Maybe Int
decimalPlaces (Decimals places) = Just places
decimalPlaces AutoFormat = Nothing

-- ======================
-- boilerplate
-- ======================

derive instance Eq Orientation

-- Hefty amount of boilerplate just for a type isomorphic to Bool :-o
orientation :: forall a. ToFrom Orientation a
orientation =
   { pack: case _ of
        Default -> Obj cDefault Nil
        Rotated -> Obj cRotated Nil
   , unpack: case _ of
        Obj c Nil
           | c == cDefault -> Right Default
           | c == cRotated -> Right Rotated
        v -> Left (typeMismatch v "Orientation")
   }

create_xAxis :: forall a r. D3.Selection -> { x :: a -> Number | r } -> D3.Ticks -> Int -> Orientation -> Effect D3.Selection
create_xAxis parent' to { count, values, places } y orient = do
   x <- xAxis to count (toNullable values) (toNullable places) =<<
      (parent' # create G [ classes [ "x-axis" ], translate { x: 0, y } ])
   when (orient == Rotated) do
      labels <- x # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "start" ]
   pure x

create_yAxis :: forall a r. D3.Selection -> { y :: a -> Number | r } -> D3.Ticks -> Orientation -> Effect D3.Selection
create_yAxis parent' to { count, values, places } orient = do
   y <- yAxis to count (toNullable values) (toNullable places) =<<
      (parent' # create G [ classes [ "y-axis" ] ])
   when (orient == Rotated) do
      labels <- y # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "end" ]
   pure y
