module App.View.Util.Scale where

import Prelude

import Data.Number (abs)

type Interval = { min :: Number, max :: Number }

data Scale
   = Auto
   | FromZero
   | Fixed Number Number
   | Padded Number

newtype Scales = Scales { x :: Scale, y :: Scale }

-- Axis domain, given extent of data
domain :: Scale -> Interval -> Interval
domain Auto extent = extent
domain FromZero extent = { min: min 0.0 extent.min, max: max 0.0 extent.max }
domain (Fixed min max) _ = { min, max }
-- Extent widened at both ends by fraction of its width; unit width if zero
domain (Padded fraction) { min, max } = { min: min - fraction * width, max: max + fraction * width }
   where
   width
      | max > min = max - min
      | min == 0.0 = 1.0
      | otherwise = abs min

-- ======================
-- boilerplate
-- ======================

derive instance Eq Scale
