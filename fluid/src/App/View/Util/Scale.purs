module App.View.Util.Scale where

import Prelude

type Interval = { min :: Number, max :: Number }

data Scale
   = Auto
   | FromZero
   | Fixed Number Number

newtype Scales = Scales { x :: Scale, y :: Scale }

-- Axis domain, given extent of data
domain :: Scale -> Interval -> Interval
domain Auto extent = extent
domain FromZero extent = { min: min 0.0 extent.min, max: max 0.0 extent.max }
domain (Fixed min max) _ = { min, max }

-- ======================
-- boilerplate
-- ======================

derive instance Eq Scale
