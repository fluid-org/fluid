module App.View.Util.Scale where

import Prelude

import Util (error)

type Interval = { min :: Number, max :: Number }

data Scale
   = Auto
   | FromZero
   | Fixed Number Number
   | Padded Number

newtype Scales = Scales { x :: Scale, y :: Scale }

-- Axis domain, given extent of data; may have zero width, which D3 renders as one tick with every point at mid-axis
domain :: Scale -> Interval -> Interval
domain Auto extent = extent
domain FromZero extent = { min: min 0.0 extent.min, max: max 0.0 extent.max }
domain (Fixed min max) _ = { min, max }
domain (Padded margin) { min, max }
   | margin < 0.0 = error ("Padded has margin " <> show margin <> ", which is negative")
   | otherwise = { min: min - margin * width, max: max + margin * width }
        where
        width = max - min

-- ======================
-- boilerplate
-- ======================

derive instance Eq Scale
