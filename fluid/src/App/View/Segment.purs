module App.View.Segment where

import Prelude

import App.Util (Attrs, Dimensions(..), Selectable, 𝕊(..), classes, colorShade, contents, getPersistent, getTransient, sel, selectionEventData')
import App.Util.Selector (ConstrArg, nthSegment)
import App.View.Util (class Viewable, Select, registerMouseListeners)
import App.View.Util.D3 (ElementType(..), bandwidth, colorScale, create, setAttrs)
import App.View.Util.D3 as D3
import Bind ((↦), (⟼))
import Data.Int (toNumber)
import Data.Newtype (class Newtype)
import Data.Tuple (uncurry)
import Effect (Effect)
import Util (Endo)

newtype Segment = Segment
   { y :: Selectable String -- overloading of y here and in SegmentContext needs fixing
   , z :: Selectable Number
   }

type Scales = { x :: String -> Number, y :: Endo Number }

type SegmentContext =
   { interior :: Dimensions Int
   , scales :: Scales
   , strokeWidth :: Int
   , x :: String
   , y :: Number -- accumulated z values of segments below me in stack
   , y_index :: Int
   }

instance Viewable Segment SegmentContext where
   isLeaf = const false

   createElement :: SegmentContext -> Segment -> D3.Selection -> Effect D3.Selection
   createElement { interior: Dimensions { height }, scales, strokeWidth, x, y } (Segment { z }) parent =
      parent
         # create Rect
              [ "x" ⟼ scales.x x
              , "y" ⟼ scales.y (contents z + y)
              , "height" ⟼ max (toNumber (height - strokeWidth / 2) - scales.y (contents z)) 0.0
              , "stroke-width" ⟼ strokeWidth
              , "width" ⟼ bandwidth scales.x
              , classes [ "bar" ]
              ]

   setSelection :: ConstrArg -> SegmentContext -> Segment -> Select -> D3.Selection -> Effect Unit
   setSelection arg { y_index } (Segment { z }) select segment = do
      segment # setAttrs attrs >>= registerMouseListeners (select <<< uncurry (\_ -> nthSegment arg y_index) <<< selectionEventData')
      where
      attrs :: Attrs
      attrs =
         [ "fill" ↦
              case persistent of
                 None -> col'
                 Secondary -> "url(#diagonalHatch-" <> show y_index <> ")"
                 Primary -> colorShade col' (-40)
         , "stroke-width" ↦ "1"
         , "stroke-dasharray" ↦ case transient of
              None -> "none"
              Secondary -> "1 2" -- "0.5 1"
              Primary -> "1 2" -- "0.5 1"
         , "stroke-linecap" ↦ "round"
         , "stroke" ↦
              if persistent /= None || transient /= None then colorShade col' (-70)
              else col'
         ]
         where
         t = sel z
         persistent = getPersistent t
         transient = getTransient t
         col' = indexCol y_index

indexCol :: Int -> String
indexCol = colorScale "schemeAccent"

-- ======================
-- boilerplate
-- ======================

derive instance Newtype Segment _
