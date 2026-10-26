module App.View.Util.D3 where

import Prelude

import App.Util (Attrs, Dimensions)
import App.View.Util.Scale (Interval)
import Bind (Bind, (↦), (⟼))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Newtype (unwrap)
import Data.Nullable (Nullable)
import Data.Show.Generic (genericShow)
import Data.String (toLower)
import Effect (Effect)
import Foreign.Object (Object, fromFoldable)
import Util (Endo)
import Web.Event.Event (EventType)
import Web.Event.EventTarget (EventListener)

type Margin =
   { top :: Int
   , right :: Int
   , bottom :: Int
   , left :: Int
   }

type Coord a =
   { x :: a
   , y :: a
   }

type Ticks =
   { count :: Number -- approximate, for d3 to choose round values
   , values :: Maybe (Array Number) -- exact positions, overriding count
   , places :: Maybe Int -- decimal places of labels, else JavaScript's default number to string conversion
   }

textWidth :: String -> String -> Int
textWidth class_ = textDimensions class_ >>> unwrap >>> _.width

textHeight :: String -> String -> Int
textHeight class_ = textDimensions class_ >>> unwrap >>> _.height

translate :: Coord Int -> Bind String
translate { x, y } = "transform" ↦ "translate(" <> show x <> ", " <> show y <> ")"

rotate :: Int -> Bind String
rotate n = "transform" ↦ "rotate(" <> show n <> ")"

rotate' :: forall a. (a -> Int) -> Bind (a -> String)
rotate' f = "transform" ↦ \a -> "rotate(" <> show (f a) <> ")"

-- Might be some PureScript library that could help here
data ElementType
   = Caption
   | Circle
   | Div
   | G
   | Line
   | Path
   | Rect
   | Span
   | SVG
   | Table
   | Text
   | TBody
   | TD
   | TH
   | THead
   | TR
   | Pattern

create :: ElementType -> Attrs -> Selection -> Effect Selection
create elementType as parent =
   fromFoldable as # createChild parent (show elementType)

setAttrs :: Attrs -> Selection -> Effect Selection
setAttrs as sel = fromFoldable as # attrs sel

setStyles :: Attrs -> Selection -> Effect Selection
setStyles as sel = fromFoldable as # styles sel

-- Intentially clunky name to differentiate from CSS :nth-child
nthChildOf :: String -> Int -> String
nthChildOf selector i = selector <> " > :nth-child(" <> show i <> ")"

scope :: String
scope = ":scope"

addHatchPattern :: Selection -> Int -> String -> Effect Unit
addHatchPattern parent' j col_j = do
   pattern <- parent' # create Pattern
      [ "id" ↦ "diagonalHatch-" <> show j
      , "patternUnits" ↦ "userSpaceOnUse"
      , "width" ⟼ 2
      , "height" ⟼ 2
      , "patternTransform" ↦ "rotate(45)"
      ]
   void $ pattern # create Rect
      [ "width" ⟼ 3.5, "height" ⟼ 3.5, "fill" ↦ col_j ]
   void $ pattern # create Line
      [ "x1" ⟼ 0
      , "y" ⟼ 0
      , "x2" ⟼ 0
      , "y2" ⟼ 3.5
      , "stroke" ↦ "rgba(255, 255, 255, 1)"
      , "stroke-width" ↦ "1"
      ]

-- Could feasibly rename to Element
foreign import data Selection :: Type

foreign import createChild :: Selection -> String -> Object String -> Effect Selection
foreign import createText :: Selection -> String -> Effect Selection
foreign import remove :: Selection -> Effect Unit
foreign import colorScale :: forall a. String -> a -> String
foreign import scaleLinear :: Interval -> Interval -> Endo Number
foreign import scaleBand :: Int -> Array String -> String -> Number
foreign import bandwidth :: (String -> Number) -> Number
-- Currently two different protocols for x and y axis; will subsume into something more general
foreign import xAxis :: forall a r. { x :: a -> Number | r } -> Number -> Nullable (Array Number) -> Nullable Int -> Selection -> Effect Selection
foreign import yAxis :: forall a r. { y :: a -> Number | r } -> Number -> Nullable (Array Number) -> Nullable Int -> Selection -> Effect Selection
foreign import numericXAxis :: Endo Number -> Selection -> Effect Selection
foreign import numericYAxis :: Endo Number -> Selection -> Effect Selection
foreign import isEmpty :: Selection -> Effect Boolean
foreign import dimensions :: Selection -> Effect (Dimensions Int)
foreign import textDimensions :: String -> String -> Dimensions Int
foreign import line :: Coord (Endo Number) -> Array (Coord Number) -> String
foreign import rootSelect :: String -> Effect Selection
foreign import select :: String -> Selection -> Effect Selection
foreign import selectAll :: String -> Selection -> Effect (Array Selection)
foreign import setText :: String -> Selection -> Effect Selection
foreign import attrs :: Selection -> Object String -> Effect Selection
foreign import styles :: Selection -> Object String -> Effect Selection
foreign import classed :: String -> Boolean -> Selection -> Effect Selection
foreign import setDatum :: forall a. a -> Selection -> Effect Selection
foreign import datum :: forall a. Selection -> Effect a
foreign import on :: EventType -> EventListener -> Selection -> Effect Selection

-- ======================
-- boilerplate
-- ======================

derive instance Generic ElementType _

instance Show ElementType
   where
   show = genericShow >>> toLower
