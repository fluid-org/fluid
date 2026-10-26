module App.View.ScatterPlot where

import Prelude

import App.Util (Selectable, classes, contents, isPrimary, isSecondary, selClasses, selClassesFor, selectionEventData')
import App.Util.Selector (ObjArg, ViewSelSetter, listElement)
import App.View.Util (class Viewable, registerMouseListeners)
import App.View.Util.Axes (AxisLabels(..))
import App.View.Util.D3 (ElementType(..), create, numericXAxis, numericYAxis, scaleLinear, setText, translate)
import App.View.Util.D3 as D3
import App.View.Util.Point (Point(..))
import Bind ((↦), (⟼))

import Types.Defs (cScatterPlot, f_points)
import Data.Array (length, range)
import Data.Foldable (maximum, minimum)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int (toNumber)
import Data.Maybe (fromMaybe)
import Data.Number (ceil)
import Data.Tuple (snd, uncurry)
import Effect (Effect, foreachE)
import Foreign.Object (fromFoldable)
import Lattice ((∨))
import Util (Endo, type (×), (!))

newtype ScatterPlot = ScatterPlot
   { caption :: Selectable String
   , points :: Array (Point Number)
   , labels :: AxisLabels
   }

type Scales = { x :: Endo Number, y :: Endo Number }

renderAxes :: Scales -> Int -> D3.Selection -> Effect Unit
renderAxes scales height rootElement = do
   void $ numericXAxis scales.x =<< (rootElement # create G [ translate { x: 0, y: height } ])
   void $ numericYAxis scales.y =<< (rootElement # create G [])

instance Viewable ScatterPlot Unit where
   isLeaf = const false

   createElement _ (ScatterPlot { caption, points, labels: AxisLabels labels }) parent = do
      let
         vals = points <#> \(Point { x, y }) -> { x: contents x, y: contents y }
         xMax = ceil (fromMaybe 0.0 (maximum (vals <#> _.x)))
         xMin = ceil (fromMaybe 0.0 (minimum (vals <#> _.x)))
         yMax = ceil (fromMaybe 0.0 (maximum (vals <#> _.y)))
         yMin = ceil (fromMaybe 0.0 (minimum (vals <#> _.y)))
         margin = { top: 20, right: 20, bottom: 40, left: 50 }
         maxWidth = 280
         maxHeight = 200
         width = maxWidth - margin.left - margin.right
         height = maxHeight - margin.top - margin.bottom

      svg <- parent # create SVG
         [ "width" ⟼ maxWidth + margin.left + margin.right
         , "height" ⟼ maxHeight + margin.top
         , classes [ "center" ]
         ]
      rootElement <- svg # create G [ translate { x: margin.left, y: margin.top } ]

      let
         scales =
            { x: scaleLinear { min: min 0.0 xMin, max: xMax } { min: 0.0, max: toNumber width }
            , y: scaleLinear { min: min 0.0 yMin, max: yMax } { min: toNumber height, max: 0.0 }
            }
      renderAxes scales height rootElement

      void $ rootElement
         # create Text
              [ "x" ⟼ width
              , "y" ⟼ height + 25
              , "style" ↦ "text-anchor: end; font-size: 10px"
              ]
         >>= setText labels.x
      void $ rootElement
         # create Text
              [ "transform" ↦ "rotate(-90)"
              , "x" ⟼ negate margin.top
              , "y" ⟼ negate margin.left + 20
              , "style" ↦ "text-anchor: end; font-size: 10px"
              ]
         >>= setText labels.y

      pointsGrp <- rootElement # create G []
      forWithIndex_ (range 0 (length points - 1)) \i _ -> do
         let
            Point { x, y } = points ! i
            cx = scales.x (contents x)
            cy = scales.y (contents y)
         circle <- pointsGrp # create Circle
            [ classes [ "scatterplot-point" ]
            , "cx" ⟼ cx
            , "cy" ⟼ cy
            , "stroke-width" ↦ "0.5"
            ]
         void $ circle # D3.setDatum { i }

      void $ rootElement
         # create Text
              [ "x" ⟼ toNumber width / 2.0
              , "y" ⟼ height + 40
              , classes [ "title-text" ]
              , "dominant-baseline" ↦ "bottom"
              , "text-anchor" ↦ "middle"
              ]
         >>= setText (contents caption)

      pure rootElement

   setSelection arg _ (ScatterPlot { points }) select rootElement = do
      pointEls <- D3.selectAll ".scatterplot-point" rootElement
      foreachE pointEls \pointEl -> do
         idx :: PointIndex <- D3.datum pointEl
         let
            Point { x, y } = points ! idx.i
            sel = snd x ∨ snd y
         void $ D3.classed selClasses false pointEl
         void $ D3.classed (selClassesFor sel) true pointEl
         void $ D3.attrs pointEl (fromFoldable (pointAttrs points idx))
         registerMouseListeners (select <<< uncurry (scatterPlotPoint arg) <<< selectionEventData') pointEl

scatterPlotPoint :: ObjArg -> ViewSelSetter PointIndex
scatterPlotPoint arg { i } = listElement i >>> arg cScatterPlot f_points

pointAttrs :: Array (Point Number) -> PointIndex -> Array (String × String)
pointAttrs points { i } =
   [ "r" ⟼ toNumber pointSmallRadius * if isPrimary sel then 1.6 else if isSecondary sel then 1.25 else 1.0 ]
   where
   Point { x, y } = points ! i
   sel = snd x ∨ snd y
   pointSmallRadius = 2

type PointIndex = { i :: Int }
