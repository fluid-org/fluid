module App.View.LineChart where

import Prelude hiding (absurd)

import App.Util (Attrs, Dimensions(..), SelStates, Selectable, 𝕊, classes, colorShade, isPersistent, isPrimary, isSecondary, isTransient, selectionEventData')
import App.Util.Selector (ObjArg, ViewSelSetter, listElement)
import App.View.Util (class Viewable, Select, registerMouseListeners)
import App.View.Util.Axes (AxisTicks(..), TickLabels(..), Ticks(..), create_xAxis, create_yAxis, decimalPlaces, tickCount, tickValues)
import App.View.Util.D3 (Coord, ElementType(..), Margin, colorScale, create, datum, dimensions, line, remove, scaleLinear, selectAll, setAttrs, setDatum, setStyles, setText, textHeight, textWidth, translate)
import App.View.Util.D3 (Selection) as D3
import App.View.Util.Point (Point(..))
import App.View.Util.Scale (Interval, Scales(..), domain)
import Bind ((↦), (⟼))
import Control.Alt ((<|>))

import Types.Defs (cLineChart, cLinePlot, f_plots, f_points)
import Data.Array (concat, elemIndex, mapWithIndex)
import Data.Array.NonEmpty (NonEmptyArray, fromArray, nub)
import Data.Foldable (intercalate, length)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap)
import Data.Semigroup.Foldable (maximum, minimum)
import Data.Tuple (fst, snd, uncurry)
import Effect (Effect, foreachE)
import Lattice ((∨), (∧))
import Util (type (×), Endo, definitely', init, nonEmpty, tail, zipWith, (!), (×))

newtype LineChart = LineChart
   { size :: Dimensions (Selectable Int)
   , tickLabels :: TickLabels
   , caption :: Selectable String
   , scales :: Scales
   , ticks :: Ticks
   , plots :: Array LinePlot
   }

newtype LinePlot = LinePlot
   { name :: Selectable String
   , points :: Array (Point Number)
   }

type LegendEntry =
   { i :: Int
   , name :: String
   }

names :: Array LinePlot -> Array String
names plots = plots <#> unwrap >>> _.name >>> fst

point_smallRadius :: Int
point_smallRadius = 2

fill :: SelStates 𝕊 -> String -> String
fill sel = if isPersistent sel then flip colorShade (-30) else identity

nameCol :: Int -> String
nameCol = colorScale "schemePastel1"

-- 0-based indices of line plot and point within line plot; see data binding in .js
type PointCoordinate = { i :: Int, j :: Int }
type SegmentCoordinates = { i :: Int, j1 :: Int, j2 :: Int }
type Segment = { name :: String, start :: Coord Number, end :: Coord Number }

instance Viewable LineChart Unit where
   isLeaf = const false

   setSelection :: ObjArg -> Unit -> LineChart -> Select -> D3.Selection -> Effect Unit
   setSelection arg _ (LineChart { plots }) redraw rootElement = do
      points <- rootElement # selectAll ".linechart-point"

      foreachE points \point -> do
         point' <- datum point
         point # setAttrs (pointAttrs point') >>= registerMouseListeners (redraw <<< uncurry pointSel <<< selectionEventData')
      segments <- rootElement # selectAll ".linechart-segment"
      foreachE segments \segment -> do
         segment' <- datum segment
         void $ segment # setAttrs (segmentAttrs segment')

      where
      pointAttrs :: PointCoordinate -> Attrs
      pointAttrs { i, j } =
         [ "r" ⟼ toNumber point_smallRadius * if isPrimary sel then 2.0 else if isSecondary sel then 1.4 else 1.0
         , "stroke" ↦ (fill' # if isTransient sel then flip colorShade (-30) else identity)
         , "fill" ↦ fill'
         ]
         where
         LinePlot { name, points } = plots ! i
         sel = selState (points ! j)
         fill' = fill sel (nameCol $ definitely' $ elemIndex (fst name) (names plots))

      segmentAttrs :: SegmentCoordinates -> Attrs
      segmentAttrs { i, j1, j2 } =
         [ "stroke" ↦ (fill' # if isTransient sel then flip colorShade (-30) else identity)
         , "stroke-width" ⟼ if isTransient sel then 2 else if isPersistent sel then 2 else 1
         ]
         where
         LinePlot { name, points } = plots ! i
         sel = selState (points ! j1) ∧ selState (points ! j2)
         fill' = fill sel (nameCol $ definitely' $ elemIndex (fst name) (names plots))

      selState :: Point Number -> SelStates 𝕊
      selState (Point { x, y }) = snd x ∨ snd y

      pointSel :: ViewSelSetter PointCoordinate
      pointSel { i, j } =
         listElement j >>> arg cLinePlot f_points >>> listElement i >>> arg cLineChart f_plots

   createElement :: Unit -> LineChart -> D3.Selection -> Effect D3.Selection
   createElement _ (LineChart { size, tickLabels, caption, scales: Scales scales, ticks: Ticks ticks, plots }) parent = do
      svg <- parent # create SVG [ "width" ⟼ width, "height" ⟼ height ]
      { x: xAxisHeight, y: yAxisWidth } <- axisWidth svg

      let
         margin :: Margin
         margin =
            { top: point_smallRadius * 3 -- otherwise points at very top are clipped
            , right: 3 -- otherwise rightmost edge of legend box is clipped
            , bottom: xAxisHeight
            , left: yAxisWidth
            }

         interior :: Dimensions Int
         interior = Dimensions
            { width: width - margin.left - margin.right - (unwrap legend_dims).width - legend_sep
            , height: height - margin.top - margin.bottom - caption_height
            }

      g <- svg # create G [ translate { x: margin.left, y: margin.top } ]
      void $ createAxes interior g
      plotArea <- createPlotArea interior g
      createLines interior plotArea
      createPoints interior plotArea
      void $ svg
         # create Text
              [ "x" ⟼ width / 2
              , "y" ⟼ height - caption_height / 2
              , classes [ caption_class ]
              , "dominant-baseline" ↦ "middle"
              , "text-anchor" ↦ "middle"
              ]
         >>= setText (fst caption)
      createLegend interior g
      pure g

      where
      caption_class = "title-text"
      caption_height = textHeight caption_class (fst caption) * 2
      Dimensions { height, width } = size <#> fst
      AxisTicks xTicks = ticks.x
      AxisTicks yTicks = ticks.y

      axisWidth :: D3.Selection -> Effect (Coord Int)
      axisWidth parent' = do
         { x: xAxis, y: yAxis } <- createAxes (size <#> fst) parent'
         x <- dimensions xAxis <#> unwrap >>> _.height
         y <- dimensions yAxis <#> unwrap >>> _.width
         remove xAxis
         remove yAxis
         pure { x, y }

      createAxes :: Dimensions Int -> D3.Selection -> Effect (Coord D3.Selection)
      createAxes range parent' = do
         let TickLabels { x: xLabels, y: yLabels } = tickLabels
         x <- create_xAxis parent' (to range)
            { count: tickCount xTicks.spacing (toNumber (length (nub points.x)))
            , values: tickValues xTicks.spacing domains.x
            , places: decimalPlaces xTicks.format
            }
            (unwrap range).height
            xLabels
         y <- create_yAxis parent' (to range)
            { count: tickCount yTicks.spacing 3.0
            , values: tickValues yTicks.spacing domains.y
            , places: decimalPlaces yTicks.format <|> Just 1
            }
            yLabels
         pure { x, y }

      -- Nested viewport clipping data outside the axes, with room for a selected point at the edge; overflow
      -- set inline to override website styles
      createPlotArea :: Dimensions Int -> D3.Selection -> Effect D3.Selection
      createPlotArea (Dimensions range) parent' =
         parent'
            # create SVG
                 [ "x" ⟼ -pad
                 , "y" ⟼ -pad
                 , "width" ⟼ width'
                 , "height" ⟼ height'
                 , "viewBox" ↦ intercalate " " (show <$> [ -pad, -pad, width', height' ])
                 ]
            >>= setStyles [ "overflow" ↦ "hidden" ]
         where
         pad = point_smallRadius * 2
         width' = range.width + 2 * pad
         height' = range.height + 2 * pad

      createLines :: Dimensions Int -> D3.Selection -> Effect Unit
      createLines range parent' =
         foreachE (concat $ mapWithIndex segments plots)
            \({ start, end } × segmentCoords) ->
               void $ parent' #
                  ( create Path [ classes [ "linechart-segment" ], "d" ↦ line (to range) [ start, end ] ]
                       >=> setDatum segmentCoords
                  )
         where
         segments :: Int -> LinePlot -> Array (Segment × SegmentCoordinates)
         segments i (LinePlot { name, points: ps }) = case fromArray ps of
            Nothing -> []
            Just ps' -> zipWith
               (\(start × j1) (end × j2) -> { name: fst name, start, end } × { i, j1, j2 })
               (mapWithIndex (\j point -> coord point × j) (init ps'))
               (mapWithIndex (\j point -> coord point × (j + 1)) (tail ps'))

         coord :: Point Number -> Coord Number
         coord (Point { x, y }) = { x: fst x, y: fst y }

      createPoints :: Dimensions Int -> D3.Selection -> Effect Unit
      createPoints range parent' =
         foreachE entries \(Point { x, y } × { i, j }) ->
            void $ parent' #
               ( create Circle
                    [ classes [ "linechart-point" ]
                    , "stroke-width" ⟼ 1
                    , "cx" ⟼ (to range).x (fst x)
                    , "cy" ⟼ (to range).y (fst y)
                    ]
                    >=> setDatum { i, j }
               )
         where
         entries :: Array (Point Number × PointCoordinate)
         entries = concat $ flip mapWithIndex plots \i (LinePlot { points: ps }) ->
            flip mapWithIndex ps \j p -> p × { i, j }

      createLegend :: Dimensions Int -> D3.Selection -> Effect Unit
      createLegend (Dimensions interior) parent' = do
         let Dimensions { height, width } = legend_dims
         legend' <- parent' # create G
            [ translate { x: interior.width + legend_sep, y: max 0 ((interior.height - height) / 2) } ]
         void $ legend' # create Rect
            [ classes [ "legend-box" ], "x" ⟼ 0, "y" ⟼ 0, "height" ⟼ height, "width" ⟼ width ]
         let circle_centre = lineHeight / 2 - point_smallRadius / 2
         foreachE entries \{ i, name } -> do
            g <- legend' # create G [ classes [ "legend-entry" ], translate { x: 0, y: entry_y i } ]
            void $ g #
               -- align text with boxes
               ( create Text [ classes [ "legend-text" ], translate { x: legend_entry_x, y: 9 } ]
                    >=> setText name
               )
            void $ g # create Circle
               [ "fill" ↦ nameCol (definitely' $ elemIndex name (names plots))
               , "r" ⟼ point_smallRadius
               , "cx" ⟼ circle_centre
               , "cy" ⟼ circle_centre
               ]
         where
         entries :: Array LegendEntry
         entries = flip mapWithIndex plots (\i (LinePlot { name }) -> { i, name: fst name })

         entry_y :: Int -> Int
         entry_y i = i * lineHeight + 2 -- tweak to emulate vertical centering of text

      to :: Dimensions Int -> Coord (Endo Number)
      to (Dimensions range) =
         { x: scaleLinear domains.x { min: 0.0, max: toNumber range.width }
         , y: scaleLinear domains.y { min: toNumber range.height, max: 0.0 }
         }

      domains :: Coord Interval
      domains = { x: domain scales.x (extent points.x), y: domain scales.y (extent points.y) }
         where
         extent xs = { min: minimum xs, max: maximum xs }

      points :: Coord (NonEmptyArray Number)
      points = { x: ps <#> unwrap >>> _.x >>> fst, y: ps <#> unwrap >>> _.y >>> fst }
         where
         ps :: NonEmptyArray (Point Number)
         ps = plots <#> unwrap >>> _.points # join >>> nonEmpty

      legend_sep :: Int
      legend_sep = 15

      lineHeight :: Int
      lineHeight = 15

      legend_entry_x :: Int
      legend_entry_x = 15

      legend_dims :: Dimensions Int
      legend_dims = Dimensions
         { width: legend_entry_x + maxTextWidth + rightMargin
         , height: lineHeight * length plots
         }
         where
         maxTextWidth :: Int
         maxTextWidth = maximum (plots <#> unwrap >>> _.name >>> fst >>> textWidth "legend-text" # nonEmpty)

         rightMargin :: Int
         rightMargin = 4

-- ======================
-- boilerplate
-- ======================

derive instance Newtype LinePlot _
