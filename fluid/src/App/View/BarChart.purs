module App.View.BarChart where

import Prelude hiding (absurd)

import App.Util (Dimensions(..), Selectable, classes, contents)
import App.Util.Selector (ObjArg, listElement)
import App.View.Segment (Segment(..), Scales, indexCol)
import App.View.StackedBar (StackedBar(..), StackedBarContext, barHeight)
import App.View.Util (class Viewable, Select, createElement, setSelection)
import App.View.Util.Axes (TickLabels(..), create_xAxis, create_yAxis)
import App.View.Util.D3 (Coord, ElementType(..), Margin, addHatchPattern, create, scaleBand, scaleLinear, selectAll, setText, textHeight, textWidth, translate)
import App.View.Util.D3 as D3
import Bind ((↦), (⟼))

import Types.Defs (cBarChart, f_stackedBars)
import Data.Array (range)
import Data.Array.NonEmpty (NonEmptyArray, head, toArray)
import Data.Foldable (length)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Number (ceil)
import Data.Semigroup.Foldable (maximum)
import Effect (Effect, foreachE)
import Util ((!))

newtype BarChart = BarChart
   { caption :: Selectable String
   , size :: Dimensions (Selectable Int)
   , tickLabels :: TickLabels
   , stackedBars :: NonEmptyArray StackedBar
   , legend :: Selectable Boolean
   }

instance Viewable BarChart Unit where
   isLeaf = const false

   setSelection :: ObjArg -> Unit -> BarChart -> Select -> D3.Selection -> Effect Unit
   setSelection arg _ chart@(BarChart { stackedBars }) select barChart' = do
      let props = barChartProps chart
      -- more robust to iterate over stackedBars and select ith DOM child instead?
      stackedBars' <- barChart' # selectAll ".stack"
      forWithIndex_ stackedBars' \i stack ->
         setSelection arg props.stackedBarContext (stackedBars ! i)
            (select <<< arg cBarChart f_stackedBars <<< listElement i)
            stack

   createElement :: Unit -> BarChart -> D3.Selection -> Effect D3.Selection
   createElement _ barChart@(BarChart { caption, stackedBars, tickLabels, legend }) parent = do
      svg <- parent # create SVG [ "width" ⟼ props.width, "height" ⟼ props.height ]
      g <- svg # create G [ translate { x: props.margin.left, y: props.margin.top } ]
      void $ createAxes g
      createStackedBars g

      foreachE (range 0 $ length props.ys - 1) \y_index ->
         addHatchPattern g y_index $ indexCol y_index

      void $ svg
         # create Text
              [ "x" ⟼ props.width / 2
              , "y" ⟼ props.height - props.caption_height / 2
              , classes [ props.caption_class ]
              , "dominant-baseline" ↦ "central"
              , "text-anchor" ↦ "middle"
              ]
         >>= setText (contents caption)

      when (contents legend) $
         createLegend props.interior g
      pure g

      where
      props = barChartProps barChart

      createAxes :: D3.Selection -> Effect (Coord D3.Selection)
      createAxes parent' = do
         let TickLabels { x: xLabels, y: yLabels } = tickLabels
         x <- create_xAxis parent' props.scales
            { count: toNumber (length props.xs), values: Nothing, places: Nothing }
            (unwrap props.interior).height
            xLabels
         y <- create_yAxis parent' props.scales { count: 3.0, values: Nothing, places: Just 0 } yLabels
         pure { x, y }

      createStackedBars :: D3.Selection -> Effect Unit
      createStackedBars parent' =
         foreachE (toArray stackedBars) \stackedBar ->
            void $ createElement props.stackedBarContext stackedBar parent'

      createLegend :: Dimensions Int -> D3.Selection -> Effect Unit
      createLegend (Dimensions interior') parent' = do
         legend' <- parent' # create G
            [ translate { x: interior'.width + 0, y: max 0 $ (interior'.height - height) / 2 } ]
         void $ legend' # create Rect
            [ classes [ "legend-box" ], "x" ⟼ 0, "y" ⟼ 0, "height" ⟼ height, "width" ⟼ width ]
         forWithIndex_ props.ys \y_index y -> do
            g <- legend' # create G [ classes [ "legend-entry" ], translate { x: 0, y: entry_y y_index } ]
            void $ g #
               ( create Text [ classes [ "legend-text" ], translate { x: entry_x, y: 9 } ]
                    >=> setText y
               )
            g # create Rect
               [ "fill" ↦ indexCol y_index
               , "width" ⟼ squareSize
               , "height" ⟼ squareSize
               , "x" ⟼ lineHeight / 2 - squareSize / 2
               , "y" ⟼ lineHeight / 2 - squareSize
               ]
         where
         height = lineHeight * length props.ys
         width = entry_x + maxTextWidth + rightMargin
         lineHeight = 15
         entry_x = 15
         squareSize = 4
         rightMargin = 4
         maxTextWidth = maximum (props.ys <#> textWidth "legend-text")
         entry_y i = i * lineHeight + 2

type BarChartProperties =
   { width :: Int
   , height :: Int
   , xs :: NonEmptyArray String
   , ys :: NonEmptyArray String
   , margin :: Margin
   , interior :: Dimensions Int
   , scales :: Scales
   , caption_class :: String
   , caption_height :: Int
   , stackedBarContext :: StackedBarContext
   }

strokeWidth :: Int
strokeWidth = 2

barChartProps :: BarChart -> BarChartProperties
barChartProps (BarChart { caption, size, stackedBars }) =
   { width
   , height
   , xs
   , ys
   , margin
   , interior
   , scales
   , caption_height
   , caption_class
   , stackedBarContext: { interior, scales, strokeWidth }
   }
   where

   xs = stackedBars <#> \(StackedBar bar) -> contents bar.x
   ys = (unwrap $ head stackedBars).segments <#> \(Segment seg) -> contents seg.y -- TODO: enforce uniformity across bars
   Dimensions { width, height } = size <#> contents

   margin :: Margin
   -- previously some right margin hack to accommodate legend
   margin = { top: 3, right: 20, bottom: 30, left: 20 }

   interior :: Dimensions Int
   interior = Dimensions
      { width: width - margin.left - margin.right
      , height: height - margin.top - margin.bottom - caption_height
      }

   scales = to interior

   caption_class = "title-text"
   caption_height = textHeight caption_class (contents caption) * 2

   to :: Dimensions Int -> Scales
   to (Dimensions { width, height }) =
      { x: scaleBand width $ (\(StackedBar bar) -> contents bar.x) <$> toArray stackedBars
      , y: scaleLinear { min: 0.0, max: y_max } { min: toNumber height, max: 0.0 }
      }

   nearest = 10.0
   y_max = ceil $ nearest * (maximum (barHeight <$> stackedBars) / nearest)
