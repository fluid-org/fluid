module App.View.StackedBar where

import Prelude

import App.Util (Dimensions, Selectable, classes, contents)
import App.Util.Selector (ConstrArg)
import App.View.Segment (Scales, Segment(..), SegmentContext)
import App.View.Util (class Viewable, Select, createElement, setSelection)
import App.View.Util.D3 (ElementType(..), create, selectAll)
import App.View.Util.D3 as D3
import Data.Array (scanl)
import Data.Array.NonEmpty (NonEmptyArray, cons', init, toArray)
import Data.Foldable (sum)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Newtype (class Newtype)
import DataType (cStackedBar, f_segments)
import Effect (Effect)
import Util ((!))

newtype StackedBar = StackedBar
   { x :: Selectable String
   , segments :: NonEmptyArray Segment
   }

type StackedBarContext =
   { interior :: Dimensions Int
   , scales :: Scales
   , strokeWidth :: Int -- should probably expect this to be set in CSS instead
   }

barHeight :: StackedBar -> Number
barHeight (StackedBar bar) = sum (map (\(Segment seg) -> contents seg.z) bar.segments)

instance Viewable StackedBar StackedBarContext where
   isLeaf = const false

   createElement :: StackedBarContext -> StackedBar -> D3.Selection -> Effect D3.Selection
   createElement context (stackedBar@(StackedBar { segments })) parent = do
      g <- parent # create G [ classes [ "stack" ] ]
      forWithIndex_ segments \y_index segment ->
         createElement (segmentContext context stackedBar y_index) segment g
      pure g

   setSelection :: ConstrArg -> StackedBarContext -> StackedBar -> Select -> D3.Selection -> Effect Unit
   setSelection arg context (stackedBar@(StackedBar { segments })) select root = do
      -- Might be more robust and more consistent with createRootElement to iterate over segments instead
      segments' <- root # selectAll ".bar" -- TODO: .bar -> .segment
      forWithIndex_ segments' \y_index segment ->
         setSelection arg (segmentContext context stackedBar y_index)
            (segments ! y_index)
            (select <<< arg cStackedBar f_segments)
            segment

segmentContext :: StackedBarContext -> StackedBar -> Int -> SegmentContext
segmentContext { interior, scales, strokeWidth } (StackedBar { x, segments }) =
   \y_index ->
      { interior, scales, strokeWidth, x: contents x, y: ys ! y_index, y_index }
   where
   ys :: Array Number
   ys = init (cons' 0.0 (scanl (+) 0.0 (segments # toArray <#> \(Segment seg) -> contents seg.z)))

-- ======================
-- boilerplate
-- ======================

derive instance Newtype StackedBar _
