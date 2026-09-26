module App.View where

import Prelude hiding (absurd)

import App.Util (Dimensions(..), SelStates, Selectable, 𝕊, dict, unpackIntOrNumber)
import App.View.BarChart (BarChart(..))
import App.View.DocView (DocView(..))
import App.View.LineChart (LineChart(..), LinePlot(..))
import App.View.MatrixView (MatrixView(..), matrixRep)
import App.View.MultiView (MultiView(..))
import App.View.Paragraph (Paragraph(..))
import App.View.ScatterPlot (ScatterPlot(..))
import App.View.Segment (Segment(..))
import App.View.StackedBar (StackedBar(..))
import App.View.TableView (TableView(..), arrayDictToArray2, headers)
import App.View.Text (Text(..))
import App.View.Util (Filter(..), View, Options, pack)
import App.View.Util.Axes (Orientation, orientation)
import App.View.Util.Point (Point(..))
import Data.Array as A
import Data.Array.NonEmpty (NonEmptyArray, cons')
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (snd)
import DataType (FieldIndex, cAxisLabels, cBarChart, cCons, cDimensions, cLineChart, cLinePlot, cLink, cMultiView, cNil, cParagraph, cPoint, cScatterPlot, cSegment, cStackedBar, cText, cTickLabels, f_caption, f_fragments, f_height, f_label, f_labels, f_legend, f_name, f_plots, f_points, f_segments, f_size, f_stackedBars, f_text, f_tickLabels, f_value, f_views, f_width, f_x, f_y, f_z)
import Dict (Dict)
import Link (Link(..))
import Literal (Literal(..))
import Pretty (prettyP)
import Primitive (boolean, int, string, typeError)
import Primitive (unpack') as P
import Util (type (×), error, (!), (×))
import Util.Map (mapWithKey)
import Val (BaseVal(..), DictRep(..), Val(..))

-- TODO: merge with 'view' below.
view' :: FieldIndex -> Options -> String -> Val (SelStates 𝕊) -> View
view' fieldIndex options title v@(Val _ v_opt _) =
   pack $ DocView { doc: reflectParagraph fieldIndex options <$> v_opt, view: view fieldIndex options title v }

-- Convert annotated value to appropriate view, discarding top-level annotations for now.
view :: FieldIndex -> Options -> String -> Val (SelStates 𝕊) -> View
view fieldIndex options title v@(Val α _ u') = case u' of
   Lit (Str str) -> pack (Text (str × α))
   Lit ℓ -> pack (Text (prettyP ℓ × α))
   Constr c _
      | c == cText -> pack (reflectText fieldIndex v)
      | c == cMultiView -> pack (reflectMultiView fieldIndex options v)
      | c == cParagraph -> pack (reflectParagraph fieldIndex options v)
      | c == cLink -> pack (reflectLink fieldIndex v)
      | c == cBarChart -> pack (reflectBarChart fieldIndex v)
      | c == cScatterPlot -> pack (reflectScatterPlot fieldIndex v)
      | c == cLineChart -> pack (reflectLineChart fieldIndex v)
      | c == cNil || c == cCons ->
           if tableView then
              let
                 rowFilter = fromMaybe Interactive options.rowFilter
                 records = dict identity <$> vs
                 colNames = headers records
                 rows = arrayDictToArray2 colNames records <#> map snd
              in
                 pack (TableView { title, rowFilter, colNames, rows })
           else pack (MultiView $ view fieldIndex options "" <$> vs)
           where
           tableView = case A.uncons vs of
              Just { head: Val _ _ (Dictionary _) } -> true
              Just { head: Val _ _ _ } -> false
              Nothing -> true
           vs = from v :: Array (Val (SelStates 𝕊))
   Matrix r ->
      pack (MatrixView { title, matrix: matrixRep r })
   Dictionary (DictRep d) ->
      pack (viewDict d)
   _ -> typeError u' "Viewable"
   where
   viewDict :: Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Dict (View × View)
   viewDict = mapWithKey \k (α' × v') -> pack (Text (k × α')) × view fieldIndex options k v'

reflectBarChart :: FieldIndex -> Val (SelStates 𝕊) -> BarChart
reflectBarChart fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cBarChart -> BarChart
      { caption: P.unpack' string (us ! fieldIndex cBarChart f_caption)
      , size: reflectDimensions fieldIndex (us ! fieldIndex cBarChart f_size)
      , tickLabels: reflectTickLabels fieldIndex (us ! fieldIndex cBarChart f_tickLabels)
      , stackedBars: reflectStackedBar fieldIndex <$> from (us ! fieldIndex cBarChart f_stackedBars)
      , legend: P.unpack' boolean (us ! fieldIndex cBarChart f_legend)
      }
   _ -> typeError u "BarChart"

reflectLineChart :: FieldIndex -> Val (SelStates 𝕊) -> LineChart
reflectLineChart fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLineChart -> LineChart
      { size: reflectDimensions fieldIndex (us ! fieldIndex cLineChart f_size)
      , tickLabels: reflectTickLabels fieldIndex (us ! fieldIndex cLineChart f_tickLabels)
      , caption: P.unpack' string (us ! fieldIndex cLineChart f_caption)
      , plots: reflectLinePlot fieldIndex <$> from (us ! fieldIndex cLineChart f_plots)
      }
   _ -> typeError u "LineChart"

reflectLinePlot :: FieldIndex -> Val (SelStates 𝕊) -> LinePlot
reflectLinePlot fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLinePlot -> LinePlot
      { name: P.unpack' string (us ! fieldIndex cLinePlot f_name)
      , points: reflectPoint fieldIndex <$> from (us ! fieldIndex cLinePlot f_points)
      }
   _ -> typeError u "LinePlot"

reflectScatterPlot :: FieldIndex -> Val (SelStates 𝕊) -> ScatterPlot
reflectScatterPlot fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cScatterPlot -> ScatterPlot
      { caption: P.unpack' string (us ! fieldIndex cScatterPlot f_caption)
      , points: reflectPoint fieldIndex <$> from (us ! fieldIndex cScatterPlot f_points)
      , labels: reflectAxisLabels fieldIndex (us ! fieldIndex cScatterPlot f_labels)
      }
   _ -> typeError u "ScatterPlot"

reflectDimensions :: FieldIndex -> Val (SelStates 𝕊) -> Dimensions (Selectable Int)
reflectDimensions fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cDimensions -> Dimensions
      { width: P.unpack' int (us ! fieldIndex cDimensions f_width)
      , height: P.unpack' int (us ! fieldIndex cDimensions f_height)
      }
   _ -> typeError u "Dimensions"

reflectPoint :: FieldIndex -> Val (SelStates 𝕊) -> Point Number
reflectPoint fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cPoint -> Point
      { x: unpackIntOrNumber (us ! fieldIndex cPoint f_x)
      , y: unpackIntOrNumber (us ! fieldIndex cPoint f_y)
      }
   _ -> typeError u "Point"

reflectAxisLabels :: FieldIndex -> Val (SelStates 𝕊) -> Point String
reflectAxisLabels fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cAxisLabels -> Point
      { x: P.unpack' string (us ! fieldIndex cAxisLabels f_x)
      , y: P.unpack' string (us ! fieldIndex cAxisLabels f_y)
      }
   _ -> typeError u "AxisLabels"

reflectTickLabels :: FieldIndex -> Val (SelStates 𝕊) -> Point Orientation
reflectTickLabels fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cTickLabels -> Point
      { x: P.unpack' orientation (us ! fieldIndex cTickLabels f_x)
      , y: P.unpack' orientation (us ! fieldIndex cTickLabels f_y)
      }
   _ -> typeError u "TickLabels"

reflectSegment :: FieldIndex -> Val (SelStates 𝕊) -> Segment
reflectSegment fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cSegment -> Segment
      { y: P.unpack' string (us ! fieldIndex cSegment f_y)
      , z: unpackIntOrNumber (us ! fieldIndex cSegment f_z)
      }
   _ -> typeError u "Segment"

reflectStackedBar :: FieldIndex -> Val (SelStates 𝕊) -> StackedBar
reflectStackedBar fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cStackedBar -> StackedBar
      { x: P.unpack' string (us ! fieldIndex cStackedBar f_x)
      , segments: reflectSegment fieldIndex <$> from (us ! fieldIndex cStackedBar f_segments)
      }
   _ -> typeError u "StackedBar"

reflectText :: FieldIndex -> Val (SelStates 𝕊) -> Text
reflectText fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cText -> case us ! fieldIndex cText f_text of
      Val α _ (Lit (Str s)) -> Text (s × α)
      _ -> typeError u "Text expects string"
   _ -> typeError u "Text"

reflectLink :: FieldIndex -> Val (SelStates 𝕊) -> Link
reflectLink fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLink -> case us ! fieldIndex cLink f_label of
      Val α' _ (Lit (Str s)) -> Link (us ! fieldIndex cLink f_value) (s × α')
      _ -> typeError u "Link expects string label"
   _ -> typeError u "Link"

reflectMultiView :: FieldIndex -> Options -> Val (SelStates 𝕊) -> MultiView
reflectMultiView fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cMultiView ->
      MultiView (view fieldIndex options "" <$> from (us ! fieldIndex cMultiView f_views))
   _ -> typeError u "MultiView"

reflectParagraph :: FieldIndex -> Options -> Val (SelStates 𝕊) -> Paragraph
reflectParagraph fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cParagraph ->
      Paragraph (view fieldIndex options "" <$> from (us ! fieldIndex cParagraph f_fragments))
   _ -> typeError u "Paragraph"

class Reflect a b where
   from :: a -> b

instance Reflect (Val a) (Dict (a × Val a)) where
   from (Val _ _ (Dictionary (DictRep d))) = d
   from (Val _ _ u) = typeError u "dict"

instance Reflect (Val a) (Array (Val a)) where
   from (Val _ _ (Constr c Nil)) | c == cNil = []
   from (Val _ _ (Constr c (u1 : u2 : Nil))) | c == cCons = u1 A.: from u2
   from (Val _ _ u) = typeError u "list"

instance Reflect (Val a) (NonEmptyArray (Val a)) where
   from v = case A.uncons (from v) of
      Just { head, tail } -> cons' head tail
      Nothing -> error "Expected non-empty list"
