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
      | c == cText -> pack (reflect fieldIndex v :: Text)
      | c == cMultiView -> pack (reflectMultiView fieldIndex options v)
      | c == cParagraph -> pack (reflectParagraph fieldIndex options v)
      | c == cLink -> pack (reflect fieldIndex v :: Link)
      | c == cBarChart -> pack (reflect fieldIndex v :: BarChart)
      | c == cScatterPlot -> pack (reflect fieldIndex v :: ScatterPlot)
      | c == cLineChart -> pack (reflect fieldIndex v :: LineChart)
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
           vs = reflect fieldIndex v :: Array (Val (SelStates 𝕊))
   Matrix r ->
      pack (MatrixView { title, matrix: matrixRep r })
   Dictionary (DictRep d) ->
      pack (viewDict d)
   _ -> typeError u' "Viewable"
   where
   viewDict :: Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Dict (View × View)
   viewDict = mapWithKey \k (α' × v') -> pack (Text (k × α')) × view fieldIndex options k v'

class Reflect b where
   reflect :: FieldIndex -> Val (SelStates 𝕊) -> b

instance Reflect (Val (SelStates 𝕊)) where
   reflect _ = identity

instance Reflect b => Reflect (Array b) where
   reflect _ (Val _ _ (Constr c Nil)) | c == cNil = []
   reflect fieldIndex (Val _ _ (Constr c (u1 : u2 : Nil))) | c == cCons = reflect fieldIndex u1 A.: reflect fieldIndex u2
   reflect _ (Val _ _ u) = typeError u "list"

instance Reflect b => Reflect (NonEmptyArray b) where
   reflect fieldIndex v = case A.uncons (reflect fieldIndex v) of
      Just { head, tail } -> cons' head tail
      Nothing -> error "Expected non-empty list"

instance Reflect BarChart where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cBarChart -> BarChart
         { caption: P.unpack' string (us ! fieldIndex cBarChart f_caption)
         , size: reflect fieldIndex (us ! fieldIndex cBarChart f_size)
         , tickLabels: reflect fieldIndex (us ! fieldIndex cBarChart f_tickLabels)
         , stackedBars: reflect fieldIndex (us ! fieldIndex cBarChart f_stackedBars)
         , legend: P.unpack' boolean (us ! fieldIndex cBarChart f_legend)
         }
      _ -> typeError u "BarChart"

instance Reflect LineChart where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cLineChart -> LineChart
         { size: reflect fieldIndex (us ! fieldIndex cLineChart f_size)
         , tickLabels: reflect fieldIndex (us ! fieldIndex cLineChart f_tickLabels)
         , caption: P.unpack' string (us ! fieldIndex cLineChart f_caption)
         , plots: reflect fieldIndex (us ! fieldIndex cLineChart f_plots)
         }
      _ -> typeError u "LineChart"

instance Reflect LinePlot where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cLinePlot -> LinePlot
         { name: P.unpack' string (us ! fieldIndex cLinePlot f_name)
         , points: reflect fieldIndex (us ! fieldIndex cLinePlot f_points)
         }
      _ -> typeError u "LinePlot"

instance Reflect ScatterPlot where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cScatterPlot -> ScatterPlot
         { caption: P.unpack' string (us ! fieldIndex cScatterPlot f_caption)
         , points: reflect fieldIndex (us ! fieldIndex cScatterPlot f_points)
         , labels: reflect fieldIndex (us ! fieldIndex cScatterPlot f_labels)
         }
      _ -> typeError u "ScatterPlot"

instance Reflect (Dimensions (Selectable Int)) where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cDimensions -> Dimensions
         { width: P.unpack' int (us ! fieldIndex cDimensions f_width)
         , height: P.unpack' int (us ! fieldIndex cDimensions f_height)
         }
      _ -> typeError u "Dimensions"

instance Reflect (Point Number) where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cPoint -> Point
         { x: unpackIntOrNumber (us ! fieldIndex cPoint f_x)
         , y: unpackIntOrNumber (us ! fieldIndex cPoint f_y)
         }
      _ -> typeError u "Point"

instance Reflect (Point String) where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cAxisLabels -> Point
         { x: P.unpack' string (us ! fieldIndex cAxisLabels f_x)
         , y: P.unpack' string (us ! fieldIndex cAxisLabels f_y)
         }
      _ -> typeError u "AxisLabels"

instance Reflect (Point Orientation) where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cTickLabels -> Point
         { x: P.unpack' orientation (us ! fieldIndex cTickLabels f_x)
         , y: P.unpack' orientation (us ! fieldIndex cTickLabels f_y)
         }
      _ -> typeError u "TickLabels"

instance Reflect Segment where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cSegment -> Segment
         { y: P.unpack' string (us ! fieldIndex cSegment f_y)
         , z: unpackIntOrNumber (us ! fieldIndex cSegment f_z)
         }
      _ -> typeError u "Segment"

instance Reflect StackedBar where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cStackedBar -> StackedBar
         { x: P.unpack' string (us ! fieldIndex cStackedBar f_x)
         , segments: reflect fieldIndex (us ! fieldIndex cStackedBar f_segments)
         }
      _ -> typeError u "StackedBar"

instance Reflect Text where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cText -> case us ! fieldIndex cText f_text of
         Val α _ (Lit (Str s)) -> Text (s × α)
         _ -> typeError u "Text expects string"
      _ -> typeError u "Text"

instance Reflect Link where
   reflect fieldIndex (Val _ _ u) = case u of
      Constr c us | c == cLink -> case us ! fieldIndex cLink f_label of
         Val α' _ (Lit (Str s)) -> Link (us ! fieldIndex cLink f_value) (s × α')
         _ -> typeError u "Link expects string label"
      _ -> typeError u "Link"

reflectMultiView :: FieldIndex -> Options -> Val (SelStates 𝕊) -> MultiView
reflectMultiView fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cMultiView ->
      MultiView (view fieldIndex options "" <$> reflect fieldIndex (us ! fieldIndex cMultiView f_views))
   _ -> typeError u "MultiView"

reflectParagraph :: FieldIndex -> Options -> Val (SelStates 𝕊) -> Paragraph
reflectParagraph fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cParagraph ->
      Paragraph (view fieldIndex options "" <$> reflect fieldIndex (us ! fieldIndex cParagraph f_fragments))
   _ -> typeError u "Paragraph"
