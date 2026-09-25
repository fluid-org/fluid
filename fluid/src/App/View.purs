module App.View where

import Prelude hiding (absurd)

import App.Util (Dimensions(..), SelStates, Selectable, 𝕊, dict, get_intOrNumber)
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
import DataType (FieldIndex, cBarChart, cCons, cLineChart, cLinePlot, cLink, cMultiView, cNil, cParagraph, cScatterPlot, cText, f_caption, f_fragments, f_height, f_label, f_labels, f_legend, f_name, f_plots, f_points, f_segments, f_size, f_stackedBars, f_text, f_tickLabels, f_value, f_views, f_width, f_x, f_y, f_z)
import Dict (Dict)
import Link (Link(..))
import Literal (Literal(..))
import Pretty (prettyP)
import Primitive (boolean, int, string, typeError)
import Primitive (unpack') as P
import Util (type (×), error, (!), (×))
import Util.Map (get, mapWithKey)
import Val (BaseVal(..), DictRep(..), Val(..))

-- TODO: merge with 'view' below.
view' :: Partial => FieldIndex -> Options -> String -> Val (SelStates 𝕊) -> View
view' fieldIndex options title v@(Val _ v_opt _) =
   pack $ DocView { doc: viewParagraph <$> v_opt, view: view fieldIndex options title v }
   where
   viewParagraph v'@(Val _ _ (Constr c _)) | c == cParagraph =
      reflectParagraph fieldIndex options v'

-- Convert annotated value to appropriate view, discarding top-level annotations for now.
-- TODO: given the typeError clause, Partial no longer needed
view :: Partial => FieldIndex -> Options -> String -> Val (SelStates 𝕊) -> View
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
   viewDict :: Partial => Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Dict (View × View)
   viewDict = mapWithKey \k (α' × v') -> pack (Text (k × α')) × view fieldIndex options k v'

reflectBarChart :: Partial => FieldIndex -> Val (SelStates 𝕊) -> BarChart
reflectBarChart fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cBarChart -> BarChart
      { caption: P.unpack' string (us ! fieldIndex cBarChart f_caption)
      , size: dict from (us ! fieldIndex cBarChart f_size)
      , tickLabels: dict from (us ! fieldIndex cBarChart f_tickLabels)
      , stackedBars: dict from <$> from (us ! fieldIndex cBarChart f_stackedBars)
      , legend: P.unpack' boolean (us ! fieldIndex cBarChart f_legend)
      }
   _ -> typeError u "BarChart"

reflectLineChart :: Partial => FieldIndex -> Val (SelStates 𝕊) -> LineChart
reflectLineChart fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLineChart -> LineChart
      { size: dict from (us ! fieldIndex cLineChart f_size)
      , tickLabels: dict from (us ! fieldIndex cLineChart f_tickLabels)
      , caption: P.unpack' string (us ! fieldIndex cLineChart f_caption)
      , plots: reflectLinePlot fieldIndex <$> (from (us ! fieldIndex cLineChart f_plots) :: Array (Val (SelStates 𝕊)))
      }
   _ -> typeError u "LineChart"

reflectLinePlot :: Partial => FieldIndex -> Val (SelStates 𝕊) -> LinePlot
reflectLinePlot fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLinePlot -> LinePlot
      { name: P.unpack' string (us ! fieldIndex cLinePlot f_name)
      , points: dict from <$> from (us ! fieldIndex cLinePlot f_points)
      }
   _ -> typeError u "LinePlot"

reflectScatterPlot :: Partial => FieldIndex -> Val (SelStates 𝕊) -> ScatterPlot
reflectScatterPlot fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cScatterPlot -> ScatterPlot
      { caption: P.unpack' string (us ! fieldIndex cScatterPlot f_caption)
      , points: dict from <$> from (us ! fieldIndex cScatterPlot f_points)
      , labels: dict from (us ! fieldIndex cScatterPlot f_labels)
      }
   _ -> typeError u "ScatterPlot"

reflectText :: Partial => FieldIndex -> Val (SelStates 𝕊) -> Text
reflectText fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cText -> case us ! fieldIndex cText f_text of
      Val α _ (Lit (Str s)) -> Text (s × α)
      _ -> typeError u "Text expects string"
   _ -> typeError u "Text"

reflectLink :: Partial => FieldIndex -> Val (SelStates 𝕊) -> Link
reflectLink fieldIndex (Val _ _ u) = case u of
   Constr c us | c == cLink -> case us ! fieldIndex cLink f_label of
      Val α' _ (Lit (Str s)) -> Link (us ! fieldIndex cLink f_value) (s × α')
      _ -> typeError u "Link expects string label"
   _ -> typeError u "Link"

reflectMultiView :: Partial => FieldIndex -> Options -> Val (SelStates 𝕊) -> MultiView
reflectMultiView fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cMultiView ->
      MultiView (view fieldIndex options "" <$> from (us ! fieldIndex cMultiView f_views))
   _ -> typeError u "MultiView"

reflectParagraph :: Partial => FieldIndex -> Options -> Val (SelStates 𝕊) -> Paragraph
reflectParagraph fieldIndex options (Val _ _ u) = case u of
   Constr c us | c == cParagraph ->
      Paragraph (view fieldIndex options "" <$> from (us ! fieldIndex cParagraph f_fragments))
   _ -> typeError u "Paragraph"

class Reflect a b where
   from :: Partial => a -> b

instance Reflect (Val a) (Dict (a × Val a)) where
   from (Val _ _ (Dictionary (DictRep d))) = d

instance Reflect (Val a) (Array (Val a)) where
   from (Val _ _ (Constr c Nil)) | c == cNil = []
   from (Val _ _ (Constr c (u1 : u2 : Nil))) | c == cCons = u1 A.: from u2

instance Reflect (Val a) (NonEmptyArray (Val a)) where
   from (Val _ _ (Constr c Nil)) | c == cNil = error "expected non-empty list"
   from (Val _ _ (Constr c (u1 : u2 : Nil))) | c == cCons = cons' u1 (from u2)

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) (Dimensions (Selectable Int)) where
   from r = Dimensions
      { width: P.unpack' int (snd (get f_width r))
      , height: P.unpack' int (snd (get f_height r))
      }

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) StackedBar where
   from r = StackedBar
      { x: P.unpack' string (snd (get f_x r))
      , segments: dict from <$> from (snd (get f_segments r))
      }

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) Segment where
   from :: Partial => Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Segment
   from r = Segment
      { y: P.unpack' string (snd (get f_y r))
      , z: get_intOrNumber f_z r
      }

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) (Point Number) where
   from r = Point
      { x: get_intOrNumber f_x r
      , y: get_intOrNumber f_y r
      }

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) (Point String) where
   from r = Point
      { x: P.unpack' string (snd (get f_x r))
      , y: P.unpack' string (snd (get f_y r))
      }

instance Reflect (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) (Point Orientation) where
   from r = Point
      { x: P.unpack' orientation (snd (get f_x r))
      , y: P.unpack' orientation (snd (get f_y r))
      }
