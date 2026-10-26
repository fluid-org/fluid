module App.View where

import Prelude hiding (absurd)

import App.Util (Dimensions(..), SelStates, Selectable, 𝕊, dict, unpackIntOrNumber)
import App.View.BarChart (BarChart(..))
import App.View.ViewWithDoc (ViewWithDoc)
import App.View.LineChart (LineChart(..), LinePlot(..))
import App.View.MatrixView (MatrixView(..), matrixRep)
import App.View.MultiView (MultiView(..))
import App.View.Paragraph (Paragraph(..))
import App.View.ScatterPlot (ScatterPlot(..))
import App.View.Segment (Segment(..))
import App.View.StackedBar (StackedBar(..))
import App.View.TableView (TableView(..), arrayDictToArray2, headers)
import App.View.Text (Text(..))
import App.View.Util (Filter(..), View, pack)
import App.View.Util.Axes (AxisLabels(..), AxisTicks(..), LabelFormat(..), TickLabels(..), TickSpacing(..), Ticks(..), orientation)
import App.View.Util.Point (Point(..))
import App.View.Util.Scale (Scale(..), Scales(..))
import Data.Array as A
import Data.Array.NonEmpty (NonEmptyArray)
import Bind (Name, Var)
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.List (List)
import Data.Tuple (fst, snd)

import Types.Defs (cAutoFormat, cAutoTicks, cAxisLabels, cAuto, cAxisTicks, cBarChart, cCount, cDecimals, cDimensions, cEvery, cFixed, cFromZero, cLineChart, cLinePlot, cLink, cMultiView, cParagraph, cPoint, cScales, cScatterPlot, cSegment, cStackedBar, cText, cTickLabels, cTicks, f_caption, f_format, f_fragments, f_height, f_label, f_labels, f_legend, f_max, f_min, f_n, f_name, f_places, f_plots, f_points, f_scales, f_segments, f_size, f_spacing, f_stackedBars, f_step, f_text, f_tickLabels, f_ticks, f_value, f_views, f_width, f_x, f_y, f_z)
import Dict (Dict)
import Link (Link(..))
import Literal (Literal(..))
import Pretty (prettyP)
import Primitive (boolean, int, string, typeError)
import Primitive (dropα, unpack') as P
import Util (type (×), absurd, error, head, nonEmpty, (×))
import Util.Map (mapWithKey)
import Val (BaseVal(..), DictRep(..), Val(..), ValWithDoc(..), attr)

type ViewOptions = { rowFilter :: Maybe Filter }

-- TODO: merge with 'view' below.
viewWithDoc :: ViewOptions -> String -> ValWithDoc (SelStates 𝕊) -> ViewWithDoc
viewWithDoc options title (ValWithDoc { val: v, doc }) =
   { doc: reflect options <$> doc :: Maybe Paragraph, view: view options title v }

-- Convert annotated value to appropriate view, discarding top-level annotations for now.
view :: ViewOptions -> String -> Val (SelStates 𝕊) -> View
view options title v@(Val α u') = case u' of
   Lit (Str str) -> pack (Text (str × α))
   Lit ℓ -> pack (Text (prettyP ℓ × α))
   Obj _ _ -> case classView options v of
      Just view' -> view'
      Nothing -> typeError u' "Viewable"
   List vs -> case head vs of
      Just v'@(Val _ (Obj c xvs)) | isNothing (classView options v') -> instanceTable c (fst <$> xvs) vs
      Just (Val _ (Obj _ _)) -> pack (MultiView (view options "" <$> vs))
      _ -> dictTable vs
   Matrix r -> pack (MatrixView { title, matrix: matrixRep r })
   Dictionary (DictRep d) -> pack (viewDict d)
   _ -> typeError u' "Viewable"
   where
   table :: Maybe Name -> Array String -> Array (Array (Val (SelStates 𝕊))) -> View
   table className colNames rows =
      pack (TableView { title, rowFilter: fromMaybe Interactive options.rowFilter, className, colNames, rows })

   instanceTable :: Name -> List Var -> Array (Val (SelStates 𝕊)) -> View
   instanceTable c xs vs = table (Just c) (A.fromFoldable xs) (vs <#> fieldValues)
      where
      fieldValues (Val _ (Obj _ xus)) = A.fromFoldable (snd <$> xus)
      fieldValues _ = error absurd

   dictTable :: Array (Val (SelStates 𝕊)) -> View
   dictTable vs = table Nothing colNames (arrayDictToArray2 colNames records <#> map snd)
      where
      records = dict identity <$> vs
      colNames = headers records

   viewDict :: Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Dict (View × View)
   viewDict = mapWithKey \k (α' × v') -> pack (Text (k × α')) × view options k v'

classView :: ViewOptions -> Val (SelStates 𝕊) -> Maybe View
classView options v@(Val _ (Obj c _))
   | c == cText = Just (pack (reflect options v :: Text))
   | c == cMultiView = Just (pack (reflect options v :: MultiView))
   | c == cParagraph = Just (pack (reflect options v :: Paragraph))
   | c == cLink = Just (pack (reflect options v :: Link))
   | c == cBarChart = Just (pack (reflect options v :: BarChart))
   | c == cScatterPlot = Just (pack (reflect options v :: ScatterPlot))
   | c == cLineChart = Just (pack (reflect options v :: LineChart))
classView _ _ = Nothing

class Reflect b where
   reflect :: ViewOptions -> Val (SelStates 𝕊) -> b

instance Reflect (Val (SelStates 𝕊)) where
   reflect _ = identity

instance Reflect b => Reflect (Array b) where
   reflect options (Val _ (List vs)) = reflect options <$> vs
   reflect _ (Val _ u) = typeError u "list"

instance Reflect b => Reflect (NonEmptyArray b) where
   reflect options v = nonEmpty (reflect options v)

instance Reflect BarChart where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cBarChart -> BarChart
         { caption: P.unpack' string (attr f_caption v)
         , size: reflect options (attr f_size v)
         , tickLabels: reflect options (attr f_tickLabels v)
         , stackedBars: reflect options (attr f_stackedBars v)
         , legend: P.unpack' boolean (attr f_legend v)
         }
      _ -> typeError u "BarChart"

instance Reflect LineChart where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cLineChart -> LineChart
         { size: reflect options (attr f_size v)
         , tickLabels: reflect options (attr f_tickLabels v)
         , caption: P.unpack' string (attr f_caption v)
         , scales: reflect options (attr f_scales v)
         , ticks: reflect options (attr f_ticks v)
         , plots: reflect options (attr f_plots v)
         }
      _ -> typeError u "LineChart"

instance Reflect LinePlot where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cLinePlot -> LinePlot
         { name: P.unpack' string (attr f_name v)
         , points: reflect options (attr f_points v)
         }
      _ -> typeError u "LinePlot"

instance Reflect ScatterPlot where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cScatterPlot -> ScatterPlot
         { caption: P.unpack' string (attr f_caption v)
         , points: reflect options (attr f_points v)
         , labels: reflect options (attr f_labels v)
         }
      _ -> typeError u "ScatterPlot"

instance Reflect (Dimensions (Selectable Int)) where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cDimensions -> Dimensions
         { width: P.unpack' int (attr f_width v)
         , height: P.unpack' int (attr f_height v)
         }
      _ -> typeError u "Dimensions"

instance Reflect (Point Number) where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cPoint -> Point
         { x: unpackIntOrNumber (attr f_x v)
         , y: unpackIntOrNumber (attr f_y v)
         }
      _ -> typeError u "Point"

instance Reflect AxisLabels where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cAxisLabels -> AxisLabels
         { x: P.dropα (P.unpack' string (attr f_x v))
         , y: P.dropα (P.unpack' string (attr f_y v))
         }
      _ -> typeError u "AxisLabels"

instance Reflect TickLabels where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cTickLabels -> TickLabels
         { x: P.dropα (P.unpack' orientation (attr f_x v))
         , y: P.dropα (P.unpack' orientation (attr f_y v))
         }
      _ -> typeError u "TickLabels"

instance Reflect Scales where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cScales -> Scales { x: reflect options (attr f_x v), y: reflect options (attr f_y v) }
      _ -> typeError u "Scales"

instance Reflect Scale where
   reflect _ v@(Val _ u) = case u of
      Obj c _
         | c == cAuto -> Auto
         | c == cFromZero -> FromZero
         | c == cFixed -> Fixed (P.dropα (unpackIntOrNumber (attr f_min v))) (P.dropα (unpackIntOrNumber (attr f_max v)))
      _ -> typeError u "Scale"

instance Reflect Ticks where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cTicks -> Ticks { x: reflect options (attr f_x v), y: reflect options (attr f_y v) }
      _ -> typeError u "Ticks"

instance Reflect AxisTicks where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cAxisTicks -> AxisTicks
         { spacing: reflect options (attr f_spacing v)
         , format: reflect options (attr f_format v)
         }
      _ -> typeError u "AxisTicks"

instance Reflect TickSpacing where
   reflect _ v@(Val _ u) = case u of
      Obj c _
         | c == cAutoTicks -> AutoTicks
         | c == cCount -> Count (P.dropα (P.unpack' int (attr f_n v)))
         | c == cEvery ->
              let
                 step = P.dropα (unpackIntOrNumber (attr f_step v))
              in
                 if step > 0.0 then Every step else error ("Every step must be positive; got " <> show step)
      _ -> typeError u "TickSpacing"

instance Reflect LabelFormat where
   reflect _ v@(Val _ u) = case u of
      Obj c _
         | c == cAutoFormat -> AutoFormat
         | c == cDecimals -> Decimals (P.dropα (P.unpack' int (attr f_places v)))
      _ -> typeError u "LabelFormat"

instance Reflect Segment where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cSegment -> Segment
         { y: P.unpack' string (attr f_y v)
         , z: unpackIntOrNumber (attr f_z v)
         }
      _ -> typeError u "Segment"

instance Reflect StackedBar where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cStackedBar -> StackedBar
         { x: P.unpack' string (attr f_x v)
         , segments: reflect options (attr f_segments v)
         }
      _ -> typeError u "StackedBar"

instance Reflect Text where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cText -> case attr f_text v of
         Val α (Lit (Str s)) -> Text (s × α)
         _ -> typeError u "Text expects string"
      _ -> typeError u "Text"

instance Reflect Link where
   reflect _ v@(Val _ u) = case u of
      Obj c _ | c == cLink -> case attr f_label v of
         Val α' (Lit (Str s)) -> Link (attr f_value v) (s × α')
         _ -> typeError u "Link expects string label"
      _ -> typeError u "Link"

instance Reflect MultiView where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cMultiView ->
         MultiView (view options "" <$> reflect options (attr f_views v))
      _ -> typeError u "MultiView"

instance Reflect Paragraph where
   reflect options v@(Val _ u) = case u of
      Obj c _ | c == cParagraph ->
         Paragraph (view options "" <$> reflect options (attr f_fragments v))
      _ -> typeError u "Paragraph"
