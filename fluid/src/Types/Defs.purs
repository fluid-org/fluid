module Types.Defs where

import Prim hiding (Type)

import Bind (FieldName, Name, Var, qual)
import Data.Foldable (class Foldable)
import Data.List (List(..), fromFoldable, (:))
import Module.Defs (builtins, prelude, view)
import Types (Primitive(..), Type(..))

object :: Type
object = PrimitiveTy Object

never :: Type
never = PrimitiveTy Never

none :: Type
none = PrimitiveTy None

bool :: Type
bool = PrimitiveTy Bool

int :: Type
int = PrimitiveTy Int

float :: Type
float = PrimitiveTy Float

str :: Type
str = PrimitiveTy Str

intPair :: Type
intPair = TupleTy (int : int : Nil)

callable :: forall f. Foldable f => f Type -> Type -> Type
callable σs τ = CallableTy (fromFoldable σs) τ

var :: Var -> Type
var = VarTy

matrix :: Type -> Type
matrix τ = ClassTy cMatrix (τ : Nil)

-- Used internally by primitives, desugaring or rendering layer.
cDefault = qual view "Default" :: Name -- Orientation
cRotated = qual view "Rotated" :: Name
cAuto = qual view "Auto" :: Name -- Scale
cFromZero = qual view "FromZero" :: Name
cFixed = qual view "Fixed" :: Name
cScales = qual view "Scales" :: Name
cBarChart = qual view "BarChart" :: Name -- View
cLineChart = qual view "LineChart" :: Name
cLinePlot = qual view "LinePlot" :: Name
cMultiView = qual view "MultiView" :: Name
cScatterPlot = qual view "ScatterPlot" :: Name
cParagraph = qual view "Paragraph" :: Name
cDimensions = qual view "Dimensions" :: Name
cPoint = qual view "Point" :: Name
cAxisLabels = qual view "AxisLabels" :: Name
cTickLabels = qual view "TickLabels" :: Name
cSegment = qual view "Segment" :: Name
cStackedBar = qual view "StackedBar" :: Name
cNonEmpty = qual prelude "NonEmpty" :: Name -- Tree
cRange = qual builtins "range" :: Name
cMatrix = qual builtins "Matrix" :: Name
cText = qual view "Text" :: Name
cLink = qual view "Link" :: Name

-- Field names used internally by rendering layer.
f_caption = "caption" :: FieldName
f_fragments = "fragments" :: FieldName
f_label = "label" :: FieldName
f_text = "text" :: FieldName
f_value = "value" :: FieldName
f_colour = "c" :: FieldName
f_left = "left" :: FieldName
f_right = "right" :: FieldName
f_height = "height" :: FieldName
f_labels = "labels" :: FieldName
f_legend = "legend" :: FieldName
f_max = "max" :: FieldName
f_min = "min" :: FieldName
f_name = "name" :: FieldName
f_plots = "plots" :: FieldName
f_points = "points" :: FieldName
f_scales = "scales" :: FieldName
f_segments = "segments" :: FieldName
f_size = "size" :: FieldName
f_stackedBars = "stackedBars" :: FieldName
f_tickLabels = "tickLabels" :: FieldName
f_views = "views" :: FieldName
f_width = "width" :: FieldName
f_x = "x" :: FieldName
f_y = "y" :: FieldName
f_z = "z" :: FieldName
