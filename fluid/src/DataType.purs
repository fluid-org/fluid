module DataType where

import Prelude hiding (absurd)

import Bind (Name, Var, dottedName, qual)
import ModuleGraph (prelude)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except.Trans (ExceptT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Trans (WriterT)
import Data.CodePoint.Unicode (isUpper)
import Data.List (List(..), elemIndex, (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..)) as NE
import Data.NonEmpty ((:|))
import Data.Map as Map
import Data.Array (last) as A
import Data.Maybe (Maybe, fromMaybe, maybe)
import Data.String (Pattern(..), split)
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (charAt)
import DefiniteAssignment (ClassEntry, fields)
import Effect.Exception (Error)
import Util (absurd, definitely, definitely', error, throw)

type FieldName = String
type Ctr = String -- newtype would require more general Dict keys

-- Distinguish constructors from identifiers syntactically, a la Haskell. In particular this is useful
-- for distinguishing pattern variables from nullary constructors when parsing patterns.
isCtrName ∷ Var → Boolean
isCtrName str = let c = definitely' $ charAt 0 str in isUpper (codePointFromChar c) || c == '_'

isCtrOp :: String -> Boolean
isCtrOp str = ':' == (definitely' $ charAt 0 str)

showCtr :: Var -> String
showCtr c
   | isCtrName c = c
   | isCtrOp c = "(" <> c <> ")"
   | otherwise = error absurd

type ClassTable = Map.Map Ctr ClassEntry -- keyed by fully-qualified name

class HasClasses m where
   askClasses :: m ClassTable

instance (Monad m, HasClasses m) => HasClasses (StateT s m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m) => HasClasses (ReaderT r m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m) => HasClasses (ExceptT e m) where
   askClasses = lift askClasses

instance (Monad m, HasClasses m, Monoid w) => HasClasses (WriterT w m) where
   askClasses = lift askClasses

fieldsOf :: ClassTable -> Ctr -> Maybe (List Var)
fieldsOf classes c = Map.lookup c classes <#> fields

classEntry :: forall m. MonadError Error m => ClassTable -> Ctr -> m ClassEntry
classEntry classes c = maybe (throw $ "Unknown dataclass: " <> showCtr (simpleName c)) pure (Map.lookup c classes)

arity :: forall m. MonadError Error m => ClassTable -> Ctr -> m Int
arity classes c = List.length <<< fields <$> classEntry classes c

checkArity :: forall m. MonadError Error m => ClassTable -> Ctr -> Int -> m Unit
checkArity classes c n = do
   n' <- arity classes c
   when (n' /= n) $ throw $ showCtr (simpleName c) <> " arity " <> show n' <> "; got " <> show n

type FieldIndex = Name -> FieldName -> Int

fieldIndex :: ClassTable -> Name -> FieldName -> Int
fieldIndex classes c field = definitely "field declared for class" do
   fs <- fieldsOf classes (dottedName c)
   elemIndex field fs

view :: Name
view = NE.NonEmptyList ("fluid" :| "view" : Nil)

-- Last (simple) segment of a possibly-qualified constructor name.
simpleName :: Ctr -> String
simpleName c = fromMaybe c (A.last (split (Pattern ".") c))

-- Used internally by primitives, desugaring or rendering layer.
cDefault = qual view "Default" :: Name -- Orientation
cRotated = qual view "Rotated" :: Name
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
cPair = qual prelude "Pair" :: Name -- Pair
cNothing = qual prelude "Nothing" :: Name -- Maybe
cJust = qual prelude "Just" :: Name
cNonEmpty = qual prelude "NonEmpty" :: Name -- Tree
cText = qual view "Text" :: Name
cLink = qual view "Link" :: Name
-- Field names used internally by rendering layer.
f_caption = "caption" :: FieldName
f_fragments = "fragments" :: FieldName
f_label = "label" :: FieldName
f_text = "text" :: FieldName
f_value = "value" :: FieldName
f_colour = "c" :: FieldName
f_fst = "fst" :: FieldName
f_snd = "snd" :: FieldName
f_left = "left" :: FieldName
f_right = "right" :: FieldName
f_height = "height" :: FieldName
f_labels = "labels" :: FieldName
f_legend = "legend" :: FieldName
f_name = "name" :: FieldName
f_plots = "plots" :: FieldName
f_points = "points" :: FieldName
f_segments = "segments" :: FieldName
f_size = "size" :: FieldName
f_stackedBars = "stackedBars" :: FieldName
f_tickLabels = "tickLabels" :: FieldName
f_views = "views" :: FieldName
f_width = "width" :: FieldName
f_x = "x" :: FieldName
f_y = "y" :: FieldName
f_z = "z" :: FieldName
