module DataType where

import Prelude hiding (join)
import Prim hiding (Type)

import Bind (Name, Var, dottedName, qual)
import ModuleGraph (builtins, prelude)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except.Trans (ExceptT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Trans (WriterT)
import Data.Foldable (and, elem, foldr)
import Data.List (List(..), elemIndex, zipWith, (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..)) as NE
import Data.NonEmpty ((:|))
import Data.Map as Map
import Data.Array (last) as A
import Data.Maybe (Maybe, fromMaybe, maybe)
import Data.String (Pattern(..), split)
import DefiniteAssignment (ClassEntry, ancestors, fields)
import Effect.Exception (Error)
import Type (Primitive(..), Type(..), baseType)
import Util (definitely', throw)

type FieldName = String
type Ctr = String -- newtype would require more general Dict keys

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

classEntry :: forall m. MonadError Error m => Ctr -> ClassTable -> m ClassEntry
classEntry c classes = maybe (throw $ "Unknown dataclass: " <> simpleName c) pure (Map.lookup c classes)

arity :: forall m. MonadError Error m => Ctr -> ClassTable -> m Int
arity c classes = List.length <<< fields <$> classEntry c classes

checkArity :: forall m. MonadError Error m => Ctr -> Int -> ClassTable -> m Unit
checkArity c n classes = do
   n' <- arity c classes
   when (n' /= n) $ throw $ simpleName c <> " arity " <> show n' <> "; got " <> show n

subtype :: ClassTable -> Type -> Type -> Boolean
subtype classes σ τ
   | σ == τ = true
   | otherwise =
        case σ, τ of
           PrimitiveTy Never, _ -> true
           _, PrimitiveTy Object -> true
           UnionTy σ1 σ2, _ -> subtype classes σ1 τ && subtype classes σ2 τ
           _, UnionTy τ1 τ2 -> subtype classes σ τ1 || subtype classes σ τ2
           LitTy _, _ -> subtype classes (baseType σ) τ
           PrimitiveTy Int, PrimitiveTy Float -> true
           -- classes with type arguments related only by equality until class table records instantiated bases
           ClassTy c Nil, ClassTy d Nil -> maybe false (elem d <<< ancestors) (Map.lookup (dottedName c) classes)
           _, PrimitiveTy Sized -> sized σ
           ListTy σ', ListTy τ' -> equiv classes σ' τ'
           DictTy σ', DictTy τ' -> equiv classes σ' τ'
           TupleTy σs, TupleTy τs -> List.length σs == List.length τs && and (zipWith (subtype classes) σs τs)
           CallableTy σs σ', CallableTy τs τ' ->
              List.length σs == List.length τs && and (zipWith (subtype classes) τs σs) && subtype classes σ' τ'
           _, _ -> false
        where
        sized (ListTy _) = true
        sized (DictTy _) = true
        sized (PrimitiveTy Str) = true
        sized (TupleTy _) = true
        sized _ = false

equiv :: ClassTable -> Type -> Type -> Boolean
equiv classes σ τ = subtype classes σ τ && subtype classes τ σ

join :: ClassTable -> Type -> Type -> Type
join classes σ τ
   | subtype classes σ τ = τ
   | subtype classes τ σ = σ
   | otherwise = UnionTy σ τ

joins :: ClassTable -> List Type -> Type
joins classes = foldr (join classes) (PrimitiveTy Never)

type FieldIndex = Name -> FieldName -> Int

fieldIndex :: ClassTable -> Name -> FieldName -> Int
fieldIndex classes c field = definitely' (elemIndex field =<< fieldsOf classes (dottedName c))

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
cNonEmpty = qual prelude "NonEmpty" :: Name -- Tree
cRange = qual builtins "range" :: Name
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
