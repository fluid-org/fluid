module DataType where

import Prelude hiding (absurd)

import Bind (Name, Var, dottedName, qual)
import Control.Monad.Error.Class (class MonadError)
import Control.Monad.Except.Trans (ExceptT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.State.Trans (StateT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer.Trans (WriterT)
import Data.CodePoint.Unicode (isUpper)
import Data.Function (on)
import Data.List (List(..), elemIndex, (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..)) as NE
import Data.NonEmpty ((:|))
import Data.Map as Map
import Data.Array (last) as A
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (Pattern(..), split)
import Data.String.CodePoints (codePointFromChar)
import Data.String.CodeUnits (charAt)
import DefiniteAssignment (ClassEntry, classFor, fields)
import Dict (Dict, fromFoldable)
import Effect.Exception (Error)
import Util (type (×), absurd, definitely, definitely', error, throw, whenever, (×))
import Util.Map (lookup)

type TypeName = String
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

data DataType = DataType TypeName (Dict CtrSig)
type CtrSig = Int

typeName :: DataType -> TypeName
typeName (DataType name _) = name

instance Eq DataType where
   eq = eq `on` typeName

instance Show DataType where
   show = typeName

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

-- FQN of the base of a class, resolved through its declaring context.
baseOf :: ClassEntry -> Maybe Ctr
baseOf cls = (dottedName <<< _.name) <$> (cls.base >>= classFor cls.cxt)

-- Root of the hierarchy containing c.
rootOf :: ClassTable -> Ctr -> Ctr
rootOf classes c = case Map.lookup c classes >>= baseOf of
   Just b -> rootOf classes b
   Nothing -> c

isLeaf :: ClassTable -> Ctr -> Boolean
isLeaf classes c = List.all (\cls -> baseOf cls /= Just c) (Map.values classes)

-- A datatype is a dataclass hierarchy, named by its root; every class belongs to the datatype of its
-- hierarchy. Its constructors are the leaves: non-leaf classes are not constructable/matchable (#1530).
dataType :: ClassTable -> Ctr -> Maybe DataType
dataType classes c = Map.lookup c classes $> DataType root (fromFoldable sigs)
   where
   root = rootOf classes c
   sigs = (Map.toUnfoldable classes :: List (Ctr × ClassEntry)) # List.mapMaybe
      \(c' × cls) -> whenever (rootOf classes c' == root && isLeaf classes c') (c' × List.length (fields cls))

fieldsOf :: ClassTable -> Ctr -> Maybe (List Var)
fieldsOf classes c = Map.lookup c classes <#> fields

classEntry :: forall m. MonadError Error m => ClassTable -> Ctr -> m ClassEntry
classEntry classes c = maybe (throw $ "Unknown dataclass: " <> showCtr (simpleName c)) pure (Map.lookup c classes)

-- Datatype of c and c's signature within it; a non-leaf class has no signature (#1530).
ctrSig :: forall m. MonadError Error m => ClassTable -> String -> Ctr -> m (DataType × CtrSig)
ctrSig classes verb c = do
   d@(DataType _ sigs) <- classEntry classes c $> definitely' (dataType classes c)
   n <- maybe (throw $ "Cannot " <> verb <> " non-leaf class: " <> showCtr (simpleName c)) pure (lookup c sigs)
   pure (d × n)

checkArity :: forall m. MonadError Error m => ClassTable -> String -> Ctr -> Int -> m Unit
checkArity classes verb c n = do
   _ × n' <- ctrSig classes verb c
   when (n' /= n) $ throw $ showCtr (simpleName c) <> " arity " <> show n' <> "; got " <> show n

type FieldIndex = Name -> FieldName -> Int

fieldIndex :: ClassTable -> Name -> FieldName -> Int
fieldIndex classes c field = definitely "field declared for class" do
   fs <- fieldsOf classes (dottedName c)
   elemIndex field fs

-- Module paths for the builtin/library constructors (hard-coded for now).
lib_builtins :: Var -> Name
lib_builtins = qual (NE.NonEmptyList ("lib" :| "builtins" : Nil))

lib_view :: Var -> Name
lib_view = qual (NE.NonEmptyList ("lib" :| "view" : Nil))

-- Last (simple) segment of a possibly-qualified constructor name.
simpleName :: Ctr -> String
simpleName c = fromMaybe c (A.last (split (Pattern ".") c))

-- Used internally by primitives, desugaring or rendering layer.
cDefault = lib_view "Default" :: Name -- Orientation
cRotated = lib_view "Rotated" :: Name
cBarChart = lib_view "BarChart" :: Name -- View
cLineChart = lib_view "LineChart" :: Name
cLinePlot = lib_view "LinePlot" :: Name
cMultiView = lib_view "MultiView" :: Name
cScatterPlot = lib_view "ScatterPlot" :: Name
cParagraph = lib_view "Paragraph" :: Name

cNil = lib_builtins "Nil" :: Name -- List
cCons = lib_builtins "Cons" :: Name
cPair = lib_builtins "Pair" :: Name -- Pair
cNothing = lib_builtins "Nothing" :: Name -- Maybe
cJust = lib_builtins "Just" :: Name

cNonEmpty = lib_builtins "NonEmpty" :: Name -- Tree
cText = lib_view "Text" :: Name
cLink = lib_view "Link" :: Name
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
