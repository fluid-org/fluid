module App.View.Util where

import Prelude

import App.Util (SelState, SelStates, Selectable, Selection, SelectionType, Selector, SetSel, 𝕊, classes, selClasses, selClassesFor)
import App.Util.Selector (ConstrArg, dictVal)
import App.View.Util.D3 (create, on, setAttrs)
import App.View.Util.D3 as D3
import Bind (Var)
import DataType (FieldIndex)
import Data.Argonaut.Decode (class DecodeJson, JsonDecodeError(..))
import Data.Argonaut.Decode.Decoders (decodeString)
import Data.Either (Either(..))
import Data.Foldable (all, sequence_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe)
import Data.Tuple (fst, snd)
import Dict (Dict)
import Effect (Effect)
import File (Folder)
import DepGraph (Labelling)
import Lattice (𝔹, (∨))
import SExpr as S
import Util (type (×), Endo, (×))
import Util.Map (toUnfoldable, values)
import Util.Set (size)
import Val (EnvWithDocs, Val, ValWithDoc)
import Web.Event.Event (Event, EventType(..))
import Web.Event.EventTarget (eventListener)

type HTMLId = String
type Redraw = Endo Fig -> Effect Unit

newtype View = View (forall r. (forall a. Viewable a Unit => a -> r) -> r)

pack :: forall a. Viewable a Unit => a -> View
pack x = View (_ $ x)

unpack :: forall r. View -> (forall a. Viewable a Unit => a -> r) -> r
unpack (View vw) k = vw k

class Viewable a b | a -> b where
   createElement :: b -> a -> D3.Selection -> Effect D3.Selection
   setSelection :: ConstrArg -> b -> a -> Select -> D3.Selection -> Effect Unit
   isLeaf :: a -> Boolean

instance Viewable View Unit where
   isLeaf view = unpack view \v -> isLeaf v
   createElement _ view parent = unpack view \v -> createElement unit v parent
   setSelection arg _ view select rootElement = unpack view \v -> setSelection arg unit v select rootElement

instance Viewable (Dict (View × View)) Unit where
   isLeaf views = size views == 0

   createElement :: Unit -> Dict (View × View) -> D3.Selection -> Effect D3.Selection
   createElement _ views parent = do
      let columnar = if all isLeaf (snd <$> values views) then [ "columnar" ] else []
      rootElement <- parent # create D3.Div [ classes $ [ "tree-children" ] <> columnar ]
      -- create views in fixed order, so can access positionally in setSelection and map back to keys
      sequence_ $ (toUnfoldable views :: Array _) <#> \(_ × (k_view × view)) -> do
         child <- rootElement # create D3.Div [ classes [ "tree-node" ] ]
         key <- createElement unit k_view child
         void $ key # setAttrs [ classes [ "tree-label" ] ]
         createElement unit view child
      pure rootElement

   setSelection :: ConstrArg -> Unit -> Dict (View × View) -> Select -> D3.Selection -> Effect Unit
   setSelection arg _ views select rootElement =
      sequence_ $
         flip mapWithIndex (toUnfoldable views :: Array _) \i (x × k_view × view) -> do
            child <- rootElement # D3.select (D3.nthChildOf D3.scope (i + 1))
            child1 <- child # D3.select (D3.nthChildOf D3.scope 1)
            child2 <- child # D3.select (D3.nthChildOf D3.scope 2)
            void $ setSelection arg unit k_view (\_ -> pure unit) child1 -- TODO: revisit!
            void $ setSelection arg unit view (dictVal x >>> select) child2

type Select = SetSel (Val (SelStates 𝔹)) -> Effect Unit

foreign import mouseButton :: Event -> Int

registerMouseListeners :: (Event -> Effect Unit) -> D3.Selection -> Effect Unit
registerMouseListeners handler element = do
   click <- eventListener \event -> when (mouseButton event == 0) (handler event)
   hover <- eventListener handler
   void $ element # on (EventType "mousedown") click
   void $ element # on (EventType "mouseenter") hover
   void $ element # on (EventType "mouseleave") hover

type UIHelpers =
   { val :: forall a. Selectable a -> a
   , selState :: forall a. Selectable a -> SelStates 𝕊
   , join :: SelStates 𝕊 -> SelStates 𝕊 -> SelStates 𝕊
   , selClasses :: String
   , selClassesFor :: SelStates 𝕊 -> String
   }

uiHelpers :: UIHelpers
uiHelpers =
   { val: fst
   , selState: snd
   , join: (∨)
   , selClasses
   , selClassesFor
   }

data Filter = Everything | Interactive | Relevant

type Options =
   { fluidSrcPaths :: Array Folder
   , inputs :: Array Var
   , query :: Boolean -- show documented intermediates
   , ignoreInputs :: Selector EnvWithDocs -- input positions left out of linked queries; retire with #1585
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

data Direction = LinkedInputs | LinkedOutputs | Intermediates

type Fig =
   { spec :: Options
   , s :: S.Stmt
   , ρ :: EnvWithDocs (SelStates 𝔹)
   , v :: ValWithDoc (SelStates 𝔹)
   , ι :: Labelling (ValWithDoc (SelStates 𝔹))
   , dir :: Selection Direction
   , linkedInputs :: SelectionType -> EnvWithDocs (SelStates 𝔹) -> QueryResult
   , linkedOutputs :: SelectionType -> ValWithDoc (SelStates 𝔹) -> QueryResult
   , linkIntermediates :: Labelling (ValWithDoc (SelStates 𝔹)) -> QueryResult
   , in_views :: Dict (Maybe View) -- strengthen this
   , out_view :: Maybe View
   , intermediate_views :: Labelling (Maybe View)
   , inertι :: Labelling (ValWithDoc 𝔹) -- inert positions of each intermediate
   , fieldIndex :: FieldIndex
   }

-- Inputs, output and intermediates reached by a query.
type QueryResult = EnvWithDocs (SelState 𝔹) × ValWithDoc (SelState 𝔹) × Labelling (ValWithDoc 𝔹)

-- ======================
-- boilerplate
-- ======================

derive instance Eq Direction
derive instance Eq Filter

instance decodeJsonFilter :: DecodeJson Filter where
   decodeJson json = do
      s <- decodeString json
      case s of
         "Everything" -> pure Everything
         "Interactive" -> pure Interactive
         "Relevant" -> pure Relevant
         _ -> Left $ TypeMismatch $ "Unknown Filter: " <> s
