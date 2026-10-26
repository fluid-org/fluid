module App.View.Text where

import Prelude

import App.Util (Attrs, Selectable, isPersistent, isPrimary, isSecondary, isTransient, sel, selectionEventData')
import App.Util.Selector (ObjArg, ViewSelSetter)
import App.View.Util (class Viewable, Select, registerMouseListeners)
import App.View.Util.D3 (create, setStyles, setText)
import App.View.Util.D3 as D3
import Bind ((↦))
import Data.Newtype (class Newtype, unwrap)
import Data.Tuple (uncurry)
import Effect (Effect)
import Primitive (dropAnnot)

class Textual a where
   getText :: a -> Selectable String

newtype Text = Text (Selectable String)

instance Viewable Text Unit where
   isLeaf = const true

   createElement :: Unit -> Text -> D3.Selection -> Effect D3.Selection
   createElement _ text parent = do
      rootElement <- parent # create D3.Span []
      rootElement # setText (dropAnnot $ getText text)

   setSelection :: ObjArg -> Unit -> Text -> Select -> D3.Selection -> Effect Unit
   setSelection _ _ text redraw rootElement = do
      rootElement # setStyles (textAttrs text) >>= registerMouseListeners (redraw <<< uncurry textSelector <<< selectionEventData')
      where
      textSelector :: ViewSelSetter Text
      textSelector _ = identity

instance Textual Text where
   getText = unwrap

textAttrs :: ∀ a. Textual a => a -> Attrs
textAttrs text =
   [ "border-bottom" ↦ bottom_border
   , "background" ↦ background
   , "color" ↦ color
   ]
   where
   sel' = sel (getText text)

   bottom_border :: String
   bottom_border
      | isTransient sel' = "1px solid blue"
      | otherwise = "none"

   background :: String
   background
      | isPrimary sel' && isPersistent sel' = "#93E9BE" -- TODO: set these via CSS
      | isSecondary sel' && isPersistent sel' = "rgb(226, 226, 226)"
      | otherwise = "white"

   color :: String
   color
      | isPrimary sel' && isTransient sel' = "blue"
      | otherwise = "black"

type TextElem = { i :: Int }

-- ======================
-- boilerplate
-- ======================

derive instance Newtype Text _
