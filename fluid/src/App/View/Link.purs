module Link where

import Prelude hiding (join)

import App.Util (SelStates, Selectable, 𝕊, classes, selectionEventData')
import App.Util.Selector (ConstrArg, ViewSelSetter)
import App.View.Text (class Textual, textAttrs)
import App.View.Util (class Viewable, Select, registerMouseListeners)
import App.View.Util.D3 (create, setDatum, setStyles, setText)
import App.View.Util.D3 as D3
import Data.Foldable (foldr)
import Data.List (List(..), (:))
import Data.Profunctor.Strong (first)
import Data.Tuple (uncurry)
import DataType (cLink)
import Effect (Effect)
import Lattice (bot, join)
import Partial.Unsafe (unsafePartial)
import Util ((×))
import Val (BaseVal(..), Val(..))

data Link = Link (Val (SelStates 𝕊)) (Selectable String)

linkContents :: Link -> String
linkContents (Link _ (s × _)) = s

instance Viewable Link Unit where
   isLeaf = const true

   createElement :: Unit -> Link -> D3.Selection -> Effect D3.Selection
   createElement _ link parent = do
      rootElement <- parent # create D3.Text [ classes [ "link" ] ]
      rootElement # setText (linkContents link) >>= setDatum link

   setSelection :: ConstrArg -> Unit -> Link -> Select -> D3.Selection -> Effect Unit
   setSelection _ _ link redraw rootElement = do
      rootElement # setStyles (textAttrs link) >>= registerMouseListeners (redraw <<< uncurry selLink <<< selectionEventData')
      where
      selLink :: ViewSelSetter Link
      selLink _ δv = unsafePartial $ case _ of
         (Val α (Constr c (v1 : v2 : Nil))) | c == cLink ->
            first (\v1' -> Val α (Constr c (v1' : v2 : Nil))) (δv v1)

instance Textual Link where
   getText (Link v (s × _)) = s × foldr join bot v
