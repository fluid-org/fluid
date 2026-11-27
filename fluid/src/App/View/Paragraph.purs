module App.View.Paragraph where

import Prelude

import App.Util.Selector (ObjArg, listElement)
import App.View.Util (class Viewable, Select, View, createElement, isLeaf, setSelection)
import App.View.Util.D3 (ElementType(..), create)
import App.View.Util.D3 as D3
import Bind ((↦))

import Types.Defs (cParagraph, f_fragments)
import Data.Array (mapWithIndex)
import Data.Foldable (all, for_, sequence_)
import Effect (Effect)

data Paragraph = Paragraph (Array View)

instance Viewable Paragraph Unit where
   isLeaf (Paragraph views) = all isLeaf views

   createElement :: Unit -> Paragraph -> D3.Selection -> Effect D3.Selection
   createElement _ (Paragraph views) parent = do
      rootElement <- parent # create Div [ "class" ↦ "para-text" ]
      for_ views \view -> createElement unit view rootElement
      pure rootElement

   setSelection :: ObjArg -> Unit -> Paragraph -> Select -> D3.Selection -> Effect Unit
   setSelection arg _ (Paragraph views) select rootElement = do
      sequence_ $ flip mapWithIndex views \i view -> do
         child <- rootElement # D3.select (D3.nthChildOf D3.scope (i + 1))
         setSelection arg unit view (listElement i >>> arg cParagraph f_fragments >>> select) child
