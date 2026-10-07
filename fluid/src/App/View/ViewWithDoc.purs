module App.View.ViewWithDoc where

import Prelude

import App.Util (SelStates, SetSel)
import App.Util.Selector (ConstrArg, docOf, valOf)
import App.View.Paragraph (Paragraph)
import App.View.Util (HTMLId, View, createElement, setSelection)
import App.View.Util.D3 (isEmpty, rootSelect, select)
import App.View.Util.D3 as D3
import Bind ((↦))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Lattice (𝔹)
import Util (check)
import Val (ValWithDoc)

-- View of a value with the view of its doc, if any.
type ViewWithDoc = { doc :: Maybe Paragraph, view :: View }

type SelectWithDoc = SetSel (ValWithDoc (SelStates 𝔹)) -> Effect Unit

createViewWithDoc :: ViewWithDoc -> D3.Selection -> Effect D3.Selection
createViewWithDoc { doc: Just doc, view } parent = do
   rootElement <- parent # D3.create D3.G []
   void $ createElement unit view rootElement
   void $ createElement unit doc rootElement
   pure rootElement
createViewWithDoc { doc: Nothing, view } parent = createElement unit view parent

-- Selections on the value reach its component, those on the doc its doc.
setSelectionWithDoc :: ConstrArg -> ViewWithDoc -> SelectWithDoc -> D3.Selection -> Effect Unit
setSelectionWithDoc arg { doc: Just doc, view } select' rootElement = do
   viewElem <- rootElement # D3.select (D3.nthChildOf D3.scope 1)
   setSelection arg unit view (valOf >>> select') viewElem
   docElem <- rootElement # D3.select (D3.nthChildOf D3.scope 2)
   setSelection arg unit doc (docOf >>> select') docElem
setSelectionWithDoc arg { doc: Nothing, view } select' rootElement =
   setSelection arg unit view (valOf >>> select') rootElement

drawView :: ConstrArg -> { divId :: HTMLId, suffix :: String, view :: ViewWithDoc } -> SelectWithDoc -> Effect Unit
drawView arg { divId, suffix, view } select' = do
   let childId = divId <> "-" <> suffix
   div <- rootSelect ("#" <> divId)
   isEmpty div <#> not >>= flip check ("Unable to insert figure: no div found with id " <> divId)
   maybeRootElement <- div # select ("#" <> childId)
   setSelectionWithDoc arg view select' =<<
      ( isEmpty maybeRootElement >>=
           if _ then
              createViewWithDoc view div <#> D3.setAttrs [ "id" ↦ childId ] # join
           else pure maybeRootElement
      )
