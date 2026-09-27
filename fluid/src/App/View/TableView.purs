module App.View.TableView where

import Prelude hiding (absurd)

import App.Util (SelStates, 𝕊(..), classes, getPersistent, getTransient, isInert, isTransient, selClasses, selClassesFor, selectionEventData')
import App.Util.Selector (ConstrArg, ViewSelSetter, dictVal, listElement)
import App.View.Util (class Viewable, Filter(..), Select, registerMouseListeners)
import App.View.Util.D3 (ElementType(..), classed, create, datum, select, selectAll, setDatum, setStyles, setText)
import App.View.Util.D3 as D3
import Bind ((↦))
import Data.Array (any, elem, filter, partition, sort, transpose, (..))
import Data.Array.NonEmpty (head)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Maybe (Maybe(..), isNothing)
import Data.Number.Format (fixed, toStringWith)
import Data.Set (toUnfoldable)
import Data.Traversable (for)
import Data.Tuple (snd, uncurry)
import Dict (Dict)
import Effect (Effect, foreachE)
import Literal (Literal(Int, Float, Str))
import Util (type (×), absurd, error, length, nonEmpty, (!), (×))
import Util.Map (get, keys)
import Val (Array2, BaseVal(..), Val(..))

type Record' = Array (Val (SelStates 𝕊)) -- somewhat anomalous, as elsewhere we have Selectables

-- Homogeneous array of records with fields of primitive type; each row has same length as colNames.
newtype TableView = TableView
   { title :: String
   , rowFilter :: Filter
   , colNames :: Array String
   , rows :: Array Record' -- non-empty?
   }

-- helpers to decompose array of records represented as dictionaries into colNames and rows
headers :: Array (Dict (SelStates 𝕊 × Val (SelStates 𝕊))) -> Array String
headers records = (sort <<< toUnfoldable <<< keys <<< head <<< nonEmpty) records

arrayDictToArray2 :: forall a. Array String -> Array (Dict a) -> Array2 a
arrayDictToArray2 = map <<< flip (map <<< flip get)

rowKey :: String
rowKey = "__n"

cell_selClassesFor :: String -> SelStates 𝕊 -> String
cell_selClassesFor colName s
   | colName == rowKey = ""
   | otherwise = selClassesFor s

visible :: Filter -> Val (SelStates 𝕊) -> Boolean
visible filter (Val α _ _) = visible' filter α
   where
   visible' Everything = const true
   visible' Interactive = not isInert
   visible' Relevant = not (isNone || isInert)

   isNone :: SelStates 𝕊 -> Boolean
   isNone a = getPersistent a == None && getTransient a == None

prim :: Val (SelStates 𝕊) -> String
prim (Val _ _ v) = v # case _ of
   Lit (Int n) -> show n
   Lit (Float n) -> toStringWith (fixed 2) n
   Lit (Str s) -> s
   _ -> error $ "TableView only supports primitive values."

data BorderVis = Transparent | Faint

unhighlightedBorder :: BorderVis -> String
unhighlightedBorder Transparent = "1px solid transparent"
unhighlightedBorder Faint = "1px solid #eee"

highlightedBorder :: BorderVis -> String
highlightedBorder _ = "1px solid blue"

instance Viewable TableView Unit where
   isLeaf = const false

   setSelection :: ConstrArg -> Unit -> TableView -> Select -> D3.Selection -> Effect Unit
   setSelection _ _ (TableView { title, colNames, rows, rowFilter }) redraw rootElement = do
      cells <- rootElement # selectAll ".table-cell"
      foreachE cells \cell -> do
         { i, j, colName } :: CellIndex <- datum cell
         if i == -1 || j == -1 then pure unit
         else do
            cell # classed selClasses false
               >>= classed (cell_selClassesFor colName (rows ! i ! j # \(Val α _ _) -> α)) true
               >>= registerMouseListeners (redraw <<< uncurry tableViewSelSetter <<< selectionEventData')
         void $ cell # setStyles
            [ "border-right" ↦ border Faint (hasRightBorder i j) (isNothing $ column_visibleSucc j)
            , "border-bottom" ↦ border Transparent (hasBottomBorder i j) (i == length rows - 1)
            ]
      hiddenRows <- hideRows
      hiddenColumns <- hideColumns
      setCaption hiddenRows hiddenColumns
      where

      row_isVisible :: Array Boolean
      row_isVisible = rows <#> any (visible rowFilter)

      column_isVisible :: Array Boolean
      column_isVisible = transpose rows <#> any (visible filter')
         where
         -- arbitrarily (for now) enable column filtering when there are a lot of columns
         filter' = if length colNames >= 10 then Interactive else Everything

      hideRows :: Effect Int
      hideRows = do
         rows' <- rootElement # selectAll ".table-row"
         { no: hidden, yes: visible' } <- partition snd <$> for rows' \row -> do
            { i } <- datum row
            pure (row × row_isVisible ! i)
         foreachE hidden $ \(row × _) ->
            void $ classed "hidden" true row
         foreachE visible' $ \(row × _) ->
            void $ classed "hidden" false row
         pure (length hidden)

      hideColumns :: Effect Int
      hideColumns = do
         let hiddenColumns = filter ((!) column_isVisible >>> not) (0 .. (length colNames - 1))
         cells <- rootElement # selectAll ".table-cell"
         foreachE cells \cell -> do
            { j } :: CellIndex <- datum cell
            void $
               if j `elem` hiddenColumns then classed "hidden" true cell
               else classed "hidden" false cell
         pure (length hiddenColumns)

      setCaption :: Int -> Int -> Effect Unit
      setCaption hiddenRows hiddenColumns = do
         void $ rootElement # select ".table-caption" >>= setText caption
         where
         caption = title <> " ("
            <> (show (length rows - hiddenRows) <> " of " <> show (length rows))
            <> " × "
            <> (show (length colNames - hiddenColumns) <> " of " <> show (length colNames))
            <> ")"

      row_visibleSucc :: Int -> Maybe Int
      row_visibleSucc i
         | i == length rows - 1 = Nothing
         | row_isVisible ! (i + 1) = Just (i + 1)
         | otherwise = row_visibleSucc (i + 1)

      -- For a non-header (>=0) row, the immediately prior visible row (potentially the header)
      row_visiblePred :: Int -> Int
      row_visiblePred i
         | i < 0 = error absurd
         | i == 0 = -1
         | row_isVisible ! (i - 1) = i - 1
         | otherwise = row_visiblePred (i - 1)

      column_visibleSucc :: Int -> Maybe Int
      column_visibleSucc i
         | i == length colNames - 1 = Nothing
         | column_isVisible ! (i + 1) = Just (i + 1)
         | otherwise = column_visibleSucc (i + 1)

      column_visiblePred :: Int -> Int
      column_visiblePred j
         | j < 0 = error absurd
         | j == 0 = -1
         | column_isVisible ! (j - 1) = j - 1
         | otherwise = column_visiblePred (j - 1)

      border :: BorderVis -> Boolean -> Boolean -> String
      border vis true _ = highlightedBorder vis
      border vis false true = unhighlightedBorder vis
      border _ false false = ""

      hasRightBorder :: Int -> Int -> Boolean
      hasRightBorder i j =
         case column_visibleSucc j of
            Nothing -> isCellTransient i j
            Just j' -> (isCellTransient i j' /= isCellTransient i (column_visiblePred j'))

      hasBottomBorder :: Int -> Int -> Boolean
      hasBottomBorder i j =
         case row_visibleSucc i of
            Nothing -> isCellTransient i j
            Just i' -> (isCellTransient i' j /= isCellTransient (row_visiblePred i') j) && i == i' - 1

      isCellTransient :: Int -> Int -> Boolean
      isCellTransient i j
         | i == -1 || j == -1 = false
         | otherwise = isTransient <<< (\(Val α _ _) -> α) $ rows ! i ! j

      tableViewSelSetter :: ViewSelSetter CellIndex
      tableViewSelSetter { i, colName } = listElement i <<< dictVal colName

   createElement :: Unit -> TableView -> D3.Selection -> Effect D3.Selection
   createElement _ (TableView { colNames, rowFilter, rows }) parent = do
      rootElement <- parent # create Div [ classes [ "table-wrapper" ] ]
      void $ rootElement # create Div -- hard to have Caption element with size independent of table contents
         [ classes [ "title-text", "table-caption" ]
         , "dominant-baseline" ↦ "middle"
         , "text-anchor" ↦ "left"
         ]
      table <- rootElement # create Table [ classes [ "table-view" ] ]
      let colNames' = [ rowKey ] <> colNames
      table # createHeader colNames'
      body <- table # create TBody []
      forWithIndex_ rows \i row -> do
         row' <- body # create TR [ classes [ "table-row" ] ] >>= setDatum { i }
         forWithIndex_ ([ show (i + 1) ] <> (row <#> prim)) \j value -> do
            row' # create TD [ classes if j >= 0 then [ "table-cell" ] else [] ]
               >>= setStyles [ "border-top" ↦ unhighlightedBorder Transparent, "border-left" ↦ unhighlightedBorder Faint ]
               >>= setText value
               >>= setDatum { i, j: j - 1, value, colName: colNames' ! j } -- TODO: rename "value" to "text"?
      pure rootElement
      where
      createHeader colNames' table = do
         row <- table # create THead [] >>= create TR []
         forWithIndex_ colNames' \j colName -> do
            let value = if colName == rowKey then if rowFilter == Relevant then "▸" else "▾" else colName
            row
               # create TH [ classes ([ "table-cell" ] <> cellClasses colName) ]
               >>= setStyles [ "border-left" ↦ unhighlightedBorder Faint ]
               >>= setText value
               >>= setDatum { i: -1, j: j - 1, value, colName: colNames' ! j }

      cellClasses colName
         | colName == rowKey = [ "filter-toggle", "toggle-button" ] -- filter-toggle currently unused
         | otherwise = []

-- 0-based index of selected record and name of field; -1th field name is "__n" (rowKey)
type CellIndex = { i :: Int, j :: Int, colName :: String, value :: String }
