module App.View.MatrixView where

import Prelude hiding (absurd)

import App.Util (SelStates, Selectable, classes, 𝕊, isTransient, selClasses, selClassesFor, selectionEventData')
import App.Util.Selector (ViewSelSetter, matrixElement)
import App.View.Util (class Viewable, Select, registerMouseListeners)
import App.View.Util.D3 (ElementType(..), create, setText)
import App.View.Util.D3 as D3
import Bind ((↦), (⟼))
import Data.Array (range)
import Data.FoldableWithIndex (forWithIndex_)
import Data.Int (toNumber)
import Data.Tuple (fst, snd, uncurry)
import Effect (Effect, foreachE)
import Primitive (int, unpack')
import Util ((!), (×))
import Val (Array2, MatrixDim(..), MatrixRep(..))

--  (Rendered) matrices are required to have element type Int for now.
type IntMatrix = { cells :: Array2 (Selectable Int), i :: Int, j :: Int }

newtype MatrixView = MatrixView { title :: String, matrix :: IntMatrix }

createBorders :: IntMatrix -> D3.Selection -> Effect Unit
createBorders matrix rootElement = do
   bordersGrp <- rootElement # create G
      [ "transform" ↦ matrixTranslate
      , "fill" ↦ "currentColor"
      , "stroke" ↦ "blue"
      , "stroke-width" ↦ "0.5"
      ]
   hGrp <- bordersGrp # create G []
   foreachE (range 0 matrix.i) \i ->
      foreachE (range 1 matrix.j) \j -> do
         line <- hGrp # create Line
            [ "x1" ⟼ (j - 1) * cellW
            , "y1" ⟼ i * cellH
            , "x2" ⟼ j * cellW
            , "y2" ⟼ i * cellH
            , classes [ "matrix-cell-hBorder" ]
            ]
         void $ line # D3.setDatum { i, j }
   vGrp <- bordersGrp # create G []
   foreachE (range 1 matrix.i) \i ->
      foreachE (range 0 matrix.j) \j -> do
         line <- vGrp # create Line
            [ "x1" ⟼ j * cellW
            , "y1" ⟼ (i - 1) * cellH
            , "x2" ⟼ j * cellW
            , "y2" ⟼ i * cellH
            , classes [ "matrix-cell-vBorder" ]
            ]
         void $ line # D3.setDatum { i, j }

cellW :: Int
cellW = 30

cellH :: Int
cellH = 30

createRootElement :: String -> IntMatrix -> D3.Selection -> Effect D3.Selection
createRootElement title matrix parent = do
   let
      width = cellW * matrix.j + 1
      height = cellH * matrix.i + 1
      hMargin = cellW / 2
      vMargin = cellH / 2
   svg <- parent # create SVG [ "width" ⟼ width + hMargin, "height" ⟼ height + vMargin ]
   void $ svg
      # create Text
           [ "x" ⟼ hMargin / 2
           , "y" ⟼ vMargin / 2
           , classes [ "title-text" ]
           , "dominant-baseline" ↦ "middle"
           , "text-anchor" ↦ "left"
           ]
      >>= setText (if title == "intermediate" then " " else title)
   pure svg

matrixTranslate :: String
matrixTranslate = "translate(" <> show (0.25 + toNumber cellW / 4.0) <> ", " <> show (0.25 + toNumber cellH / 2.0) <> ")"

createCells :: IntMatrix -> D3.Selection -> Effect Unit
createCells matrix rootElement = do
   matrixGrp <- rootElement # create G
      [ "transform" ↦ matrixTranslate
      , "fill" ↦ "currentColor"
      , "stroke" ↦ "currentColor"
      , "stroke-width" ↦ ".25"
      ]
   forWithIndex_ (range 0 (matrix.i - 1)) \i _ ->
      forWithIndex_ (range 0 (matrix.j - 1)) \j _ -> do
         let n = fst (matrix.cells ! i ! j)
         rect <- matrixGrp # create Rect
            [ "x" ⟼ j * cellW
            , "y" ⟼ i * cellH
            , "width" ⟼ cellW
            , "height" ⟼ cellH
            , classes [ "matrix-cell" ]
            , "stroke-width" ↦ "0.5"
            ]
         void $ rect # D3.setDatum { i, j }
         text <- matrixGrp # create Text
            [ "x" ⟼ toNumber (j * cellW) + toNumber cellW / 2.0
            , "y" ⟼ toNumber (i * cellH) + toNumber cellH / 2.0
            , classes [ "matrix-cell-text" ]
            , "text-anchor" ↦ "middle"
            , "dominant-baseline" ↦ "middle"
            , "pointer-events" ↦ "none"
            ]
         void $ text # D3.setDatum { i, j }
         void $ text # setText (show n)

instance Viewable MatrixView Unit where
   isLeaf = const false
   createElement _ (MatrixView { title, matrix }) parent = do
      rootElement <- createRootElement title matrix parent
      createCells matrix rootElement
      createBorders matrix rootElement
      pure rootElement
   setSelection _ _ (MatrixView { matrix }) select rootElement = do
      setCellSelection matrix select rootElement
      setBorderStyles matrix rootElement

setCellSelection :: IntMatrix -> Select -> D3.Selection -> Effect Unit
setCellSelection matrix select rootElement = do
   cells <- D3.selectAll ".matrix-cell" rootElement
   foreachE cells \cell -> do
      coord :: MatrixCellCoordinate <- D3.datum cell
      let selState = snd (matrix.cells ! coord.i ! coord.j)
      void $ D3.classed selClasses false cell
      void $ D3.classed (selClassesFor selState) true cell
      registerMouseListeners (select <<< uncurry element <<< selectionEventData') cell
   texts <- D3.selectAll ".matrix-cell-text" rootElement
   foreachE texts \text -> do
      coord :: MatrixCellCoordinate <- D3.datum text
      let selState = snd (matrix.cells ! coord.i ! coord.j)
      void $ D3.classed selClasses false text
      void $ D3.classed (selClassesFor selState) true text
   where
   element :: ViewSelSetter MatrixCellCoordinate
   element { i, j } = matrixElement i j

setBorderStyles :: IntMatrix -> D3.Selection -> Effect Unit
setBorderStyles matrix rootElement = do
   hBorders <- D3.selectAll ".matrix-cell-hBorder" rootElement
   foreachE hBorders \border -> do
      coord :: MatrixBorderCoordinate <- D3.datum border
      void $ D3.setAttrs [ "style" ↦ hBorderStyles matrix coord ] border
   vBorders <- D3.selectAll ".matrix-cell-vBorder" rootElement
   foreachE vBorders \border -> do
      coord :: MatrixBorderCoordinate <- D3.datum border
      void $ D3.setAttrs [ "style" ↦ vBorderStyles matrix coord ] border

data ShadowDirection = North | South | East | West | None

hBorderStyles :: IntMatrix -> MatrixBorderCoordinate -> String
hBorderStyles m = borderStyles <<< shadowDirection m
   where
   shadowDirection :: IntMatrix -> MatrixBorderCoordinate -> ShadowDirection
   shadowDirection { cells, i: height } { i, j }
      | i == 0 = if isCellTransient cells i (j - 1) then South else None
      | i == height = if isCellTransient cells (i - 1) (j - 1) then North else None
      | isCellTransient cells i (j - 1) && not isCellTransient cells (i - 1) (j - 1) = South
      | not isCellTransient cells i (j - 1) && isCellTransient cells (i - 1) (j - 1) = North
      | otherwise = None

vBorderStyles :: IntMatrix -> MatrixBorderCoordinate -> String
vBorderStyles m = borderStyles <<< shadowDirection m
   where
   shadowDirection :: IntMatrix -> MatrixBorderCoordinate -> ShadowDirection
   shadowDirection { cells, j: width } { i, j }
      | j == 0 = if isCellTransient cells (i - 1) j then East else None
      | j == width = if isCellTransient cells (i - 1) (j - 1) then West else None
      | isCellTransient cells (i - 1) j && not isCellTransient cells (i - 1) (j - 1) = East
      | not isCellTransient cells (i - 1) j && isCellTransient cells (i - 1) (j - 1) = West
      | otherwise = None

isCellTransient :: forall a. Array2 (Selectable a) -> Int -> Int -> Boolean
isCellTransient arr2d i j = isTransient $ snd $ arr2d ! i ! j

borderStyles :: ShadowDirection -> String
borderStyles North = "filter: drop-shadow(0px -1px 1px blue);"
borderStyles South = "filter: drop-shadow(0px 1px 1px blue);"
borderStyles East = "filter: drop-shadow(1px 0px 1px blue);"
borderStyles West = "filter: drop-shadow(-1px 0px 1px blue);"
borderStyles None = "visibility: hidden;"

matrixRep :: MatrixRep (SelStates 𝕊) -> IntMatrix
matrixRep (MatrixRep (vss × MatrixDim (i × _) × MatrixDim (j × _))) =
   { cells: (unpack' int <$> _) <$> vss, i, j }

-- 1-based indices of selected cell; see data binding in .js
type MatrixCellCoordinate = { i :: Int, j :: Int }
type MatrixBorderCoordinate = { i :: Int, j :: Int }
