module App.View.Util.Axes where

import Prelude

import App.Util (classes)
import App.View.Util.D3 (ElementType(..), create, rotate, selectAll, setAttrs, setStyles, translate, xAxis, yAxis)
import App.View.Util.D3 as D3
import Bind ((↦))
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.List (List(..))
import Data.Maybe (Maybe)
import Data.Nullable (toNullable)
import Types.Defs (cDefault, cRotated)
import Effect (Effect)
import Primitive (ToFrom, typeMismatch)
import Val (BaseVal(..))

data Orientation
   = Default
   | Rotated

-- ======================
-- boilerplate
-- ======================

derive instance Eq Orientation

-- Hefty amount of boilerplate just for a type isomorphic to Bool :-o
orientation :: forall a. ToFrom Orientation a
orientation =
   { pack: case _ of
        Default -> Obj cDefault Nil
        Rotated -> Obj cRotated Nil
   , unpack: case _ of
        Obj c Nil
           | c == cDefault -> Right Default
           | c == cRotated -> Right Rotated
        v -> Left (typeMismatch v "Orientation")
   }

type TickSpec =
   { count :: Number -- approximate, for d3 to choose round values
   , values :: Maybe (Array Number) -- exact positions, overriding count
   , places :: Maybe Int -- decimal places of labels, else JavaScript's default number to string conversion
   }

create_xAxis :: forall a r. D3.Selection -> { x :: a -> Number | r } -> TickSpec -> Int -> Orientation -> Effect D3.Selection
create_xAxis parent' to { count, values, places } y orient = do
   x <- xAxis to count (toNullable values) (toNullable places) =<<
      (parent' # create G [ classes [ "x-axis" ], translate { x: 0, y } ])
   when (orient == Rotated) do
      labels <- x # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "start" ]
   pure x

create_yAxis :: forall a r. D3.Selection -> { y :: a -> Number | r } -> TickSpec -> Orientation -> Effect D3.Selection
create_yAxis parent' to { count, values, places } orient = do
   y <- yAxis to count (toNullable values) (toNullable places) =<<
      (parent' # create G [ classes [ "y-axis" ] ])
   when (orient == Rotated) do
      labels <- y # selectAll "text"
      for_ labels $
         setAttrs [ rotate 45 ] >=> setStyles [ "text-anchor" ↦ "end" ]
   pure y
