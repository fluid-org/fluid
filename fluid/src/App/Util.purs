module App.Util where

import Prelude hiding (absurd, join)

import Bind (Bind, Var, (↦))
import Control.Apply (lift2)
import Data.Array (concat)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Generic.Rep (class Generic)
import Data.Int (fromStringAs, hexadecimal, toStringAs)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Profunctor.Strong ((&&&), first)
import Data.Show.Generic (genericShow)
import Data.String (joinWith, length)
import Data.String.CodeUnits (drop, take)
import Data.Traversable (sequence, sequence_)
import Data.Tuple (fst, snd)
import Dict (Dict)
import Effect (Effect)
import Effect.Aff (Aff, runAff_)
import Effect.Class.Console (log)
import Foreign.Object (Object, empty, fromFoldable, union)
import Lattice (class BoundedJoinSemilattice, class BoundedMeetSemilattice, class JoinSemilattice, class MeetSemilattice, 𝔹, bot, neg, (∧), (∨))
import Pretty (prettyP)
import Primitive (as, intOrNumber, unpack')
import Primitive as P
import Test.Util.Debug (tracing)
import Unsafe.Coerce (unsafeCoerce)
import Util (type (×), Endo, definitely', error, shapeMismatch, spyWhen, (×))
import Util.Map (get)
import Val (class Highlightable, Val, highlightIf)
import Web.Event.Event (Event, EventType(..), target, type_)
import Web.Event.EventTarget (EventTarget)

type Selector f = SetSel (f (SelStates 𝔹)) -- modifies selection state
type SetSel a = a -> a × SelectionType

-- Selection can occur on data that can be interacted with, reactive data rather than inert data. Within
-- reactive data, selection has two dimensions: persistent or transient. An element can be persistently *and*
-- transiently selected at the same time; these need to be visually distinct (so that for example clicking
-- during mouseover visibly changes the state). Types of selection are primary/secondary/none. These are
-- visually distinct but not orthogonal; primary should (visually) subsume secondary.

data SelState a
   = Inert
   | Reactive a

newtype SelStates a = SelStates (SelState (Selection a))

inert :: forall a. SelStates a
inert = SelStates Inert

type Selection a = { persistent :: a, transient :: a }

data SelectionType = Persistent | Transient

selStates :: forall a. 𝔹 -> a -> a -> SelStates a
selStates true _ _ = SelStates Inert
selStates false b1 b2 = SelStates $ Reactive { persistent: b1, transient: b2 }

selState :: forall a. 𝔹 -> a -> SelState a
selState true = const Inert
selState false = Reactive

selection :: forall a. 𝔹 -> a -> a -> Selection (SelState a)
selection true _ _ = { persistent: Inert, transient: Inert }
selection false b1 b2 = { persistent: Reactive b1, transient: Reactive b2 }

contents :: forall a. Selectable a -> a
contents = fst

sel :: forall a. Selectable a -> SelStates 𝕊
sel = snd

data 𝕊 = None | Secondary | Primary

type Selectable a = a × SelStates 𝕊

isPrimary :: SelStates 𝕊 -> 𝔹
isPrimary (SelStates Inert) = false
isPrimary (SelStates (Reactive { persistent, transient })) =
   persistent == Primary || transient == Primary

isSecondary :: SelStates 𝕊 -> 𝔹
isSecondary (SelStates Inert) = false
isSecondary (SelStates (Reactive { persistent, transient })) =
   persistent == Secondary || transient == Secondary

isInert :: forall a. SelStates a -> 𝔹
isInert (SelStates Inert) = true
isInert (SelStates (Reactive _)) = false

getSel :: forall a. SelectionType -> SelStates a -> SelState a
getSel selType s = unwrap s <#> case selType of
   Persistent -> _.persistent
   Transient -> _.transient

getPersistent :: forall a. BoundedJoinSemilattice a => SelStates a -> a
getPersistent (SelStates Inert) = bot
getPersistent (SelStates (Reactive { persistent })) = persistent

to𝔹 :: SelState 𝔹 -> 𝔹
to𝔹 Inert = false
to𝔹 (Reactive b) = b

getTransient :: forall a. BoundedJoinSemilattice a => SelStates a -> a
getTransient (SelStates Inert) = bot
getTransient (SelStates (Reactive { transient })) = transient

isPersistent :: SelStates 𝕊 -> 𝔹
isPersistent = getPersistent >>> (_ /= None)

isTransient :: SelStates 𝕊 -> 𝔹
isTransient = getTransient >>> (_ /= None)

-- UI sometimes merges 𝕊 values, e.g. x and y coordinates in a scatter plot
compare' :: 𝕊 -> 𝕊 -> Ordering
compare' None None = EQ
compare' None _ = LT
compare' Secondary Secondary = EQ
compare' Secondary Primary = LT
compare' Secondary None = GT
compare' Primary Primary = EQ
compare' Primary _ = GT

instance Eq 𝕊 where
   eq s s' = compare' s s' == EQ

instance Ord 𝕊 where
   compare = compare'

instance JoinSemilattice 𝕊 where
   join = max

instance MeetSemilattice 𝕊 where
   meet = min

instance BoundedJoinSemilattice 𝕊 where
   bot = None

as𝕊 :: 𝔹 -> 𝔹 -> 𝕊
as𝕊 false false = None
as𝕊 false true = Secondary
as𝕊 true false = None -- this should be error absurd, but see case #
as𝕊 true true = Primary

to𝕊 :: 𝔹 -> 𝕊
to𝕊 true = Primary
to𝕊 false = None

primary :: forall f. Apply f => f (SelState 𝔹) -> f (SelState 𝕊)
primary x = (to𝕊 <$> _) <$> x

primaryOrSecondary :: forall f. Apply f => SelectionType -> f (SelStates 𝔹) -> f (SelState 𝔹) -> f (SelState 𝕊)
primaryOrSecondary selType x x' = lift2 as𝕊 <$> (getSel selType <$> x) <*> x'

unselected :: SelStates 𝔹
unselected = SelStates $ Reactive { persistent: false, transient: false }

get_intOrNumber :: Var -> Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> Selectable Number
get_intOrNumber x r = first as (unpack' intOrNumber (snd (get x r)))

-- Assumes fields are all of primitive type.
dict :: forall a. (Dict (SelStates 𝕊 × Val (SelStates 𝕊)) -> a) -> Val (SelStates 𝕊) -> a
dict toDict v = toDict (fst (unpack' P.dict v))

runAffs_ :: forall a. (a -> Effect Unit) -> Array (Aff a) -> Effect Unit
runAffs_ f as = flip runAff_ (sequence as) case _ of
   Left err -> log $ show err
   Right as' -> as' <#> f # sequence_

selectionEventData' :: forall a. Event -> a × SetSel (Val (SelStates 𝔹))
selectionEventData' = (eventData &&& type_ >>> selector)

eventData :: forall a. Event -> a
eventData = target >>> unsafeEventData
   where
   unsafeEventData :: Maybe EventTarget -> a
   unsafeEventData tgt = (unsafeCoerce $ definitely' tgt).__data__

selector :: EventType -> SetSel (Val (SelStates 𝔹))
selector (EventType ev) v =
   (reportSelStates <<< setSel <$> reportTarget v) × selType
   where
   setSel :: Endo (SelStates 𝔹)
   setSel (SelStates Inert) = SelStates Inert
   setSel (SelStates (Reactive sel'))
      | ev == "mousedown" = SelStates (Reactive (sel' { persistent = neg sel'.persistent }))
      | ev == "mouseenter" = SelStates (Reactive (sel' { transient = true }))
      | ev == "mouseleave" = SelStates (Reactive (sel' { transient = false }))
      | otherwise = error "Unsupported event type"

   reportSelStates = spyWhen tracing.mouseEvent "to " show
   reportTarget = spyWhen tracing.mouseEvent "Setting selStates of " prettyP

   selType :: SelectionType
   selType
      | ev == "mousedown" = Persistent
      | ev == "mouseenter" = Transient
      | ev == "mouseleave" = Transient
      | otherwise = error "Unsupported event type"

-- https://stackoverflow.com/questions/5560248
colorShade :: String -> Int -> String
colorShade col n =
   -- remove and reinstate leading "#"
   "#" <> shade (take 2 $ drop 1 col) <> shade (take 2 $ drop 3 col) <> shade (take 2 $ drop 5 col)
   where
   shade :: String -> String
   shade rgbComponent =
      definitely' (fromStringAs hexadecimal rgbComponent) + n
         # clamp 0 255
         # (\x -> let s = toStringAs hexadecimal x in if length s == 1 then "0" <> s else s)

css
   :: { sel ::
           { transient ::
                { primary :: String
                , secondary :: String
                }
           , persistent ::
                { primary :: String
                , secondary :: String
                }
           }
      , inert :: String
      }
css =
   { sel:
        { transient:
             { primary: "selected-primary-transient"
             , secondary: "selected-secondary-transient"
             }
        , persistent:
             { primary: "selected-primary-persistent"
             , secondary: "selected-secondary-persistent"
             }
        }
   , inert: "inert"
   }

classes :: Array String -> Bind String
classes = joinWith " " >>> ("class" ↦ _)

selClasses :: String
selClasses = joinWith " " $
   [ css.sel.transient.primary
   , css.sel.transient.secondary
   , css.sel.persistent.primary
   , css.sel.persistent.secondary
   , css.inert
   ]

selClassesFor :: SelStates 𝕊 -> String
selClassesFor (SelStates Inert) = css.inert
selClassesFor t =
   joinWith " " $ concat
      [ case getPersistent t of
           Secondary -> [ css.sel.persistent.secondary ]
           Primary -> [ css.sel.persistent.primary ]
           None -> []
      , case getTransient t of
           Secondary -> [ css.sel.transient.secondary ]
           Primary -> [ css.sel.transient.primary ]
           None -> []
      ]

type Attrs = Array (Bind String)

attrs :: Array Attrs -> Object String
attrs = foldl (\kvs -> (kvs `union` _) <<< fromFoldable) empty

newtype Dimensions a = Dimensions
   { width :: a
   , height :: a
   }

-- ======================
-- boilerplate
-- ======================
derive instance Generic 𝕊 _
instance Show 𝕊 where
   show = genericShow

derive instance Eq SelectionType

derive instance Functor SelState
derive instance Functor SelStates
derive instance Generic (SelStates a) _
derive instance Generic (SelState a) _

derive instance Newtype (SelStates a) _

instance Show a => Show (SelState a) where
   show = genericShow

instance Show a => Show (SelStates a) where
   show = genericShow

instance Apply SelState where
   apply Inert Inert = Inert
   apply (Reactive fs) (Reactive s) =
      Reactive (fs s)
   apply _ _ = shapeMismatch unit

instance Apply SelStates where
   apply (SelStates Inert) (SelStates Inert) = SelStates Inert
   apply (SelStates (Reactive { persistent: fs, transient: fs' })) (SelStates (Reactive { persistent: s, transient: s' })) =
      SelStates (Reactive { persistent: fs s, transient: fs' s' })
   apply _ _ = shapeMismatch unit

instance JoinSemilattice a => JoinSemilattice (SelState a)
   where
   join s Inert = s
   join Inert s = s
   join (Reactive s) (Reactive s') =
      Reactive (s ∨ s')

-- This SelStates boilerplate preferable to Selection-as-newtype boilerplate
instance JoinSemilattice a => JoinSemilattice (SelStates a) where
   join (SelStates s) (SelStates Inert) = SelStates s
   join (SelStates Inert) (SelStates s) = SelStates s
   join (SelStates (Reactive { persistent, transient })) (SelStates (Reactive { persistent: persistent', transient: transient' })) =
      SelStates (Reactive { persistent: persistent ∨ persistent', transient: transient ∨ transient' })

instance MeetSemilattice a => MeetSemilattice (SelState a)
   where
   meet _ Inert = Inert
   meet Inert _ = Inert
   meet (Reactive s) (Reactive s') =
      Reactive (s ∧ s')

instance MeetSemilattice a => MeetSemilattice (SelStates a)
   where
   meet _ (SelStates Inert) = SelStates Inert
   meet (SelStates Inert) _ = SelStates Inert
   meet (SelStates (Reactive { persistent, transient })) (SelStates (Reactive { persistent: persistent', transient: transient' })) =
      SelStates (Reactive { persistent: persistent ∧ persistent', transient: transient ∧ transient' })

instance BoundedJoinSemilattice a => BoundedJoinSemilattice (SelState a)
   where
   bot = Inert

instance BoundedJoinSemilattice a => BoundedJoinSemilattice (SelStates a)
   where
   bot = SelStates Inert

instance (Bounded a, BoundedMeetSemilattice a) => BoundedMeetSemilattice (SelState a)
   where
   top = Reactive top

instance (Bounded a, BoundedMeetSemilattice a) => BoundedMeetSemilattice (SelStates a)
   where
   top = SelStates (Reactive { persistent: top, transient: top })

derive instance Eq a => Eq (SelState a)

derive instance Eq a => Eq (SelStates a)

instance (Highlightable a, JoinSemilattice a) => Highlightable (SelState a) where
   highlightIf Inert = highlightIf false
   highlightIf (Reactive s) = highlightIf s

instance (Highlightable a, JoinSemilattice a) => Highlightable (SelStates a) where
   highlightIf (SelStates Inert) = highlightIf false
   highlightIf (SelStates (Reactive { persistent, transient })) = highlightIf (persistent ∨ transient)

derive instance Newtype (Dimensions a) _
derive instance Functor Dimensions
derive instance Generic (Dimensions a) _
instance Show a => Show (Dimensions a) where
   show = genericShow
