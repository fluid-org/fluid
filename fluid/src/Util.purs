module Util where

import Prelude hiding (absurd)

import Control.Alt ((<|>))
import Control.Apply (lift2)
import Control.Monad.Error.Class (class MonadError, class MonadThrow, catchError, liftEither, throwError)
import Control.Monad.Except (Except, ExceptT, runExcept)
import Control.MonadPlus (class Alt, class Alternative, guard)
import Data.Array ((!!), updateAt)
import Data.Array as A
import Data.Array.NonEmpty (NonEmptyArray, fromArray)
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, foldr)
import Data.Functor.Compose (Compose)
import Data.Functor.Product (Product)
import Data.Identity (Identity(..))
import Data.List (List, intercalate)
import Data.List as L
import Data.List.NonEmpty (NonEmptyList(..), fromList)
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.NonEmpty ((:|))
import Data.Profunctor.Strong (class Strong, (&&&), (***))
import Data.Set (Set)
import Data.Set as Set
import Data.Set.NonEmpty (NonEmptySet)
import Data.Set.NonEmpty as NonEmptySet
import Data.Tuple (Tuple(..), fst, snd)
import Debug as Debug
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Effect.Class.Console (log)
import Effect.Exception (Error, message)
import Effect.Exception (error) as E
import Effect.Unsafe (unsafePerformEffect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Test.Util.Debug (checking)

debug
   :: { logging :: Boolean -- logging via "log"; requires an effect context
      , tracing :: Boolean -- tracing via "trace"; no effect context required
      }

debug =
   { logging: false
   , tracing: true
   }

type Thunk a = Unit -> a -- similar to Lazy but without datatype

force :: forall a. Thunk a -> a
force = (_ $ unit)

type 𝔹 = Boolean

-- Surely × should have higher precedence than + by convention..
infixr 6 type Tuple as × -- standard library has \/
infixr 6 Tuple as ×

-- Similar to Data.Tuple.Nested but without terminating unit.
tuple3 :: forall a b c. a -> b -> c -> a × b × c
tuple3 a b c = a × b × c

uncurry3 :: forall a b c r. (a -> b -> c -> r) -> a × b × c -> r
uncurry3 f (a × b × c) = f a b c

infixr 6 type Either as + -- standard library has \/

type AffError m a = MonadAff m => MonadError Error m => m a
type EffectError m a = MonadEffect m => MonadError Error m => m a

-- Rethink: has same name as Effect.Exception.error but without the type :-o
error :: ∀ a. String -> a
error msg = unsafePerformEffect (throw msg)

shapeMismatch :: forall a. Thunk a
shapeMismatch _ = error "Shape mismatch"

throw :: forall m a. MonadThrow Error m => String -> m a
throw = throwError <<< E.error

assert :: ∀ a. Boolean -> Endo a
assert = assertWith ""

assertWith :: ∀ a. String -> Boolean -> Endo a
assertWith _ true = identity
assertWith msg false = \_ -> error ("Assertion failure: " <> msg)

assertWhen :: ∀ a. Boolean -> String -> Thunk Boolean -> Endo a
assertWhen false _ = const identity
assertWhen true msg = force >>> assertWith msg

validate :: ∀ a. String -> (a -> Boolean) -> Endo a
validate = validateWhen true

validateWhen :: ∀ a. Boolean -> String -> (a -> Boolean) -> Endo a
validateWhen b msg p a = assertWhen b msg (\_ -> p a) a

-- Prefer this to Debug.spy/spyWith (Debug.spyWith doesn't seem to work).
spy :: forall a b. String -> (a -> b) -> Endo a
spy = spyWhen true

spyWhen :: forall a b. Boolean -> String -> (a -> b) -> Endo a
spyWhen true msg show x | debug.tracing == true =
   Debug.trace (msg <> ":") \_ -> Debug.trace (show x) (const x)
spyWhen _ _ _ x = x

spyFunWhen :: forall a b c1 c2. Boolean -> String -> (a -> c1) -> (b -> c2) -> Endo (a -> b)
spyFunWhen b s showIn showOut f =
   unwrap <<< spyFunWhenM b s showIn showOut (Identity <<< f)

spyFunWhenM :: forall a b c1 c2 m. Functor m => Boolean -> String -> (a -> c1) -> (b -> c2) -> Endo (a -> m b)
spyFunWhenM b s showIn showOut f x =
   f (x # spyWhen b (s <> " input") showIn) <#> spyWhen b (s <> " output") showOut

trace :: forall m. Applicative m => String -> m Unit
trace = traceWhen true

traceWhen :: forall m. Applicative m => Boolean -> String -> m Unit
traceWhen true msg | debug.tracing == true = Debug.trace msg \_ -> pure unit
traceWhen _ _ = pure unit

log' :: forall m. MonadEffect m => String -> m Unit
log' msg = when debug.logging (log msg)

-- First element that occurs earlier in the list.
firstDuplicate :: forall a. Ord a => List a -> Maybe a
firstDuplicate xs = L.head (xs L.\\ L.nub xs)

absurd :: String
absurd = "absurd"

unimplemented :: String
unimplemented = "unimplemented"

whenever :: forall a. Boolean -> a -> Maybe a
whenever false = const Nothing
whenever true = Just

definitely :: forall a. String -> Maybe a -> a
definitely _ (Just a) = a
definitely msg Nothing = error ("definitely " <> msg)

definitely' :: forall a. Maybe a -> a
definitely' = definitely absurd

onlyIf :: forall m a. Bind m => Alternative m => Boolean -> a -> m a
onlyIf b a = do
   guard b
   pure a

type MayFail a = Except Error a
type MayFailT m = ExceptT Error m

orElse :: forall a m. MonadThrow Error m => String -> Maybe a -> m a
orElse s Nothing = throw s
orElse _ (Just x) = pure x

throwLeft :: forall a e m. MonadError Error m => Show e => Either e a -> m a
throwLeft = liftEither <<< lmap (E.error <<< show)

orThrow :: forall a m. MonadThrow Error m => Either String a -> m a
orThrow (Left s) = throw s
orThrow (Right x) = pure x

defined :: forall a. MayFail a -> a
defined = runExcept >>> case _ of
   Right x -> x
   Left e -> error $ show e

definedWith :: String -> forall a. MayFail a -> a
definedWith msg = defined <<< withMsg msg

withMsg :: forall a m. MonadError Error m => String -> Endo (m a)
withMsg msg m = catchError m \e ->
   throw $ message e <> if msg == "" then "" else ("\n" <> msg)

check :: forall m. MonadThrow Error m => Boolean -> String -> m Unit
check false = throw
check true = const $ pure unit

-- Like shouldSatisfy in Test.Spec.Assertions but with error message.
checkSatisfies :: forall m a. MonadThrow Error m => Show a => String -> a -> (a -> Boolean) -> m Unit
checkSatisfies msg x pred =
   unless (pred x) $
      throw (show x <> " doesn't satisfy " <> msg)

mayEq :: forall a. Eq a => a -> a -> Maybe a
mayEq x x' = whenever (x == x') x

mustEq :: forall a. Eq a => Show a => a -> Endo a
mustEq x x' = assertWhen checking.mustEq "mustEq" (\_ -> x == x') x

unionWithMaybe :: forall a b. Ord a => (b -> b -> Maybe b) -> Map a b -> Map a b -> Map a (Maybe b)
unionWithMaybe f m m' = M.unionWith (\x -> lift2 f x >>> join) (Just <$> m) (Just <$> m')

mayFailEq :: forall a m. MonadThrow Error m => Show a => Eq a => a -> a -> m a
mayFailEq x x' = x ≟ x' # orElse (show x <> " ≠ " <> show x')

infixl 4 mayEq as ≟
infixl 4 mayFailEq as ≞
infixl 4 mustEq as ≜

-- could be more efficient
intersperse :: forall a. a -> Endo (List a)
intersperse x xs = intercalate (pure x) (pure <$> xs)

om :: forall a b c m. Monad m => (a -> b -> m c) -> m a -> b -> m c
om f m x = m >>= flip f x

bind2Flipped :: forall m a b c. Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2Flipped f x y = join (lift2 f x y)

infixr 1 bind2Flipped as =<<<

-- like Endo in prelude but specialised to functions, to avoid newtype clutter
type Endo a = a -> a

-- version of this in Data.Array uses unsafePartial
class UnsafeArray (f :: Type -> Type) where
   unsafeIndex :: forall a. f a -> Int -> a
   unsafeUpdateAt :: forall a. Int -> a -> Endo (f a)

withinBounds :: forall a. Maybe a -> a
withinBounds = definitely "index within bounds"

instance UnsafeArray Array where
   unsafeIndex xs i = withinBounds (xs !! i)
   unsafeUpdateAt i x = updateAt i x >>> withinBounds

instance UnsafeArray NonEmptyArray where
   unsafeIndex xs i = withinBounds (xs NEA.!! i)
   unsafeUpdateAt i x = NEA.updateAt i x >>> withinBounds

instance UnsafeArray List where
   unsafeIndex xs i = withinBounds (xs L.!! i)
   unsafeUpdateAt i x = L.updateAt i x >>> withinBounds

infixl 8 unsafeIndex as !

-- Similar to NonEmptyList.appendFoldable but without copying the list
appendList :: forall a. NonEmptyList a -> List a -> NonEmptyList a
appendList (NonEmptyList (x :| xs)) ys = NonEmptyList (x :| (xs <> ys))

-- Also defined in Data.Profunctor.Monoidal, but perhaps not "standard library"
dup :: forall a. a -> a × a
dup x = x × x

unzip :: forall t a b. Functor t => t (a × b) -> t a × t b
unzip = (fst <$> _) &&& (snd <$> _)

both :: forall a b c. Category a => Strong a => a b c -> a (b × b) (c × c)
both f = f *** f

with :: forall a b. a -> (a -> b) -> a × b
with x f = x × f x

assoc1 :: forall a b c. (a × b) × c -> a × (b × c)
assoc1 ((a × b) × c) = a × (b × c)

assoc2 :: forall a b c. a × (b × c) -> (a × b) × c
assoc2 (a × (b × c)) = (a × b) × c

-- Not sure what provision there is for composition of functors with types
data WithTypeLeft (t :: Type) (f :: Type -> Type) a = WithTypeLeft t (f a)

infixr 6 type WithTypeLeft as <×|
infixr 6 WithTypeLeft as <×|

derive instance Functor f => Functor (t <×| f)

infixr 9 type Compose as ○
infixr 7 type Product as *

slipl :: forall a b c d. (a -> b -> c -> d) -> c -> a -> b -> d
slipl f c a b = f a b c

infixl 8 slipl as ~~$

-- Haven't found this yet in PureScript
concatM :: forall f m a. Foldable f => Monad m => f (a -> m a) -> a -> m a
concatM = foldr (>=>) pure

findM
   :: forall m f a b t
    . Alt t
   => Monad m
   => Foldable f
   => f a
   -> (a -> m (t b))
   -> t b
   -> m (t b)
findM xs f base =
   foldr step (pure base) xs
   where
   step :: a -> m (t b) -> m (t b)
   step x acc = acc `lift2 (<|>)` f x

infixr 7 Set.intersection as ∩
infixl 4 Set.subset as ⊆

-- Simplify overloading.
class Singleton f where
   singleton :: forall a. a -> f a

instance Singleton Array where
   singleton = pure

instance Singleton List where
   singleton = pure

instance Singleton NonEmptyList where
   singleton = pure

instance Singleton Set where
   singleton = Set.singleton

instance Singleton NonEmptySet where
   singleton = NonEmptySet.singleton

class NonEmpty (f :: Type -> Type) (g :: Type -> Type) | f -> g where
   nonEmpty :: forall a. f a -> g a
   init :: forall a. g a -> f a
   tail :: forall a. g a -> f a

instance NonEmpty List NonEmptyList where
   nonEmpty = definitely "non-empty" <<< fromList
   init = NEL.init
   tail = NEL.tail

instance NonEmpty Array NonEmptyArray where
   nonEmpty = definitely "non-empty" <<< fromArray
   init = NEA.init
   tail = NEA.tail

class IsEmpty a where
   isEmpty :: a -> Boolean

instance IsEmpty (Set a) where
   isEmpty = Set.isEmpty

instance IsEmpty (Object a) where
   isEmpty = Object.isEmpty

-- Foldable.length returns an arbitrary semiring which is a bit too general
class Length (f :: Type -> Type) where
   length :: forall a. f a -> Int

instance Length List where
   length = L.length

instance Length Array where
   length = A.length

class Zip (f :: Type -> Type) where
   zip :: forall a b. f a -> f b -> f (a × b)
   zipWith :: forall a b c. (a -> b -> c) -> f a -> f b -> f c

instance Zip Array where
   zip = A.zip
   zipWith = A.zipWith

instance Zip List where
   zip = L.zip
   zipWith = L.zipWith
