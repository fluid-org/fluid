module DepGraph where

import Prelude hiding (absurd, compose)

import Control.Apply (lift2)
import Control.Monad.State (class MonadState, execState, gets, modify_)
import Data.Foldable (any, foldMap, foldl, foldr)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map, fromFoldableWith, insertWith, unionWith)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (fst, snd)
import Dict (Dict)
import Lattice (class DepSemiring, ctrlWeight)
import Path (Path, PathSet, Step(..), Vertex(..), members, pathSet, sourceRoot)
import Util (class IsEmpty, type (×), Endo, absurd, assert, error, isEmpty, singleton, (×))
import Util.Map (delete, difference, filterKeys, get, insert, keys, lookup, maplet, toUnfoldable)
import Util.Set (class Set, empty, filter, union, (∈), (∪))

-- Labels with a path to each position
class Traversable f <= Paths f where
   paths :: forall a. f a -> f (Path × a)

positions :: forall f a. Traversable f => f a -> List a
positions = traverse (\a -> modify_ (a : _)) >>> flip execState Nil >>> L.reverse

zeros :: forall f a s. Functor f => Semiring s => f a -> f s
zeros = map (const zero)

scale :: forall f s. Functor f => Semiring s => s -> f s -> f s
scale a = map (mul a)

plus :: forall f s. Apply f => Semiring s => f s -> f s -> f s
plus = lift2 add

-- Control sources, then non-zero weight of every other source
data Support c s = Support c (Map Path s)

instance (Set c Path, Semiring s) => Semigroup (Support c s) where
   append (Support ps ws) (Support ps' ws') = Support (ps ∪ ps') (unionWith add ws ws')

-- Control dependence on each of ps
control :: forall c s. c -> Support c s
control ps = Support ps empty

-- Dependence on p with weight one
unitWeight :: forall c s. Set c Path => Semiring s => Path -> Support c s
unitWeight p = Support empty (maplet p one)

positionsOf :: forall s. Support (Set Path) s -> Set Path
positionsOf (Support ps ws) = ps ∪ keys ws

weights :: forall s. DepSemiring s => Support PathSet s -> Map Path s
weights (Support ps ws) = unionWith add (Set.toMap (members ps) $> ctrlWeight) ws

-- Weights of source positions grouped by source vertex
bySource :: forall a. Map Path a -> Labelling (Map Path a)
bySource ws = fromFoldableWith union $
   (toUnfoldable ws :: List _) <#> case _ of
      (EdgeSrc a : p) × w -> a × maplet p w
      _ -> error absurd

-- Leave control sources unchanged, since control weight absorbs non-zero w
scaleSupport :: forall c s. Eq s => Semiring s => s -> Endo (Support c s)
scaleSupport w support@(Support ps ws)
   | w == one = support
   | otherwise = assert (w /= zero) (Support ps (mul w <$> ws))

-- Sources of the target root, then relation into each part; zero relations absent
data Rel c s = Rel (Support c s) (Map Step (Rel c s))

instance (Set c Path, Semiring s) => Semigroup (Rel c s) where
   append (Rel support rs) (Rel support' rs') = Rel (support <> support') (unionWith append rs rs')

nonZero :: forall c s. IsEmpty c => Rel c s -> Maybe (Rel c s)
nonZero r@(Rel support rs)
   | isEmpty support && isEmpty rs = Nothing
   | otherwise = Just r

-- Relation of the target root to the given sources
onto :: forall c s. Support c s -> Rel c s
onto support = Rel support empty

ι :: forall c s. Set c Path => Semiring s => Path -> Endo (Rel c s)
ι p r = foldr (\step r' -> Rel mempty (maybe empty (maplet step) (nonZero r'))) r p

π :: forall c s. Set c Path => Semiring s => Path -> Endo (Rel c s)
π Nil r = r
π (step : p) (Rel _ rs) = maybe mempty (π p) (lookup step rs)

data Restructuring c
   = Reuse c Path
   | NoReuse c
   | Parts c (Map Step (Restructuring c))
   | ExtendEnv c (Restructuring c) (Dict (Restructuring c))

ctrl :: forall c. Restructuring c -> c
ctrl (Reuse ps _) = ps
ctrl (NoReuse ps) = ps
ctrl (Parts ps _) = ps
ctrl (ExtendEnv ps _ _) = ps

withCtrl :: forall c. Set c Path => c -> Endo (Restructuring c)
withCtrl ps' (Reuse ps p) = Reuse (ps ∪ ps') p
withCtrl ps' (NoReuse ps) = NoReuse (ps ∪ ps')
withCtrl ps' (Parts ps θs) = Parts (ps ∪ ps') θs
withCtrl ps' (ExtendEnv ps θ θs) = ExtendEnv (ps ∪ ps') θ θs

pathAfter :: forall c. Set c Path => Path -> Restructuring c -> Restructuring c
pathAfter Nil θ = θ
pathAfter p@(step : p') θ = (if any intoClosure p then identity else withCtrl (ctrl θ)) case θ of
   Reuse _ q -> Reuse empty (q <> p)
   NoReuse _ -> NoReuse empty
   Parts _ θs -> pathAfter p' (get step θs)
   ExtendEnv _ θ' θs -> case step of
      Binding x | Just θ'' <- lookup x θs -> pathAfter p' θ''
      _ -> pathAfter p θ'
   where
   intoClosure :: Step -> Boolean
   intoClosure ClosureEnv = true
   intoClosure PartialFun = true
   intoClosure (PartialArg _) = true
   intoClosure _ = false

type Dependence c s = Restructuring c × Rel c s

reuse :: forall c s. Set c Path => Semiring s => Path -> Dependence c s
reuse p = Reuse empty p × mempty

-- Add control dependence of the target on each of ps
under :: forall c s. Set c Path => c -> Endo (Dependence c s)
under ps (θ × r) = withCtrl ps θ × r

supp :: forall c s. Set c Path => Semiring s => Dependence c s -> Path -> Support c s
supp (θ × r) q = case pathAfter q θ of
   Reuse ps p -> Support ps (maplet p one)
   θ' -> Support (ctrl θ') empty <> support
   where
   Rel support _ = π q r

-- Control sources which hold every source of every position in qs
supps :: forall s. Semiring s => Dependence PathSet s -> Set Path -> PathSet
supps δ qs = foldMap (supp δ >>> \(Support ps ws) -> ps ∪ foldMap pathSet (keys ws)) qs

restructuringAfter :: forall s. Semiring s => Restructuring (Set Path) -> Dependence PathSet s -> Restructuring PathSet
restructuringAfter (Reuse ps p) δ@(θ × _) = withCtrl (supps δ ps) (pathAfter p θ)
restructuringAfter (NoReuse ps) δ = NoReuse (supps δ ps)
restructuringAfter (Parts ps θs) δ = Parts (supps δ ps) (flip restructuringAfter δ <$> θs)
restructuringAfter (ExtendEnv ps θ θs) δ = ExtendEnv (supps δ ps) (restructuringAfter θ δ) (flip restructuringAfter δ <$> θs)

restructuringAfterRel :: forall s. Semiring s => Restructuring (Set Path) -> Rel PathSet s -> Rel PathSet s
restructuringAfterRel θ r = case θ of
   Reuse _ p -> π p r
   NoReuse _ -> mempty
   Parts _ θs -> Rel mempty (members θs)
   ExtendEnv _ θ' θs -> case restructuringAfterRel θ' r × bindings θs of
      Rel support rs × θs' -> Rel support (members θs' ∪ difference rs θs')
   where
   members = Map.mapMaybe (flip restructuringAfterRel r >>> nonZero)

-- Relation after the relation of a dependence
relAfter :: forall s. DepSemiring s => Rel (Set Path) s -> Dependence PathSet s -> Rel PathSet s
relAfter (Rel (Support ps ws) rs) δ =
   Rel (foldlWithIndex (\p support w -> support <> scaleSupport w (supp δ p)) (Support (supps δ ps) empty) ws)
      (Map.mapMaybe (flip relAfter δ >>> nonZero) rs)

compose :: forall s. DepSemiring s => Dependence (Set Path) s -> Dependence PathSet s -> Dependence PathSet s
compose (θ' × r') δ@(_ × r) = restructuringAfter θ' δ × (restructuringAfterRel θ' r <> relAfter r' δ)

-- Members of an environment by step
bindings :: forall a. Dict a -> Map Step a
bindings ρ = Map.fromFoldable ((toUnfoldable ρ :: List _) <#> \(x × a) -> Binding x × a)

tupling :: forall c s. Set c Path => Semiring s => Map Step (Dependence c s) -> Dependence c s
tupling δs = Parts empty (fst <$> δs) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Dependence of a value built around parts δs, or with nothing reused if δs is empty; root depends on support
construct :: forall c s. Set c Path => Semiring s => Support c s -> Map Step (Dependence c s) -> Dependence c s
construct support δs
   | isEmpty δs = NoReuse empty × onto support
   | otherwise = map (onto support <> _) (tupling δs)

-- Dependence of the environment at position p with members δs replaced or added
extend :: forall c s. Set c Path => Semiring s => Path -> Dict (Dependence c s) -> Dependence c s
extend p δs
   | isEmpty δs = reuse p
   | otherwise = ExtendEnv empty (Reuse empty p) (fst <$> δs) × Rel mempty (Map.mapMaybe (snd >>> nonZero) (bindings δs))

type Labelling a = Map Vertex a

-- Vertices which hold the source positions
vertices :: forall s. Dependence (Set Path) s -> Set Vertex
vertices (θ × r) = Set.map holder (ofRestructuring θ ∪ ofRel r)
   where
   ofRestructuring θ' = Set.mapMaybe L.head (ctrl θ') ∪ case θ' of
      Reuse _ p -> Set.mapMaybe L.head (singleton p)
      NoReuse _ -> empty
      Parts _ θs -> foldMap ofRestructuring θs
      ExtendEnv _ θ'' θs -> ofRestructuring θ'' ∪ foldMap ofRestructuring θs
   ofRel (Rel support rs) = Set.mapMaybe L.head (positionsOf support) ∪ foldMap ofRel rs

   holder (EdgeSrc a) = a
   holder _ = error absurd

-- Vertices labelled by values of shape f; at most one edge into each vertex
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Labelling (f Unit)
   , docs :: Labelling Vertex -- documented vertex ↦ vertex of doc
   , edges :: Labelling (Set Vertex × Dependence (Set Path) s) -- target ↦ sources and dependence on their values
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: empty, docs: empty, edges: empty }

valAt :: forall f s. DepGraph f s -> Vertex -> f Unit
valAt g a = get a g.vals

newVertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> Dependence (Set Path) s -> m Vertex
newVertex v δ = do
   size <- gets _.size
   let a = Vertex size
   modify_ \g -> g { size = size + 1, vals = insert a v g.vals, edges = insert a (vertices δ × δ) g.edges }
   pure a

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Vertex -> Vertex -> m Unit
attachDoc a b = modify_ \g -> g { docs = insert a b g.docs }

-- Visible vertices with values; edges left by hiding every other vertex
type VisibleGraph (f :: Type -> Type) s =
   { vals :: Labelling (f Unit)
   , edges :: Labelling (Map Path (Support PathSet s)) -- target ↦ position ↦ non-empty support
   }

-- Relies on edges running from earlier to later vertices in evaluation order.
materialise :: forall f s. Paths f => DepSemiring s => DepGraph f s -> Set Vertex -> VisibleGraph f s
materialise g visible =
   { vals
   , edges: (foldl step { θs: empty, rs: empty, edges: empty } (toUnfoldable g.edges :: List _)).edges
   }
   where
   vals = filterKeys (_ ∈ visible) g.vals

   -- Tupled dependence of every vertex so far on the visible vertices, as restructurings θs and relations rs
   step { θs, rs, edges } (a × (_ × δ)) =
      if a ∈ visible then
         { θs: free a (insert (EdgeSrc a) (Reuse empty (sourceRoot a)) θs)
         , rs: free a rs
         , edges: insert a (supports a (θ' × r')) edges
         }
      else { θs: free a (insert (EdgeSrc a) θ' θs), rs: free a (Map.alter (const (nonZero r')) (EdgeSrc a) rs), edges }
      where
      θ' × r' = compose δ (Parts empty θs × Rel mempty rs)

   -- Free the entry of each vertex which has a as last dependent
   free :: forall a. Vertex -> Endo (Map Step a)
   free a xs = foldr (EdgeSrc >>> delete) xs (fromMaybe Nil (lookup a byLastDependent))

   -- Last dependent of each vertex; vertex without dependents counts as dependent on itself
   lastDependent :: Labelling Vertex
   lastDependent = foldlWithIndex dependent empty g.edges
      where
      dependent a m (bs × _) = foldl (\m' b -> insert b a m') (insert a a m) bs

   byLastDependent :: Labelling (List Vertex)
   byLastDependent = fromFoldableWith (<>) $
      (toUnfoldable lastDependent :: List _) <#> \(b × a) -> a × (b : Nil)

   supports :: Vertex -> Dependence PathSet s -> Map Path (Support PathSet s)
   supports a δ = Map.filter (not <<< isEmpty) $
      Map.fromFoldable (positions (paths (get a vals)) <#> \(q × _) -> q × supp δ q)

-- Control sources of every support
controlSets :: forall s. Labelling (Map Path (Support PathSet s)) -> Set PathSet
controlSets = foldMap (foldMap \(Support ps _) -> singleton ps)

-- Restrict every support and target to the positions which satisfy the predicate
mask :: forall f s. Paths f => (Vertex -> f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = mapWithIndex (\b -> filterKeys (_ ∈ get b kept) >>> Map.mapMaybe restrict) g.edges }
   where
   kept = mapWithIndex (\a -> keep a >>> selected) g.vals

   restrict (Support ps ws) = if isEmpty support then Nothing else Just support
      where
      support = Support (get ps restricted) (filterKeys keptSource ws)

   restricted :: Map PathSet PathSet
   restricted = Set.toMap (controlSets g.edges) # mapWithIndex \ps _ -> filter keptSource ps

   keptSource (EdgeSrc a : p) = p ∈ get a kept
   keptSource _ = error absurd

-- Positions carrying true
selected :: forall f. Paths f => f Boolean -> Set Path
selected v = Set.fromFoldable (L.mapMaybe (\(p × b) -> if b then Just p else Nothing) (positions (paths v)))

-- Add weights at a vertex.
add' :: forall s. Semiring s => Vertex -> Map Path s -> Labelling (Map Path s) -> Labelling (Map Path s)
add' = insertWith (unionWith add)

-- Weight 1 at the selected positions.
unitWeights :: forall s. Semiring s => Labelling (Set Path) -> Labelling (Map Path s)
unitWeights = map (Set.toMap >>> map (const one))

-- Weights at each visible vertex as a value, zero where absent.
fromSparse :: forall f s. Paths f => Semiring s => VisibleGraph f s -> Labelling (Map Path s) -> Labelling (f s)
fromSparse g wss = g.vals # mapWithIndex \a v ->
   paths v <#> \(p × _) -> fromMaybe zero (lookup a wss >>= lookup p)

-- Forward and backward queries, each the transpose of the other.
type ConjugatePair a b = { fwd :: a -> b, bwd :: a -> b }

dimap :: forall a a' b b'. (a' -> a) -> (b -> b') -> ConjugatePair a b -> ConjugatePair a' b'
dimap f g pair = { fwd: g <<< pair.fwd <<< f, bwd: g <<< pair.bwd <<< f }

queries :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> ConjugatePair (Labelling (Set Path)) (Labelling (f s))
queries g = { fwd: fwd g, bwd: bwd g }

-- Dependence of the selection on the positions of each visible vertex.
bwd :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
bwd g selection = fromSparse g (foldr step (unitWeights selection) (toUnfoldable g.edges :: List _))
   where
   step :: Vertex × Map Path (Support PathSet s) -> Endo (Labelling (Map Path s))
   step (b × supports) wss = case lookup b wss of
      Nothing -> wss
      Just ws -> foldlWithIndex (\a wss' ws' -> add' a ws' wss') wss $
         bySource (weights (foldlWithIndex (from supports) mempty ws))

   from :: Map Path (Support PathSet s) -> Path -> Support PathSet s -> s -> Support PathSet s
   from supports q support w = maybe support (scaleSupport w >>> (support <> _)) (lookup q supports)

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
fwd g selection = fromSparse g (foldl step (unitWeights selection) (toUnfoldable g.edges :: List _))
   where
   step :: Labelling (Map Path s) -> Vertex × Map Path (Support PathSet s) -> Labelling (Map Path s)
   step wss (b × supports) = add' b (Map.mapMaybe weight supports) wss
      where
      weightAt :: Path -> s
      weightAt (EdgeSrc a : p) = fromMaybe zero (lookup a wss >>= lookup p)
      weightAt _ = error absurd

      -- Whether each set of control sources has a member with non-zero weight
      reached :: Map PathSet Boolean
      reached = Set.toMap (controlSets (maplet b supports)) # mapWithIndex \ps _ ->
         any (weightAt >>> (_ /= zero)) (members ps)

      weight :: Support PathSet s -> Maybe s
      weight (Support ps ws) = if w == zero then Nothing else Just w
         where
         w = foldlWithIndex (\p w' x -> w' + weightAt p * x) (if get ps reached then ctrlWeight else zero) ws

-- ======================
-- boilerplate
-- ======================
instance (Set c Path, Semiring s) => Monoid (Support c s) where
   mempty = Support empty empty

instance IsEmpty c => IsEmpty (Support c s) where
   isEmpty (Support ps ws) = isEmpty ps && isEmpty ws

instance (Set c Path, Semiring s) => Monoid (Rel c s) where
   mempty = Rel mempty empty
