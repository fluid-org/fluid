module DepGraph where

import Prelude hiding (absurd, compose)

import Control.Monad.State (class MonadState, execState, gets, modify_)
import Data.Foldable (any, foldMap, foldl, foldr)
import Data.FoldableWithIndex (foldMapWithIndex, foldlWithIndex)
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
import Path (Path, PathSet, Step(..), Vertex(..), members, pathSet, sourceAt, sourceRoot, sourceVertex)
import Util (class IsEmpty, type (×), Endo, absurd, assert, error, isEmpty, singleton, (×))
import Util.Map (delete, difference, filterKeys, get, insert, keys, lookup, maplet, toUnfoldable)
import Util.Set (class Set, empty, filter, union, (∈), (∪))

-- Labels with a path to each position
class Traversable f <= Paths f where
   paths :: forall a. f a -> f (Path × a)

positions :: forall f a. Traversable f => f a -> List a
positions = traverse (\a -> modify_ (a : _)) >>> flip execState Nil >>> L.reverse

-- Positions carrying true
selected :: forall f. Paths f => f Boolean -> Set Path
selected v = Set.fromFoldable (L.mapMaybe (\(p × b) -> if b then Just p else Nothing) (positions (paths v)))

-- Control sources as a set of type c, then non-zero weight of every other source
data Support c s = Support c (Map Path s)

instance (Set c Path, Semiring s) => Semigroup (Support c s) where
   append (Support ps ws) (Support ps' ws') = Support (ps ∪ ps') (unionWith add ws ws')

controlDep :: forall c s. c -> Support c s
controlDep ps = Support ps empty

dataDep :: forall c s. Set c Path => Semiring s => Path -> Support c s
dataDep p = Support empty (maplet p one)

-- Leave control sources unchanged, since control weight absorbs non-zero w
scaleSupport :: forall c s. Eq s => Semiring s => s -> Endo (Support c s)
scaleSupport w support@(Support ps ws)
   | w == one = support
   | otherwise = assert (w /= zero) (Support ps (mul w <$> ws))

-- Support of target root, then relation into each child; zero relations absent
data Rel c s = Rel (Support c s) (Map Step (Rel c s))

instance (Set c Path, Semiring s) => Semigroup (Rel c s) where
   append (Rel support rs) (Rel support' rs') = Rel (support <> support') (unionWith append rs rs')

nonZero :: forall c s. IsEmpty c => Rel c s -> Maybe (Rel c s)
nonZero r@(Rel support rs)
   | isEmpty support && isEmpty rs = Nothing
   | otherwise = Just r

ι :: forall c s. Set c Path => Semiring s => Path -> Endo (Rel c s)
ι p r = foldr (\step r' -> Rel mempty (maybe empty (maplet step) (nonZero r'))) r p

π :: forall c s. Set c Path => Semiring s => Path -> Endo (Rel c s)
π Nil r = r
π (step : p) (Rel _ rs) = maybe mempty (π p) (lookup step rs)

data Restructuring c
   = Reuse c Path
   | NoReuse c
   | Tupling c (Map Step (Restructuring c))
   | ExtendEnv c (Restructuring c) (Dict (Restructuring c))

ctrl :: forall c. Restructuring c -> c
ctrl (Reuse ps _) = ps
ctrl (NoReuse ps) = ps
ctrl (Tupling ps _) = ps
ctrl (ExtendEnv ps _ _) = ps

withCtrl :: forall c. Set c Path => c -> Endo (Restructuring c)
withCtrl ps' (Reuse ps p) = Reuse (ps ∪ ps') p
withCtrl ps' (NoReuse ps) = NoReuse (ps ∪ ps')
withCtrl ps' (Tupling ps θs) = Tupling (ps ∪ ps') θs
withCtrl ps' (ExtendEnv ps θ θs) = ExtendEnv (ps ∪ ps') θ θs

pathAfter :: forall c. Set c Path => Path -> Restructuring c -> Restructuring c
pathAfter Nil θ = θ
pathAfter p@(step : p') θ = (if any intoClosure p then identity else withCtrl (ctrl θ)) case θ of
   Reuse _ q -> Reuse empty (q <> p)
   NoReuse _ -> NoReuse empty
   Tupling _ θs -> pathAfter p' (get step θs)
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

supportAt :: forall c s. Set c Path => Semiring s => Dependence c s -> Path -> Support c s
supportAt (θ × r) q = case pathAfter q θ of
   Reuse ps p -> Support ps (maplet p one)
   θ' -> Support (ctrl θ') empty <> support
   where
   Rel support _ = π q r

-- Control sources which hold every source of every position in qs
supportsAt :: forall s. Semiring s => Dependence PathSet s -> Set Path -> PathSet
supportsAt δ qs = foldMap (supportAt δ >>> \(Support ps ws) -> ps ∪ foldMap pathSet (keys ws)) qs

restructuringAfter :: forall s. Semiring s => Restructuring (Set Path) -> Dependence PathSet s -> Restructuring PathSet
restructuringAfter (Reuse ps p) δ@(θ × _) = withCtrl (supportsAt δ ps) (pathAfter p θ)
restructuringAfter (NoReuse ps) δ = NoReuse (supportsAt δ ps)
restructuringAfter (Tupling ps θs) δ = Tupling (supportsAt δ ps) (flip restructuringAfter δ <$> θs)
restructuringAfter (ExtendEnv ps θ θs) δ = ExtendEnv (supportsAt δ ps) (restructuringAfter θ δ) (flip restructuringAfter δ <$> θs)

restructuringAfterRel :: forall s. Semiring s => Restructuring (Set Path) -> Rel PathSet s -> Rel PathSet s
restructuringAfterRel θ r = case θ of
   Reuse _ p -> π p r
   NoReuse _ -> mempty
   Tupling _ θs -> Rel mempty (relsAfter θs)
   ExtendEnv _ θ' θs -> case restructuringAfterRel θ' r × bindings θs of
      Rel support rs × θs' -> Rel support (relsAfter θs' ∪ difference rs θs')
   where
   relsAfter = Map.mapMaybe (flip restructuringAfterRel r >>> nonZero)

-- Relation after the relation of a dependence
relAfter :: forall s. DepSemiring s => Rel (Set Path) s -> Dependence PathSet s -> Rel PathSet s
relAfter (Rel (Support ps ws) rs) δ =
   Rel (foldlWithIndex (\p support w -> support <> scaleSupport w (supportAt δ p)) (Support (supportsAt δ ps) empty) ws)
      (Map.mapMaybe (flip relAfter δ >>> nonZero) rs)

compose :: forall s. DepSemiring s => Dependence (Set Path) s -> Dependence PathSet s -> Dependence PathSet s
compose (θ' × r') δ@(_ × r) = restructuringAfter θ' δ × (restructuringAfterRel θ' r <> relAfter r' δ)

bindings :: forall a. Dict a -> Map Step a
bindings ρ = Map.fromFoldable ((toUnfoldable ρ :: List _) <#> \(x × a) -> Binding x × a)

tupling :: forall c s. Set c Path => Semiring s => Map Step (Dependence c s) -> Dependence c s
tupling δs = Tupling empty (fst <$> δs) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Dependence of value with children δs, or with nothing reused if δs is empty; root depends on support
construct :: forall c s. Set c Path => Semiring s => Support c s -> Map Step (Dependence c s) -> Dependence c s
construct support δs
   | isEmpty δs = NoReuse empty × Rel support empty
   | otherwise = map (Rel support empty <> _) (tupling δs)

-- Dependence of environment at position p with bindings δs added or replaced
extend :: forall c s. Set c Path => Semiring s => Path -> Dict (Dependence c s) -> Dependence c s
extend p δs
   | isEmpty δs = reuse p
   | otherwise = ExtendEnv empty (Reuse empty p) (fst <$> δs) × Rel mempty (Map.mapMaybe (snd >>> nonZero) (bindings δs))

type Labelling a = Map Vertex a

-- Vertices labelled by values of shape f; at most one edge into each vertex
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Labelling (f Unit)
   , docs :: Labelling Vertex -- documented vertex ↦ vertex of doc
   , edges :: Labelling (Set Vertex × Dependence (Set Path) s) -- target ↦ sources and dependence on their values
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: empty, docs: empty, edges: empty }

-- Vertices which hold the source positions
vertices :: forall s. Dependence (Set Path) s -> Set Vertex
vertices (θ × r) = Set.map sourceVertex (ofRestructuring θ ∪ ofRel r)
   where
   ofRestructuring θ' = ctrl θ' ∪ case θ' of
      Reuse _ p -> singleton p
      NoReuse _ -> empty
      Tupling _ θs -> foldMap ofRestructuring θs
      ExtendEnv _ θ'' θs -> ofRestructuring θ'' ∪ foldMap ofRestructuring θs
   ofRel (Rel (Support ps ws) rs) = ps ∪ keys ws ∪ foldMap ofRel rs

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

   -- Compose dependence of a with tupling which holds dependence of each earlier vertex on visible vertices
   step { θs, rs, edges } (a × (_ × δ)) =
      if a ∈ visible then
         { θs: free a (insert (EdgeSrc a) (Reuse empty (sourceRoot a)) θs)
         , rs: free a rs
         , edges: insert a (supports a (θ' × r')) edges
         }
      else { θs: free a (insert (EdgeSrc a) θ' θs), rs: free a (Map.alter (const (nonZero r')) (EdgeSrc a) rs), edges }
      where
      θ' × r' = compose δ (Tupling empty θs × Rel mempty rs)

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
      Map.fromFoldable (positions (paths (get a vals)) <#> \(q × _) -> q × supportAt δ q)

-- Control sources of every support
controlSets :: forall s. Labelling (Map Path (Support PathSet s)) -> Set PathSet
controlSets = foldMap (foldMap \(Support ps _) -> singleton ps)

-- Weights of source positions grouped by source vertex
bySource :: forall a. Map Path a -> Labelling (Map Path a)
bySource ws = fromFoldableWith union $
   (toUnfoldable ws :: List _) <#> case _ of
      (EdgeSrc a : p) × w -> a × maplet p w
      _ -> error absurd

-- Restrict every support and target to the positions which satisfy the predicate
mask :: forall f s. Paths f => (Vertex -> f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = mapWithIndex (\b -> filterKeys (sourceAt b >>> (_ ∈ kept)) >>> restrict) g.edges }
   where
   kept :: Set Path
   kept = foldMapWithIndex (\a v -> Set.map (sourceAt a) (selected (keep a v))) g.vals

   restrict :: Endo (Map Path (Support PathSet s))
   restrict = map (\(Support ps ws) -> Support (get ps restricted) (filterKeys (_ ∈ kept) ws)) >>> Map.filter (not <<< isEmpty)

   restricted :: Map PathSet PathSet
   restricted = Set.toMap (controlSets g.edges) # mapWithIndex \ps _ -> filter (_ ∈ kept) ps

-- Add weights at a vertex.
addAt :: forall s. Semiring s => Vertex -> Labelling (Map Path s) -> Map Path s -> Labelling (Map Path s)
addAt a wss ws = insertWith (unionWith add) a ws wss

-- Weight 1 at the selected positions.
unitWeights :: forall s. Semiring s => Labelling (Set Path) -> Labelling (Map Path s)
unitWeights = map (Set.toMap >>> map (const one))

-- Weights at each visible vertex as a value, zero where absent.
fromSparse :: forall f s. Paths f => Semiring s => VisibleGraph f s -> Labelling (Map Path s) -> Labelling (f s)
fromSparse g wss = g.vals # mapWithIndex \a v ->
   paths v <#> \(p × _) -> fromMaybe zero (lookup a wss >>= lookup p)

-- Dependence of the selection on the positions of each visible vertex.
bwd :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
bwd g selection = fromSparse g (foldr step (unitWeights selection) (toUnfoldable g.edges :: List _))
   where
   step :: Vertex × Map Path (Support PathSet s) -> Endo (Labelling (Map Path s))
   step (b × supports) wss = case lookup b wss of
      Nothing -> wss
      Just ws -> foldlWithIndex addAt wss (bySource (weights (foldlWithIndex (from supports) mempty ws)))

   weights :: Support PathSet s -> Map Path s
   weights (Support ps ws) = unionWith add (Set.toMap (members ps) $> ctrlWeight) ws

   from :: Map Path (Support PathSet s) -> Path -> Support PathSet s -> s -> Support PathSet s
   from supports q support w = maybe support (scaleSupport w >>> (support <> _)) (lookup q supports)

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
fwd g selection = fromSparse g (foldl step (unitWeights selection) (toUnfoldable g.edges :: List _))
   where
   step :: Labelling (Map Path s) -> Vertex × Map Path (Support PathSet s) -> Labelling (Map Path s)
   step wss (b × supports) = addAt b wss (Map.mapMaybe weight supports)
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
