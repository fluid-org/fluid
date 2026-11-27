module DepGraph where

import Prelude hiding (compose)

import Control.Monad.ST (for, foreach) as ST
import Control.Monad.State (class MonadState, execState, gets, modify_)
import Data.Array (mapWithIndex, replicate) as A
import Data.Array.ST (modify, peek, poke, run, thaw) as STA
import Data.Foldable (any, foldMap, foldl, foldr, for_, traverse_)
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
import Path (Path, Position, PositionSet, Step(..), Vertex(..), followedBy, members, positionSet, ε)
import Util (class IsEmpty, type (×), Endo, assert, isEmpty, singleton, (!), (×))
import Util.Map (delete, filterKeys, get, insert, keys, lookup, maplet, toUnfoldable)
import Util.Set (class Set, empty, filter, union, (∈), (∪))

-- Annotate each position with its path
class Traversable f <= Paths f where
   paths :: forall a. f a -> f (Path × a)

positions :: forall f a. Traversable f => f a -> List a
positions = traverse (\a -> modify_ (a : _)) >>> flip execState Nil >>> L.reverse

-- Paths of positions annotated with true
selected :: forall f. Paths f => f Boolean -> Set Path
selected v = Set.fromFoldable (L.mapMaybe (\(p × b) -> if b then Just p else Nothing) (positions (paths v)))

-- Set of control sources, then weights of other sources; zero weights absent
data Support c s = Support c (Map Position s)

instance (Set c Position, Semiring s) => Semigroup (Support c s) where
   append (Support ps ws) (Support ps' ws') = Support (ps ∪ ps') (unionWith add ws ws')

controlDep :: forall c s. c -> Support c s
controlDep ps = Support ps empty

dataDep :: forall c s. Set c Position => Semiring s => Position -> Support c s
dataDep p = Support empty (maplet p one)

-- Scale weights by w; control sources stay, since control weight absorbs non-zero w
scaleSupport :: forall c s. Eq s => Semiring s => s -> Endo (Support c s)
scaleSupport w support@(Support ps ws)
   | w == one = support
   | otherwise = assert (w /= zero) (Support ps (mul w <$> ws))

-- Support of target root, then relation into each child; zero relations absent
data Rel c s = Rel (Support c s) (Map Step (Rel c s))

instance (Set c Position, Semiring s) => Semigroup (Rel c s) where
   append (Rel support rs) (Rel support' rs') = Rel (support <> support') (unionWith append rs rs')

nonZero :: forall c s. IsEmpty c => Rel c s -> Maybe (Rel c s)
nonZero r@(Rel support rs)
   | isEmpty support && isEmpty rs = Nothing
   | otherwise = Just r

ι :: forall c s. Set c Position => Semiring s => Path -> Endo (Rel c s)
ι p r = foldr (\step r' -> Rel mempty (maybe empty (maplet step) (nonZero r'))) r p

π :: forall c s. Set c Position => Semiring s => Path -> Endo (Rel c s)
π Nil r = r
π (step : p) (Rel _ rs) = maybe mempty (π p) (lookup step rs)

data Restructuring c
   = Reuse c Position
   | NoReuse c
   | Tupling c (Map Step (Restructuring c))

ctrl :: forall c. Restructuring c -> c
ctrl (Reuse ps _) = ps
ctrl (NoReuse ps) = ps
ctrl (Tupling ps _) = ps

withCtrl :: forall c. Set c Position => c -> Endo (Restructuring c)
withCtrl ps' (Reuse ps p) = Reuse (ps ∪ ps') p
withCtrl ps' (NoReuse ps) = NoReuse (ps ∪ ps')
withCtrl ps' (Tupling ps θs) = Tupling (ps ∪ ps') θs

pathAfter :: forall c. Set c Position => Path -> Restructuring c -> Restructuring c
pathAfter Nil θ = θ
pathAfter p@(step : p') θ = (if any intoClosure p then identity else withCtrl (ctrl θ)) case θ of
   Reuse _ q -> Reuse empty (q `followedBy` p)
   NoReuse _ -> NoReuse empty
   Tupling _ θs -> pathAfter p' (get step θs)
   where
   intoClosure :: Step -> Boolean
   intoClosure ClosureEnv = true
   intoClosure PartialFun = true
   intoClosure (PartialArg _) = true
   intoClosure _ = false

type Dependence c s = Restructuring c × Rel c s

reuse :: forall c s. Set c Position => Semiring s => Position -> Dependence c s
reuse p = Reuse empty p × mempty

supportAt :: forall c s. Set c Position => Semiring s => Dependence c s -> Path -> Support c s
supportAt (θ × r) q = case pathAfter q θ of
   Reuse ps p -> Support ps (maplet p one)
   θ' -> Support (ctrl θ') empty <> support
   where
   Rel support _ = π q r

-- Dependence of each source vertex; zero relations absent
type Dependences c s = Labelling (Restructuring c) × Labelling (Rel c s)

-- Support of a source position in the dependence of its vertex
sourceSupport :: forall c s. Set c Position => Semiring s => Dependences c s -> Position -> Support c s
sourceSupport (θs × rs) (a × p) = supportAt (get a θs × fromMaybe mempty (lookup a rs)) p

-- Every source of given positions
sourcesOf :: forall s. Semiring s => Dependences PositionSet s -> Set Position -> PositionSet
sourcesOf δs qs = foldMap (sourceSupport δs >>> \(Support ps ws) -> ps ∪ foldMap positionSet (keys ws)) qs

restructuringAfter :: forall s. Semiring s => Restructuring (Set Position) -> Dependences PositionSet s -> Restructuring PositionSet
restructuringAfter (Reuse ps (a × p)) δs@(θs × _) = withCtrl (sourcesOf δs ps) (pathAfter p (get a θs))
restructuringAfter (NoReuse ps) δs = NoReuse (sourcesOf δs ps)
restructuringAfter (Tupling ps θs) δs = Tupling (sourcesOf δs ps) (flip restructuringAfter δs <$> θs)

restructuringAfterRel :: forall s. Semiring s => Restructuring (Set Position) -> Labelling (Rel PositionSet s) -> Rel PositionSet s
restructuringAfterRel θ rs = case θ of
   Reuse _ (a × p) -> maybe mempty (π p) (lookup a rs)
   NoReuse _ -> mempty
   Tupling _ θs -> Rel mempty (relsAfter θs)
   where
   relsAfter = Map.mapMaybe (flip restructuringAfterRel rs >>> nonZero)

-- Compose relation with dependence of each source vertex
relAfter :: forall s. DepSemiring s => Rel (Set Position) s -> Dependences PositionSet s -> Rel PositionSet s
relAfter (Rel (Support ps ws) rs) δs =
   Rel (foldlWithIndex (\p support w -> support <> scaleSupport w (sourceSupport δs p)) (Support (sourcesOf δs ps) empty) ws)
      (Map.mapMaybe (flip relAfter δs >>> nonZero) rs)

compose :: forall s. DepSemiring s => Dependence (Set Position) s -> Dependences PositionSet s -> Dependence PositionSet s
compose (θ' × r') δs@(_ × rs) = restructuringAfter θ' δs × (restructuringAfterRel θ' rs <> relAfter r' δs)

bindings :: forall a. Dict a -> Map Step a
bindings ρ = Map.fromFoldable ((toUnfoldable ρ :: List _) <#> \(x × a) -> Binding x × a)

tupling :: forall c s. Set c Position => Semiring s => Map Step (Dependence c s) -> Dependence c s
tupling δs = Tupling empty (fst <$> δs) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Dependence of value constructed from given children; root depends on support
construct :: forall c s. Set c Position => Semiring s => Support c s -> Map Step (Dependence c s) -> Dependence c s
construct support δs
   | isEmpty δs = NoReuse empty × Rel support empty
   | otherwise = map (Rel support empty <> _) (tupling δs)

type Labelling a = Map Vertex a

-- Vertices labelled by values of shape f; at most one edge into each vertex
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Labelling (f Unit)
   , docs :: Labelling Vertex -- documented vertex ↦ vertex of doc
   , edges :: Labelling (Set Vertex × Dependence (Set Position) s) -- target ↦ sources and dependence on their values
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: empty, docs: empty, edges: empty }

-- Vertices which hold the source positions
vertices :: forall s. Dependence (Set Position) s -> Set Vertex
vertices (θ × r) = Set.map fst (ofRestructuring θ ∪ ofRel r)
   where
   ofRestructuring θ' = ctrl θ' ∪ case θ' of
      Reuse _ p -> singleton p
      NoReuse _ -> empty
      Tupling _ θs -> foldMap ofRestructuring θs
   ofRel (Rel (Support ps ws) rs) = ps ∪ keys ws ∪ foldMap ofRel rs

newVertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> Dependence (Set Position) s -> m Vertex
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
   , edges :: Labelling (Map Path (Support PositionSet s)) -- target ↦ position ↦ non-empty support
   }

-- Hide every vertex outside the visible set; relies on edges running from earlier to later vertices
materialise :: forall f s. Paths f => DepSemiring s => DepGraph f s -> Set Vertex -> VisibleGraph f s
materialise g visible =
   { vals
   , edges: (foldl step { θs: empty, rs: empty, edges: empty } (toUnfoldable g.edges :: List _)).edges
   }
   where
   vals = filterKeys (_ ∈ visible) g.vals

   -- Compose dependence of a with dependence of each earlier vertex on visible vertices
   step { θs, rs, edges } (a × (_ × δ)) =
      if a ∈ visible then
         { θs: free a (insert a (Reuse empty (a × ε)) θs)
         , rs: free a rs
         , edges: insert a (supports a (θ' × r')) edges
         }
      else { θs: free a (insert a θ' θs), rs: free a (Map.alter (const (nonZero r')) a rs), edges }
      where
      θ' × r' = compose δ (θs × rs)

   -- Free the entry of each vertex which has a as last dependent
   free :: forall a. Vertex -> Endo (Labelling a)
   free (Vertex a) xs = foldr delete xs (byLastDependent ! a)

   -- Vertices without dependents count as dependent on themselves
   byLastDependent :: Array (List Vertex)
   byLastDependent = STA.run do
      lastDependent <- STA.thaw (A.mapWithIndex const (A.replicate g.size unit))
      ST.foreach (toUnfoldable g.edges) \(Vertex a × bs × _) -> for_ bs \(Vertex b) -> STA.poke b a lastDependent
      vertices' <- STA.thaw (A.replicate g.size Nil)
      ST.for 0 g.size \b -> STA.peek b lastDependent >>= traverse_ \a -> STA.modify a (Vertex b : _) vertices'
      pure vertices'

   supports :: Vertex -> Dependence PositionSet s -> Map Path (Support PositionSet s)
   supports a δ = Map.filter (not <<< isEmpty) $
      Map.fromFoldable (positions (paths (get a vals)) <#> \(q × _) -> q × supportAt δ q)

-- Control sources of every support
controlSets :: forall s. Labelling (Map Path (Support PositionSet s)) -> Set PositionSet
controlSets = foldMap (foldMap \(Support ps _) -> singleton ps)

-- Weights of source positions grouped by source vertex
bySource :: forall a. Map Position a -> Labelling (Map Path a)
bySource ws = fromFoldableWith union ((toUnfoldable ws :: List _) <#> \((a × p) × w) -> a × maplet p w)

-- Restrict every support and target to the positions which satisfy the predicate
mask :: forall f s. Paths f => (Vertex -> f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = mapWithIndex (\b -> filterKeys ((b × _) >>> (_ ∈ kept)) >>> restrict) g.edges }
   where
   kept :: Set Position
   kept = foldMapWithIndex (\a v -> Set.map (a × _) (selected (keep a v))) g.vals

   restrict :: Endo (Map Path (Support PositionSet s))
   restrict = map (\(Support ps ws) -> Support (get ps restricted) (filterKeys (_ ∈ kept) ws)) >>> Map.filter (not <<< isEmpty)

   restricted :: Map PositionSet PositionSet
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
   step :: Vertex × Map Path (Support PositionSet s) -> Endo (Labelling (Map Path s))
   step (b × supports) wss = case lookup b wss of
      Nothing -> wss
      Just ws -> foldlWithIndex addAt wss (bySource (weights (foldlWithIndex (from supports) mempty ws)))

   weights :: Support PositionSet s -> Map Position s
   weights (Support ps ws) = unionWith add (Set.toMap (members ps) $> ctrlWeight) ws

   from :: Map Path (Support PositionSet s) -> Path -> Support PositionSet s -> s -> Support PositionSet s
   from supports q support w = maybe support (scaleSupport w >>> (support <> _)) (lookup q supports)

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Paths f => DepSemiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
fwd g selection = fromSparse g (foldl step (unitWeights selection) (toUnfoldable g.edges :: List _))
   where
   step :: Labelling (Map Path s) -> Vertex × Map Path (Support PositionSet s) -> Labelling (Map Path s)
   step wss (b × supports) = addAt b wss (Map.mapMaybe weight supports)
      where
      weightAt :: Position -> s
      weightAt (a × p) = fromMaybe zero (lookup a wss >>= lookup p)

      -- Whether each set of control sources has a member with non-zero weight
      reached :: Map PositionSet Boolean
      reached = Set.toMap (controlSets (maplet b supports)) # mapWithIndex \ps _ ->
         any (weightAt >>> (_ /= zero)) (members ps)

      weight :: Support PositionSet s -> Maybe s
      weight (Support ps ws) = if w == zero then Nothing else Just w
         where
         w = foldlWithIndex (\p w' x -> w' + weightAt p * x) (if get ps reached then ctrlWeight else zero) ws

-- ======================
-- boilerplate
-- ======================
instance (Set c Position, Semiring s) => Monoid (Support c s) where
   mempty = Support empty empty

instance IsEmpty c => IsEmpty (Support c s) where
   isEmpty (Support ps ws) = isEmpty ps && isEmpty ws

instance (Set c Position, Semiring s) => Monoid (Rel c s) where
   mempty = Rel mempty empty
