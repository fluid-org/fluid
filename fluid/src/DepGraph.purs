module DepGraph where

import Prelude hiding (absurd, compose)

import Bind (Var)
import Control.Apply (lift2)
import Control.Monad.State (class MonadState, execState, gets, modify_)
import Data.Foldable (any, foldMap, foldl, foldr)
import Data.FoldableWithIndex (foldlWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map, fromFoldableWith, insertWith, lookup, unionWith)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype)
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable, traverse)
import Data.Tuple (fst, snd)
import Lattice (class DepSemiring, ctrlWeight)
import Util (type (×), Endo, absurd, error, singleton, (×))
import Util.Map (get, maplet)
import Util.Set ((∪))
import Unsafe.Reference (unsafeRefEq)

newtype Vertex = Vertex Int

-- Step to part of value or member of family
data Step
   = Source Vertex -- of edge
   | InEnv -- environment of inputs
   | InCtl -- control input
   | Binding Var
   | Field Var
   | Element Int -- of list or tuple
   | Key String -- of dictionary entry
   | Entry String -- value of dictionary entry
   | MatrixElement Int Int
   | MatrixRows
   | MatrixCols
   | ClosureEnv
   | PartialFun
   | PartialArg Int

type Path = List Step

ε :: Path
ε = Nil

-- Position p of source vertex a
sourceAt :: Vertex -> Path -> Path
sourceAt a p = Source a : p

sourceRoot :: Vertex -> Path
sourceRoot a = sourceAt a ε

-- Whether the step leads from a function value to a value held by the function
uncl :: Step -> Boolean
uncl ClosureEnv = true
uncl PartialFun = true
uncl (PartialArg _) = true
uncl _ = false

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

-- Same as union, except that a result equal to ps or ps' is that argument
unionShared :: Set Path -> Set Path -> Set Path
unionShared ps ps'
   | unsafeRefEq ps ps' = ps
   | otherwise = argument (ps ∪ ps')
        where
        argument qs
           | Set.size qs == Set.size ps = ps
           | Set.size qs == Set.size ps' = ps'
           | otherwise = qs

-- Sources of a target position: set of sources with control weight, then non-zero weight of every other source
data Sources s = Sources (Set Path) (Map Path s)

instance Semiring s => Semigroup (Sources s) where
   append (Sources ps ws) (Sources ps' ws') = Sources (unionShared ps ps') (unionWith add ws ws')

instance Semiring s => Monoid (Sources s) where
   mempty = Sources Set.empty Map.empty

-- Control dependence on each of ps
control :: forall s. Set Path -> Sources s
control ps = Sources ps Map.empty

-- Dependence on p with weight one
unitWeight :: forall s. Semiring s => Path -> Sources s
unitWeight p = Sources Set.empty (Map.singleton p one)

positionsOf :: forall s. Sources s -> Set Path
positionsOf (Sources ps ws) = ps ∪ Map.keys ws

weights :: forall s. DepSemiring s => Sources s -> Map Path s
weights (Sources ps ws) = unionWith add (Set.toMap ps $> ctrlWeight) ws

-- Product of non-zero w with the weight of every source; unchanged for a source with control weight
scaleSources :: forall s. Eq s => Semiring s => s -> Endo (Sources s)
scaleSources w srcs@(Sources ps ws)
   | w == one = srcs
   | otherwise = Sources ps (mul w <$> ws)

-- Sources of the target root, then relation into each part; zero relations absent
data Rel s = Rel (Sources s) (Map Step (Rel s))

instance Semiring s => Semigroup (Rel s) where
   append (Rel srcs rs) (Rel srcs' rs') = Rel (srcs <> srcs') (unionWith append rs rs')

instance Semiring s => Monoid (Rel s) where
   mempty = Rel mempty Map.empty

nonZero :: forall s. Rel s -> Maybe (Rel s)
nonZero r@(Rel (Sources ps ws) rs)
   | Set.isEmpty ps && Map.isEmpty ws && Map.isEmpty rs = Nothing
   | otherwise = Just r

-- Relation of the target root to the given sources
onto :: forall s. Sources s -> Rel s
onto srcs = Rel srcs Map.empty

ι :: forall s. Semiring s => Path -> Endo (Rel s)
ι p r = foldr (\step r' -> Rel mempty (maybe Map.empty (maplet step) (nonZero r'))) r p

π :: forall s. Semiring s => Path -> Endo (Rel s)
π Nil r = r
π (step : p) (Rel _ rs) = maybe mempty (π p) (lookup step rs)

-- Control dependence of the target on a set of source positions, with a form
data Restructuring = Restructuring (Set Path) Form

data Form
   = Reuse Path -- subvalue of source at path
   | Zero -- nothing reused
   | Family (Map Step Restructuring) -- restructuring into each part
   | Extend Restructuring (Map Step Restructuring) -- restructuring into environment; restructuring into each replacement member

restructuring :: Form -> Restructuring
restructuring = Restructuring Set.empty

withCtrl :: Set Path -> Endo Restructuring
withCtrl ps' (Restructuring ps ψ) = Restructuring (unionShared ps ps') ψ

pathAfter :: Path -> Restructuring -> Restructuring
pathAfter Nil θ = θ
pathAfter p@(step : p') (Restructuring ps ψ) = (if any uncl p then identity else withCtrl ps) case ψ of
   Reuse q -> restructuring (Reuse (q <> p))
   Zero -> restructuring Zero
   Family θs -> pathAfter p' (get step θs)
   Extend θ θs -> case lookup step θs of
      Just θ' -> pathAfter p' θ'
      Nothing -> pathAfter p θ

type Dependence s = Restructuring × Rel s

reuse :: forall s. Semiring s => Path -> Dependence s
reuse p = restructuring (Reuse p) × mempty

-- Add control dependence of the target on each of ps
under :: forall s. Set Path -> Endo (Dependence s)
under ps (θ × r) = withCtrl ps θ × r

supp :: forall s. Semiring s => Dependence s -> Path -> Sources s
supp (θ × r) q = case pathAfter q θ of
   Restructuring ps (Reuse p) -> Sources ps (Map.singleton p one)
   Restructuring ps _ -> Sources ps Map.empty <> srcs
   where
   Rel srcs _ = π q r

-- Sources of every position in qs
supps :: forall s. Semiring s => Dependence s -> Set Path -> Set Path
supps δ qs = positionsOf (foldMap (supp δ) qs)

restructuringAfter :: forall s. Semiring s => Restructuring -> Dependence s -> Restructuring
restructuringAfter (Restructuring ps ψ) δ@(θ × _) = withCtrl (supps δ ps) case ψ of
   Reuse p -> pathAfter p θ
   Zero -> restructuring Zero
   Family θs -> restructuring (Family (flip restructuringAfter δ <$> θs))
   Extend θ' θs -> restructuring (Extend (restructuringAfter θ' δ) (flip restructuringAfter δ <$> θs))

restructuringAfterRel :: forall s. Semiring s => Restructuring -> Rel s -> Rel s
restructuringAfterRel (Restructuring _ ψ) r = case ψ of
   Reuse p -> π p r
   Zero -> mempty
   Family θs -> Rel mempty (members θs)
   Extend θ θs -> case restructuringAfterRel θ r of
      Rel srcs rs -> Rel srcs (Map.union (members θs) (Map.difference rs θs))
   where
   members = Map.mapMaybe (flip restructuringAfterRel r >>> nonZero)

-- Relation after the relation of a dependence
relAfter :: forall s. DepSemiring s => Rel s -> Dependence s -> Rel s
relAfter (Rel (Sources ps ws) rs) δ =
   Rel (foldlWithIndex (\p srcs w -> srcs <> scaleSources w (supp δ p)) (Sources (supps δ ps) Map.empty) ws)
      (Map.mapMaybe (flip relAfter δ >>> nonZero) rs)

compose :: forall s. DepSemiring s => Dependence s -> Dependence s -> Dependence s
compose (θ' × r') δ@(_ × r) = restructuringAfter θ' δ × (restructuringAfterRel θ' r <> relAfter r' δ)

tupling :: forall s. Semiring s => Map Step (Dependence s) -> Dependence s
tupling δs = restructuring (Family (fst <$> δs)) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Dependence of a value built around parts δs, or with nothing reused if δs is empty; root depends on srcs
construct :: forall s. Semiring s => Sources s -> Map Step (Dependence s) -> Dependence s
construct srcs δs
   | Map.isEmpty δs = restructuring Zero × onto srcs
   | otherwise = map (onto srcs <> _) (tupling δs)

-- Dependence of the environment at position p with members δs replaced or added
extend :: forall s. Semiring s => Path -> Map Step (Dependence s) -> Dependence s
extend p δs
   | Map.isEmpty δs = reuse p
   | otherwise =
        restructuring (Extend (restructuring (Reuse p)) (fst <$> δs)) × Rel mempty (Map.mapMaybe (snd >>> nonZero) δs)

-- Vertices which hold the source positions
vertices :: forall s. Dependence s -> Set Vertex
vertices (θ × r) = Set.map holder (ofRestructuring θ ∪ ofRel r)
   where
   ofRestructuring (Restructuring ps ψ) = Set.mapMaybe L.head ps ∪ case ψ of
      Reuse p -> Set.mapMaybe L.head (singleton p)
      Zero -> Set.empty
      Family θs -> foldMap ofRestructuring θs
      Extend θ' θs -> ofRestructuring θ' ∪ foldMap ofRestructuring θs
   ofRel (Rel srcs rs) = Set.mapMaybe L.head (positionsOf srcs) ∪ foldMap ofRel rs

   holder (Source a) = a
   holder _ = error absurd

type Labelling a = Map Vertex a
type Edges r = Labelling (Labelling r) -- target ↦ source ↦ dependence relation

-- Vertices labelled by values of shape f; at most one edge into each vertex
type DepGraph (f :: Type -> Type) s =
   { size :: Int -- vertices allocated so far
   , vals :: Labelling (f Unit)
   , docs :: Labelling Vertex -- documented vertex ↦ vertex of doc
   , edges :: Labelling (Set Vertex × Dependence s) -- target ↦ sources, with dependence on their values
   }

emptyGraph :: forall f s. DepGraph f s
emptyGraph = { size: 0, vals: Map.empty, docs: Map.empty, edges: Map.empty }

valAt :: forall f s. DepGraph f s -> Vertex -> f Unit
valAt g a = get a g.vals

newVertex :: forall f s m. MonadState (DepGraph f s) m => f Unit -> Dependence s -> m Vertex
newVertex v δ = do
   size <- gets _.size
   let a = Vertex size
   modify_ \g -> g { size = size + 1, vals = Map.insert a v g.vals, edges = Map.insert a (vertices δ × δ) g.edges }
   pure a

attachDoc :: forall f s m. MonadState (DepGraph f s) m => Vertex -> Vertex -> m Unit
attachDoc a b = modify_ \g -> g { docs = Map.insert a b g.docs }

-- Pair present exactly when its weight is non-zero
newtype SparseRel s = SparseRel
   { out :: Map Path (Map Path s) -- source ↦ labelled target neighbours
   , in_ :: Map Path (Map Path s) -- target ↦ labelled source neighbours
   }

sparseRel :: forall s. Map Path (Map Path s) -> SparseRel s
sparseRel in_ = SparseRel { out, in_ }
   where
   out = fromFoldableWith Map.union
      (Map.toUnfoldable in_ >>= \(q × m) -> (Map.toUnfoldable m :: List _) <#> \(p × w) -> p × maplet q w)

-- Visible vertices with their values; edges labelled by the dependence relations left by hiding every other vertex
type VisibleGraph (f :: Type -> Type) s =
   { vals :: Labelling (f Unit)
   , edges :: Edges (SparseRel s)
   }

-- Relies on edges running from earlier to later vertices in evaluation order.
materialise :: forall f s. Paths f => DepSemiring s => DepGraph f s -> Set Vertex -> VisibleGraph f s
materialise g visible =
   { vals
   , edges: (foldl step { θs: Map.empty, rs: Map.empty, edges: Map.empty } (Map.toUnfoldable g.edges :: List _)).edges
   }
   where
   vals = Map.filterKeys (_ `Set.member` visible) g.vals

   -- Tupled dependence of every vertex so far on the visible vertices, as restructurings θs and relations rs
   step { θs, rs, edges } (a × (_ × δ)) =
      if Set.member a visible then
         { θs: free a (Map.insert (Source a) (restructuring (Reuse (singleton (Source a)))) θs)
         , rs: free a rs
         , edges: Map.insert a (sparseRel <$> edgesInto a (θ' × r')) edges
         }
      else { θs: free a (Map.insert (Source a) θ' θs), rs: free a (Map.alter (const (nonZero r')) (Source a) rs), edges }
      where
      θ' × r' = compose δ (restructuring (Family θs) × Rel mempty rs)

   -- Free the entry of each vertex which has a as last dependent
   free :: forall a. Vertex -> Endo (Map Step a)
   free a xs = foldr (Source >>> Map.delete) xs (fromMaybe Nil (lookup a byLastDependent))

   -- Last dependent of each vertex; vertex without dependents counts as dependent on itself
   lastDependent :: Labelling Vertex
   lastDependent = foldlWithIndex dependent Map.empty g.edges
      where
      dependent a m (bs × _) = foldl (\m' b -> Map.insert b a m') (Map.insert a a m) bs

   byLastDependent :: Labelling (List Vertex)
   byLastDependent = fromFoldableWith (<>) $
      (Map.toUnfoldable lastDependent :: List _) <#> \(b × a) -> a × (b : Nil)

   -- Edges into a visible vertex from each visible vertex
   edgesInto :: Vertex -> Dependence s -> Labelling (Map Path (Map Path s))
   edgesInto a δ = foldl (unionWith Map.union) Map.empty $
      positions (paths (get a vals)) <#> \(q × _) -> maplet q <$> bySource (weights (supp δ q))

   bySource :: Map Path s -> Labelling (Map Path s)
   bySource row = fromFoldableWith Map.union $
      (Map.toUnfoldable row :: List _) <#> case _ of
         (Source b : p) × w -> b × maplet p w
         _ -> error absurd

-- Restrict every dependence relation to the positions where the predicate holds.
mask :: forall f s. Paths f => (Vertex -> f Unit -> f Boolean) -> VisibleGraph f s -> VisibleGraph f s
mask keep g = g { edges = mapWithIndex (\b -> mapWithIndex (rel b)) g.edges }
   where
   kept = mapWithIndex (\a -> keep a >>> selected) g.vals
   rel b a (SparseRel r) = SparseRel { in_: only ps_b ps_a r.in_, out: only ps_a ps_b r.out }
      where
      ps_b = get b kept
      ps_a = get a kept
   only ps ps' m = Map.filter (not <<< Map.isEmpty) $
      Map.filterKeys (_ `Set.member` ps') <$> Map.filterKeys (_ `Set.member` ps) m

-- Positions carrying true.
selected :: forall f. Paths f => f Boolean -> Set Path
selected v = Set.fromFoldable (L.mapMaybe (\(p × b) -> if b then Just p else Nothing) (positions (paths v)))

-- Sparse dependence relation applied to sparse weights.
applySparse :: forall s. Semiring s => Map Path (Map Path s) -> Map Path s -> Map Path s
applySparse r w = foldl (unionWith add) Map.empty $
   mapWithIndex (\p w' -> maybe Map.empty (map (w' * _)) (lookup p r)) w

-- Add weights at a vertex.
add' :: forall s. Semiring s => Vertex -> Map Path s -> Labelling (Map Path s) -> Labelling (Map Path s)
add' = insertWith (unionWith add)

-- Weight 1 at the selected positions.
unitWeights :: forall s. Semiring s => Labelling (Set Path) -> Labelling (Map Path s)
unitWeights = map (Set.toMap >>> map (const one))

-- Weights at each visible vertex as a value, zero where absent.
dense :: forall f s. Paths f => Semiring s => VisibleGraph f s -> Labelling (Map Path s) -> Labelling (f s)
dense g ws = g.vals # mapWithIndex \a v ->
   paths v <#> \(p × _) -> fromMaybe zero (lookup a ws >>= lookup p)

-- Forward and backward queries, each the transpose of the other.
type ConjugatePair a b = { fwd :: a -> b, bwd :: a -> b }

dimap :: forall a a' b b'. (a' -> a) -> (b -> b') -> ConjugatePair a b -> ConjugatePair a' b'
dimap f g pair = { fwd: g <<< pair.fwd <<< f, bwd: g <<< pair.bwd <<< f }

queries :: forall f s. Paths f => Semiring s => VisibleGraph f s -> ConjugatePair (Labelling (Set Path)) (Labelling (f s))
queries g = { fwd: fwd g, bwd: bwd g }

-- Dependence of the selection on the positions of each visible vertex.
bwd :: forall f s. Paths f => Semiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
bwd g selection = dense g (foldr step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step (p × sources) ws = case lookup p ws of
      Nothing -> ws
      Just w -> foldlWithIndex (\q ws' (SparseRel r) -> add' q (applySparse r.in_ w) ws') ws sources

-- Dependence of the positions of each visible vertex on the selection.
fwd :: forall f s. Paths f => Semiring s => VisibleGraph f s -> Labelling (Set Path) -> Labelling (f s)
fwd g selection = dense g (foldl step (unitWeights selection) (Map.toUnfoldable g.edges :: List _))
   where
   step ws (p × sources) = foldlWithIndex (\q ws' r -> maybe ws' (into p ws' r) (lookup q ws)) ws sources
   into p ws (SparseRel r) w = add' p (applySparse r.out w) ws

-- ======================
-- boilerplate
-- ======================
derive instance Eq Vertex
derive instance Ord Vertex
derive instance Eq Step
derive instance Ord Step
derive instance Generic Step _

instance Show Step where
   show = genericShow

derive instance Newtype Vertex _
derive newtype instance Show Vertex
