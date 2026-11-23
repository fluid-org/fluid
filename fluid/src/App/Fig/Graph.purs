module App.Fig.Graph where

import Prelude hiding (absurd)

import App.View.Util (Filter)
import Bind (FieldName, Name, dottedName)
import Data.Argonaut.Core (Json, caseJson, fromArray, fromBoolean, fromNumber, fromObject, fromString, jsonNull)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError)
import Data.Argonaut.Encode (encodeJson)
import Data.Array as A
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..), note)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Foldable (foldMap)
import Data.List as L
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe, fromMaybe)
import Data.Number (infinity, isFinite, isNaN, nan)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), split)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DepGraph (Labelling, Support(..), VisibleGraph, bySource, controlSets, paths, positions)
import Dict (Dict(..))
import Dict as D
import Foreign.Object (Object)
import Foreign.Object as O
import Lattice (DepKind(..))
import Literal (Literal(..))
import Path (Path, PathSet, Vertex(..), members, pathSet, sourceAt)
import Pretty (prettyP)
import Util (type (×), MayFail, absurd, definitely', error, (!), (×))
import Util.Map (get, insert, lookup, maplet, toUnfoldable)
import Util.Set (empty, unions)
import Val (BaseVal(..), VertexWithDoc, DictRep(..), MatrixRep(..), Val(..))

-- Data sufficient to draw and query a figure without parser or evaluator
type FigGraph =
   { graph :: VisibleGraph Val DepKind
   , ins :: Dict VertexWithDoc -- input name ↦ vertex
   , out :: VertexWithDoc
   , ιs :: Labelling VertexWithDoc -- documented intermediates
   , ignored :: Labelling (Set Path) -- input positions left out of linked queries
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

str
   :: { output :: String -- pseudo-variable to use as name of output view
      , input :: String -- prefix for input views
      , intermediate :: String
      }
str =
   { output: "output"
   , input: "input"
   , intermediate: "intermediate"
   }

type VertexWithDocRep = Int × Maybe Int

-- Position in a value as its index under the position ordering
type PosRep = Int

-- Source positions by source vertex
type SourcesRep a = Array (Int × Array a)

-- Index of control sources among the path sets, then weight of every other source
type SupportRep = Int × SourcesRep (PosRep × Int)

type Classes = Object (Array FieldName) -- class ↦ field names

type FigGraphRep =
   { classes :: Classes
   , vals :: Array (Int × Json)
   , pathSets :: Array (SourcesRep PosRep)
   , edges :: Array (Int × Array (PosRep × SupportRep)) -- target ↦ position ↦ support
   , ins :: Array (String × VertexWithDocRep)
   , out :: VertexWithDocRep
   , intermediates :: Array (Int × VertexWithDocRep)
   , ignored :: Array (Int × Array PosRep)
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

encodeFigGraph :: FigGraph -> MayFail Json
encodeFigGraph { graph, ins, out, ιs, ignored, linking, rowFilter } = do
   vals <- for (Map.toUnfoldable graph.vals) \(p@(Vertex i) × v) -> bimap (failure p) (i × _) (encodeVal v)
   pure $ encodeJson
      ( { classes: unions (classes <$> Map.values graph.vals)
        , vals
        , pathSets: pathSets <#> \ps -> map (map fst) <$> encodeSources (Set.toMap (members ps))
        , edges: Map.toUnfoldable graph.edges <#> \(b × supports) ->
             encodeVertex b × reindex (index b) (encodeSupport <$> supports)
        , ins: map encodeVertexWithDoc <$> D.toArrayWithKey (×) ins
        , out: encodeVertexWithDoc out
        , intermediates: labelling encodeVertexWithDoc ιs
        , ignored: Map.toUnfoldable ignored <#> \(a × ps) -> encodeVertex a × Set.toUnfoldable (Set.map (index a) ps)
        , linking
        , rowFilter
        } :: FigGraphRep
      )
   where
   failure :: Vertex -> String -> String
   failure p construct = construct <> " in " <> fromMaybe "doc" (Map.lookup p vertexRole)
      <> " is currently unsupported in a figure graph"

   vertexRole :: Labelling String
   vertexRole = Map.insert (fst out) str.output $ Map.union
      (ιs <#> \(_ × d) -> str.intermediate <> foldMap (\d' -> " " <> prettyP (get d' graph.vals)) d)
      (Map.fromFoldable (D.toArrayWithKey (\x (p × _) -> p × (str.input <> " " <> prettyP (Str x))) ins))

   labelling :: forall a b. (a -> b) -> Labelling a -> Array (Int × b)
   labelling f = Map.toUnfoldable >>> map (bimap encodeVertex f)

   encodeVertex :: Vertex -> Int
   encodeVertex (Vertex a) = a

   encodeVertexWithDoc :: VertexWithDoc -> VertexWithDocRep
   encodeVertexWithDoc (a × d) = encodeVertex a × (encodeVertex <$> d)

   -- Index of every position at each vertex
   indices :: Labelling (Map.Map Path PosRep)
   indices = graph.vals <#> \v -> Map.fromFoldable (mapWithIndex (\i (p × _) -> p × i) (positions (paths v)))

   index :: Vertex -> Path -> PosRep
   index a p = get p (get a indices)

   pathSets :: Array PathSet
   pathSets = Set.toUnfoldable (controlSets graph.edges)

   pathSetIndex :: Map.Map PathSet Int
   pathSetIndex = Map.fromFoldable (mapWithIndex (flip (×)) pathSets)

   encodeSupport :: Support PathSet DepKind -> SupportRep
   encodeSupport (Support ps ws) = get ps pathSetIndex × encodeSources (encodeDepKind <$> ws)

   encodeSources :: forall a. Map.Map Path a -> SourcesRep (PosRep × a)
   encodeSources ws = Map.toUnfoldable (bySource ws) <#> \(a × ws') -> encodeVertex a × reindex (index a) ws'

   reindex :: forall a. (Path -> PosRep) -> Map.Map Path a -> Array (PosRep × a)
   reindex f m = Map.toUnfoldable (Map.fromFoldable (lmap f <$> (Map.toUnfoldable m :: Array _)))

decodeFigGraph :: Json -> MayFail FigGraph
decodeFigGraph json = do
   rep :: FigGraphRep <- lmap printJsonDecodeError (decodeJson json)
   vals <- Map.fromFoldable <$> traverse (\(a × v) -> (Vertex a × _) <$> decodeVal rep.classes v) rep.vals
   let
      -- Paths at each vertex in the position ordering
      pathsAt = vals <#> \v -> A.fromFoldable (fst <$> positions (paths v))
      path a i = get (Vertex a) pathsAt ! i
      source a i = sourceAt (Vertex a) (path a i)
      pathSets = rep.pathSets <#> foldMap \(a × is) -> foldMap (source a >>> pathSet) is
      decodeSupport (k × ws) = Support (pathSets ! k) $
         Map.fromFoldable (ws >>= \(a × ws') -> bimap (source a) decodeDepKind <$> ws')
   pure
      { graph:
           { vals
           , edges: Map.fromFoldable $ rep.edges <#> \(b × supports) ->
                Vertex b × Map.fromFoldable (bimap (path b) decodeSupport <$> supports)
           }
      , ins: D.fromFoldable (map decodeVertexWithDoc <$> rep.ins)
      , out: decodeVertexWithDoc rep.out
      , ιs: labelling decodeVertexWithDoc rep.intermediates
      , ignored: Map.fromFoldable (rep.ignored <#> \(a × is) -> Vertex a × Set.fromFoldable (path a <$> is))
      , linking: rep.linking
      , rowFilter: rep.rowFilter
      }
   where
   labelling :: forall a b. (a -> b) -> Array (Int × a) -> Labelling b
   labelling f = map (bimap Vertex f) >>> Map.fromFoldable

   decodeVertexWithDoc :: VertexWithDocRep -> VertexWithDoc
   decodeVertexWithDoc (p × d) = Vertex p × (Vertex <$> d)

encodeDepKind :: DepKind -> Int
encodeDepKind Zero = error absurd
encodeDepKind Ctrl = 1
encodeDepKind Data = 2

decodeDepKind :: Int -> DepKind
decodeDepKind 1 = Ctrl
decodeDepKind 2 = Data
decodeDepKind _ = error absurd

classes :: Val Unit -> Classes
classes (Val _ u) = case u of
   Obj c xvs -> insert (dottedName c) (A.fromFoldable (fst <$> xvs)) (unions (classes <<< snd <$> xvs))
   List vs -> unions (classes <$> vs)
   Tuple vs -> unions (classes <$> vs)
   Dictionary (DictRep (Dict d)) -> unions (classes <<< snd <$> d)
   Matrix (MatrixRep (vss × _ × _)) -> unions (unions <<< map classes <$> vss)
   _ -> empty

encodeVal :: Val Unit -> MayFail Json
encodeVal (Val _ u) = case u of
   Lit (Int n) -> pure (tagged "int" (encodeJson n))
   Lit (Float x)
      | x == 0.0 && 1.0 / x < 0.0 -> pure (float "-0")
      | isFinite x -> pure (fromNumber x)
      | otherwise -> pure (float (if isNaN x then "nan" else if x > 0.0 then "inf" else "-inf"))
   Lit (Str s) -> pure (fromString s)
   Lit (Bool b) -> pure (fromBoolean b)
   Lit None -> pure jsonNull
   Obj c xvs -> do
      fields <- traverse encodeVal (O.fromFoldable xvs)
      pure (tagged "object" (encodeJson { "class": dottedName c, fields }))
   List vs -> fromArray <$> traverse encodeVal vs
   Tuple vs -> tagged "tuple" <<< fromArray <$> traverse encodeVal vs
   Dictionary (DictRep (Dict d)) -> tagged "dict" <<< fromObject <$> traverse (snd >>> encodeVal) d
   Matrix (MatrixRep (vss × i × j)) -> do
      elements <- traverse (traverse encodeVal) vss
      (\rows columns -> tagged "matrix" (encodeJson { elements, rows, columns })) <$> encodeVal i <*> encodeVal j
   Opaque q -> pure (tagged "opaque" (fromString (dottedName q)))
   Module q -> pure (tagged "module" (fromString (dottedName q)))
   Unbound -> pure (tagged "unbound" jsonNull)
   Fun _ -> unsupported "Function"
   TypeAlias _ _ -> unsupported "Type alias"
   where
   unsupported :: String -> MayFail Json
   unsupported = Left

   tagged :: String -> Json -> Json
   tagged tag = maplet tag >>> fromObject

   float :: String -> Json
   float = fromString >>> tagged "float"

decodeVal :: Classes -> Json -> MayFail (Val Unit)
decodeVal cs = val
   where
   val :: Json -> MayFail (Val Unit)
   val json = caseJson
      (const (lit None))
      (lit <<< Bool)
      (lit <<< Float)
      (lit <<< Str)
      (\vs -> Val unit <<< List <$> traverse val vs)
      ( toUnfoldable >>> case _ of
           [ tag × json' ] -> Val unit <$> tagged tag json'
           _ -> Left "Object with other than one key"
      )
      json

   lit :: Literal -> MayFail (Val Unit)
   lit = pure <<< Val unit <<< Lit

   decode :: forall a. DecodeJson a => Json -> MayFail a
   decode = decodeJson >>> lmap printJsonDecodeError

   name :: String -> Name
   name = split (Pattern ".") >>> NEL.fromFoldable >>> definitely'

   tagged :: String -> Json -> MayFail (BaseVal Unit)
   tagged "int" n = Lit <<< Int <$> decode n
   tagged "float" x = decode x >>= case _ of
      "nan" -> pure (Lit (Float nan))
      "inf" -> pure (Lit (Float infinity))
      "-inf" -> pure (Lit (Float (-infinity)))
      "-0" -> pure (Lit (Float ((-1.0) / infinity)))
      s -> Left ("Float " <> s)
   tagged "object" json = do
      { "class": c, fields } :: { "class" :: String, fields :: Object Json } <- decode json
      xs <- note ("Class " <> c <> " without field names") (lookup c cs)
      Obj (name c) <<< L.fromFoldable <$> for xs \x ->
         (x × _) <$> (note ("Object of class " <> c <> " without field " <> x) (lookup x fields) >>= val)
   tagged "tuple" vs = Tuple <$> (decode vs >>= traverse val)
   tagged "dict" kvs = do
      d :: Object Json <- decode kvs
      Dictionary <<< DictRep <<< Dict <<< map (unit × _) <$> traverse val d
   tagged "matrix" json = do
      { elements, rows, columns } :: { elements :: Array (Array Json), rows :: Json, columns :: Json } <- decode json
      vss <- traverse (traverse val) elements
      (\i j -> Matrix (MatrixRep (vss × i × j))) <$> val rows <*> val columns
   tagged "opaque" q = Opaque <<< name <$> decode q
   tagged "module" q = Module <<< name <$> decode q
   tagged "unbound" _ = pure Unbound
   tagged tag _ = Left ("Tag " <> tag)
