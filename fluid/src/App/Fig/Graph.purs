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
import DepGraph (Deriv(..), Edges, Labelling, Pos, SparseRel(..), VisibleGraph, sparseRel)
import Dict (Dict(..))
import Dict as D
import Foreign.Object (Object)
import Foreign.Object as O
import Lattice (DepKind(..))
import Literal (Literal(..))
import Pretty (prettyP)
import Util (type (×), MayFail, absurd, definitely', error, (×))
import Util.Map (get, insert, lookup, maplet, toUnfoldable)
import Util.Set (empty, unions)
import Val (BaseVal(..), DerivWithDoc, DictRep(..), MatrixRep(..), Val(..))

-- Data sufficient to draw and query a figure without parser or evaluator
type FigGraph =
   { graph :: VisibleGraph Val DepKind
   , ins :: Dict DerivWithDoc -- input name ↦ vertex
   , out :: DerivWithDoc
   , ιs :: Labelling DerivWithDoc -- documented intermediates
   , ignored :: Labelling (Set Pos) -- input positions left out of linked queries
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

type DerivWithDocRep = Int × Maybe Int

-- Dependence relation as target position ↦ source position ↦ weight
type RelRep = Array (Pos × Array (Pos × Int))

type Classes = Object (Array FieldName) -- class ↦ field names

type FigGraphRep =
   { classes :: Classes
   , vals :: Array (Int × Json)
   , edges :: Array (Int × Array (Int × RelRep)) -- target ↦ source ↦ relation
   , ins :: Array (String × DerivWithDocRep)
   , out :: DerivWithDocRep
   , intermediates :: Array (Int × DerivWithDocRep)
   , ignored :: Array (Int × Array Pos)
   , linking :: Boolean
   , rowFilter :: Maybe Filter
   }

encodeFigGraph :: FigGraph -> MayFail Json
encodeFigGraph { graph, ins, out, ιs, ignored, linking, rowFilter } = do
   vals <- for (Map.toUnfoldable graph.vals) \(p@(Deriv i) × v) -> bimap (failure p) (i × _) (encodeVal v)
   pure $ encodeJson
      ( { classes: unions (classes <$> Map.values graph.vals)
        , vals
        , edges: labelling (labelling encodeRel) graph.edges
        , ins: map encodeDeriv <$> D.toArrayWithKey (×) ins
        , out: encodeDeriv out
        , intermediates: labelling encodeDeriv ιs
        , ignored: labelling Set.toUnfoldable ignored
        , linking
        , rowFilter
        } :: FigGraphRep
      )
   where
   failure :: Deriv -> String -> String
   failure p kind = fromMaybe "Doc" (Map.lookup p parts) <> " contains a " <> kind
      <> ", which is currently unsupported in a figure graph"

   -- Name of input, intermediate or output at each vertex other than a doc
   parts :: Labelling String
   parts = Map.insert (fst out) "Output" $ Map.union
      (ιs <#> \(_ × d) -> "Intermediate" <> foldMap (\d' -> " " <> prettyP (get d' graph.vals)) d)
      (Map.fromFoldable (D.toArrayWithKey (\x (p × _) -> p × ("Input " <> prettyP (Str x))) ins))

   labelling :: forall a b. (a -> b) -> Labelling a -> Array (Int × b)
   labelling f = Map.toUnfoldable >>> map (bimap (\(Deriv p) -> p) f)

   encodeDeriv :: DerivWithDoc -> DerivWithDocRep
   encodeDeriv (Deriv p × d) = p × (d <#> \(Deriv q) -> q)

   encodeRel :: SparseRel DepKind -> RelRep
   encodeRel (SparseRel { in_ }) = Map.toUnfoldable (in_ <#> (map encodeDepKind >>> Map.toUnfoldable))

decodeFigGraph :: Json -> MayFail FigGraph
decodeFigGraph json = do
   rep :: FigGraphRep <- lmap printJsonDecodeError (decodeJson json)
   vals <- traverse (\(p × v) -> (Deriv p × _) <$> decodeVal rep.classes v) rep.vals
   pure
      { graph: { vals: Map.fromFoldable vals, edges: edges rep.edges }
      , ins: D.fromFoldable (map decodeDeriv <$> rep.ins)
      , out: decodeDeriv rep.out
      , ιs: labelling decodeDeriv rep.intermediates
      , ignored: labelling Set.fromFoldable rep.ignored
      , linking: rep.linking
      , rowFilter: rep.rowFilter
      }
   where
   labelling :: forall a b. (a -> b) -> Array (Int × a) -> Labelling b
   labelling f = map (bimap Deriv f) >>> Map.fromFoldable

   edges :: Array (Int × Array (Int × RelRep)) -> Edges (SparseRel DepKind)
   edges = labelling (labelling decodeRel)

   decodeDeriv :: DerivWithDocRep -> DerivWithDoc
   decodeDeriv (p × d) = Deriv p × (Deriv <$> d)

   decodeRel :: RelRep -> SparseRel DepKind
   decodeRel = map (map (map (map decodeDepKind) >>> Map.fromFoldable)) >>> Map.fromFoldable >>> sparseRel

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
   Fun _ -> unsupported "function"
   TypeAlias _ _ -> unsupported "type alias"
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
