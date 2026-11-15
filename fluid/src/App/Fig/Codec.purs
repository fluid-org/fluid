module App.Fig.Codec where

import Prelude hiding (absurd)

import App.Fig (FigGraph)
import Bind (FieldName, Name, dottedName)
import Data.Argonaut.Core (Json, caseJson, fromArray, fromBoolean, fromNumber, fromObject, fromString, jsonNull)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError)
import Data.Argonaut.Encode (encodeJson)
import Data.Array as A
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..), note)
import Data.List as L
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Number (infinity, isFinite, isNaN, nan)
import Data.Set as Set
import Data.String (Pattern(..), split)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import DepGraph (Deriv(..), Edges, Labelling, Pos, SparseRel(..), sparseRel)
import Dict (Dict(..))
import Dict as D
import Foreign.Object (Object)
import Foreign.Object as O
import Lattice (DepKind(..))
import Literal (Literal(..))
import Util (type (×), MayFail, absurd, definitely', error, (×))
import Util.Map (insert, lookup, maplet, toUnfoldable)
import Util.Set (empty, unions)
import Val (BaseVal(..), DerivWithDoc, DictRep(..), MatrixRep(..), Val(..))

type DerivWithDocRep = Int × Maybe Int

-- Dependence relation as target position ↦ source position ↦ weight.
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
   }

encodeFigGraph :: FigGraph -> MayFail Json
encodeFigGraph { graph, ins, out, ιs, ignored, linking } = do
   vals <- traverse (\(Deriv p × v) -> (p × _) <$> encodeVal v) (Map.toUnfoldable graph.vals)
   pure $ encodeJson
      ( { classes: unions (classes <$> Map.values graph.vals)
        , vals
        , edges: labelling (labelling encodeRel) graph.edges
        , ins: map encodeDeriv <$> D.toArrayWithKey (×) ins
        , out: encodeDeriv out
        , intermediates: labelling encodeDeriv ιs
        , ignored: labelling Set.toUnfoldable ignored
        , linking
        } :: FigGraphRep
      )
   where
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

-- Classes of objects within the given value, each class with its field names.
classes :: Val Unit -> Classes
classes (Val _ u) = case u of
   Obj c xvs -> insert (dottedName c) (A.fromFoldable (fst <$> xvs)) (unions (classes <<< snd <$> xvs))
   List vs -> unions (classes <$> vs)
   Tuple vs -> unions (classes <$> vs)
   Dictionary (DictRep (Dict d)) -> unions (classes <<< snd <$> d)
   Matrix (MatrixRep (vss × _ × _)) -> unions (unions <<< map classes <$> vss)
   _ -> empty

-- List as array, finite float other than negative zero as number, string as string, Boolean as Boolean and
-- None as null; any other value as a JSON object with the name of its kind as the only key.
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
   Fun _ -> Left "Function in value shown in figure"
   TypeAlias _ _ -> Left "Type alias in value shown in figure"
   where
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
