module App.Fig.Codec where

import Prelude hiding (absurd)

import App.Fig (FigGraph)
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
import Data.Traversable (traverse)
import Data.Tuple (snd)
import DepGraph (Deriv(..), Edges, Labelling, Pos, SparseRel(..), sparseRel)
import Dict (Dict(..))
import Dict as D
import Foreign.Object as O
import Lattice (DepKind(..))
import Literal (Literal(..))
import Util (type (×), MayFail, absurd, error, (×))
import Val (BaseVal(..), DerivWithDoc, DictRep(..), MatrixRep(..), Val(..))

type DerivWithDocRep = Int × Maybe Int

-- Dependence relation as target position ↦ source position ↦ weight.
type RelRep = Array (Pos × Array (Pos × Int))

type FigGraphRep =
   { vals :: Array (Int × Json)
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
      ( { vals
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
   vals <- traverse (\(p × v) -> (Deriv p × _) <$> decodeVal v) rep.vals
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

-- List as array, finite float other than negative zero as number, string as string, Boolean as Boolean and
-- None as null; any other value as an object with the name of its kind as the only key.
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
      fields <- traverse (traverse encodeVal) (A.fromFoldable xvs)
      pure (tagged "object" (encodeJson { "class": A.fromFoldable c, fields }))
   List vs -> fromArray <$> traverse encodeVal vs
   Tuple vs -> tagged "tuple" <<< fromArray <$> traverse encodeVal vs
   Dictionary (DictRep (Dict d)) -> tagged "dict" <<< fromObject <$> traverse (snd >>> encodeVal) d
   Matrix (MatrixRep (vss × i × j)) -> do
      elements <- traverse (traverse encodeVal) vss
      (\rows columns -> tagged "matrix" (encodeJson { elements, rows, columns })) <$> encodeVal i <*> encodeVal j
   Opaque q -> pure (tagged "opaque" (encodeJson (A.fromFoldable q)))
   Module q -> pure (tagged "module" (encodeJson (A.fromFoldable q)))
   Unbound -> pure (tagged "unbound" jsonNull)
   Fun _ -> Left "Function in value shown in figure"
   TypeAlias _ _ -> Left "Type alias in value shown in figure"
   where
   tagged :: String -> Json -> Json
   tagged tag = O.singleton tag >>> fromObject

   float :: String -> Json
   float = fromString >>> tagged "float"

decodeVal :: Json -> MayFail (Val Unit)
decodeVal = caseJson
   (const (lit None))
   (lit <<< Bool)
   (lit <<< Float)
   (lit <<< Str)
   (\vs -> Val unit <<< List <$> traverse decodeVal vs)
   ( O.toUnfoldable >>> case _ of
        [ tag × json ] -> Val unit <$> tagged tag json
        _ -> Left "Object with other than one key"
   )
   where
   lit :: Literal -> MayFail (Val Unit)
   lit = pure <<< Val unit <<< Lit

   decode :: forall a. DecodeJson a => Json -> MayFail a
   decode = decodeJson >>> lmap printJsonDecodeError

   name :: Json -> MayFail (NEL.NonEmptyList String)
   name json = (decode json :: MayFail (Array String)) >>= (NEL.fromFoldable >>> note "Empty name")

   tagged :: String -> Json -> MayFail (BaseVal Unit)
   tagged "int" n = Lit <<< Int <$> decode n
   tagged "float" x = decode x >>= case _ of
      "nan" -> pure (Lit (Float nan))
      "inf" -> pure (Lit (Float infinity))
      "-inf" -> pure (Lit (Float (-infinity)))
      "-0" -> pure (Lit (Float ((-1.0) / infinity)))
      s -> Left ("Float " <> s)
   tagged "object" json = do
      { "class": c, fields } :: { "class" :: Json, fields :: Array (String × Json) } <- decode json
      Obj <$> name c <*> (L.fromFoldable <$> traverse (traverse decodeVal) fields)
   tagged "tuple" vs = Tuple <$> (decode vs >>= traverse decodeVal)
   tagged "dict" kvs = do
      d :: O.Object Json <- decode kvs
      Dictionary <<< DictRep <<< Dict <<< map (unit × _) <$> traverse decodeVal d
   tagged "matrix" json = do
      { elements, rows, columns } :: { elements :: Array (Array Json), rows :: Json, columns :: Json } <- decode json
      vss <- traverse (traverse decodeVal) elements
      (\i j -> Matrix (MatrixRep (vss × i × j))) <$> decodeVal rows <*> decodeVal columns
   tagged "opaque" q = Opaque <$> name q
   tagged "module" q = Module <$> name q
   tagged "unbound" _ = pure Unbound
   tagged tag _ = Left ("Tag " <> tag)
