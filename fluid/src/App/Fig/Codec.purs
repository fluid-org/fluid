module App.Fig.Codec where

import Prelude hiding (absurd)

import App.Fig (FigGraph)
import Data.Argonaut.Core (Json, caseJson, fromArray, fromBoolean, fromNumber, fromString, jsonNull)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, printJsonDecodeError)
import Data.Argonaut.Encode (encodeJson)
import Data.Array as A
import Data.Bifunctor (bimap, lmap)
import Data.Either (Either(..), note)
import Data.List (List)
import Data.List as L
import Data.List.NonEmpty as NEL
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.Number (infinity, isFinite, isNaN, nan)
import Data.Set as Set
import Data.Traversable (traverse)
import DepGraph (Deriv(..), Edges, Labelling, Pos, SparseRel(..), sparseRel)
import Dict as D
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

-- Finite float as number, string as string, Boolean as Boolean and None as null; any other value as an array
-- headed by a tag.
encodeVal :: Val Unit -> MayFail Json
encodeVal (Val _ u) = case u of
   Lit (Int n) -> pure (tagged "i" [ encodeJson n ])
   Lit (Float x)
      | isFinite x -> pure (fromNumber x)
      | otherwise -> pure (tagged "f" [ fromString (if isNaN x then "nan" else if x > 0.0 then "inf" else "-inf") ])
   Lit (Str s) -> pure (fromString s)
   Lit (Bool b) -> pure (fromBoolean b)
   Lit None -> pure jsonNull
   Obj c xvs -> do
      fields <- traverse (\(x × v) -> (\v' -> fromArray [ fromString x, v' ]) <$> encodeVal v) (A.fromFoldable xvs)
      pure (tagged "o" [ encodeJson (A.fromFoldable c), fromArray fields ])
   List vs -> tagged "l" <$> traverse encodeVal vs
   Tuple vs -> tagged "t" <$> traverse encodeVal vs
   Dictionary (DictRep d) ->
      tagged "d" <$> traverse (\(k × _ × v) -> (\v' -> fromArray [ fromString k, v' ]) <$> encodeVal v)
         (D.toArrayWithKey (×) d)
   Matrix (MatrixRep (vss × i × j)) -> do
      rows <- traverse (traverse encodeVal >>> map fromArray) vss
      tagged "m" <$> ((\i' j' -> [ fromArray rows, i', j' ]) <$> encodeVal i <*> encodeVal j)
   Opaque q -> pure (tagged "q" [ encodeJson (A.fromFoldable q) ])
   Module q -> pure (tagged "M" [ encodeJson (A.fromFoldable q) ])
   Unbound -> pure (tagged "u" [])
   Fun _ -> Left "Function in value shown in figure"
   TypeAlias _ _ -> Left "Type alias in value shown in figure"
   where
   tagged :: String -> Array Json -> Json
   tagged tag = A.cons (fromString tag) >>> fromArray

decodeVal :: Json -> MayFail (Val Unit)
decodeVal = caseJson
   (const (lit None))
   (lit <<< Bool)
   (lit <<< Float)
   (lit <<< Str)
   (\js -> note "Empty array" (A.uncons js) >>= \{ head, tail } -> decode head >>= \tag -> Val unit <$> tagged tag tail)
   (const (Left "Object"))
   where
   lit :: Literal -> MayFail (Val Unit)
   lit = pure <<< Val unit <<< Lit

   decode :: forall a. DecodeJson a => Json -> MayFail a
   decode = decodeJson >>> lmap printJsonDecodeError

   pair :: Json -> MayFail (String × Val Unit)
   pair json = decode json >>= case _ of
      [ k, v ] -> (×) <$> decode k <*> decodeVal v
      _ -> Left "Pair expected"

   name :: Json -> MayFail (NEL.NonEmptyList String)
   name json = (decode json :: MayFail (Array String)) >>= (NEL.fromFoldable >>> note "Empty name")

   tagged :: String -> Array Json -> MayFail (BaseVal Unit)
   tagged "i" [ n ] = Lit <<< Int <$> decode n
   tagged "f" [ x ] = decode x >>= case _ of
      "nan" -> pure (Lit (Float nan))
      "inf" -> pure (Lit (Float infinity))
      "-inf" -> pure (Lit (Float (-infinity)))
      s -> Left ("Float " <> s)
   tagged "o" [ c, fields ] = Obj <$> name c <*> (decode fields >>= traverse pair <#> toList)
   tagged "l" vs = List <$> traverse decodeVal vs
   tagged "t" vs = Tuple <$> traverse decodeVal vs
   tagged "d" kvs = Dictionary <<< DictRep <<< D.fromFoldable <<< map (map (unit × _)) <$> traverse pair kvs
   tagged "m" [ rows, i, j ] = do
      vss <- decode rows >>= traverse (traverse decodeVal)
      (\i' j' -> Matrix (MatrixRep (vss × i' × j'))) <$> decodeVal i <*> decodeVal j
   tagged "q" [ q ] = Opaque <$> name q
   tagged "M" [ q ] = Module <$> name q
   tagged "u" [] = pure Unbound
   tagged tag _ = Left ("Tag " <> tag)

   toList :: forall a. Array a -> List a
   toList = L.fromFoldable
