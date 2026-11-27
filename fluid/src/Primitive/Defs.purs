module Primitive.Defs where

import Prelude hiding (absurd, apply, div, mod, top)

import Bind (Bind, Name, Var, dottedName, qual, varName)
import Control.Monad.Error.Class (class MonadError)
import Control.Alt ((<|>))
import Data.Argonaut.Core (Json, caseJson, isNull, stringify, toArray, toBoolean, toObject, toString)
import Data.Argonaut.Core (toNumber) as J
import Data.Argonaut.Decode (parseJson)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either(..))
import Data.Foldable (foldM, foldl)
import Data.Int (ceil, floor, toNumber)
import Data.Int (quot, rem) as I
import Data.Int as Int
import Data.List (List(..), (:))
import Data.List as L
import Data.List.NonEmpty (last)
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (wrap)
import Data.Number (fromString)
import Data.Number (cos, e, exp, floor, log, pi, round, sin, sqrt, tan) as N
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Traversable (for, traverse)
import Data.Lazy (defer, force)
import Data.Tuple (fst, snd)
import Classes (ClassTable, askClasses, fields)
import Types.Defs (cMatrix, cRange, callable, matrix, var)
import Cxt (CxtEntry(..)) as Cxt
import Cxt (Cxt, CxtEntry(Assigned), generalise)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (apply) as Dep
import Expr (Binop(..))
import File (class LoadFile, File(..), loadFileFromPath)
import DepGraph (zeros)
import Lattice (class BoundedJoinSemilattice, class DepSemiring, Raw, bot, ctrlWeight)
import Literal (Literal(..), showFloat)
import Primitive (binopRel, boolean, int, intOrNumber, number, string, typeMismatch, unary, union1, unpack)
import Util (MayFail, cons, type (+), type (×), definitely, definitely', orElse, orThrow, quoted, quotedList, singleton, throw, whenever, (×))
import Module.Defs (ModuleName, builtins, dataclasses, math, sys, typing)
import Foreign.Object (keys, lookup) as O
import Pretty (prettyP)
import Types (Primitive(..), Type(..), baseType) as T
import Types.Defs (float, int, intPair, none, object, str) as T
import Util.Map (lookup, unionWith_never, (\\))
import Util.Map as Dict
import Util.Map as Map
import Val (BaseVal(..), DepOp, DictRep(..), Env, ForeignOp(..), ForeignOp'(..), Fun(..), GVal, MatrixRep(..), Val(..), construct, deliver, dictEntries, dictEntry, elementCount, fromRel, gval, matrixPut, pureRel, root, via)

extern :: forall a. BoundedJoinSemilattice a => ForeignOp -> Bind (Val a)
extern (ForeignOp (id × φ)) =
   id × Val bot (Fun (Prim (ForeignOp (id × φ))))

predefinedClasses :: ClassTable
predefinedClasses = M.fromFoldable
   [ cRange × { typeParams: Nil, fields: ("start" × int) : ("stop" × int) : Nil, base: Nothing }
   , cMatrix × { typeParams: "T" : Nil, fields: Nil, base: Nothing }
   ]
   where
   int = T.PrimitiveTy T.Int

predefined :: Map ModuleName (Cxt × Raw Env)
predefined = M.fromFoldable
   [ predefinedModule builtins [ "None", "object", "bool", "int", "float", "str", "list", "dict", "tuple", "type" ]
        [ cRange, cMatrix ]
        [ extern print_ × generalise (callable [ T.object ] T.none)
        , extern len × generalise (callable [ T.PrimitiveTy T.Sized ] T.int)
        , extern sorted × generalise (callable [ T.ListTy (var "T") ] (T.ListTy (var "T")))
        , unary "round" { i: intOrNumber, o: int, fwd: identity `union1` round } × generalise (callable [ T.float ] T.int)
        , extern dims × generalise (callable [ matrix (var "T") ] T.intPair)
        , extern loadJson × generalise (callable [ T.TypeTy (var "T"), T.str ] (var "T"))
        , unary "str_to_float" { i: string, o: number, fwd: definitely' <<< fromString } × generalise (callable [ T.str ] T.float)
        , unary "num_to_str" { i: intOrNumber, o: string, fwd: numToStr } × generalise (callable [ T.float ] T.str) -- rename to 'str' (more Pythonic)
        -- TODO: rename the rest of these (apart from dict_map?) to lose the dict_ prefix
        , extern dict_difference × generalise (callable [ T.DictTy (var "T"), T.DictTy (var "U") ] (T.DictTy (var "T")))
        , extern dict_disjointUnion × generalise (callable [ T.DictTy (var "T"), T.DictTy (var "T") ] (T.DictTy (var "T")))
        , extern foldl_with_index × generalise (callable [ callable [ T.str, var "U", var "T" ] (var "U"), var "U", T.DictTy (var "T") ] (var "U"))
        , extern get × generalise (callable [ T.str, T.DictTy (var "T") ] (T.UnionTy (var "T") T.none))
        , extern insert × generalise (callable [ T.DictTy (var "T"), T.str, var "T" ] (T.DictTy (var "T")))
        , extern dict_intersectionWith × generalise (callable [ callable [ var "T", var "U" ] (var "V"), T.DictTy (var "T"), T.DictTy (var "U") ] (T.DictTy (var "V")))
        , extern dict_map × generalise (callable [ callable [ var "T" ] (var "U"), T.DictTy (var "T") ] (T.DictTy (var "U")))
        , extern matrixUpdate × generalise (callable [ matrix (var "T"), T.intPair, var "T" ] (matrix (var "T")))
        , extern find_str × generalise (callable [ T.str, T.str ] T.int)
        , extern search × generalise (callable [ T.str, T.str ] (T.UnionTy T.int T.none))
        , extern split × generalise (callable [ T.int, T.str ] (T.TupleTy (T.str : T.str : Nil)))
        , extern quot × generalise (callable [ T.int, T.int ] T.int)
        , extern rem × generalise (callable [ T.int, T.int ] T.int)
        ]
   , predefinedModule math [] []
        [ ("pi" × Val bot (Lit (Float N.pi))) × generalise T.float
        , ("e" × Val bot (Lit (Float N.e))) × generalise T.float
        , unary "sqrt" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sqrt) `union1` N.sqrt } × generalise (callable [ T.float ] T.float)
        , unary "exp" { i: intOrNumber, o: number, fwd: (toNumber >>> N.exp) `union1` N.exp } × generalise (callable [ T.float ] T.float)
        , unary "log" { i: intOrNumber, o: number, fwd: (toNumber >>> N.log) `union1` N.log } × generalise (callable [ T.float ] T.float)
        , unary "sin" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sin) `union1` N.sin } × generalise (callable [ T.float ] T.float)
        , unary "cos" { i: intOrNumber, o: number, fwd: (toNumber >>> N.cos) `union1` N.cos } × generalise (callable [ T.float ] T.float)
        , unary "tan" { i: intOrNumber, o: number, fwd: (toNumber >>> N.tan) `union1` N.tan } × generalise (callable [ T.float ] T.float)
        , unary "floor" { i: intOrNumber, o: int, fwd: identity `union1` floor } × generalise (callable [ T.float ] T.int)
        , unary "ceil" { i: intOrNumber, o: int, fwd: identity `union1` ceil } × generalise (callable [ T.float ] T.int)
        ]
   , predefinedModule sys [] []
        [ ("argv" × Val bot (List [])) × generalise (T.ListTy T.str)
        , extern exit × generalise (callable [ T.int ] (T.PrimitiveTy T.Never))
        ]
   , predefinedModule typing [ "Callable", "Literal", "Never", "Sized" ] [] []
   , predefinedModule dataclasses [ "dataclass" ] [] []
   ]
   where
   predefinedModule :: ModuleName -> Array Var -> Array Name -> Array (Bind (Val Unit) × Cxt.CxtEntry) -> ModuleName × (Cxt × Raw Env)
   predefinedModule q names classes members =
      q × (M.fromFoldable (lmap fst <$> bindings) × wrap (D.fromFoldable (fst <$> bindings)))
      where
      bindings = cons ((varName × Val bot (Lit (Str (dottedName q)))) × Assigned T.str) members
         <> (classes <#> \c -> (last c × Val bot (Fun (Type (T.ClassTy c Nil)))) × Cxt.Type c)
         <> (names <#> \x -> (x × Val bot (Opaque (qual q x))) × Cxt.PredefName)

len :: ForeignOp
len =
   ForeignOp ("len" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (v@(Val α u) : Nil) = case elementCount v of
      Just n -> Right (Val α (Lit (Int n)))
      Nothing -> Left (typeMismatch u "Sized")
   depRel _ = Left "Single argument expected"

sorted :: ForeignOp
sorted =
   ForeignOp ("sorted" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. DepSemiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (List vs) : Nil) = sort (L.fromFoldable vs) <#> \vs' -> Val α (List (Array.fromFoldable vs'))
   depRel (Val _ u : Nil) = Left (typeMismatch u "list")
   depRel _ = Left "Single argument expected"

   sort :: forall a. DepSemiring a => List (Val a) -> MayFail (List (Val a))
   sort vs
      | L.length vs < 2 = pure vs
      | otherwise = join (merge zero <$> sort (L.take n vs) <*> sort (L.drop n vs))
           where
           n = L.length vs / 2

   merge :: forall a. DepSemiring a => a -> List (Val a) -> List (Val a) -> MayFail (List (Val a))
   merge β Nil vs' = pure (withCtrl β <$> vs')
   merge β vs Nil = pure (withCtrl β <$> vs)
   merge β (v : vs) (v' : vs') = binopRel Lt v' v >>= unpack boolean >>= \(b × γ) -> take b (β + γ)
      where
      take true β' = (withCtrl β' v' : _) <$> merge β' (v : vs) vs'
      take false β' = (withCtrl β' v : _) <$> merge β' vs (v' : vs')

   withCtrl :: forall a. DepSemiring a => a -> Val a -> Val a
   withCtrl β (Val α u) = Val (α + ctrlWeight * β) u

exit :: ForeignOp
exit =
   ForeignOp ("exit" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (Val _ (Lit (Int n)) : Nil) = Left ("Exit status " <> show n)
   depRel (Val _ u : Nil) = Left (typeMismatch u "int")
   depRel _ = Left "Single argument expected"

print_ :: ForeignOp
print_ =
   ForeignOp ("print" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (_ : Nil) = pure (Val zero (Lit None))
   depRel _ = Left "Single argument expected"

loadJson :: ForeignOp
loadJson =
   ForeignOp ("load_json" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp ctrl vs@({ val: Val _ (Fun (Type τ)) } : { val: Val _ (Lit (Str path)) } : Nil) = do
      classes <- askClasses
      json <- loadJsonFile path
      v <- orThrow (jsonVal classes τ json)
      fromRel (\us -> ctrlWeight * foldl add zero (root <$> us) <$ v) ctrl vs
   depOp _ _ = throw "Type and string expected"

loadJsonFile :: forall m. MonadError Error m => MonadAff m => LoadFile m => String -> m Json
loadJsonFile path = do
   str <- loadFileFromPath (File path) >>= orElse ("File not found: " <> path)
   case parseJson str of
      Left err -> throw ("Failed to parse JSON: " <> show err)
      Right json -> pure json

jsonVal :: ClassTable -> T.Type -> Json -> MayFail (Raw Val)
jsonVal classes τ json = case τ of
   T.ListTy σ -> val <<< List <$> (traverse (jsonVal classes σ) =<< expect "array" (toArray json))
   T.TupleTy σs -> do
      elems <- expect ("array of length " <> show (L.length σs))
         (toArray json >>= \js -> whenever (Array.length js == L.length σs) js)
      val <<< Tuple <$> traverse (\(σ × j) -> jsonVal classes σ j) (Array.zip (Array.fromFoldable σs) elems)
   T.DictTy σ -> val <<< dictionary <$> (traverse (jsonVal classes σ) =<< expect "object" (toObject json))
   T.ClassTy c _ -> do
      obj <- expect "object" (toObject json)
      let xσs = fields classes c
      when (Set.fromFoldable (O.keys obj) /= Set.fromFoldable (fst <$> xσs))
         $ Left ("Expected fields of " <> quoted (last c) <> ": " <> quotedList (fst <$> xσs) <> "; got " <> quotedList (O.keys obj))
      val <<< Obj c <$> traverse (\(x × σ) -> (x × _) <$> jsonVal classes σ (definitely' (O.lookup x obj))) xσs
   T.PrimitiveTy T.Int -> val <<< Lit <<< Int <$> expect "integer" (J.toNumber json >>= Int.fromNumber)
   T.PrimitiveTy T.Float -> val <<< Lit <<< Float <$> expect "number" (J.toNumber json)
   T.PrimitiveTy T.Str -> val <<< Lit <<< Str <$> expect "string" (toString json)
   T.PrimitiveTy T.Bool -> val <<< Lit <<< Bool <$> expect "boolean" (toBoolean json)
   T.PrimitiveTy T.None -> val (Lit None) <$ expect "null" (whenever (isNull json) unit)
   T.UnionTy σ σ' -> jsonVal classes σ json <|> jsonVal classes σ' json
   T.LitTy ℓ -> jsonVal classes (T.baseType (T.LitTy ℓ)) json
   _ -> caseJson
      (\_ -> expect "value" Nothing)
      (pure <<< val <<< Lit <<< Bool)
      (\n -> pure (val (Lit (maybe (Float n) Int (Int.fromNumber n)))))
      (pure <<< val <<< Lit <<< Str)
      (traverse (jsonVal classes τ) >>> map (val <<< List))
      (traverse (jsonVal classes τ) >>> map (val <<< dictionary))
      json
   where
   val = Val unit

   expect :: forall a. String -> Maybe a -> MayFail a
   expect what = maybe (Left ("Expected " <> what <> " at " <> prettyP τ <> ", got " <> stringify json)) pure

   dictionary = map (unit × _) >>> wrap >>> DictRep >>> Dictionary

dims :: ForeignOp
dims =
   ForeignOp ("dims" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (Val α (Matrix (MatrixRep (_ × i × j))) : Nil) = pure (Val α (Tuple [ i, j ]))
   depRel _ = Left "Matrix expected"

matrixUpdate :: ForeignOp
matrixUpdate =
   ForeignOp ("matrixUpdate" × ForeignOp' { arity: 3, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (Val α (Matrix r) : Val _ (Tuple [ Val _ (Lit (Int i)), Val _ (Lit (Int j)) ]) : v : Nil) =
      pure (Val α (Matrix (matrixPut i j (const v) r)))
   depRel _ = Left "Matrix, pair of integers and value expected"

find_str :: ForeignOp
find_str =
   ForeignOp ("find_str" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Lit (Str s1)) : Val β (Lit (Str s2)) : Nil) = pure (Val (α + β) (Lit (Int (find s1 s2))))
   depRel _ = Left "Two strings expected"

   find :: String -> String -> Int
   find s1 s2 = fromMaybe (-1) (String.indexOf (Pattern s1) s2)

search :: ForeignOp
search =
   ForeignOp ("search" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Lit (Str regex)) : Val β (Lit (Str str)) : Nil) = matchIndex regex str <#> Val (α + β)
   depRel _ = Left "Two strings expected"

   matchIndex :: forall a. String -> String -> MayFail (BaseVal a)
   matchIndex regex str = case Regex.regex regex noFlags of
      Left msg -> Left ("Regex expected: " <> msg)
      Right regex' -> pure (Lit (maybe None Int (Regex.search regex' str)))

-- When strings implement an abstract sequence type can express in terms of take/drop
split :: ForeignOp
split =
   ForeignOp ("split" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Lit (Int n)) : Val β (Lit (Str str)) : Nil) =
      pure (Val (α + β) (Tuple [ part (String.take n str), part (String.drop n str) ]))
      where
      part w = Val (α + β) (Lit (Str w))
   depRel _ = Left "Int and string expected"

dict_difference :: ForeignOp
dict_difference =
   ForeignOp ("dict_difference" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Dictionary (DictRep d)) : Val β (Dictionary (DictRep d')) : Nil) =
      pure (Val (α + β) (Dictionary (DictRep (d \\ d'))))
   depRel _ = Left "Dictionaries expected."

dict_disjointUnion :: ForeignOp
dict_disjointUnion =
   ForeignOp ("dict_disjointUnion" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Dictionary (DictRep d)) : Val β (Dictionary (DictRep d')) : Nil) =
      pure (Val (α + β) (Dictionary (DictRep (unionWith_never d d'))))
   depRel _ = Left "Dictionaries expected"

foldl_with_index :: ForeignOp
foldl_with_index =
   ForeignOp ("foldl_with_index" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp ctrl (g : v : d : Nil) = do
      f <- gval <$> deliver ctrl g
      r <- deliver ctrl v
      foldM (step f) r (Dict.toUnfoldable (dictEntries d.val) :: List (String × (Unit × Raw Val)))
      where
      step f acc (k × _) = Dep.apply ctrl f (key : gval acc : entryValue k d : Nil)
         where
         key = { val: Val unit (Lit (Str k)), inEdges: via (\x -> Val (fst (dictEntry k x)) (Lit (Str k))) d }
   depOp _ _ = throw "Function, value and dictionary expected"

get :: ForeignOp
get =
   ForeignOp ("get" × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (Val α (Lit (Str s)) : Val _ (Dictionary (DictRep d)) : Nil) =
      pure (maybe (Val α (Lit None)) snd (lookup s d))
   depRel _ = Left "String and dictionary expected"

insert :: ForeignOp
insert =
   ForeignOp ("insert" × ForeignOp' { arity: 3, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (Val α (Dictionary (DictRep d)) : Val α' (Lit (Str k)) : v : Nil) =
      pure (Val α (Dictionary (DictRep (Map.insert k (α' × v) d))))
   depRel _ = Left "Dictionary, key and value expected"

dict_intersectionWith :: ForeignOp
dict_intersectionWith =
   ForeignOp ("dict_intersectionWith" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp ctrl (g : d1 : d2 : Nil) = do
      f <- gval <$> deliver ctrl g
      results <- for (L.filter (\(k × _) -> lookup k (dictEntries d2.val) /= Nothing) (Dict.toUnfoldable (dictEntries d1.val))) \(k × _) -> do
         r <- Dep.apply ctrl f (entryValue k d1 : entryValue k d2 : Nil)
         pure (k × gval r)
      construct ctrl (dictFrom (d1 : d2 : Nil) results)
   depOp _ _ = throw "Function and two dictionaries expected"

dict_map :: ForeignOp
dict_map =
   ForeignOp ("dict_map" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp ctrl (g : d : Nil) = do
      f <- gval <$> deliver ctrl g
      results <- for (Dict.toUnfoldable (dictEntries d.val) :: List (String × (Unit × Raw Val))) \(k × _) -> do
         r <- Dep.apply ctrl f (singleton (entryValue k d))
         pure (k × gval r)
      construct ctrl (dictFrom (singleton d) results)
   depOp _ _ = throw "Function and dictionary expected"

entryValue :: forall s. String -> GVal s -> GVal s
entryValue k d = { val: snd (dictEntry k d.val), inEdges: via (dictEntry k >>> snd) d }

-- Dictionary with the given values, its root and key positions from those of the dictionary values.
dictFrom :: forall s. Semiring s => List (GVal s) -> List (String × GVal s) -> GVal s
dictFrom ds kvs =
   { val: Val unit (Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × v) -> k × (unit × v.val)))))
   , inEdges: L.concat (ds <#> via \x -> Val (root x) (Dictionary (DictRep (Dict.mapWithKey (\k (_ × zu) -> fst (dictEntry k x) × zu) (force zd)))))
        <> L.concat (kvs <#> \(k × v) -> via (\y -> dict (Map.insert k (zero × y) (force zd))) v)
   }
   where
   zd = defer \_ -> D.fromFoldable (kvs <#> \(k × v) -> k × (zero × zeros v.val))
   dict = DictRep >>> Dictionary >>> Val zero

quot :: ForeignOp
quot = intBinary "quot" I.quot

rem :: ForeignOp
rem = intBinary "rem" I.rem

intBinary :: String -> (Int -> Int -> Int) -> ForeignOp
intBinary id f =
   ForeignOp (id × ForeignOp' { arity: 2, depOp: pureRel depRel })
   where
   depRel :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depRel (Val α (Lit (Int m)) : Val β (Lit (Int n)) : Nil) = pure (Val (α + β) (Lit (Int (f m n))))
   depRel _ = Left "Two integers expected"

round :: Number -> Int
round x = definitely "round of non-finite or out-of-range number" (Int.fromNumber r)
   where
   r = if x - N.floor x == 0.5 then 2.0 * N.round (x / 2.0) else N.round x

numToStr :: Int + Number -> String
numToStr = show `union1` showFloat
