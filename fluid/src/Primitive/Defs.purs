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
import Data.Foldable (foldM, foldMap)
import Data.FunctorWithIndex (mapWithIndex)
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
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd)
import Classes (ClassTable, askClasses, fields)
import Path (Path, Step(..))
import Types.Defs (cMatrix, cRange, callable, matrix, var)
import Cxt (CxtEntry(..)) as Cxt
import Cxt (Cxt, CxtEntry(Assigned), generalise)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Expr (Binop(..))
import File (class LoadFile, File(..), loadFileFromPath)
import Control.Monad.State (class MonadState)
import DepGraph (DepGraph, Support(..), construct, controlDep, dataDep, supportAt)
import Lattice (class BoundedJoinSemilattice, DepKind, Raw, bot)
import Literal (Literal(..), showFloat)
import Primitive (binopFun, boolean, fromDepFun, int, intOrNumber, number, string, typeMismatch, unary, union1, unpack)
import Util (MayFail, cons, type (+), type (×), definitely, definitely', orElse, orThrow, quoted, quotedList, singleton, throw, whenever, (×))
import Module.Defs (ModuleName, builtins, dataclasses, math, sys, typing)
import Foreign.Object (keys, lookup) as O
import Pretty (prettyP)
import Types (Primitive(..), Type(..), baseType) as T
import Types.Defs (float, int, intPair, none, object, str) as T
import Util.Map (lookup, unionWith_never, (\\))
import Util.Set (empty, (∈), (∪))
import Util.Map as Dict
import Util.Map as Map
import Val (BaseVal(..), DepOp, DictRep(..), Env, ForeignOp(..), ForeignOp'(..), Fun(..), GVal, Label, MatrixRep(..), Position, Val(..), dictEntries, elementCount, matrixPut)
import Val.Dependence (applyDepFun, childAt, deliver, dictionary, elementsAt, newValue, positionsIn, reuseAt, sequenceOf)

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
        , extern min_ × generalise (callable [ T.ListTy (var "T") ] (var "T"))
        , extern max_ × generalise (callable [ T.ListTy (var "T") ] (var "T"))
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
   ForeignOp ("len" × ForeignOp' { arity: 1, depOp: fromDepFun depFun })
   where
   depFun :: forall a. List (Val a) -> MayFail (Val a)
   depFun (v@(Val α u) : Nil) = case elementCount v of
      Just n -> Right (Val α (Lit (Int n)))
      Nothing -> Left (typeMismatch u "Sized")
   depFun _ = Left "Single argument expected"

sorted :: ForeignOp
sorted =
   ForeignOp ("sorted" × ForeignOp' { arity: 1, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (l@(_ × Val _ (List _)) : Nil) = sort (elementsAt l <#> (_ × empty)) <#> \us ->
      deliver (singleton ctl) $ sequenceOf List (dataDep (fst l)) $
         us <#> \(u × ps) -> deliver (singleton (fst l) ∪ ps) (reuseAt u)
   depOp _ _ ((_ × Val _ u) : Nil) = throw (typeMismatch u "list")
   depOp _ _ _ = throw "Single argument expected"

   sort :: forall m. MonadError Error m => List (Position × Set Path) -> m (List (Position × Set Path))
   sort us
      | L.length us < 2 = pure us
      | otherwise = join (merge empty <$> sort (L.take n us) <*> sort (L.drop n us))
           where
           n = L.length us / 2

   merge
      :: forall m
       . MonadError Error m
      => Set Path
      -> List (Position × Set Path)
      -> List (Position × Set Path)
      -> m (List (Position × Set Path))
   merge ps Nil us' = pure (map (ps ∪ _) <$> us')
   merge ps us Nil = pure (map (ps ∪ _) <$> us)
   merge ps ((u × qs) : us) ((u' × qs') : us') = compareAt Lt u' u >>= \(b × ps') ->
      let
         ps'' = ps ∪ ps' ∪ qs ∪ qs'
      in
         if b then ((u' × ps'') : _) <$> merge ps'' ((u × qs) : us) us'
         else ((u × ps'') : _) <$> merge ps'' us ((u' × qs') : us')

min_ :: ForeignOp
min_ = extremum "min" Lt

max_ :: ForeignOp
max_ = extremum "max" Gt

extremum :: String -> Binop -> ForeignOp
extremum id op =
   ForeignOp (id × ForeignOp' { arity: 1, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (l@(_ × Val _ (List _)) : Nil) = case elementsAt l of
      Nil -> throw ("ValueError: " <> id <> "() iterable argument is empty")
      u : us -> foldM step (u × empty) us <#> \(u' × ps) ->
         deliver (Set.fromFoldable [ ctl, fst l ] ∪ ps) (reuseAt u')
   depOp _ _ ((_ × Val _ u) : Nil) = throw (typeMismatch u "list")
   depOp _ _ _ = throw "Single argument expected"

   step :: forall m. MonadError Error m => Position × Set Path -> Position -> m (Position × Set Path)
   step (u × ps) u' = compareAt op u' u <#> \(b × ps') -> (if b then u' else u) × (ps ∪ ps')

exit :: ForeignOp
exit =
   ForeignOp ("exit" × ForeignOp' { arity: 1, depOp: fromDepFun depFun })
   where
   depFun :: forall a. List (Val a) -> MayFail (Val a)
   depFun (Val _ (Lit (Int n)) : Nil) = Left ("Exit status " <> show n)
   depFun (Val _ u : Nil) = Left (typeMismatch u "int")
   depFun _ = Left "Single argument expected"

print_ :: ForeignOp
print_ =
   ForeignOp ("print" × ForeignOp' { arity: 1, depOp: fromDepFun depFun })
   where
   depFun :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depFun (_ : Nil) = pure (Val zero (Lit None))
   depFun _ = Left "Single argument expected"

loadJson :: ForeignOp
loadJson =
   ForeignOp ("load_json" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp _ ctl rs
      | Val _ (Fun (Type τ)) : Val _ (Lit (Str path)) : Nil <- snd <$> rs = do
           classes <- askClasses
           json <- loadJsonFile path
           v <- orThrow (jsonVal classes τ json)
           pure (deliver (Set.fromFoldable (ctl : (fst <$> rs))) (v × construct mempty M.empty))
   depOp _ _ _ = throw "Type and string expected"

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
   ForeignOp ("dims" × ForeignOp' { arity: 1, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (m@(_ × Val _ (Matrix _)) : Nil) =
      pure $ deliver (singleton ctl) $ sequenceOf Tuple (dataDep (fst m)) $
         deliver (singleton (fst m)) <<< reuseAt <$> (childAt MatrixRows m : childAt MatrixCols m : Nil)
   depOp _ _ _ = throw "Matrix expected"

matrixUpdate :: ForeignOp
matrixUpdate =
   ForeignOp ("matrixUpdate" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (m@(_ × Val _ (Matrix r@(MatrixRep (vss × _ × _)))) : ix : v : Nil)
      | Val _ (Tuple [ Val _ (Lit (Int i)), Val _ (Lit (Int j)) ]) <- snd ix =
           let
              kept step = step × snd (deliver (singleton (fst m)) (reuseAt (childAt step m)))
              element i' j' _
                 | i' == i && j' == j = MatrixElement i j × snd (deliver (positionsIn ix) (reuseAt v))
                 | otherwise = kept (MatrixElement i' j')
              elements = Array.concat (mapWithIndex (mapWithIndex <<< element) vss)
           in
              pure $ deliver (singleton ctl) $ Val unit (Matrix (matrixPut i j (const (snd v)) r)) ×
                 construct (dataDep (fst m)) (M.fromFoldable ([ kept MatrixRows, kept MatrixCols ] <> elements))
   depOp _ _ _ = throw "Matrix, pair of integers and value expected"

find_str :: ForeignOp
find_str =
   ForeignOp ("find_str" × ForeignOp' { arity: 2, depOp: fromDepFun depFun })
   where
   depFun :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depFun (Val α (Lit (Str s1)) : Val β (Lit (Str s2)) : Nil) = pure (Val (α + β) (Lit (Int (find s1 s2))))
   depFun _ = Left "Two strings expected"

   find :: String -> String -> Int
   find s1 s2 = fromMaybe (-1) (String.indexOf (Pattern s1) s2)

search :: ForeignOp
search =
   ForeignOp ("search" × ForeignOp' { arity: 2, depOp: fromDepFun depFun })
   where
   depFun :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depFun (Val α (Lit (Str regex)) : Val β (Lit (Str str)) : Nil) = matchIndex regex str <#> Val (α + β)
   depFun _ = Left "Two strings expected"

   matchIndex :: forall a. String -> String -> MayFail (BaseVal a)
   matchIndex regex str = case Regex.regex regex noFlags of
      Left msg -> Left ("Regex expected: " <> msg)
      Right regex' -> pure (Lit (maybe None Int (Regex.search regex' str)))

-- When strings implement an abstract sequence type can express in terms of take/drop
split :: ForeignOp
split =
   ForeignOp ("split" × ForeignOp' { arity: 2, depOp: fromDepFun depFun })
   where
   depFun :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depFun (Val α (Lit (Int n)) : Val β (Lit (Str str)) : Nil) =
      pure (Val (α + β) (Tuple [ part (String.take n str), part (String.drop n str) ]))
      where
      part w = Val (α + β) (Lit (Str w))
   depFun _ = Left "Int and string expected"

dict_difference :: ForeignOp
dict_difference =
   ForeignOp ("dict_difference" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (d@(_ × Val _ (Dictionary (DictRep es))) : d'@(_ × Val _ (Dictionary (DictRep es'))) : Nil) =
      pure $ deliver (singleton ctl) $ dictionary (dataDep (fst d) <> dataDep (fst d')) $
         entryAt (Set.fromFoldable [ fst d, fst d' ]) d <$> L.fromFoldable (Map.keys (es \\ es'))
   depOp _ _ _ = throw "Dictionaries expected."

dict_disjointUnion :: ForeignOp
dict_disjointUnion =
   ForeignOp ("dict_disjointUnion" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (d@(_ × Val _ (Dictionary (DictRep es))) : d'@(_ × Val _ (Dictionary (DictRep es'))) : Nil) =
      pure $ deliver (singleton ctl) $ dictionary (dataDep (fst d) <> dataDep (fst d')) $
         L.fromFoldable (Map.keys (unionWith_never es es')) <#> \k ->
            if k ∈ es then entryAt (singleton (fst d)) d k else entryAt (singleton (fst d')) d' k
   depOp _ _ _ = throw "Dictionaries expected"

foldl_with_index :: ForeignOp
foldl_with_index =
   ForeignOp ("foldl_with_index" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp apply ctl (g : r : d : Nil) = do
      g' <- newValue (deliver (singleton ctl) (reuseAt g))
      r' <- newValue (deliver (singleton ctl) (reuseAt r))
      reuseAt <$> foldM (step g') r' (Dict.toUnfoldable (dictEntries (snd d)) :: List (String × (Unit × Raw Val)))
      where
      step g' acc (k × _) = entryValue k d >>= \u -> apply g' (childAt (DictKey k) d : acc : u : Nil)
   depOp _ _ _ = throw "Function, value and dictionary expected"

get :: ForeignOp
get =
   ForeignOp ("get" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (k@(_ × Val _ (Lit (Str x))) : d@(_ × Val _ (Dictionary (DictRep es))) : Nil) =
      pure $ deliver (singleton ctl) case lookup x es of
         Nothing -> Val unit (Lit None) × construct (dataDep (fst k) <> dataDep (fst d)) M.empty
         Just _ -> deliver (Set.fromFoldable [ fst k, fst d, fst (childAt (DictKey x) d) ]) (reuseAt (childAt (DictVal x) d))
   depOp _ _ _ = throw "String and dictionary expected"

insert :: ForeignOp
insert =
   ForeignOp ("insert" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp _ ctl (d@(_ × Val _ (Dictionary (DictRep es))) : k@(_ × Val _ (Lit (Str x))) : v : Nil) =
      pure $ deliver (singleton ctl) $ dictionary (dataDep (fst d)) $
         (entryAt (singleton (fst d)) d <$> L.fromFoldable (Set.delete x (Map.keys es))) <> singleton (reuseAt k × reuseAt v)
   depOp _ _ _ = throw "Dictionary, key and value expected"

dict_intersectionWith :: ForeignOp
dict_intersectionWith =
   ForeignOp ("dict_intersectionWith" × ForeignOp' { arity: 3, depOp })
   where
   depOp :: DepOp
   depOp apply ctl (g : d1 : d2 : Nil) = do
      g' <- newValue (deliver (singleton ctl) (reuseAt g))
      dictFrom ctl (d1 : d2 : Nil) <$>
         for (L.filter (\(k × _) -> lookup k (dictEntries (snd d2)) /= Nothing) (Dict.toUnfoldable (dictEntries (snd d1))))
            \(k × _) -> (k × _) <$> do
               u1 <- entryValue k d1
               u2 <- entryValue k d2
               apply g' (u1 : u2 : Nil)
   depOp _ _ _ = throw "Function and two dictionaries expected"

dict_map :: ForeignOp
dict_map =
   ForeignOp ("dict_map" × ForeignOp' { arity: 2, depOp })
   where
   depOp :: DepOp
   depOp apply ctl (g : d : Nil) = do
      g' <- newValue (deliver (singleton ctl) (reuseAt g))
      dictFrom ctl (singleton d) <$>
         for (Dict.toUnfoldable (dictEntries (snd d)) :: List (String × (Unit × Raw Val)))
            \(k × _) -> (k × _) <$> (entryValue k d >>= \u -> apply g' (singleton u))
   depOp _ _ _ = throw "Function and dictionary expected"

-- Outcome and source positions of comparing the values at two positions
compareAt :: forall m. MonadError Error m => Binop -> Position -> Position -> m (Boolean × Set Path)
compareAt op u u' = do
   v × δ <- orThrow (applyDepFun (binopFun op) empty (u : u' : Nil) :: MayFail (GVal DepKind))
   b × _ <- orThrow (unpack boolean v)
   pure (b × case supportAt δ Nil of Support ps ws -> ps ∪ Map.keys ws)

-- Reuse key and value of a dictionary entry under control of given positions
entryAt :: forall s. Semiring s => Set Path -> Position -> String -> GVal s × GVal s
entryAt ps d k = deliver ps (reuseAt (childAt (DictKey k) d)) × deliver ps (reuseAt (childAt (DictVal k) d))

-- Entry k of the dictionary at position d, as a value at a new vertex
entryValue
   :: forall m s
    . MonadState (DepGraph Label s) m
   => Semiring s
   => String
   -> Position
   -> m Position
entryValue k d =
   newValue $ deliver (Set.fromFoldable [ fst d, fst (childAt (DictKey k) d) ]) (reuseAt (childAt (DictVal k) d))

-- Dictionary with the values at given positions; root and keys depend on the roots and keys of the dictionaries ds
dictFrom :: forall s. Semiring s => Path -> List Position -> List (String × Position) -> GVal s
dictFrom ctl ds kvs = dictionary (controlDep (singleton ctl) <> foldMap (fst >>> dataDep) ds) $
   kvs <#> \(k × r) ->
      (Val unit (Lit (Str k)) × construct (foldMap (\d -> dataDep (fst (childAt (DictKey k) d))) ds) M.empty) × reuseAt r

quot :: ForeignOp
quot = intBinary "quot" I.quot

rem :: ForeignOp
rem = intBinary "rem" I.rem

intBinary :: String -> (Int -> Int -> Int) -> ForeignOp
intBinary id f =
   ForeignOp (id × ForeignOp' { arity: 2, depOp: fromDepFun depFun })
   where
   depFun :: forall a. Semiring a => List (Val a) -> MayFail (Val a)
   depFun (Val α (Lit (Int m)) : Val β (Lit (Int n)) : Nil) = pure (Val (α + β) (Lit (Int (f m n))))
   depFun _ = Left "Two integers expected"

round :: Number -> Int
round x = definitely "round of non-finite or out-of-range number" (Int.fromNumber r)
   where
   r = if x - N.floor x == 0.5 then 2.0 * N.round (x / 2.0) else N.round x

numToStr :: Int + Number -> String
numToStr = show `union1` showFloat
