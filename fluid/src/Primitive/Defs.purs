module Primitive.Defs where

import Prelude hiding (absurd, apply, div, mod, top)

import Bind (Bind, Var, dottedName, qual)
import Control.Monad.Error.Class (class MonadError)
import Data.Argonaut.Core (Json, caseJson)
import Data.Argonaut.Decode (parseJson)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM, foldl)
import Data.Int (ceil, floor, toNumber)
import Data.Int (quot, rem) as I
import Data.Int as Int
import Data.List (List(..), (:))
import Data.List as L
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (wrap)
import Data.Number (fromString)
import Data.Number (cos, e, exp, log, pi, sin, sqrt, tan) as N
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Traversable (for)
import Data.Tuple (fst, snd)
import DataType (cRange)
import DefiniteAssignment (ClassEntry, Cxt, Entry(..))
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (Error)
import Eval (apply) as Dep
import File (class LoadFile, File(..), loadFileFromPath)
import DepGraph (zeros)
import Lattice (class BoundedJoinSemilattice, Raw, bot, ctrlWeight)
import Literal (Literal(..))
import Primitive (int, intOrNumber, number, string, typeMismatch, unary, union1)
import Util (MayFail, type (+), type (×), definitely', error, orElse, singleton, throw, (×))
import ModuleGraph (ModuleName, builtins, dataclasses, math, sys, typing)
import Util.Map (constMap, keys, lookup, unionWith_never, (\\))
import Util.Map as Dict
import Util.Map as Map
import Val (BaseVal(..), DepOp, DictRep(..), Env, ForeignOp(..), ForeignOp'(..), Fun(..), GVal, MatrixRep(..), Val(..), construct, deliver, dictEntries, dictEntry, elementCount, fromRel, gval, matrixPut, pureRel, root, via)

extern :: forall a. BoundedJoinSemilattice a => ForeignOp -> Bind (Val a)
extern (ForeignOp (id × φ)) =
   id × Val bot (Fun (Prim (ForeignOp (id × φ))))

predefined :: Map ModuleName (Cxt × Raw Env)
predefined = M.fromFoldable
   [ predefinedModule builtins ("None" : "object" : "bool" : "int" : "float" : "str" : "list" : "dict" : "tuple" : Nil)
        [ "range" × { cxt: M.empty, name: cRange, typeParams: Nil, base: Nothing, fields: "start" : "stop" : Nil } ]
        [ extern print_
        , extern len
        -- Fluid-only members, without spec counterpart
        , extern dims
        , extern loadJson
        , unary "str_to_float" { i: string, o: number, fwd: definitely' <<< fromString }
        , unary "num_to_str" { i: intOrNumber, o: string, fwd: numToStr } -- rename to 'str' (more Pythonic)
        -- TODO: rename the rest of these (apart from dict_map?) to lose the dict_ prefix
        , extern dict_difference
        , extern dict_disjointUnion
        , extern foldl_with_index
        , extern get
        , extern insert
        , extern dict_intersectionWith
        , extern dict_map
        , extern matrixUpdate
        , extern find_str
        , extern search
        , extern split
        , extern quot
        , extern rem
        ]
   , predefinedModule math Nil []
        [ "pi" × Val bot (Lit (Float N.pi))
        , "e" × Val bot (Lit (Float N.e))
        , unary "sqrt" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sqrt) `union1` N.sqrt }
        , unary "exp" { i: intOrNumber, o: number, fwd: (toNumber >>> N.exp) `union1` N.exp }
        , unary "log" { i: intOrNumber, o: number, fwd: (toNumber >>> N.log) `union1` N.log }
        , unary "sin" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sin) `union1` N.sin }
        , unary "cos" { i: intOrNumber, o: number, fwd: (toNumber >>> N.cos) `union1` N.cos }
        , unary "tan" { i: intOrNumber, o: number, fwd: (toNumber >>> N.tan) `union1` N.tan }
        , unary "floor" { i: intOrNumber, o: int, fwd: identity `union1` floor }
        , unary "ceil" { i: intOrNumber, o: int, fwd: identity `union1` ceil }
        ]
   , predefinedModule sys Nil []
        [ "argv" × Val bot (List [])
        , extern exit
        ]
   , predefinedModule typing ("Callable" : "Literal" : "Never" : "Sized" : Nil) [] []
   , predefinedModule dataclasses ("dataclass" : Nil) [] []
   ]
   where
   predefinedModule :: ModuleName -> List Var -> Array (Bind ClassEntry) -> Array (Bind (Val Unit)) -> ModuleName × (Cxt × Raw Env)
   predefinedModule q names classes members = q × (cxt × wrap (ρ `unionWith_never` ρ_classes `unionWith_never` ρ_names))
      where
      ρ = D.fromFoldable (Array.cons ("__name__" × Val bot (Lit (Str (dottedName q)))) members)
      ρ_classes = D.fromFoldable classes <#> \cls -> Val bot (Fun (Type cls.name))
      ρ_names = D.fromFoldable (names <#> \x -> x × Val bot (Opaque (qual q x)))
      cxt = M.unions [ constMap PredefName (Set.fromFoldable names), Class <$> M.fromFoldable classes, constMap Assigned (keys ρ) ]

len :: ForeignOp
len =
   ForeignOp ("len" × ForeignOp' { arity: 1, depOp: pureRel depRel })
   where
   depRel :: forall a. List (Val a) -> MayFail (Val a)
   depRel (v@(Val α u) : Nil) = maybe (Left (typeMismatch u "Sized")) (\n -> Right (Val α (Lit (Int n)))) (elementCount v)
   depRel _ = Left "Single argument expected"

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
   ForeignOp ("load_json" × ForeignOp' { arity: 1, depOp })
   where
   depOp :: DepOp
   depOp ctrl vs@({ val: Val _ (Lit (Str path)) } : Nil) = do
      json <- loadJsonFile path
      fromRel (\us -> jsonVal (ctrlWeight * foldl add zero (root <$> us)) json) ctrl vs
   depOp _ _ = throw "String expected"

loadJsonFile :: forall m. MonadError Error m => MonadAff m => LoadFile m => String -> m Json
loadJsonFile path = do
   str <- loadFileFromPath (File path) >>= orElse ("File not found: " <> path)
   case parseJson str of
      Left err -> throw ("Failed to parse JSON: " <> show err)
      Right json -> pure json

-- Weight α at every position.
jsonVal :: forall a. a -> Json -> Val a
jsonVal α json = caseJson
   (\_ -> error "Null JSON value cannot be converted to Val")
   (Bool >>> lit)
   (\n -> lit (maybe (Float n) Int (Int.fromNumber n)))
   (Str >>> lit)
   (map (jsonVal α) >>> List >>> Val α)
   (map (\x -> α × jsonVal α x) >>> wrap >>> DictRep >>> Dictionary >>> Val α)
   json
   where
   lit = Lit >>> Val α

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
   , inEdges: L.concat (ds <#> via \x -> Val (root x) (Dictionary (DictRep (Dict.mapWithKey (\k (_ × zu) -> fst (dictEntry k x) × zu) zd))))
        <> L.concat (kvs <#> \(k × v) -> via (\y -> dict (Map.insert k (zero × y) zd)) v)
   }
   where
   zd = D.fromFoldable (kvs <#> \(k × v) -> k × (zero × zeros v.val))
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

numToStr :: Int + Number -> String
numToStr = show `union1` show
