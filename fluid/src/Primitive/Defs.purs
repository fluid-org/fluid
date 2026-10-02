module Primitive.Defs where

import Prelude hiding (absurd, apply, div, mod, top)

import Bind (Bind, Var, dottedName)
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
import Data.Set (empty)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (fst, snd)
import DataType (cPair)
import DefiniteAssignment (Cxt, Entry(..))
import Debug (trace)
import Dict (fromFoldable) as D
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import Eval (apply) as G
import Eval.Dep (apply) as Dep
import File (class LoadFile, File(..), loadFileFromPath)
import Foreign.Object as FO
import Graph (Vertex)
import Graph.Dep (zeros)
import Graph.WithGraph (class MonadWithGraphAlloc)
import Lattice (class BoundedJoinSemilattice, Raw, bot, ctrlWeight)
import Literal (Literal(..))
import Primitive (int, intOrNumber, number, string, typeMismatch, unary, union1)
import Util (type (+), type (×), definitely, definitely', error, orThrow, singleton, throw, (×))
import ModuleGraph (ModuleName, builtins, dataclasses, math, typing)
import Util.Map (constMap, intersectionWith, keys, lookup, unionWith_never, (\\))
import Util.Map as Dict
import Util.Map as Map
import Val (BaseVal(..), DepOp, DictRep(..), Env, ForeignOp(..), ForeignOp'(..), Fun(..), GVal, MatrixDim(..), MatrixRep(..), Op, Val(..), construct, deliver, dictEntries, dictEntry, fromRel, gval, matrixPut, pureRel, rootOf, val, via)

extern :: forall a. BoundedJoinSemilattice a => ForeignOp -> Bind (Val a)
extern (ForeignOp (id × φ)) =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × φ))))

predefined :: Map ModuleName (Cxt × Raw Env)
predefined = M.fromFoldable
   [ predefinedModule builtins ("None" : "object" : "bool" : "int" : "float" : "str" : "list" : "dict" : "tuple" : Nil)
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
   , predefinedModule math Nil
        [ "pi" × Val bot Nothing (Lit (Float N.pi))
        , "e" × Val bot Nothing (Lit (Float N.e))
        , unary "sqrt" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sqrt) `union1` N.sqrt }
        , unary "exp" { i: intOrNumber, o: number, fwd: (toNumber >>> N.exp) `union1` N.exp }
        , unary "log" { i: intOrNumber, o: number, fwd: (toNumber >>> N.log) `union1` N.log }
        , unary "sin" { i: intOrNumber, o: number, fwd: (toNumber >>> N.sin) `union1` N.sin }
        , unary "cos" { i: intOrNumber, o: number, fwd: (toNumber >>> N.cos) `union1` N.cos }
        , unary "tan" { i: intOrNumber, o: number, fwd: (toNumber >>> N.tan) `union1` N.tan }
        , unary "floor" { i: intOrNumber, o: int, fwd: identity `union1` floor }
        , unary "ceil" { i: intOrNumber, o: int, fwd: identity `union1` ceil }
        ]
   , predefinedModule typing ("Callable" : "Literal" : "Never" : "Sized" : Nil) []
   , predefinedModule dataclasses ("dataclass" : Nil) []
   ]
   where
   predefinedModule :: ModuleName -> List Var -> Array (Bind (Val Unit)) -> ModuleName × (Cxt × Raw Env)
   predefinedModule q names members = q × (cxt × ρ)
      where
      ρ = wrap (D.fromFoldable (Array.cons ("__name__" × Val bot Nothing (Lit (Str (dottedName q)))) members))
      cxt = M.union (constMap PredefName (Set.fromFoldable names)) (constMap (VarStatus true) (keys ρ))

len :: ForeignOp
len =
   ForeignOp ("len" × ForeignOp' { arity: 1, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ u : Nil) = do
      n <- orThrow (count u)
      val doc_opt (singleton α) (Lit (Int n))
   op _ _ = throw "Single argument expected"

   rel :: forall a. List (Val a) -> Either String (Val a)
   rel (Val α _ u : Nil) = count u <#> \n -> Val α Nothing (Lit (Int n))
   rel _ = Left "Single argument expected"

   count :: forall a. BaseVal a -> Either String Int
   count (List vs) = pure (Array.length vs)
   count (Dictionary (DictRep d)) = pure (Set.size (keys d))
   count (Lit (Str s)) = pure (String.length s)
   count u = Left (typeMismatch u "Sized")

print_ :: ForeignOp
print_ =
   ForeignOp ("print" × ForeignOp' { arity: 1, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (x : Nil) = trace x \_ -> val doc_opt empty (Lit None)
   op _ _ = throw "Single argument expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (_ : Nil) = pure (Val zero Nothing (Lit None))
   rel _ = Left "Single argument expected"

loadJson :: ForeignOp
loadJson =
   ForeignOp ("load_json" × ForeignOp' { arity: 1, op, depOp })
   where
   op :: Op
   op doc_opt (Val _ _ (Lit (Str path)) : Nil) = loadJsonFile path >>= fromJson doc_opt
   op _ _ = throw "String expected"

   depOp :: DepOp
   depOp ctrl vs@({ val: Val _ _ (Lit (Str path)) } : Nil) = do
      json <- loadJsonFile path
      fromRel (\us -> jsonVal (ctrlWeight * foldl add zero (rootOf <$> us)) json) ctrl vs
   depOp _ _ = throw "String expected"

loadJsonFile :: forall m. MonadError Error m => MonadAff m => LoadFile m => String -> m Json
loadJsonFile path = do
   str <- definitely ("File \"" <> path <> "\" exists") <$> loadFileFromPath (File path)
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
   (map (jsonVal α) >>> List >>> Val α Nothing)
   (map (\x -> α × jsonVal α x) >>> wrap >>> DictRep >>> Dictionary >>> Val α Nothing)
   json
   where
   lit = Lit >>> Val α Nothing

fromJson :: forall m. MonadWithGraphAlloc m => MonadEffect m => Maybe (Val Vertex) -> Json -> m (Val Vertex)
fromJson doc_opt =
   caseJson
      caseNull
      caseBool
      caseNumber
      caseString
      caseArray
      caseObject
   where
   caseNull :: Unit -> m (Val Vertex)
   caseNull _ =
      error ("Error, Null JSON value cannot be converted to Val")

   caseBool :: Boolean -> m (Val Vertex)
   caseBool b =
      val doc_opt empty (Lit (Bool b))

   caseNumber :: Number -> m (Val Vertex)
   caseNumber n =
      case Int.fromNumber n of
         Just n' -> val doc_opt empty (Lit (Int n'))
         Nothing -> val doc_opt empty (Lit (Float n))

   caseString :: String -> m (Val Vertex)
   caseString s =
      val doc_opt empty (Lit (Str s))

   caseArray :: Array Json -> m (Val Vertex)
   caseArray xs = do
      vs <- traverse (fromJson Nothing) xs
      val doc_opt empty (List vs)

   caseObject :: FO.Object Json -> m (Val Vertex)
   caseObject obj = do
      let kvs = FO.toUnfoldable obj :: Array (String × Json)
      entries <- for kvs \(k × x) -> do
         Val α _ _ <- val doc_opt empty (Lit (Str k))
         v <- fromJson Nothing x
         pure (k × α × v)
      val doc_opt empty (Dictionary (DictRep (D.fromFoldable entries)))

dims :: ForeignOp
dims =
   ForeignOp ("dims" × ForeignOp' { arity: 1, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Matrix (MatrixRep (_ × MatrixDim (i × β1) × MatrixDim (j × β2)))) : Nil) = do
      v1 <- val Nothing (singleton β1) $ Lit (Int i)
      v2 <- val Nothing (singleton β2) $ Lit (Int j)
      val doc_opt (singleton α) $ Constr cPair (v1 : v2 : Nil)
   op _ _ = throw "Matrix expected"

   rel :: forall a. List (Val a) -> Either String (Val a)
   rel (Val α _ (Matrix (MatrixRep (_ × MatrixDim (i × β1) × MatrixDim (j × β2)))) : Nil) =
      pure (Val α Nothing (Constr cPair (Val β1 Nothing (Lit (Int i)) : Val β2 Nothing (Lit (Int j)) : Nil)))
   rel _ = Left "Matrix expected"

matrixUpdate :: ForeignOp
matrixUpdate =
   ForeignOp ("matrixUpdate" × ForeignOp' { arity: 3, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Matrix r) : Val _ _ (Constr c (Val _ _ (Lit (Int i)) : Val _ _ (Lit (Int j)) : Nil)) : v : Nil)
      | c == cPair = val doc_opt (singleton α) (Matrix (matrixPut i j (const v) r))
   op _ _ = throw "Matrix, pair of integers and value expected"

   rel :: forall a. List (Val a) -> Either String (Val a)
   rel (Val α _ (Matrix r) : Val _ _ (Constr c (Val _ _ (Lit (Int i)) : Val _ _ (Lit (Int j)) : Nil)) : v : Nil)
      | c == cPair = pure (Val α Nothing (Matrix (matrixPut i j (const v) r)))
   rel _ = Left "Matrix, pair of integers and value expected"

find_str :: ForeignOp
find_str =
   ForeignOp ("find_str" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str s1)) : Val β _ (Lit (Str s2)) : Nil) =
      val doc_opt (singleton α # Set.insert β) (Lit (Int (find s1 s2)))
   op _ _ = throw "Two strings expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Lit (Str s1)) : Val β _ (Lit (Str s2)) : Nil) = pure (Val (α + β) Nothing (Lit (Int (find s1 s2))))
   rel _ = Left "Two strings expected"

   find :: String -> String -> Int
   find s1 s2 = fromMaybe (-1) (String.indexOf (Pattern s1) s2)

search :: ForeignOp
search =
   ForeignOp ("search" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str regex)) : Val β _ (Lit (Str str)) : Nil) = do
      ℓ <- orThrow (matchIndex regex str)
      val doc_opt (singleton α # Set.insert β) ℓ
   op _ _ = throw "Two strings expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Lit (Str regex)) : Val β _ (Lit (Str str)) : Nil) = matchIndex regex str <#> Val (α + β) Nothing
   rel _ = Left "Two strings expected"

   matchIndex :: forall a. String -> String -> Either String (BaseVal a)
   matchIndex regex str = case Regex.regex regex noFlags of
      Left msg -> Left ("Regex expected: " <> msg)
      Right regex' -> pure (Lit (maybe None Int (Regex.search regex' str)))

-- When strings implement an abstract sequence type can express in terms of take/drop
split :: ForeignOp
split =
   ForeignOp ("split" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Int n)) : Val β _ (Lit (Str str)) : Nil) = do
      let αs = singleton α # Set.insert β
      before <- val Nothing αs $ Lit $ Str $ String.take n str
      after <- val Nothing αs $ Lit $ Str $ String.drop n str
      val doc_opt αs (Constr cPair (before : after : Nil))
   op _ _ = throw "Int and string expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Lit (Int n)) : Val β _ (Lit (Str str)) : Nil) =
      pure (Val (α + β) Nothing (Constr cPair (part (String.take n str) : part (String.drop n str) : Nil)))
      where
      part w = Val (α + β) Nothing (Lit (Str w))
   rel _ = Left "Int and string expected"

dict_difference :: ForeignOp
dict_difference =
   ForeignOp ("dict_difference" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) =
      val doc_opt (singleton α # Set.insert β) (Dictionary (DictRep (d \\ d')))
   op _ _ = throw "Dictionaries expected."

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) =
      pure (Val (α + β) Nothing (Dictionary (DictRep (d \\ d'))))
   rel _ = Left "Dictionaries expected."

dict_disjointUnion :: ForeignOp
dict_disjointUnion =
   ForeignOp ("dict_disjointUnion" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) = do
      val doc_opt (singleton α # Set.insert β) (Dictionary (DictRep (unionWith_never d d')))
   op _ _ = throw "Dictionaries expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) =
      pure (Val (α + β) Nothing (Dictionary (DictRep (unionWith_never d d'))))
   rel _ = Left "Dictionaries expected"

foldl_with_index :: ForeignOp
foldl_with_index =
   ForeignOp ("foldl_with_index" × ForeignOp' { arity: 3, op, depOp })
   where
   op :: Op
   op doc_opt (v : u : Val _ _ (Dictionary (DictRep d)) : Nil) =
      foldM
         ( \(u1 × doc_opt') (k × (α × u2)) ->
              G.apply doc_opt' v (Val α Nothing (Lit (Str k)) : u1 : u2 : Nil)
                 <#> (_ × Nothing)
         )
         (u × doc_opt)
         kvs
         <#> fst
      where
      kvs :: List _
      kvs = Dict.toUnfoldable d
   op _ _ = throw "Function, value and dictionary expected"

   depOp :: DepOp
   depOp ctrl (g : v : d : Nil) = do
      f <- gval <$> deliver ctrl g
      r <- deliver ctrl v
      foldM (step f) r (Dict.toUnfoldable (dictEntries d.val) :: List (String × (Unit × Raw Val)))
      where
      step f acc (k × _) = Dep.apply ctrl f (key : gval acc : entryValue k d : Nil)
         where
         key = { val: Val unit Nothing (Lit (Str k)), inEdges: via (\x -> Val (fst (dictEntry k x)) Nothing (Lit (Str k))) d }
   depOp _ _ = throw "Function, value and dictionary expected"

get :: ForeignOp
get =
   ForeignOp ("get" × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str s)) : Val _ _ (Dictionary (DictRep d)) : Nil) =
      case lookup s d of
         Nothing -> val doc_opt (singleton α) (Lit None)
         Just (_ × v) -> pure v
   op _ _ = throw "String and dictionary expected"

   rel :: forall a. List (Val a) -> Either String (Val a)
   rel (Val α _ (Lit (Str s)) : Val _ _ (Dictionary (DictRep d)) : Nil) =
      pure (maybe (Val α Nothing (Lit None)) snd (lookup s d))
   rel _ = Left "String and dictionary expected"

insert :: ForeignOp
insert =
   ForeignOp ("insert" × ForeignOp' { arity: 3, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val α' _ (Lit (Str k)) : v : Nil) =
      val doc_opt (singleton α) (Dictionary (DictRep (Map.insert k (α' × v) d)))
   op _ _ = throw "Dictionary, key and value expected"

   rel :: forall a. List (Val a) -> Either String (Val a)
   rel (Val α _ (Dictionary (DictRep d)) : Val α' _ (Lit (Str k)) : v : Nil) =
      pure (Val α Nothing (Dictionary (DictRep (Map.insert k (α' × v) d))))
   rel _ = Left "Dictionary, key and value expected"

dict_intersectionWith :: ForeignOp
dict_intersectionWith =
   ForeignOp ("dict_intersectionWith" × ForeignOp' { arity: 3, op, depOp })
   where
   op :: Op
   op doc_opt (v : Val α _ (Dictionary (DictRep d1)) : Val α' _ (Dictionary (DictRep d2)) : Nil) = do
      v' <- Dictionary <$> (DictRep <$> sequence (intersectionWith apply' d1 d2))
      val doc_opt (singleton α # Set.insert α') v'
      where
      apply' (β × u) (β' × u') = do
         v''@(Val _ _ key) <- G.apply Nothing v (u : u' : Nil)
         Val β'' _ _ <- val Nothing (singleton β # Set.insert β') key
         pure (β'' × v'')
   op _ _ = throw "Function and two dictionaries expected"

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
   ForeignOp ("dict_map" × ForeignOp' { arity: 2, op, depOp })
   where
   op :: Op
   op doc_opt (v : Val α _ (Dictionary (DictRep d)) : Nil) = do
      d' <- traverse (\(β × u) -> (β × _) <$> G.apply Nothing v (u : Nil)) d
      val doc_opt (singleton α) (Dictionary (DictRep d'))
   op _ _ = throw "Function and dictionary expected"

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
   { val: Val unit Nothing (Dictionary (DictRep (D.fromFoldable (kvs <#> \(k × v) -> k × (unit × v.val)))))
   , inEdges: L.concat (ds <#> via \x -> Val (rootOf x) Nothing (Dictionary (DictRep (Dict.mapWithKey (\k (_ × zu) -> fst (dictEntry k x) × zu) zd))))
        <> L.concat (kvs <#> \(k × v) -> via (\y -> dict (Map.insert k (zero × y) zd)) v)
   }
   where
   zd = D.fromFoldable (kvs <#> \(k × v) -> k × (zero × zeros v.val))
   dict = DictRep >>> Dictionary >>> Val zero Nothing

quot :: ForeignOp
quot = intBinary "quot" I.quot

rem :: ForeignOp
rem = intBinary "rem" I.rem

intBinary :: String -> (Int -> Int -> Int) -> ForeignOp
intBinary id f =
   ForeignOp (id × ForeignOp' { arity: 2, op, depOp: pureRel rel })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Int m)) : Val β _ (Lit (Int n)) : Nil) =
      val doc_opt (singleton α # Set.insert β) (Lit (Int (f m n)))
   op _ _ = throw "Two integers expected"

   rel :: forall a. Semiring a => List (Val a) -> Either String (Val a)
   rel (Val α _ (Lit (Int m)) : Val β _ (Lit (Int n)) : Nil) = pure (Val (α + β) Nothing (Lit (Int (f m n))))
   rel _ = Left "Two integers expected"

numToStr :: Int + Number -> String
numToStr = show `union1` show
