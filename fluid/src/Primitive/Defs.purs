module Primitive.Defs where

import Prelude hiding (absurd, apply, div, mod, top)

import Bind (Bind, Var, dottedName)
import Control.Monad.Error.Class (class MonadError)
import Data.Argonaut.Core (Json, caseJson)
import Data.Argonaut.Decode (parseJson)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Int (ceil, floor, toNumber)
import Data.Int (quot, rem) as I
import Data.Int as Int
import Data.List (List(..), (:))
import Data.Map (Map)
import Data.Map as M
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.Number (fromString)
import Data.Number (cos, e, exp, log, pi, pow, sin, sqrt, tan) as N
import Data.Set (Set, empty)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.Traversable (for, sequence, traverse)
import Data.Tuple (fst)
import DataType (cCons, cNil, cNothing, cPair, cJust)
import DefiniteAssignment (Cxt, Entry(..))
import Debug (trace)
import Dict (fromFoldable)
import Dict (fromFoldable) as D
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import Eval (apply) as G
import File (File(..), loadFileFromPath)
import Foreign.Object as FO
import Graph (Vertex)
import Graph.WithGraph (class MonadWithGraphAlloc)
import Lattice (class BoundedJoinSemilattice, Raw, bot)
import Literal (Literal(..))
import Primitive (binary, binaryZero, boolean, int, intOrNumber, intOrNumberOrString, number, string, typeMismatch, unary, union, union1, unionStr)
import Util (type (+), type (×), Endo, definitely, definitely', error, singleton, throw, (×))
import ModuleGraph (ModuleName, builtins, dataclasses, math, typing)
import Util.Map (constMap, intersectionWith, keys, lookup, unionWith_never, (\\))
import Util.Map as Dict
import Util.Map as Map
import Val (BaseVal(..), DictRep(..), Env, ForeignOp(..), ForeignOp'(..), Fun(..), MatrixDim(..), MatrixRep(..), Op, Val(..), matrixGet, matrixPut, val)

extern :: forall a. BoundedJoinSemilattice a => ForeignOp -> Bind (Val a)
extern (ForeignOp (id × φ)) =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × φ))))

predefined :: Map ModuleName (Cxt × Raw Env)
predefined = M.fromFoldable
   [ predefinedModule builtins ("None" : "object" : "bool" : "int" : "float" : "str" : "list" : "dict" : "tuple" : Nil)
        [ extern print_
        , extern len
        -- Fluid-only members, without spec counterpart
        , ":" × Val bot Nothing (Fun (Type cCons))
        , extern dims
        , extern loadJson
        , unary "str_to_float" { i: string, o: number, fwd: definitely' <<< fromString }
        , unary "num_to_str" { i: intOrNumber, o: string, fwd: numToStr } -- rename to 'str' (more Pythonic)
        , binary "+" { i1: intOrNumber, i2: intOrNumber, o: intOrNumber, fwd: plus }
        , binary "-" { i1: intOrNumber, i2: intOrNumber, o: intOrNumber, fwd: minus }
        , binaryZero "*" { i: intOrNumber, o: intOrNumber, fwd: times }
        , binaryZero "**" { i: intOrNumber, o: intOrNumber, fwd: pow }
        , binaryZero "/" { i: intOrNumber, o: intOrNumber, fwd: divide }
        , binary "==" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: equals }
        , binary "/=" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: notEquals }
        , binary "<" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: lessThan }
        , binary ">" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: greaterThan }
        , binary "<=" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: lessThanEquals }
        , binary ">=" { i1: intOrNumberOrString, i2: intOrNumberOrString, o: boolean, fwd: greaterThanEquals }
        , binary "++" { i1: string, i2: string, o: string, fwd: concat }
        , extern matrixLookup
        -- TODO: rename the rest of these (apart from dict_map?) to lose the dict_ prefix
        , extern dict_difference
        , extern dict_disjointUnion
        , extern foldl_with_index
        , extern get
        , extern insert
        , extern dict_intersectionWith
        , extern dict_map
        , extern pairsToDict
        , extern matrixUpdate
        , extern find_str
        , extern search
        , extern split
        , binaryZero "//" { i: int, o: int, fwd: div }
        , binaryZero "%" { i: int, o: int, fwd: mod }
        , binaryZero "quot" { i: int, o: int, fwd: quot }
        , binaryZero "rem" { i: int, o: int, fwd: rem }
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
   ForeignOp ("len" × ForeignOp' { arity: 1, op })
   where
   op :: Op
   op doc_opt (v : Nil) = do
      αs × n <- count v
      val doc_opt αs (Lit (Int n))
      where
      count :: forall m. MonadError Error m => Val Vertex -> m (Set Vertex × Int)
      count (Val α _ (Constr c Nil)) | c == cNil = pure (singleton α × 0)
      count (Val α _ (Constr c (_ : v' : Nil))) | c == cCons = count v' <#> \(αs × n) -> Set.insert α αs × (n + 1)
      count (Val α _ (Dictionary (DictRep d))) = pure (singleton α × Set.size (keys d))
      count (Val α _ (Lit (Str s))) = pure (singleton α × String.length s)
      count (Val _ _ u) = throw (typeMismatch u "Sized")
   op _ _ = throw "Single argument expected"

print_ :: ForeignOp
print_ =
   ForeignOp ("print" × ForeignOp' { arity: 1, op })
   where
   op :: Op
   op doc_opt (x : Nil) = trace x \_ -> val doc_opt empty (Lit None)
   op _ _ = throw "Single argument expected"

loadJson :: ForeignOp
loadJson =
   ForeignOp ("load_json" × ForeignOp' { arity: 1, op })
   where
   op :: Op
   op doc_opt (Val _ _ (Lit (Str path)) : Nil) = do
      str <- definitely ("File \"" <> path <> "\" exists") <$> loadFileFromPath (File path)
      case parseJson str of
         Left err -> throw ("Failed to parse JSON: " <> show err)
         Right json -> fromJson doc_opt json
   op _ _ = throw "String expected"

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
      toList doc_opt (Array.toUnfoldable vs)
      where
      toList :: Maybe (Val Vertex) -> List (Val Vertex) -> m (Val Vertex)
      toList doc_opt' Nil = val doc_opt' empty (Constr cNil Nil)
      toList doc_opt' (v : vs) = do
         v' <- toList Nothing vs
         val doc_opt' empty (Constr cCons (v : v' : Nil))

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
   ForeignOp ("dims" × ForeignOp' { arity: 1, op })
   where
   op :: Op
   op doc_opt (Val α _ (Matrix (MatrixRep (_ × MatrixDim (i × β1) × MatrixDim (j × β2)))) : Nil) = do
      v1 <- val Nothing (singleton β1) $ Lit (Int i)
      v2 <- val Nothing (singleton β2) $ Lit (Int j)
      val doc_opt (singleton α) $ Constr cPair (v1 : v2 : Nil)
   op _ _ = throw "Matrix expected"

matrixLookup :: ForeignOp
matrixLookup =
   ForeignOp ("!" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op _ (Val _ _ (Matrix r) : Val _ _ (Constr c (Val _ _ (Lit (Int i)) : Val _ _ (Lit (Int j)) : Nil)) : Nil) | c == cPair =
      pure $ matrixGet i j r
   op _ _ = throw "Matrix and pair of integers expected"

matrixUpdate :: ForeignOp
matrixUpdate =
   ForeignOp ("matrixUpdate" × ForeignOp' { arity: 3, op })
   where
   op :: Op
   op doc_opt (Val α _ (Matrix r) : Val _ _ (Constr c (Val _ _ (Lit (Int i)) : Val _ _ (Lit (Int j)) : Nil)) : v : Nil)
      | c == cPair = val doc_opt (singleton α) (Matrix (matrixPut i j (const v) r))
   op _ _ = throw "Matrix, pair of integers and value expected"

find_str :: ForeignOp
find_str =
   ForeignOp ("find_str" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str s1)) : Val β _ (Lit (Str s2)) : Nil) = do
      val doc_opt (singleton α # Set.insert β) (Lit (Int i))
      where
      i = fromMaybe (-1) (String.indexOf (Pattern s1) s2)
   op _ _ = throw "Two strings expected"

search :: ForeignOp
search =
   ForeignOp ("search" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str regex)) : Val β _ (Lit (Str str)) : Nil) = do
      case Regex.regex regex noFlags of
         Left msg -> throw $ "Regex expected: " <> msg
         Right regex' -> do
            let αs = singleton α # Set.insert β
            case Regex.search regex' str of
               Nothing -> val doc_opt αs (Constr cNothing Nil)
               Just n -> do
                  v <- val Nothing αs (Lit (Int n))
                  val doc_opt αs (Constr cJust (v : Nil))
   op _ _ = throw "Two strings expected"

-- When strings implement an abstract sequence type can express in terms of take/drop
split :: ForeignOp
split =
   ForeignOp ("split" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Int n)) : Val β _ (Lit (Str str)) : Nil) = do
      let αs = singleton α # Set.insert β
      before <- val Nothing αs $ Lit $ Str $ String.take n str
      after <- val Nothing αs $ Lit $ Str $ String.drop n str
      val doc_opt αs (Constr cPair (before : after : Nil))
   op _ _ = throw "Int and string expected"

dict_difference :: ForeignOp
dict_difference =
   ForeignOp ("dict_difference" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) =
      val doc_opt (singleton α # Set.insert β) (Dictionary (DictRep (d \\ d')))
   op _ _ = throw "Dictionaries expected."

dict_disjointUnion :: ForeignOp
dict_disjointUnion =
   ForeignOp ("dict_disjointUnion" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val β _ (Dictionary (DictRep d')) : Nil) = do
      val doc_opt (singleton α # Set.insert β) (Dictionary (DictRep (unionWith_never d d')))
   op _ _ = throw "Dictionaries expected"

foldl_with_index :: ForeignOp
foldl_with_index =
   ForeignOp ("foldl_with_index" × ForeignOp' { arity: 3, op })
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

get :: ForeignOp
get =
   ForeignOp ("get" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (Val α _ (Lit (Str s)) : Val _ _ (Dictionary (DictRep d)) : Nil) =
      case lookup s d of
         Nothing -> val doc_opt (singleton α) (Constr cNothing Nil)
         Just (β × v) -> val doc_opt (Set.insert β (singleton α)) (Constr cJust (v : Nil))
   op _ _ = throw "String and dictionary expected"

insert :: ForeignOp
insert =
   ForeignOp ("insert" × ForeignOp' { arity: 3, op })
   where
   op :: Op
   op doc_opt (Val α _ (Dictionary (DictRep d)) : Val α' _ (Lit (Str k)) : v : Nil) =
      val doc_opt (singleton α) (Dictionary (DictRep (Map.insert k (α' × v) d)))
   op _ _ = throw "Dictionary, key and value expected"

dict_intersectionWith :: ForeignOp
dict_intersectionWith =
   ForeignOp ("dict_intersectionWith" × ForeignOp' { arity: 3, op })
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

dict_map :: ForeignOp
dict_map =
   ForeignOp ("dict_map" × ForeignOp' { arity: 2, op })
   where
   op :: Op
   op doc_opt (v : Val α _ (Dictionary (DictRep d)) : Nil) = do
      d' <- traverse (\(β × u) -> (β × _) <$> G.apply Nothing v (u : Nil)) d
      val doc_opt (singleton α) (Dictionary (DictRep d'))
   op _ _ = throw "Function and dictionary expected"

pairsToDict :: ForeignOp
pairsToDict =
   ForeignOp ("pairs_to_dict" × ForeignOp' { arity: 1, op })
   where
   op :: Op
   op doc_opt (v : Nil) = do
      αs × kvs <- kvs' v
      val doc_opt αs (Dictionary (DictRep $ fromFoldable kvs))
      where
      kvs' :: forall m. MonadError Error m => Val Vertex -> m (Set Vertex × List (String × (Vertex × Val Vertex)))
      kvs' (Val α _ (Constr c Nil)) | c == cNil = pure $ singleton α × Nil
      kvs' (Val α _ (Constr c (Val β' _ (Constr c' (Val β _ (Lit (Str k)) : u : Nil)) : v' : Nil)))
         | c == cCons && c' == cPair = do
              αs' × kvs <- kvs' v'
              pure $ Set.insert α (Set.insert β' αs') × ((k × (β × u)) : kvs)
      kvs' _ = throw $ "List of (key, value) pairs expected"
   op _ _ = throw "Single argument expected"

plus :: Int + Number -> Endo (Int + Number)
plus = (+) `union` (+)

minus :: Int + Number -> Endo (Int + Number)
minus = (-) `union` (-)

times :: Int + Number -> Endo (Int + Number)
times = (*) `union` (*)

-- PureScript's / and pow aren't defined at Int -> Int -> Number, so roll our own
pow :: Int + Number -> Endo (Int + Number)
pow = (\x y -> toNumber x `N.pow` toNumber y) `union` N.pow

divide :: Int + Number -> Endo (Int + Number)
divide = (\x y -> toNumber x / toNumber y) `union` (/)

-- See T-, F- and E-definitions discussed at https://github.com/purescript/purescript-prelude/issues/161
-- and https://github.com/fluid-org/fluid/issues/1450
div :: Int -> Endo Int
div = (\x y -> floor (toNumber x / toNumber y))

mod :: Int -> Endo Int
mod = (\x y -> x - y * div x y)

quot :: Int -> Endo Int
quot = I.quot

rem :: Int -> Endo Int
rem = I.rem

equals :: Int + Number + String -> Int + Number + String -> Boolean
equals = (==) `union` ((==) `unionStr` (==))

notEquals :: Int + Number + String -> Int + Number + String -> Boolean
notEquals = (/=) `union` ((/=) `unionStr` (/=))

lessThan :: Int + Number + String -> Int + Number + String -> Boolean
lessThan = (<) `union` ((<) `unionStr` (<))

greaterThan :: Int + Number + String -> Int + Number + String -> Boolean
greaterThan = (>) `union` ((>) `unionStr` (>))

lessThanEquals :: Int + Number + String -> Int + Number + String -> Boolean
lessThanEquals = (<=) `union` ((<=) `unionStr` (<=))

greaterThanEquals :: Int + Number + String -> Int + Number + String -> Boolean
greaterThanEquals = (>=) `union` ((>=) `unionStr` (>=))

concat :: String -> Endo String
concat = (<>)

numToStr :: Int + Number -> String
numToStr = show `union1` show
