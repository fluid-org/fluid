module Primitive where

import Prelude hiding (absurd, apply, div, top)

import Bind (Bind)
import Data.Either (Either(..), either)
import Data.Int (toNumber)
import Data.Int as Int
import Data.Array (replicate)
import Data.List (List(..), concat, fromFoldable, (:))
import Data.Maybe (Maybe(..))
import Data.Number as N
import Data.Profunctor.Strong (first)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.Tuple (fst, snd)
import DataType (cCons, cNil, cPair)
import Dict (Dict)
import Expr (Binop(..), Unop(..))
import Lattice (class BoundedJoinSemilattice, bot, erase)
import Literal (Literal(..), eqLiteral)
import Partial.Unsafe (unsafePartial)
import Pretty (prettyP)
import Util (type (+), type (×), absurd, definitely', error, orThrow, singleton, (×))
import Util.Map (keys, lookup, values)
import Util.Set ((∪))
import Val (BaseVal(..), DictRep(..), ForeignOp(..), ForeignOp'(..), Fun(..), MatrixDim(..), MatrixRep(..), Op, Val(..), val)

-- Mediate between wrapped values and underlying datatype d. Wasn't able to make a typeclass version
-- work with required higher-rank polymorphism.
type ToFrom d a =
   { pack :: d -> BaseVal a
   , unpack :: BaseVal a -> Either String d
   }

unpack :: forall d a. ToFrom d a -> Val a -> Either String (d × a)
unpack toFrom (Val α _ v) = toFrom.unpack v <#> (_ × α)

-- For values whose shape is known.
unpack' :: forall d a. ToFrom d a -> Val a -> d × a
unpack' toFrom = unpack toFrom >>> either error identity

pack :: forall d a. ToFrom d a -> d × a -> Val a
pack toFrom (v × α) = Val α Nothing (toFrom.pack v)

typeMismatch :: forall a. BaseVal a -> String -> String
typeMismatch v typeName = "Found " <> prettyP (erase v) <> ", expected " <> typeName

typeError :: forall a b. BaseVal a -> String -> b
typeError v typeName = error (typeMismatch v typeName)

int :: forall a. ToFrom Int a
int =
   { pack: Lit <<< Int
   , unpack: case _ of
        Lit (Int n) -> Right n
        v -> Left (typeMismatch v "int")
   }

number :: forall a. ToFrom Number a
number =
   { pack: Lit <<< Float
   , unpack: case _ of
        Lit (Float n) -> Right n
        v -> Left (typeMismatch v "float")
   }

string :: forall a. ToFrom String a
string =
   { pack: Lit <<< Str
   , unpack: case _ of
        Lit (Str str) -> Right str
        v -> Left (typeMismatch v "str")
   }

intOrNumber :: forall a. ToFrom (Int + Number) a
intOrNumber =
   { pack: case _ of
        Left n -> Lit (Int n)
        Right n -> Lit (Float n)
   , unpack: case _ of
        Lit (Int n) -> Right (Left n)
        Lit (Float n) -> Right (Right n)
        v -> Left (typeMismatch v "int or float")
   }

intOrNumberOrString :: forall a. ToFrom (Int + Number + String) a
intOrNumberOrString =
   { pack: case _ of
        Left n -> Lit (Int n)
        Right (Left n) -> Lit (Float n)
        Right (Right str) -> Lit (Str str)
   , unpack: case _ of
        Lit (Int n) -> Right (Left n)
        Lit (Float n) -> Right (Right (Left n))
        Lit (Str str) -> Right (Right (Right str))
        v -> Left (typeMismatch v "int, float or str")
   }

intPair :: forall a. ToFrom ((Int × a) × (Int × a)) a
intPair =
   { pack: \(nβ × mβ') -> Constr cPair (pack int nβ : pack int mβ' : Nil)
   , unpack: case _ of
        Constr c (v : v' : Nil) | c == cPair -> (×) <$> unpack int v <*> unpack int v'
        v -> Left (typeMismatch v "Pair")
   }

matrixRep :: forall a. ToFrom (MatrixRep a) a
matrixRep =
   { pack: Matrix
   , unpack: case _ of
        Matrix m -> Right m
        v -> Left (typeMismatch v "matrix")
   }

dict :: forall a. ToFrom (Dict (a × Val a)) a
dict =
   { pack: Dictionary <<< DictRep
   , unpack: case _ of
        Dictionary (DictRep d) -> Right d
        v -> Left (typeMismatch v "dict")
   }

boolean :: forall a. ToFrom Boolean a
boolean =
   { pack: Lit <<< Bool
   , unpack: case _ of
        Lit (Bool b) -> Right b
        v -> Left (typeMismatch v "bool")
   }

-- Need to be careful about type variables escaping higher-rank quantification.
type Unary i o a =
   { i :: ToFrom i a
   , o :: ToFrom o a
   , fwd :: i -> o
   }

unary :: forall i o a'. BoundedJoinSemilattice a' => String -> (forall a. Unary i o a) -> Bind (Val a')
unary id f =
   id × Val bot Nothing (Fun (Prim (ForeignOp (id × op))))
   where
   op :: ForeignOp'
   op = ForeignOp' { arity: 1, op: unsafePartial op' }

   op' :: Partial => Op
   op' doc_opt (Val α _ v : Nil) = do
      x <- orThrow (f.i.unpack v)
      val doc_opt (singleton α) (f.o.pack (f.fwd x))

class As a b where
   as :: a -> b

instance asIntNumber :: As Int Number where
   as = toNumber

instance asIntorNumberNumber :: As (Int + Number) Number where
   as (Left n) = as n
   as (Right n) = n

union1 :: forall a1 b. (a1 -> b) -> (Number -> b) -> a1 + Number -> b
union1 f _ (Left x) = f x
union1 _ g (Right x) = g x

binop :: forall a. Ord a => Binop -> Val a -> Val a -> Either String (BaseVal a × Set a)
binop Eq v v'
   | bothNan v v' = pure (Lit (Bool false) × vertices2 v v')
   | otherwise = first (Lit <<< Bool) <$> eqOp v v'
binop Ne v v'
   | bothNan v v' = pure (Lit (Bool true) × vertices2 v v')
   | otherwise = first (Lit <<< Bool <<< not) <$> eqOp v v'
binop In v v' = first (Lit <<< Bool) <$> memOp v' v
binop NotIn v v' = first (Lit <<< Bool <<< not) <$> memOp v' v
binop Add (Val α _ (Lit (Str w))) (Val β _ (Lit (Str w'))) = pure (Lit (Str (w <> w')) × Set.fromFoldable [ α, β ])
binop Mul (Val α _ (Lit (Str w))) (Val β _ (Lit (Int n))) = pure (repeatStr w n × (if n == 0 then Set.singleton β else Set.fromFoldable [ α, β ]))
binop Mul (Val α _ (Lit (Int n))) (Val β _ (Lit (Str w))) = pure (repeatStr w n × (if n == 0 then Set.singleton α else Set.fromFoldable [ α, β ]))
binop op (Val α _ u) (Val β _ u') = do
   x <- operand u
   y <- operand u'
   case op of
      Lt -> compare (<) x y
      Le -> compare (<=) x y
      Gt -> compare (>) x y
      Ge -> compare (>=) x y
      Add -> (_ × both) <$> arith (+) (+) x y
      Sub -> (_ × both) <$> arith (-) (-) x y
      Mul -> (_ × zeroDeps x y) <$> arith (*) (*) x y
      Pow -> (_ × zeroDeps x y) <$> case x, y of
         Left m, Left n | n >= 0 -> pure (Lit (Int (Int.pow m n)))
         _, _ -> Lit <<< Float <$> (N.pow <$> float x <*> float y)
      Div -> nonZero y *> (Lit <<< Float <$> ((/) <$> float x <*> float y)) <#> (_ × both)
      FloorDiv -> nonZero y *> arith floorDiv (\r r' -> N.floor (r / r')) x y <#> (_ × both)
      Mod -> nonZero y *> arith (\m n -> m - n * floorDiv m n) (\r r' -> r - r' * N.floor (r / r')) x y <#> (_ × both)
      _ -> error absurd
   where
   both = Set.fromFoldable [ α, β ]

   -- Zero operand absorbs: result depends on it alone
   zeroDeps :: Operand -> Operand -> Set a
   zeroDeps x y
      | isZero x = Set.singleton α
      | isZero y = Set.singleton β
      | otherwise = both

   operand :: BaseVal a -> Either String Operand
   operand (Lit (Int n)) = pure (Left n)
   operand (Lit (Float r)) = pure (Right (Left r))
   operand (Lit (Str w)) = pure (Right (Right w))
   operand u'' = Left (typeMismatch u'' "int, float or str")

   float :: Operand -> Either String Number
   float (Left n) = pure (toNumber n)
   float (Right (Left r)) = pure r
   float (Right (Right w)) = Left (typeMismatch (Lit (Str w)) "int or float")

   compare :: (forall b. Ord b => b -> b -> Boolean) -> Operand -> Operand -> Either String (BaseVal a × Set a)
   compare f (Right (Right w)) (Right (Right w')) = pure (Lit (Bool (f w w')) × both)
   compare f (Left m) (Left n) = pure (Lit (Bool (f m n)) × both)
   compare f x y = (\r r' -> Lit (Bool (f r r')) × both) <$> float x <*> float y

   arith :: (Int -> Int -> Int) -> (Number -> Number -> Number) -> Operand -> Operand -> Either String (BaseVal a)
   arith f _ (Left m) (Left n) = pure (Lit (Int (f m n)))
   arith _ g x y = Lit <<< Float <$> (g <$> float x <*> float y)

   floorDiv :: Int -> Int -> Int
   floorDiv m n = Int.floor (toNumber m / toNumber n)

   nonZero :: Operand -> Either String Unit
   nonZero y = when (isZero y) (Left "ZeroDivisionError: division by zero")

   isZero :: Operand -> Boolean
   isZero (Left 0) = true
   isZero (Right (Left 0.0)) = true
   isZero _ = false

type Operand = Int + Number + String

bothNan :: forall a. Val a -> Val a -> Boolean
bothNan (Val _ _ (Lit (Float r))) (Val _ _ (Lit (Float r'))) = N.isNaN r && N.isNaN r'
bothNan _ _ = false

vertices2 :: forall a. Ord a => Val a -> Val a -> Set a
vertices2 (Val α _ _) (Val β _ _) = Set.fromFoldable [ α, β ]

repeatStr :: forall a. String -> Int -> BaseVal a
repeatStr w n = Lit (Str (String.joinWith "" (replicate n w)))

unop :: forall a. Ord a => Unop -> Val a -> Either String (BaseVal a × Set a)
unop Not (Val α _ (Lit (Bool b))) = pure (Lit (Bool (not b)) × Set.singleton α)
unop Not (Val _ _ u) = Left (typeMismatch u "bool")
unop Neg (Val α _ (Lit (Int n))) = pure (Lit (Int (negate n)) × Set.singleton α)
unop Neg (Val α _ (Lit (Float r))) = pure (Lit (Float (negate r)) × Set.singleton α)
unop Pos (Val α _ u@(Lit (Int _))) = pure (u × Set.singleton α)
unop Pos (Val α _ u@(Lit (Float _))) = pure (u × Set.singleton α)
unop _ (Val _ _ u) = Left (typeMismatch u "int or float")

eqOp :: forall a. Ord a => Val a -> Val a -> Either String (Boolean × Set a)
eqOp (Val α _ u) (Val β _ u') = case u, u' of
   Lit (Float r), Lit (Float r') | N.isNaN r || N.isNaN r' -> Left "Cannot compare nan"
   Lit ℓ, Lit ℓ' | kind ℓ == kind ℓ' -> pure (eqLiteral ℓ ℓ' × both)
   Lit None, _ -> pure (false × both)
   _, Lit None -> pure (false × both)
   Constr c vs, Constr d ws
      | c == d -> eqElems both vs ws
      | otherwise -> pure (false × both)
   Dictionary (DictRep d), Dictionary (DictRep d')
      | keys d == keys d' -> eqElems (both ∪ keyVertices d ∪ keyVertices d') (snd <$> values d) ((\k -> snd (definitely' (lookup k d'))) <$> Set.toUnfoldable (keys d))
      | otherwise -> pure (false × (both ∪ keyVertices d ∪ keyVertices d'))
   Matrix (MatrixRep (vss × MatrixDim (i × γ) × MatrixDim (j × δ))), Matrix (MatrixRep (vss' × MatrixDim (i' × γ') × MatrixDim (j' × δ')))
      | i == i' && j == j' -> eqElems (both ∪ Set.fromFoldable [ γ, δ, γ', δ' ]) (concat (fromFoldable <$> fromFoldable vss)) (concat (fromFoldable <$> fromFoldable vss'))
      | otherwise -> pure (false × (both ∪ Set.fromFoldable [ γ, δ, γ', δ' ]))
   _, _ -> Left ("Cannot compare " <> prettyP (erase u) <> " with " <> prettyP (erase u'))
   where
   both = Set.fromFoldable [ α, β ]

   keyVertices :: Dict (a × Val a) -> Set a
   keyVertices = values >>> map fst >>> Set.fromFoldable

   kind :: Literal -> String
   kind (Int _) = "number"
   kind (Float _) = "number"
   kind (Str _) = "str"
   kind (Bool _) = "bool"
   kind None = "None"

eqElems :: forall a. Ord a => Set a -> List (Val a) -> List (Val a) -> Either String (Boolean × Set a)
eqElems αs Nil Nil = pure (true × αs)
eqElems αs (v : vs) (v' : vs') = do
   b × βs <- eqOp v v'
   if b then eqElems (αs ∪ βs) vs vs' else pure (false × (αs ∪ βs))
eqElems αs _ _ = pure (false × αs)

memOp :: forall a. Ord a => Val a -> Val a -> Either String (Boolean × Set a)
memOp (Val α _ u') v@(Val β _ u) = case u', u of
   Constr c Nil, _ | c == cNil -> pure (false × Set.singleton α)
   Constr c (v' : vs : Nil), _ | c == cCons -> do
      b × βs <- eqOp v v'
      if b then pure (true × Set.insert α βs) else map (Set.insert α <<< (βs ∪ _)) <$> memOp vs v
   Dictionary (DictRep d), Lit (Str w) -> pure (Set.member w (keys d) × Set.fromFoldable [ α, β ])
   Dictionary _, _ -> Left (typeMismatch u "str")
   Lit (Str w'), Lit (Str w) -> pure (String.contains (Pattern w) w' × Set.fromFoldable [ α, β ])
   Lit (Str _), _ -> Left (typeMismatch u "str")
   _, _ -> Left (typeMismatch u' "list, dict or str")
