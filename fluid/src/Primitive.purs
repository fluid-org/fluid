module Primitive where

import Prelude hiding (absurd, apply, div, top)

import Bind (Bind)
import Data.Either (Either(..), either)
import Data.Foldable (elem, foldl)
import Data.Maybe (Maybe(..))
import Data.Int (toNumber)
import Data.Int as Int
import Data.Array (replicate)
import Data.List (List(..), fromFoldable, (:))
import Data.List (concat) as L
import Data.Number as N
import Data.Profunctor.Strong (first, second)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..))
import Data.String as String
import Data.Tuple (fst, snd)
import DepGraph (dataDep)
import Dict (Dict)
import Expr (Binop(..), Unop(..))
import Lattice (class BoundedJoinSemilattice, class DepSemiring, bot, erase)
import Literal (Literal(..), asFloat, eqLiteral)
import Path (Position)
import Partial.Unsafe (unsafePartial)
import Pretty (prettyP)
import Util (type (+), type (×), MayFail, absurd, definitely', error, orThrow, singleton, (×))
import Util.Map (keys, lookup, values)
import Util.Set ((∪))
import Types.Defs (cComplex, cRange, f_imag, f_real)
import Val (BaseVal(..), DepFun, DepOp, DictRep(..), ForeignOp(..), GVal, ValAt, ForeignOp'(..), Fun(..), MatrixRep(..), Val(..), elements, root)
import Val.Dependence (applyDepFun, concatOf, deliver, elementsAt, reuseAt, sequenceOf)

-- Mediate between wrapped values and underlying datatype d. Wasn't able to make a typeclass version
-- work with required higher-rank polymorphism.
type ToFrom d a =
   { pack :: d -> BaseVal a
   , unpack :: BaseVal a -> MayFail d
   }

unpack :: forall d a. ToFrom d a -> Val a -> MayFail (d × a)
unpack toFrom (Val α v) = toFrom.unpack v <#> (_ × α)

-- Int or float as float
unpackFloat :: forall a. Val a -> MayFail (Number × a)
unpackFloat v = first (either toNumber identity) <$> unpack intOrNumber v

-- For values whose shape is known.
unpack' :: forall d a. ToFrom d a -> Val a -> d × a
unpack' toFrom = unpack toFrom >>> either error identity

dropα :: forall d a. d × a -> d
dropα = fst

pack :: forall d a. ToFrom d a -> d × a -> Val a
pack toFrom (v × α) = Val α (toFrom.pack v)

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
-- Foreign function with dependence given by f
fromDepFun :: DepFun -> DepOp
fromDepFun f ps pvs = orThrow (applyDepFun f ps Set.empty pvs)

type Unary i o a =
   { i :: ToFrom i a
   , o :: ToFrom o a
   , fwd :: i -> o
   }

unary :: forall i o a'. BoundedJoinSemilattice a' => String -> (forall a. Unary i o a) -> Bind (Val a')
unary id f =
   id × Val bot (Fun (Prim (ForeignOp (id × op))))
   where
   op :: ForeignOp'
   op = ForeignOp' { arity: 1, depOp: fromDepFun (unsafePartial depFun) }

   depFun :: forall a. Partial => List (Val a) -> MayFail (Val a)
   depFun (Val α v : Nil) = f.i.unpack v <#> \x -> Val α (f.o.pack (f.fwd x))

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

-- Dependence relations of the operators, from the positions their evaluation inspects.
binopFun :: forall a. DepSemiring a => Binop -> List (Val a) -> MayFail (Val a)
binopFun op (v : v' : Nil)
   | op `elem` [ Add, Sub, Mul, Div, Pow ]
   , isComplex v || isComplex v'
   , Just z <- complexOperand v
   , Just w <- complexOperand v' = complexBinop op z w
   | otherwise = binop op v v' <#> \(u × αs) -> Val (foldl add zero αs) u
binopFun _ _ = error absurd

unopFun :: forall a. Ord a => Semiring a => Unop -> List (Val a) -> MayFail (Val a)
unopFun op (Val α (Obj c ((_ × x) : (_ × y) : Nil)) : Nil) | c == cComplex =
   complexVal α <$> unopFun op (x : Nil) <*> unopFun op (y : Nil)
unopFun op (v : Nil) = unop op v <#> \(u × αs) -> Val (foldl add zero αs) u
unopFun _ _ = error absurd

isComplex :: forall a. Val a -> Boolean
isComplex (Val _ (Obj c _)) = c == cComplex
isComplex _ = false

complexVal :: forall a. a -> Val a -> Val a -> Val a
complexVal α x y = Val α (Obj cComplex ((f_real × x) : (f_imag × y) : Nil))

-- Annotation of root with real and imaginary part
type ComplexOperand a = a × Val a × Val a

-- Complex operand, or int or float operand as complex number with constant zero as imaginary part
complexOperand :: forall a. Semiring a => Val a -> Maybe (ComplexOperand a)
complexOperand (Val α (Obj c ((_ × x) : (_ × y) : Nil))) | c == cComplex = Just (α × x × y)
complexOperand (Val α (Lit ℓ)) | Just x <- asFloat ℓ = Just (zero × Val α (Lit (Float x)) × floatVal 0.0)
complexOperand _ = Nothing

floatVal :: forall a. Semiring a => Number -> Val a
floatVal = Val zero <<< Lit <<< Float

complexBinop :: forall a. DepSemiring a => Binop -> ComplexOperand a -> ComplexOperand a -> MayFail (Val a)
complexBinop op z w = complexArith op z w <#> \(α × x × y) -> complexVal α x y

-- Apply arithmetic operator to parts of complex operands by CPython algorithms
complexArith :: forall a. DepSemiring a => Binop -> ComplexOperand a -> ComplexOperand a -> MayFail (ComplexOperand a)
complexArith op z@(α × x × y) (β × x' × y') = case op of
   Add -> result <$> arith Add x x' <*> arith Add y y'
   Sub -> result <$> arith Sub x x' <*> arith Sub y y'
   Mul -> result <$> join (arith Sub <$> arith Mul x x' <*> arith Mul y y')
      <*> join (arith Add <$> arith Mul x y' <*> arith Mul y x')
   Div -> do
      a <- complexPart x'
      b <- complexPart y'
      if N.abs a >= N.abs b then
         if a == 0.0 then divisionByZero
         else do
            ratio <- arith Div y' x'
            denom <- arith Add x' =<< arith Mul y' ratio
            result <$> (flip (arith Div) denom =<< arith Add x =<< arith Mul y ratio)
               <*> (flip (arith Div) denom =<< arith Sub y =<< arith Mul x ratio)
      else if N.abs b >= N.abs a then do
         ratio <- arith Div x' y'
         denom <- flip (arith Add) y' =<< arith Mul x' ratio
         result <$> (flip (arith Div) denom =<< flip (arith Add) y =<< arith Mul x ratio)
            <*> (flip (arith Div) denom =<< flip (arith Sub) x =<< arith Mul y ratio)
      else pure (result nan nan)
   Pow -> do
      a <- complexPart x
      b <- complexPart y
      a' <- complexPart x'
      b' <- complexPart y'
      let
         vabs = N.sqrt (a * a + b * b)
         at = N.atan2 b a
         len = if b' /= 0.0 then N.pow vabs a' / N.exp (at * b') else N.pow vabs a'
         phase = if b' /= 0.0 then at * a' + b' * N.log vabs else at * a'
         γ = foldl add zero (root <$> [ x, y, x', y' ])
         -- Each part of power depends on every part of base and exponent
         power (_ × Val _ u × Val _ u') = result (Val γ u) (Val γ u')
      if a == 0.0 && b == 0.0 && (b' /= 0.0 || a' < 0.0) then
         Left "ZeroDivisionError: zero to a negative or complex power"
      else if b' == 0.0 && a' == N.floor a' && N.abs a' <= 100.0 then
         power <$>
            if a' > 0.0 then powu one z (Int.floor a')
            else complexArith Div one =<< powu one z (Int.floor (-a'))
      else if a == 0.0 && b == 0.0 then pure (power (zero × floatVal 0.0 × floatVal 0.0))
      else pure (power (zero × floatVal (len * N.cos phase) × floatVal (len * N.sin phase)))
   _ -> error absurd
   where
   result :: Val a -> Val a -> ComplexOperand a
   result u u' = (α `add` β) × u × u'

   arith op' u u' = binopFun op' (u : u' : Nil)
   complexPart u = fst <$> unpackFloat u
   one = zero × floatVal 1.0 × floatVal 0.0
   nan = Val (root x' `add` root y') (Lit (Float N.nan))

   -- Multiply r by nth power of p by repeated squaring
   powu :: ComplexOperand a -> ComplexOperand a -> Int -> MayFail (ComplexOperand a)
   powu r _ 0 = pure r
   powu r p n = do
      r' <- if Int.odd n then complexArith Mul r p else pure r
      p' <- complexArith Mul p p
      powu r' p' (n / 2)

divisionByZero :: forall a. MayFail a
divisionByZero = Left "ZeroDivisionError: division by zero"

-- Concatenation and repetition reuse elements of operand sequences
applyBinop :: forall s. DepSemiring s => Binop -> Set Position -> ValAt -> ValAt -> MayFail (GVal s)
applyBinop Add _ pv@(_ × Val _ (List _)) pv'@(_ × Val _ (List _)) = pure (concatOf List mempty (pv : pv' : Nil))
applyBinop Add _ pv@(_ × Val _ (Tuple _)) pv'@(_ × Val _ (Tuple _)) = pure (concatOf Tuple mempty (pv : pv' : Nil))
applyBinop Mul _ pv@(_ × Val _ (List _)) pv'@(_ × Val _ (Lit (Int n))) = pure (repeatList pv pv' n)
applyBinop Mul _ pv'@(_ × Val _ (Lit (Int n))) pv@(_ × Val _ (List _)) = pure (repeatList pv pv' n)
applyBinop op ps pv pv' = applyDepFun (binopFun op) Set.empty ps (pv : pv' : Nil)

-- List pv repeated n times, for integer n at p'
repeatList :: forall s. Semiring s => ValAt -> ValAt -> Int -> GVal s
repeatList pv@(p × _) (p' × _) n = sequenceOf List (dataDep p' <> (if n <= 0 then mempty else dataDep p)) $
   L.concat (fromFoldable (replicate n (deliver (singleton p) <<< reuseAt <$> elementsAt pv)))

type Operand = Int + Number + String

binop :: forall a. DepSemiring a => Binop -> Val a -> Val a -> MayFail (BaseVal a × Set a)
binop Eq v v'
   | bothNan v v' = pure (Lit (Bool false) × vertices2 v v')
   | otherwise = first (Lit <<< Bool) <$> eqOp v v'
binop Ne v v'
   | bothNan v v' = pure (Lit (Bool true) × vertices2 v v')
   | otherwise = first (Lit <<< Bool <<< not) <$> eqOp v v'
binop In v v' = first (Lit <<< Bool) <$> contains v' v
binop NotIn v v' = first (Lit <<< Bool <<< not) <$> contains v' v
binop Add (Val α (Lit (Str w))) (Val β (Lit (Str w'))) =
   pure (Lit (Str (w <> w')) × Set.fromFoldable [ α, β ])
binop Mul (Val α (Lit (Str w))) (Val β (Lit (Int n))) = pure (repeatStr w α n β)
binop Mul (Val α (Lit (Int n))) (Val β (Lit (Str w))) = pure (repeatStr w β n α)
binop op (Val α u) (Val β u') = do
   x <- intOrNumberOrString.unpack u
   y <- intOrNumberOrString.unpack u'
   case op of
      Lt -> comparison (_ == LT) x y
      Le -> comparison (_ /= GT) x y
      Gt -> comparison (_ == GT) x y
      Ge -> comparison (_ /= LT) x y
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

   -- Zero operand determines the result, so dependencies of the zero operand alone
   zeroDeps :: Operand -> Operand -> Set a
   zeroDeps x y
      | isZero x = singleton α
      | isZero y = singleton β
      | otherwise = both

   comparison :: (Ordering -> Boolean) -> Operand -> Operand -> MayFail (BaseVal a × Set a)
   comparison f x y
      | isNan x || isNan y = pure (Lit (Bool false) × both)
      | otherwise = ordering x y <#> \o -> Lit (Bool (f o)) × both

   arith :: (Int -> Int -> Int) -> (Number -> Number -> Number) -> Operand -> Operand -> MayFail (BaseVal a)
   arith f _ (Left m) (Left n) = pure (Lit (Int (f m n)))
   arith _ g x y = Lit <<< Float <$> (g <$> float x <*> float y)

   floorDiv :: Int -> Int -> Int
   floorDiv m n = Int.floor (toNumber m / toNumber n)

   nonZero :: Operand -> MayFail Unit
   nonZero y = when (isZero y) divisionByZero

   isZero :: Operand -> Boolean
   isZero (Left 0) = true
   isZero (Right (Left 0.0)) = true
   isZero _ = false

   isNan :: Operand -> Boolean
   isNan (Right (Left r)) = N.isNaN r
   isNan _ = false

   float :: Operand -> MayFail Number
   float (Left n) = pure (toNumber n)
   float (Right (Left r)) = pure r
   float (Right (Right w)) = Left (typeMismatch (Lit (Str w)) "int or float")

   ordering :: Operand -> Operand -> MayFail Ordering
   ordering (Right (Right w)) (Right (Right w')) = pure (compare w w')
   ordering (Left m) (Left n) = pure (compare m n)
   ordering x y = compare <$> float x <*> float y

bothNan :: forall a. Val a -> Val a -> Boolean
bothNan (Val _ (Lit (Float r))) (Val _ (Lit (Float r'))) = N.isNaN r && N.isNaN r'
bothNan _ _ = false

vertices2 :: forall a. Ord a => Val a -> Val a -> Set a
vertices2 (Val α _) (Val β _) = Set.fromFoldable [ α, β ]

repeatStr :: forall a. Ord a => String -> a -> Int -> a -> BaseVal a × Set a
repeatStr w α n β = Lit (Str (String.joinWith "" (replicate n w))) × deps
   where
   deps = if n <= 0 then singleton β else Set.fromFoldable [ α, β ]

unop :: forall a. Ord a => Unop -> Val a -> MayFail (BaseVal a × Set a)
unop Not (Val α (Lit (Bool b))) = pure (Lit (Bool (not b)) × singleton α)
unop Not (Val _ u) = Left (typeMismatch u "bool")
unop Neg (Val α (Lit (Int n))) = pure (Lit (Int (negate n)) × singleton α)
unop Neg (Val α (Lit (Float r))) = pure (Lit (Float (negate r)) × singleton α)
unop Pos (Val α u@(Lit (Int _))) = pure (u × singleton α)
unop Pos (Val α u@(Lit (Float _))) = pure (u × singleton α)
unop _ (Val _ u) = Left (typeMismatch u "int or float")

eqOp :: forall a. Ord a => Val a -> Val a -> MayFail (Boolean × Set a)
eqOp v@(Val α u) v'@(Val β u') = case u, u' of
   Lit (Float r), Lit (Float r') | N.isNaN r && N.isNaN r' -> Left "Cannot compare nan with nan in container"
   Lit ℓ, Lit ℓ' | sameKind ℓ ℓ' -> pure (eqLiteral ℓ ℓ' × both)
   Lit (Bool _), Lit (Int _) -> undefined unit
   Lit (Bool _), Lit (Float _) -> undefined unit
   Lit (Int _), Lit (Bool _) -> undefined unit
   Lit (Float _), Lit (Bool _) -> undefined unit
   Fun _, Fun _ -> undefined unit
   Obj c _, Obj d _ | c == cRange && d == cRange -> eqElems both (elements v) (elements v')
   Obj c ((_ × x) : (_ × y) : Nil), Lit ℓ
      | c == cComplex && isNumber ℓ -> eqElems both (x : y : Nil) (v' : Val β (Lit (Float 0.0)) : Nil)
   Lit ℓ, Obj c ((_ × x) : (_ × y) : Nil)
      | c == cComplex && isNumber ℓ -> eqElems both (v : Val α (Lit (Float 0.0)) : Nil) (x : y : Nil)
   Obj c xvs, Obj d yus
      | c == d -> eqElems both (snd <$> xvs) (snd <$> yus)
      | otherwise -> pure (false × both)
   List _, List _ -> eqElems both (elements v) (elements v')
   Tuple _, Tuple _ -> eqElems both (elements v) (elements v')
   Dictionary (DictRep d), Dictionary (DictRep d') -> eqDict d d'
   Matrix r, Matrix r' -> eqMatrix r r'
   _, _ -> pure (false × both) -- different forms
   where
   both = Set.fromFoldable [ α, β ]
   undefined _ = Left ("Cannot compare " <> prettyP (erase u) <> " with " <> prettyP (erase u'))

   eqDict :: Dict (a × Val a) -> Dict (a × Val a) -> MayFail (Boolean × Set a)
   eqDict d d' =
      if keys d == keys d' then
         eqElems αs (snd <$> values d) (snd <<< definitely' <<< flip lookup d' <$> Set.toUnfoldable (keys d))
      else pure (false × αs)
      where
      αs = both ∪ keyVertices d ∪ keyVertices d'

   keyVertices :: Dict (a × Val a) -> Set a
   keyVertices = values >>> map fst >>> Set.fromFoldable

   eqMatrix :: MatrixRep a -> MatrixRep a -> MayFail (Boolean × Set a)
   eqMatrix (MatrixRep (vss × i × j)) (MatrixRep (vss' × i' × j')) =
      if dropα (unpack' int i) == dropα (unpack' int i') && dropα (unpack' int j) == dropα (unpack' int j') then eqElems αs (elems vss) (elems vss')
      else pure (false × αs)
      where
      αs = both ∪ Set.fromFoldable (root <$> [ i, j, i', j' ])

   elems :: Array (Array (Val a)) -> List (Val a)
   elems = fromFoldable >>> map fromFoldable >>> L.concat

   isNumber :: Literal -> Boolean
   isNumber (Int _) = true
   isNumber (Float _) = true
   isNumber _ = false

   sameKind :: Literal -> Literal -> Boolean
   sameKind ℓ ℓ' = case ℓ, ℓ' of
      Int _, Int _ -> true
      Int _, Float _ -> true
      Float _, Int _ -> true
      Float _, Float _ -> true
      Str _, Str _ -> true
      Bool _, Bool _ -> true
      None, None -> true
      _, _ -> false

eqElems :: forall a. Ord a => Set a -> List (Val a) -> List (Val a) -> MayFail (Boolean × Set a)
eqElems αs Nil Nil = pure (true × αs)
eqElems αs (v : vs) (v' : vs') = do
   b × βs <- eqOp v v'
   if b then eqElems (αs ∪ βs) vs vs' else pure (false × (αs ∪ βs))
eqElems αs _ _ = pure (false × αs)

contains :: forall a. Ord a => Val a -> Val a -> MayFail (Boolean × Set a)
contains (Val α u') v@(Val β u) = case u', u of
   List _, _ -> second (Set.insert α) <$> elem (elements (Val α u'))
   Tuple _, _ -> second (Set.insert α) <$> elem (elements (Val α u'))
   Dictionary (DictRep d), Lit (Str w) -> pure (Set.member w (keys d) × Set.fromFoldable [ α, β ])
   Dictionary _, _ -> Left (typeMismatch u "str")
   Lit (Str w'), Lit (Str w) -> pure (String.contains (Pattern w) w' × Set.fromFoldable [ α, β ])
   Lit (Str _), _ -> Left (typeMismatch u "str")
   _, _ -> Left (typeMismatch u' "list, tuple, dict or str")
   where
   elem :: List (Val a) -> MayFail (Boolean × Set a)
   elem Nil = pure (false × Set.empty)
   elem (v' : vs) = do
      b × βs <- eqOp v v'
      if b then pure (true × βs) else second (βs ∪ _) <$> elem vs
