module Operator where

import Prelude hiding (join)
import Prim hiding (Type)

import Bind (Name)
import Data.Array (findIndex)
import Data.Foldable (all, and, elem, find)
import Data.Bifunctor (lmap)
import Data.List (List(..), mapMaybe, nubEq, reverse, zipWith, (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Classes (ClassTable, comparable, fieldsAt, join, joins, subtype)
import Expr (Binop(..), Unop(..))
import Literal as L
import Parsing.Expr (Assoc(..))
import Types (Type(..), baseType)
import Types.Defs (bool, complex, float, int, str)
import Util (type (×), definitely', whenever, (×))

data Operator = Binary Binop | Unary Unop | AndOp | OrOp

derive instance Eq Operator

-- Precedence levels, loosest first
levels :: Array (Array Operator)
levels =
   [ [ OrOp ]
   , [ AndOp ]
   , [ Unary Not ]
   , Binary <$> comparisons
   , [ Binary BitOr ]
   , [ Binary Add, Binary Sub ]
   , [ Binary Mul, Binary Div, Binary FloorDiv, Binary Mod ]
   , [ Unary Pos, Unary Neg ]
   , [ Binary Pow ]
   ]

comparisons :: Array Binop
comparisons = [ Eq, Ne, Lt, Le, Gt, Ge, In, NotIn ]

-- Chained comparisons and boolean operators prohibited
assoc :: Operator -> Assoc
assoc (Binary Pow) = AssocRight
assoc (Binary b) | elem b comparisons = AssocNone
assoc AndOp = AssocNone
assoc OrOp = AssocNone
assoc _ = AssocLeft

prec :: Operator -> Int
prec op = definitely' (findIndex (elem op) levels)

binopSymbol :: Binop -> String
binopSymbol Eq = "=="
binopSymbol Ne = "!="
binopSymbol Lt = "<"
binopSymbol Le = "<="
binopSymbol Gt = ">"
binopSymbol Ge = ">="
binopSymbol In = "in"
binopSymbol BitOr = "|"
binopSymbol NotIn = "not in"
binopSymbol Add = "+"
binopSymbol Sub = "-"
binopSymbol Mul = "*"
binopSymbol Div = "/"
binopSymbol FloorDiv = "//"
binopSymbol Mod = "%"
binopSymbol Pow = "**"

unopSymbol :: Unop -> String
unopSymbol Not = "not"
unopSymbol Pos = "+"
unopSymbol Neg = "-"

-- Parameter types and result type
type Overload = List Type × Type

resolveBinop :: ClassTable -> Binop -> Type -> Type -> Maybe Type
resolveBinop classes op σ τ =
   least classes (nubEq (resolved σ τ <> resolved (baseType σ) (baseType τ)))
   where
   resolved σ' τ' = mapMaybe (\overload -> overload σ' τ') (binopOverloads classes op)

resolveUnop :: ClassTable -> Unop -> Type -> Maybe Type
resolveUnop classes op σ =
   least classes (nubEq (resolved σ <> resolved (baseType σ)))
   where
   resolved σ' = mapMaybe (\overload -> overload σ') (unopOverloads classes op)

least :: ClassTable -> List Overload -> Maybe Type
least classes os = snd <$> find (\(σs × _) -> all (\(τs × _) -> and (zipWith (subtype classes) σs τs)) os) os

binopOverloads :: ClassTable -> Binop -> List (Type -> Type -> Maybe Overload)
binopOverloads classes op = case op of
   Eq -> equality classes : Nil
   Ne -> equality classes : Nil
   In -> membership
   NotIn -> membership
   BitOr -> Nil
   Lt -> ordering
   Le -> ordering
   Gt -> ordering
   Ge -> ordering
   Add -> arithmetic int : arithmetic float : complexArithmetic <> (both str str : concatList classes : concatTuple classes : Nil)
   Sub -> arithmetic int : arithmetic float : complexArithmetic
   Mul -> arithmetic int : arithmetic float : complexArithmetic <> (repeatStr classes : reflected repeatStr classes : repeatList classes : reflected repeatList classes : Nil)
   Div -> arithmetic float : complexArithmetic
   FloorDiv -> arithmetic int : arithmetic float : Nil
   Mod -> arithmetic int : arithmetic float : Nil
   Pow -> powerInt classes : arithmetic float : Nil
   where
   sub σ τ = subtype classes σ τ

   both bound result σ τ = whenever (sub σ bound && sub τ bound) ((bound : bound : Nil) × result)
   arithmetic τ = both τ τ

   -- One operand complex and other operand complex or float
   complexArithmetic = operands complex complex : operands complex float : operands float complex : Nil
   operands bound bound' σ τ = whenever (sub σ bound && sub τ bound') ((bound : bound' : Nil) × complex)
   ordering = both float bool : both str bool : Nil

   membership = membershipList classes : membershipTuple classes : both str bool : membershipDict classes : Nil

type BinopOverload = ClassTable -> Type -> Type -> Maybe Overload

equality :: BinopOverload
equality classes σ τ =
   whenever (comparable classes σ τ && equalityType classes σ && equalityType classes τ) ((σ : τ : Nil) × bool)

membershipList :: BinopOverload
membershipList classes σ τ@(ListTy τ') = whenever (comparable classes σ τ') ((σ : τ : Nil) × bool)
membershipList _ _ _ = Nothing

membershipTuple :: BinopOverload
membershipTuple classes σ τ@(TupleTy τs) = whenever (comparable classes σ (joins classes τs)) ((σ : τ : Nil) × bool)
membershipTuple _ _ _ = Nothing

membershipDict :: BinopOverload
membershipDict classes σ τ@(DictTy _) = whenever (subtype classes σ str) ((str : τ : Nil) × bool)
membershipDict _ _ _ = Nothing

concatList :: BinopOverload
concatList classes σ@(ListTy σ') τ@(ListTy τ') = Just ((σ : τ : Nil) × ListTy (join classes σ' τ'))
concatList _ _ _ = Nothing

concatTuple :: BinopOverload
concatTuple _ σ@(TupleTy σs) τ@(TupleTy τs) = Just ((σ : τ : Nil) × TupleTy (σs <> τs))
concatTuple _ _ _ = Nothing

repeatStr :: BinopOverload
repeatStr classes σ τ = whenever (subtype classes σ str && subtype classes τ int) ((str : int : Nil) × str)

repeatList :: BinopOverload
repeatList classes σ@(ListTy _) τ = whenever (subtype classes τ int) ((σ : int : Nil) × σ)
repeatList _ _ _ = Nothing

reflected :: BinopOverload -> BinopOverload
reflected overload classes σ τ = lmap reverse <$> overload classes τ σ

powerInt :: BinopOverload
powerInt classes σ τ@(LitTy (L.Int n)) = whenever (subtype classes σ int) ((int : τ : Nil) × if n < 0 then float else int)
powerInt _ _ _ = Nothing

unopOverloads :: ClassTable -> Unop -> List (Type -> Maybe Overload)
unopOverloads classes op = case op of
   Not -> sign bool : Nil
   Pos -> sign int : sign float : sign complex : Nil
   Neg -> sign int : sign float : sign complex : Nil
   where
   sign τ σ = whenever (subtype classes σ τ) ((τ : Nil) × τ)

equalityType :: ClassTable -> Type -> Boolean
equalityType classes = go Nil
   where
   go :: List Name -> Type -> Boolean
   go _ (CallableTy _ _) = false
   go _ (VarTy _) = false
   go cs (ListTy σ) = go cs σ
   go cs (DictTy σ) = go cs σ
   go cs (TupleTy τs) = all (go cs) τs
   go cs (UnionTy σ τ) = go cs σ && go cs τ
   go cs (ClassTy c τs)
      | c `elem` cs = true
      | otherwise = all (go (c : cs) <<< snd) (fieldsAt classes c τs)
   go _ _ = true
