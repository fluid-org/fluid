module Operator where

import Prelude

import Data.Array (findIndex)
import Data.Foldable (elem)
import Expr (Binop(..), Unop(..))
import Parsing.Expr (Assoc(..))
import Util (definitely')

data Operator = Binary Binop | Unary Unop | AndOp | OrOp | InfixOp | ConsOp

derive instance Eq Operator

-- Precedence levels, loosest first, per the spec; e |f| e' and :| are Fluid's
levels :: Array (Array Operator)
levels =
   [ [ OrOp ]
   , [ AndOp ]
   , [ Unary Not ]
   , [ Binary Eq, Binary Ne, Binary Lt, Binary Le, Binary Gt, Binary Ge, Binary In, Binary NotIn ]
   , [ InfixOp ]
   , [ ConsOp ]
   , [ Binary Add, Binary Sub ]
   , [ Binary Mul, Binary Div, Binary FloorDiv, Binary Mod ]
   , [ Unary Pos, Unary Neg ]
   , [ Binary Pow ]
   ]

assoc :: Operator -> Assoc
assoc (Binary Pow) = AssocRight
assoc ConsOp = AssocRight
assoc _ = AssocLeft

-- Higher binds tighter
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

