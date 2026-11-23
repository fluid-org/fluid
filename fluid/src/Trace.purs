module Trace where

import Bind (Name, Var)
import Data.Foldable (class Foldable, foldMap)
import Data.List (List, singleton)
import Data.Maybe (Maybe)
import Dict (Dict)
import Expr (Binop, Def, Expr, Qualifier, Unop)
import Literal (Literal)
import Util.Pair (Pair)


data Trace v a
   = ExprTrace (ExprTrace v a)
   | QualifierTrace (QualifierTrace v a)
   | StmtTrace (StmtTrace a)

data StmtTrace a = Returned a --for now

data ExprTrace v a
   = Variable Var
   | Literal Literal
   | Binary Binop a a
   | Unary Unop a
   | AndShort a Expr
   | AndFull a a
   | OrShort a Expr
   | OrFull a a
   | CondTrue a a Expr
   | CondFalse a Expr a
   | ListLiteral (List a)
   | TupleLiteral (List a)
   | DictLiteral (List (Pair a))
   | DictComp Expr Expr (List Qualifier) a
   | ListComp Expr (List Qualifier) a
   | Lambda Def
   | Application a (List a) a
   | PartialApplication a (List a)
   | PrimitiveOp String a (List a)
   | Matrix a (Array (Array a))
   | Subscript a a
   | ObjectConstructor Name (List a)
   | Attribute Var a
   | ValueLeaf v

--Nothing marks a failed generator pattern
--bodies are now separate nodes a instead of nested QualifierTraces
data QualifierTrace v a
   = GeneratorTrace a (List (Maybe a))
   | GuardPassed a a
   | GuardFailed a
   | DeclTrace a a
   | ListYield (CompYield v a)
   | DictYield (CompYield v (Pair a))

--bindings for display
type CompYield v b = { bindings :: Dict v, body :: b }

derive instance Foldable (ExprTrace v)
derive instance Foldable (QualifierTrace v)
derive instance Foldable StmtTrace
derive instance Foldable (Trace v)

premises :: forall f a. Foldable f => f a -> List a
premises = foldMap singleton

valueTrace :: forall v a. v -> ExprTrace v a
valueTrace = ValueLeaf
