module Rules where

import Prelude

import Bind (Name, Var)
import Data.Foldable (class Foldable, foldr, sum)
import Data.List (List(..), (:))
import Data.Traversable (class Traversable)
import Expr (Binop, Def, Expr, Unop)
import Literal (Literal)


data Rule v a
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
   | Lambda Def
   | Application a (List a) a --function closure, args, callee
   | PartialApplication a (List a)
   | PrimitiveOp String a (List a)
   | ObjectConstructor Name (List a)
   | Subscript a a
   | Attribute Var a
   | ValueLeaf v

derive instance Functor (Rule v)
derive instance Foldable (Rule v)
derive instance Traversable (Rule v)

-- Field order is premise order: application visits the function, arguments,
-- then callee. Repeated references remain separate argument positions.
premises :: forall v a. Rule v a -> List a
premises = foldr (:) Nil

-- Fallback for values without an evaluator rule yet.
valueRule :: forall v a. v -> Rule v a
valueRule = ValueLeaf
