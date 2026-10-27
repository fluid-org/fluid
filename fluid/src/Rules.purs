module Rules where

import Prelude

import Data.Either (Either(..))
import Data.Foldable (sum)
import Data.List (List, length)
import Bind (Var)
import Expr (Binop, Unop, Expr, Def)
import Literal (Literal)

data RuleContext v
    = Hole
    | Variable Var
    | Literal Literal
    | Binary Binop (RuleContext v) (RuleContext v)
    | Unary Unop (RuleContext v)

    | AndShort (RuleContext v) Expr --first false
    | AndFull (RuleContext v) (RuleContext v)
    | OrShort (RuleContext v) Expr --first true
    | OrFull (RuleContext v) (RuleContext v)
    | CondTrue (RuleContext v) (RuleContext v) Expr
    | CondFalse (RuleContext v) Expr (RuleContext v)

    | ListLiteral (List (RuleContext v))
    | TupleLiteral (List (RuleContext v))

    | Lambda Def
    | Application
        (RuleContext v) --function closure
        (List (RuleContext v)) --arguments in eval order
        (RuleContext v) --function callee
    | ValueLeaf v

type Rule v a =
    { context :: RuleContext v
    , premises :: List a --subderiv nodes
    }

contextArity :: forall v. RuleContext v -> Int
contextArity = case _ of
    Hole -> 1
    Variable _ -> 0
    Literal _ -> 0
    Binary _ left right -> contextArity left + contextArity right
    Unary _ operand -> contextArity operand

    AndShort left _ -> contextArity left
    AndFull left right -> contextArity left + contextArity right
    OrShort left _ -> contextArity left
    OrFull left right -> contextArity left + contextArity right
    CondTrue condition chosen _ -> contextArity condition + contextArity chosen
    CondFalse condition _ chosen -> contextArity condition + contextArity chosen

    ListLiteral children -> sum (map contextArity children)
    TupleLiteral children -> sum (map contextArity children)

    Lambda _ -> 0
    Application fun args callee ->
        contextArity fun + sum (map contextArity args) + contextArity callee
    ValueLeaf _ -> 0

