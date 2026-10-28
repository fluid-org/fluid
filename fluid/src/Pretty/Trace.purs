module Pretty.Trace (renderTrace) where

import Prelude

import Bind (dottedName)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set as Set
import Data.String (Pattern(..), joinWith, split)
import Data.String.CodePoints as String
import DepGraph (Deriv, valAt)
import Eval (Eval)
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Rules as R
import Val (Val)

type TraceRow =
   { vertex :: String
   , rule :: String
   , premises :: String
   }

renderTrace :: Eval -> String
renderTrace { g, root } =
   joinWith "\n"
      ([ "root: " <> show root, "" ]
         <> map formatRow ([ header ] <> rows)
         <> [ "", "result: " <> singleLine (prettyP (valAt g root)) ])
   where
   header = { vertex: "vertex", rule: "rule", premises: "premises" }

   vertices = Set.toUnfoldable (reachable Set.empty (root : Nil)) :: Array Deriv
   rows = map row vertices

   vertexWidth = foldl (\width r -> max width (String.length r.vertex)) (String.length header.vertex) rows
   ruleWidth = foldl (\width r -> max width (String.length r.rule)) (String.length header.rule) rows

   formatRow r =
      padRight vertexWidth r.vertex <> "  "
         <> padRight ruleWidth r.rule <> "  "
         <> r.premises

   ruleAt p = fromMaybe (R.valueRule (valAt g p)) (Map.lookup p g.rules)

   reachable seen Nil = seen
   reachable seen (p : pending)
      | Set.member p seen = reachable seen pending
      | otherwise = reachable (Set.insert p seen) ((ruleAt p).premises <> pending)

   row :: Deriv -> TraceRow
   row p =
      let rule = ruleAt p
      in
         { vertex: show p
         , rule: ruleSummary rule.context
         , premises: show (Array.fromFoldable rule.premises)
         }

padRight :: Int -> String -> String
padRight width value =
   value <> joinWith "" (Array.replicate (width - String.length value) " ")

singleLine :: String -> String
singleLine = split (Pattern "\n") >>> joinWith " "

ruleSummary :: R.RuleContext (Val Unit) -> String
ruleSummary = case _ of
   R.Hole -> "Hole"
   R.Variable x -> "Variable " <> show x
   R.Literal literal -> "Literal " <> prettyP literal
   R.Binary op _ _ -> "Binary " <> show (binopSymbol op)
   R.Unary op _ -> "Unary " <> show (unopSymbol op)
   R.AndShort _ _ -> "AndShort"
   R.AndFull _ _ -> "AndFull"
   R.OrShort _ _ -> "OrShort"
   R.OrFull _ _ -> "OrFull"
   R.CondTrue _ _ _ -> "CondTrue"
   R.CondFalse _ _ _ -> "CondFalse"
   R.ListLiteral _ -> "ListLiteral"
   R.TupleLiteral _ -> "TupleLiteral"
   R.Lambda _ -> "Lambda"
   R.Application _ _ _ -> "Application"
   R.PartialApplication _ _ -> "PartialApplication"
   R.PrimitiveOp name _ -> "PrimitiveOp " <> show name
   R.ObjectConstructor name _ -> "ObjectConstructor " <> dottedName name
   R.ValueLeaf value -> "ValueLeaf " <> singleLine (prettyP value)
