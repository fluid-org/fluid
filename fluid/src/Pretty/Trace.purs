module Pretty.Trace (renderTrace) where

import Prelude

import Bind (dottedName)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.String.CodePoints as String
import DepGraph (Deriv, valAt)
import Eval (Eval)
import Literal as Literal
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Rules as R
import Util ((×))
import Util.Set (size)
import Val (DictRep(..), ForeignOp(..), MatrixRep(..), Val(..))
import Val as V

type TraceRow =
   { vertex :: String
   , rule :: String
   , value :: String
   , premises :: String
   }

renderTrace :: Eval -> String
renderTrace { g, root } =
   joinWith "\n"
      ([ "root: " <> show root, "" ]
         <> map formatRow ([ header ] <> rows)
         <> [ "", "result: " <> valueSummary (valAt g root) ])
   where
   header = { vertex: "vertex", rule: "rule", value: "value", premises: "premises" }

   vertices = Set.toUnfoldable (reachable Set.empty (root : Nil)) :: Array Deriv
   rows = map row vertices

   vertexWidth = foldl (\width r -> max width (String.length r.vertex)) (String.length header.vertex) rows
   ruleWidth = foldl (\width r -> max width (String.length r.rule)) (String.length header.rule) rows
   valueWidth = foldl (\width r -> max width (String.length r.value)) (String.length header.value) rows

   formatRow r =
      padRight vertexWidth r.vertex <> "  "
         <> padRight ruleWidth r.rule <> "  "
         <> padRight valueWidth r.value <> "  "
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
         , rule: abbreviate 64 (ruleSummary rule.context)
         , value: valueSummary (valAt g p)
         , premises: show (Array.fromFoldable rule.premises)
         }

padRight :: Int -> String -> String
padRight width value =
   value <> joinWith "" (Array.replicate (width - String.length value) " ")

-- Inspect only a small prefix; do not pretty-print an entire value and then
-- truncate it. In particular, never descend into a function's environment.
valueSummary :: forall a. Val a -> String
valueSummary = preview 2
   where
   preview depth (Val _ value) = abbreviate 64 case value of
      V.Lit literal -> literalSummary literal
      V.List values -> sequencePreview depth "[" "]" values
      V.Tuple values ->
         let closing = if Array.length values == 1 then ",)" else ")"
         in sequencePreview depth "(" closing values
      V.Obj name fields ->
         "<" <> abbreviate 24 (dottedName name) <> "; " <> show (List.length fields) <> " fields>"
      V.Dictionary (DictRep entries) -> "<dict; " <> show (size entries) <> " entries>"
      V.Matrix (MatrixRep (_ × height × width)) ->
         "<matrix " <> dimension height <> "x" <> dimension width <> ">"
      V.Fun (V.Closure _ _ _) -> "<closure>"
      V.Fun (V.Prim (ForeignOp (name × _))) -> "<primitive " <> abbreviate 32 name <> ">"
      V.Fun (V.Partial _ args) -> "<partial; " <> show (List.length args) <> " supplied>"
      V.Fun (V.Type _) -> "<constructor>"
      V.Opaque name -> "<opaque " <> abbreviate 32 (dottedName name) <> ">"
      V.Module name -> "<module " <> abbreviate 32 (dottedName name) <> ">"
      V.Unbound -> "<unbound>"
      V.TypeAlias _ _ -> "<type alias>"

   sequencePreview depth opening closing values =
      let
         count = Array.length values
         suffix = if count > 3 || depth <= 0 then " (" <> show count <> " items)" else ""
         contents
            | count == 0 = ""
            | depth <= 0 = "…"
            | otherwise = joinWith ", "
                 (map (preview (depth - 1)) (Array.take 3 values)
                    <> if count > 3 then [ "…" ] else [])
      in opening <> contents <> closing <> if count == 0 then "" else suffix

   dimension (Val _ (V.Lit (Literal.Int n))) = show n
   dimension _ = "?"

literalSummary :: Literal.Literal -> String
literalSummary = case _ of
   Literal.Str value -> show (abbreviate 24 value)
   literal -> prettyP literal

abbreviate :: Int -> String -> String
abbreviate limit value =
   let prefix = String.take (limit + 1) value
   in if String.length prefix > limit then String.take (limit - 1) prefix <> "…" else prefix

ruleSummary :: R.RuleContext (Val Unit) -> String
ruleSummary = case _ of
   R.Hole -> "Hole"
   R.Variable x -> "Variable " <> show x
   R.Literal literal -> "Literal " <> literalSummary literal
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
   R.PrimitiveOp name _ _ -> "PrimitiveOp " <> show name
   R.ObjectConstructor name _ -> "ObjectConstructor " <> dottedName name
   R.Subscript _ _ -> "Subscript"
   R.Attribute x _ -> "Attribute " <> show x
   R.ValueLeaf _ -> "ValueLeaf"
