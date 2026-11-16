module Pretty.Trace (renderTrace) where

import Prelude

import Bind (dottedName)
import Data.Array as Array
import Data.Foldable (foldr)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.String.CodePoints as String
import DepGraph (Deriv, valAt)
import Dict as Dict
import Eval (Eval)
import Literal as Literal
import Operator (binopSymbol, unopSymbol)
import Pretty (prettyP)
import Rules as R
import Util (type (×), (×))
import Util.Pair (Pair(..))
import Util.Set (size)
import Val (DictRep(..), ForeignOp(..), MatrixRep(..), Val(..))
import Val as V

-- The tree is a display of the rule graph. Labels organise the children
-- of rules whose premises have distinct roles.
data TraceNode
   = Vertex String Deriv
   | Branch String (List TraceNode)

type TracePosition = { linePrefix :: String, childPrefix :: String }

renderTrace :: Eval -> String
renderTrace { g, root } =
   -- joinWith "\n" (Array.fromFoldable (List.reverse lines) <> [ "", "result: " <> valueSummary (valAt g root) ])
   joinWith "\n" (Array.fromFoldable (List.reverse lines))
   where
   lines = render Set.empty (({ linePrefix: "", childPrefix: "" } × Vertex "" root) : Nil) Nil

   render :: Set.Set Deriv -> List (TracePosition × TraceNode) -> List String -> List String
   render seen pending output = case pending of
      Nil -> output
      (position × Branch label children) : rest ->
         render seen (positionChildren position.childPrefix children <> rest)
            ((position.linePrefix <> label) : output)
      (position × Vertex role p) : rest
         | Set.member p seen ->
              render seen rest ((position.linePrefix <> role <> "#" <> show p) : output)
         | otherwise ->
              let
                 value = valAt g p
                 rule = fromMaybe (R.valueRule value) (Map.lookup p g.rules)
                 label = role <> "#" <> show p <> " " <> abbreviate 64 (ruleSummary rule)
                    <> " -> " <> valueSummary value
                 children = positionChildren position.childPrefix (traceChildren rule)
              in render (Set.insert p seen) (children <> rest) ((position.linePrefix <> label) : output)

positionChildren :: String -> List TraceNode -> List (TracePosition × TraceNode)
positionChildren prefix = foldr position Nil
   where
   position child Nil =
      ({ linePrefix: prefix <> "└─ ", childPrefix: prefix <> "   " } × child) : Nil
   position child siblings =
      ({ linePrefix: prefix <> "├─ ", childPrefix: prefix <> "│  " } × child) : siblings

traceChildren :: R.Rule (Val Unit) Deriv -> List TraceNode
traceChildren = case _ of
   R.ListComp _ _ run ->
      qualifierTree (\body -> Vertex "body " body : Nil) run : Nil
   R.DictComp _ _ _ run ->
      qualifierTree (\(Pair key value) -> Vertex "key " key : Vertex "value " value : Nil) run : Nil
   R.Application fun args callee ->
      Vertex "function " fun : (map (Vertex "argument ") args <> (Vertex "callee " callee : Nil))
   rule -> map (Vertex "") (R.premises rule)

-- Nesting shows which qualifier branch supplied each body. The body
-- evaluations still run after the qualifier phase completes.
qualifierTree
   :: forall b
    . (b -> List TraceNode)
   -> R.QualifierRun Deriv (R.CompYield (Val Unit) b)
   -> TraceNode
qualifierTree bodyChildren = case _ of
   R.GeneratorRun source branches ->
      Branch "generator" (Vertex "source " source : mapWithIndex candidate branches)
   R.GuardPassed condition rest ->
      Branch "guard passed" (Vertex "condition " condition : qualifierTree bodyChildren rest : Nil)
   R.GuardFailed condition ->
      Branch "guard failed" (Vertex "condition " condition : Nil)
   R.DeclRun init rest ->
      Branch "declaration" (Vertex "initialiser " init : qualifierTree bodyChildren rest : Nil)
   R.Yield { bindings, body } ->
      let assignments = Dict.toArrayWithKey (\name value -> name <> " = " <> valueSummary value) bindings
      in Branch ("yield {" <> joinWith ", " assignments <> "}") (bodyChildren body)
   where
   candidate index = case _ of
      Nothing -> Branch ("candidate " <> show index <> " (pattern did not match)") Nil
      Just run -> Branch ("candidate " <> show index) (qualifierTree bodyChildren run : Nil)

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

ruleSummary :: forall a. R.Rule (Val Unit) a -> String
ruleSummary = case _ of
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
   R.DictLiteral _ -> "DictLiteral"
   R.DictComp _ _ _ _ -> "DictComp"
   R.ListComp _ _ _ -> "ListComp"
   R.Lambda _ -> "Lambda"
   R.Application _ _ _ -> "Application"
   R.PartialApplication _ _ -> "PartialApplication"
   R.PrimitiveOp name _ _ -> "PrimitiveOp " <> show name
   R.Matrix _ _ -> "Matrix"
   R.Subscript _ _ -> "Subscript"
   R.ObjectConstructor name _ -> "ObjectConstructor " <> dottedName name
   R.Attribute x _ -> "Attribute " <> show x
   R.ValueLeaf _ -> "ValueLeaf"
