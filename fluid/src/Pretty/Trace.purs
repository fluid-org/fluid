module Pretty.Trace (renderTrace) where

import Prelude hiding (absurd)

import Bind (dottedName)
import Data.Array as Array
import Data.Foldable (foldr)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Set as Set
import Data.String (joinWith)
import Data.String.CodePoints as String
import Eval (Eval)
import Dict as Dict
import Literal as Literal
import Operator (binopSymbol, unopSymbol)
import Path (Path, Step(..), Vertex(..), sourceRoot)
import Pretty (prettyP)
import Trace as Tr
import Util (type (×), absurd, error, (×))
import Util.Map (get)
import Util.Pair (Pair(..))
import Util.Set (size)
import Val (DictRep(..), Env(..), ForeignOp(..), Label(..), MatrixRep(..), Val(..), child)
import Val as V

data TraceNode
   = At String Path
   | Branch String (List TraceNode)

type TreePosition = { linePrefix :: String, childPrefix :: String }

renderTrace :: Eval -> String
renderTrace { g, out } = joinWith "\n" (Array.fromFoldable (List.reverse lines))
   where
   lines = render Set.empty (({ linePrefix: "", childPrefix: "" } × At "" (sourceRoot out)) : Nil) Nil

   render :: Set.Set Path -> List (TreePosition × TraceNode) -> List String -> List String
   render seen pending output = case pending of
      Nil -> output
      (position × Branch label children) : rest ->
         render seen (positionChildren position.childPrefix children <> rest)
            ((position.linePrefix <> label) : output)
      (position × At role p@(EdgeSrc a : steps)) : rest
         | Set.member p seen -> render seen rest ((position.linePrefix <> role <> pathName p) : output)
         | otherwise ->
              let
                 trace = if List.null steps then Map.lookup a g.traces else Nothing
                 rule = if List.null steps then maybe "Untraced" traceSummary trace else "Position"
                 label = position.linePrefix <> role <> pathName p <> " " <> abbreviate 80 rule
                    <> " -> " <> positionSummary (get a g.vals) steps
                 children = maybe Nil traceChildren trace
              in render (Set.insert p seen)
                 (positionChildren position.childPrefix children <> rest) (label : output)
      _ -> error absurd

positionChildren :: String -> List TraceNode -> List (TreePosition × TraceNode)
positionChildren prefix = foldr position Nil
   where
   position node Nil =
      ({ linePrefix: prefix <> "└─ ", childPrefix: prefix <> "   " } × node) : Nil
   position node siblings =
      ({ linePrefix: prefix <> "├─ ", childPrefix: prefix <> "│  " } × node) : siblings

pathName :: Path -> String
pathName (EdgeSrc (Vertex a) : steps) = "#" <> show a <>
   (if List.null steps then "" else "/" <> joinWith "/" (Array.fromFoldable (show <$> steps)))
pathName _ = error absurd

indexed :: String -> List Path -> List TraceNode
indexed role = mapWithIndex (\i -> At (role <> " " <> show i <> " "))

traceChildren :: Tr.Trace (Label Unit) Path -> List TraceNode
traceChildren = case _ of
   Tr.ExprTrace trace -> case trace of
      Tr.Application fun args callee ->
         At "function " fun : (indexed "argument" args <> (At "body " callee : Nil))
      Tr.PartialApplication fun args -> At "function " fun : indexed "argument" args
      Tr.PrimitiveOp _ fun args -> At "function " fun : indexed "argument" args
      Tr.ListComp _ _ run -> At "qualifiers " run : Nil
      Tr.DictComp _ _ _ run -> At "qualifiers " run : Nil
      Tr.DictLiteral entries -> mapWithIndex (\i (Pair k v) ->
         Branch ("entry " <> show i) (At "key " k : At "value " v : Nil)) entries
      Tr.Matrix dims rows -> At "dimensions " dims : Array.toUnfoldable
         (mapWithIndex (\i row -> Branch ("row " <> show i) (indexed "cell" (Array.toUnfoldable row))) rows)
      Tr.Subscript container index -> At "container " container : At "index " index : Nil
      Tr.Attribute _ receiver -> At "receiver " receiver : Nil
      Tr.DocExpr body doc -> At "body " body : At "documentation " doc : Nil
      _ -> At "" <$> Tr.premises trace
   Tr.QualifierTrace trace -> case trace of
      Tr.GeneratorTrace source branches -> At "source " source : mapWithIndex candidate branches
      Tr.GuardPassed condition rest -> At "condition " condition : At "rest " rest : Nil
      Tr.GuardFailed condition -> At "condition " condition : Nil
      Tr.DeclTrace value rest -> At "initializer " value : At "rest " rest : Nil
      Tr.ListYield { body } -> At "body " body : Nil
      Tr.DictYield { body: Pair k v } -> At "key " k : At "value " v : Nil
   Tr.StmtTrace trace -> case trace of
      Tr.IfTaken conditions branch -> indexed "condition" conditions <> (At "branch " branch : Nil)
      Tr.IfSkipped conditions -> indexed "condition" conditions
      Tr.MatchTaken value _ branch -> At "scrutinee " value : At "branch " branch : Nil
      Tr.MatchFailed value -> At "scrutinee " value : Nil
      Tr.SeqFull first second -> At "first " first : At "second " second : Nil
      Tr.SeqReturned first _ -> At "first " first : Nil
      _ -> At "" <$> Tr.premises trace
   where
   candidate i branch = Branch ("candidate " <> show i <> maybe " (pattern did not match)" (const "") branch)
      (maybe Nil (\p -> At "" p : Nil) branch)

traceSummary :: forall a. Tr.Trace (Label Unit) a -> String
traceSummary = case _ of
   Tr.ExprTrace trace -> case trace of
      Tr.Variable x -> "Variable " <> show x
      Tr.Literal literal -> "Literal " <> literalSummary literal
      Tr.Binary op _ _ -> "Binary " <> binopSymbol op
      Tr.Unary op _ -> "Unary " <> unopSymbol op
      Tr.AndShort _ _ -> "AndShort"
      Tr.AndFull _ _ -> "AndFull"
      Tr.OrShort _ _ -> "OrShort"
      Tr.OrFull _ _ -> "OrFull"
      Tr.CondTrue _ _ _ -> "CondTrue"
      Tr.CondFalse _ _ _ -> "CondFalse"
      Tr.ListLiteral _ -> "ListLiteral"
      Tr.TupleLiteral _ -> "TupleLiteral"
      Tr.DictLiteral _ -> "DictLiteral"
      Tr.DictComp _ _ _ _ -> "DictComp"
      Tr.ListComp _ _ _ -> "ListComp"
      Tr.Lambda _ -> "Lambda"
      Tr.Application _ _ _ -> "Application"
      Tr.PartialApplication _ _ -> "PartialApplication"
      Tr.PrimitiveOp name _ _ -> "PrimitiveOp " <> show name
      Tr.Matrix _ _ -> "Matrix"
      Tr.Subscript _ _ -> "Subscript"
      Tr.ObjectConstructor name _ -> "ObjectConstructor " <> dottedName name
      Tr.Attribute x _ -> "Attribute " <> show x
      Tr.DocExpr _ _ -> "DocExpr"
      Tr.ValueLeaf _ -> "ValueLeaf"
   Tr.QualifierTrace trace -> case trace of
      Tr.GeneratorTrace _ _ -> "GeneratorTrace"
      Tr.GuardPassed _ _ -> "GuardPassed"
      Tr.GuardFailed _ -> "GuardFailed"
      Tr.DeclTrace _ _ -> "DeclTrace"
      Tr.ListYield { bindings } -> "ListYield " <> displayBindings labelSummary bindings
      Tr.DictYield { bindings } -> "DictYield " <> displayBindings labelSummary bindings
   Tr.StmtTrace trace -> case trace of
      Tr.Return _ -> "Return"
      Tr.IfTaken _ _ -> "IfTaken"
      Tr.IfSkipped _ -> "IfSkipped"
      Tr.MatchTaken _ pattern _ -> "MatchTaken " <> prettyP pattern
      Tr.MatchFailed _ -> "MatchFailed"
      Tr.Declare x -> "Declare " <> x
      Tr.Assign pattern _ -> "Assign " <> prettyP pattern
      Tr.DefRegion ds -> "DefRegion " <> joinWith ", " (Dict.toArrayWithKey (\name _ -> name) ds)
      Tr.Pass -> "Pass"
      Tr.ExprStmt _ -> "ExprStmt"
      Tr.AssertPassed _ -> "AssertPassed"
      Tr.Dataclass name -> "Dataclass " <> dottedName name
      Tr.TypeAlias x _ _ -> "TypeAlias " <> x
      Tr.SeqFull _ _ -> "SeqFull"
      Tr.SeqReturned _ _ -> "SeqReturned"

positionSummary :: Label Unit -> Path -> String
positionSummary label Nil = labelSummary label
positionSummary (Value v) steps = valueSummary (valueAt v steps)
positionSummary (Bindings (Env bindings)) (Binding x : steps) = valueSummary (valueAt (get x bindings) steps)
positionSummary (Inputs _ env) (InputsEnv : steps) = positionSummary (Bindings env) steps
positionSummary (Inputs _ _) (InputsCtl : Nil) = "<control>"
positionSummary _ _ = error absurd

valueAt :: Val Unit -> Path -> Val Unit
valueAt v Nil = v
valueAt (Val _ (V.Fun (V.Closure (Env bindings) _ _))) (ClosureEnv : Binding x : steps) =
   valueAt (get x bindings) steps
valueAt v (step : steps) = valueAt (child step v) steps

labelSummary :: Label Unit -> String
labelSummary (Value v) = valueSummary v
labelSummary (Bindings env) = bindingsSummary env
labelSummary (Inputs _ env) = "inputs " <> bindingsSummary env

bindingsSummary :: Env Unit -> String
bindingsSummary (Env bindings) = displayBindings valueSummary bindings

displayBindings :: forall v. (v -> String) -> Dict.Dict v -> String
displayBindings summary bindings = "{" <> joinWith ", " entries <> suffix <> "}"
   where
   entries = map (\(name × value) -> name <> " = " <> summary value)
      (Array.take 3 (Dict.toArrayWithKey (\name value -> name × value) bindings))
   suffix = if size bindings > 3 then ", …" else ""

valueSummary :: forall a. Val a -> String
valueSummary = preview 2
   where
   preview depth (Val _ value) = abbreviate 64 case value of
      V.Lit literal -> literalSummary literal
      V.List values -> sequencePreview depth "[" "]" values
      V.Tuple values -> sequencePreview depth "(" (if Array.length values == 1 then ",)" else ")") values
      V.Obj name fields -> "<" <> abbreviate 24 (dottedName name) <> "; " <> show (List.length fields) <> " fields>"
      V.Dictionary (DictRep entries) -> "<dict; " <> show (size entries) <> " entries>"
      V.Matrix (MatrixRep (_ × height × width)) -> "<matrix " <> dimension height <> "x" <> dimension width <> ">"
      V.Fun (V.Closure _ _ _) -> "<closure>"
      V.Fun (V.Prim (ForeignOp (name × _))) -> "<primitive " <> abbreviate 32 name <> ">"
      V.Fun (V.Partial _ args) -> "<partial; " <> show (List.length args) <> " supplied>"
      V.Fun (V.Type _) -> "<constructor>"
      V.Opaque name -> "<opaque " <> abbreviate 32 (dottedName name) <> ">"
      V.Module name -> "<module " <> abbreviate 32 (dottedName name) <> ">"
      V.Unbound -> "<unbound>"
      V.TypeAlias _ _ -> "<type alias>"

   sequencePreview depth opening closing values = opening <> contents <> closing <> suffix
      where
      count = Array.length values
      suffix = if count > 3 || depth <= 0 then " (" <> show count <> " items)" else ""
      contents
         | count == 0 = ""
         | depth <= 0 = "…"
         | otherwise = joinWith ", " (map (preview (depth - 1)) (Array.take 3 values)
              <> if count > 3 then [ "…" ] else [])

   dimension (Val _ (V.Lit (Literal.Int n))) = show n
   dimension _ = "?"

literalSummary :: Literal.Literal -> String
literalSummary (Literal.Str value) = show (abbreviate 24 value)
literalSummary literal = prettyP literal

abbreviate :: Int -> String -> String
abbreviate limit value =
   if String.length prefix > limit then String.take (limit - 1) prefix <> "…" else prefix
   where
   prefix = String.take (limit + 1) value
