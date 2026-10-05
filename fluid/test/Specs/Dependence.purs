module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (matrixElement, select)
import DataType (cPair, f_fst, f_snd)
import Test.Util (DepSpec)

-- Select whole output of a file under dependence/.
onOutput :: String -> String -> DepSpec
onOutput file expect = { file: "dependence/" <> file, doc: false, δv: \_ -> select, expect, fwd_expect: "" }

dep_cases :: Array DepSpec
dep_cases =
   [ onOutput "var.fld" "x: ⸨[⸨1⸩, ⸨2⸩]⸩"
   , onOutput "cond.fld" "b: ⟪True⟫\ny: ⸨1⸩\nz: 2"
   , onOutput "match_fallthrough.fld" "v: ⟪Bar()⟫\nw: ⸨5⸩"
   , onOutput "early_return.fld" "a: 1\nb: ⸨2⸩\nc: ⟪False⟫"
   , onOutput "attribute.fld" "p: ⟪P(⸨1⸩, 2)⟫"
   , onOutput "subscript.fld" "i: ⟪1⟫\nxs: ⟪[3, ⸨4⸩, 5]⟫"
   , onOutput "filter.fld" "n: ⟪5⟫\nxs: ⟪[⸨8⸩, ⟪4⟫, ⸨7⸩, ⟪3⟫]⟫"
   , onOutput "closure.fld" "a: ⸨1⸩\nb: ⸨2⸩"
   , onOutput "partial.fld" "a: ⸨1⸩\nb: ⸨2⸩"
   , onOutput "len.fld" "len: ⟪len⟫\nxs: ⸨[1, 2]⸩"
   , onOutput "dict_lookup.fld" "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫"
   , onOutput "dict_pattern.fld" "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫"
   , (onOutput "seq.fld" "a: 1\nb: 2\nc: ⟪True⟫\nd: ⸨4⸩") { δv = \arg -> arg cPair f_snd select }
   , (onOutput "doc_this.fld" "x: ⸨1⸩\ny: ⸨2⸩\n@doc(⸨Paragraph(⸨[⸨\"Sum\"⸩, ⸨\"is\"⸩, ⸨3⸩]⸩)⸩) ⸨3⸩") { doc = true }
   , { file: "slicing/matrix/matmul.fld"
     , doc: false
     , δv: \arg -> arg cPair f_fst $ matrixElement 0 0 select
     , expect:
          """leftMatrix: ⟪⸨1⸩, ⸨2⸩, ⸨3⸩,
4, 5, 6⟫
mat_mul: ⟪cl⟫
rightMatrix: ⟪⸨1⸩, 2,
⸨3⸩, 4,
⸨5⸩, 6⟫
@doc(Paragraph(["Intermediate", "matrix"])) ⸨22⸩, 28,
49, 64
@doc(Paragraph(["Intermediate", "matrix"])) 9, 12, 15,
19, 26, 33,
29, 40, 51"""
     , fwd_expect:
          """(⟪⸨22⸩, ⸨28⸩,
⸨49⸩, ⟪64⟫⟫, ⟪⸨9⸩, ⸨12⸩, ⸨15⸩,
⸨19⸩, ⸨26⸩, ⸨33⸩,
⸨29⸩, ⸨40⸩, ⸨51⸩⟫)"""
     }
   ]
