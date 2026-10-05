module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (matrixElement, select)
import DataType (cPair, f_fst, f_snd)
import Test.Util (DepSpec, Dir(..), Visible(..))

-- Select whole output of a file under dependence/.
bwd :: String -> String -> DepSpec
bwd file expect = { file: "dependence/" <> file, on: Output, δv: \_ -> select, dir: Bwd, expect }

-- Select whole of an input of a file under dependence/.
fwd :: String -> String -> String -> DepSpec
fwd file x expect = { file: "dependence/" <> file, on: Input x, δv: \_ -> select, dir: Fwd, expect }

dep_cases :: Array DepSpec
dep_cases =
   [ bwd "var.fld" "x: ⸨[⸨1⸩, ⸨2⸩]⸩\n⸨[⸨1⸩, ⸨2⸩]⸩"
   , bwd "cond.fld" "b: ⟪True⟫\ny: ⸨1⸩\nz: 2\n⸨1⸩"
   , bwd "match_fallthrough.fld" "v: ⟪Bar()⟫\nw: ⸨5⸩\n⸨5⸩"
   , bwd "early_return.fld" "a: 1\nb: ⸨2⸩\nc: ⟪False⟫\n⸨2⸩"
   , bwd "attribute.fld" "p: ⟪P(⸨1⸩, 2)⟫\n⸨1⸩"
   , bwd "subscript.fld" "i: ⟪1⟫\nxs: ⟪[3, ⸨4⸩, 5]⟫\n⸨4⸩"
   , bwd "filter.fld" "n: ⟪5⟫\nxs: ⟪[⸨8⸩, ⟪4⟫, ⸨7⸩, ⟪3⟫]⟫\n⸨[⸨8⸩, ⸨7⸩]⸩"
   , bwd "closure.fld" "a: ⸨1⸩\nb: ⸨2⸩\n⸨3⸩"
   , bwd "partial.fld" "a: ⸨1⸩\nb: ⸨2⸩\n⸨3⸩"
   , bwd "len.fld" "len: ⟪len⟫\nxs: ⸨[1, 2]⸩\n⸨2⸩"
   , bwd "dict_lookup.fld" "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
   , bwd "dict_pattern.fld" "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
   , (bwd "seq.fld" "a: 1\nb: 2\nc: ⟪True⟫\nd: ⸨4⸩\n(1, ⸨4⸩)") { δv = \arg -> arg cPair f_snd select }
   , (bwd "doc_this.fld" "x: ⸨1⸩\ny: ⸨2⸩\n@doc(⸨Paragraph(⸨[⸨\"Sum\"⸩, ⸨\"is\"⸩, ⸨3⸩]⸩)⸩) ⸨3⸩") { on = OutputDoc }
   , fwd "cond.fld" "b" "b: ⸨True⸩\ny: 1\nz: 2\n⟪1⟫"
   , fwd "cond.fld" "y" "b: True\ny: ⸨1⸩\nz: 2\n⸨1⸩"
   , fwd "early_return.fld" "c" "a: 1\nb: 2\nc: ⸨False⸩\n⟪2⟫"
   , fwd "filter.fld" "n" "n: ⸨5⸩\nxs: [8, 4, 7, 3]\n⟪[⟪8⟫, ⟪7⟫]⟫"
   , fwd "seq.fld" "c" "a: 1\nb: 2\nc: ⸨True⸩\nd: 4\n⟪(⟪1⟫, ⟪4⟫)⟫"
   , fwd "doc_this.fld" "x" "x: ⸨1⸩\ny: 2\n@doc(Paragraph([\"Sum\", \"is\", ⸨3⸩])) ⸨3⸩"
   , { file: "slicing/matrix/matmul.fld"
     , on: Output
     , δv: \arg -> arg cPair f_fst $ matrixElement 0 0 select
     , dir: Bwd
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
29, 40, 51
(⸨22⸩, 28,
49, 64, 9, 12, 15,
19, 26, 33,
29, 40, 51)"""
     }
   , { file: "slicing/matrix/matmul.fld"
     , on: Documented 0
     , δv: \_ -> matrixElement 0 0 select
     , dir: Bwd
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
29, 40, 51
(22, 28,
49, 64, 9, 12, 15,
19, 26, 33,
29, 40, 51)"""
     }
   , { file: "slicing/matrix/matmul.fld"
     , on: Documented 0
     , δv: \_ -> matrixElement 0 0 select
     , dir: Fwd
     , expect:
          """leftMatrix: 1, 2, 3,
4, 5, 6
mat_mul: cl
rightMatrix: 1, 2,
3, 4,
5, 6
@doc(Paragraph(["Intermediate", "matrix"])) ⸨22⸩, 28,
49, 64
@doc(Paragraph(["Intermediate", "matrix"])) 9, 12, 15,
19, 26, 33,
29, 40, 51
(⸨22⸩, 28,
49, 64, 9, 12, 15,
19, 26, 33,
29, 40, 51)"""
     }
   , { file: "slicing/matrix/matmul.fld"
     , on: Input "leftMatrix"
     , δv: \_ -> matrixElement 0 0 select
     , dir: Fwd
     , expect:
          """leftMatrix: ⸨1⸩, 2, 3,
4, 5, 6
mat_mul: cl
rightMatrix: 1, 2,
3, 4,
5, 6
@doc(Paragraph(["Intermediate", "matrix"])) ⸨22⸩, ⸨28⸩,
49, 64
@doc(Paragraph(["Intermediate", "matrix"])) ⸨9⸩, 12, 15,
⸨19⸩, 26, 33,
⸨29⸩, 40, 51
(⸨22⸩, ⸨28⸩,
49, 64, ⸨9⸩, 12, 15,
⸨19⸩, 26, 33,
⸨29⸩, 40, 51)"""
     }
   ]
