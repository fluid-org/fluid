module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (matrixElement, select)
import DataType (cPair, f_fst, f_snd)
import Test.Util (DepSpec)

dep_cases :: Array DepSpec
dep_cases =
   [ { file: "dependence/var.fld", doc: false, δv: \_ -> select, expect: "x: ⸨[⸨1⸩, ⸨2⸩]⸩" }
   , { file: "dependence/cond.fld", doc: false, δv: \_ -> select, expect: "b: ⟪True⟫\ny: ⸨1⸩\nz: 2" }
   , { file: "dependence/match_fallthrough.fld", doc: false, δv: \_ -> select, expect: "v: ⟪Bar()⟫\nw: ⸨5⸩" }
   , { file: "dependence/early_return.fld", doc: false, δv: \_ -> select, expect: "a: 1\nb: ⸨2⸩\nc: ⟪False⟫" }
   , { file: "dependence/attribute.fld", doc: false, δv: \_ -> select, expect: "p: ⟪P(⸨1⸩, 2)⟫" }
   , { file: "dependence/subscript.fld", doc: false, δv: \_ -> select, expect: "i: ⟪1⟫\nxs: ⟪[3, ⸨4⸩, 5]⟫" }
   , { file: "dependence/filter.fld", doc: false, δv: \_ -> select, expect: "n: ⟪5⟫\nxs: ⟪[⸨8⸩, ⟪4⟫, ⸨7⸩, ⟪3⟫]⟫" }
   , { file: "dependence/closure.fld", doc: false, δv: \_ -> select, expect: "a: ⸨1⸩\nb: ⸨2⸩" }
   , { file: "dependence/partial.fld", doc: false, δv: \_ -> select, expect: "a: ⸨1⸩\nb: ⸨2⸩" }
   , { file: "dependence/len.fld", doc: false, δv: \_ -> select, expect: "len: ⟪len⟫\nxs: ⸨[1, 2]⸩" }
   , { file: "dependence/dict_lookup.fld", doc: false, δv: \_ -> select, expect: "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫" }
   , { file: "dependence/dict_pattern.fld", doc: false, δv: \_ -> select, expect: "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫" }
   , { file: "dependence/seq.fld", doc: false, δv: \arg -> arg cPair f_snd select, expect: "a: 1\nb: 2\nc: ⟪True⟫\nd: ⸨4⸩" }
   , { file: "dependence/doc_this.fld"
     , doc: true
     , δv: \_ -> select
     , expect: "x: ⸨1⸩\ny: ⸨2⸩\n@doc(⸨Paragraph(⸨[⸨\"Sum\"⸩, ⸨\"is\"⸩, ⸨3⸩]⸩)⸩) ⸨3⸩"
     }
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
     }
   ]
