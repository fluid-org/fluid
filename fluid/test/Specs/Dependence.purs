module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (listElement, matrixElement, select)
import DataType (cPair, cParagraph, f_fragments, f_fst, f_snd)
import Test.Util (DepSpec, Query(..), Visible(..))

dep_cases :: Array DepSpec
dep_cases =
   [ { file: "dependence/var.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 0 select) "x: [⸨1⸩, 2]\n[⸨1⸩, 2]"
          , Fwd (Input "x") (\_ -> listElement 1 select) "x: [1, ⸨2⸩]\n[1, ⸨2⸩]"
          ]
     }
   , { file: "dependence/cond.fld"
     , queries:
          [ Bwd Output (\_ -> select) "b: ⟪True⟫\ny: ⸨1⸩\nz: 2\n⸨1⸩"
          , Fwd (Input "b") (\_ -> select) "b: ⸨True⸩\ny: 1\nz: 2\n⟪1⟫"
          , Fwd (Input "y") (\_ -> select) "b: True\ny: ⸨1⸩\nz: 2\n⸨1⸩"
          ]
     }
   , { file: "dependence/match_fallthrough.fld"
     , queries:
          [ Bwd Output (\_ -> select) "v: ⟪Bar()⟫\nw: ⸨5⸩\n⸨5⸩"
          ]
     }
   , { file: "dependence/early_return.fld"
     , queries:
          [ Bwd Output (\_ -> select) "a: 1\nb: ⸨2⸩\nc: ⟪False⟫\n⸨2⸩"
          , Fwd (Input "c") (\_ -> select) "a: 1\nb: 2\nc: ⸨False⸩\n⟪2⟫"
          ]
     }
   , { file: "dependence/attribute.fld"
     , queries:
          [ Bwd Output (\_ -> select) "p: ⟪P(⸨1⸩, 2)⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/subscript.fld"
     , queries:
          [ Bwd Output (\_ -> select) "i: ⟪1⟫\nxs: ⟪[3, ⸨4⸩, 5]⟫\n⸨4⸩"
          ]
     }
   , { file: "dependence/filter.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 0 select) "n: ⟪5⟫\nxs: ⟪[⸨8⸩, 4, 7, 3]⟫\n[⸨8⸩, 7]"
          , Fwd (Input "n") (\_ -> select) "n: ⸨5⸩\nxs: [8, 4, 7, 3]\n⟪[⟪8⟫, ⟪7⟫]⟫"
          , Fwd (Input "xs") (\_ -> listElement 2 select) "n: 5\nxs: [8, 4, ⸨7⸩, 3]\n⟪[8, ⸨7⸩]⟫"
          ]
     }
   , { file: "dependence/closure.fld"
     , queries:
          [ Bwd Output (\_ -> select) "a: ⸨1⸩\nb: ⸨2⸩\n⸨3⸩"
          ]
     }
   , { file: "dependence/partial.fld"
     , queries:
          [ Bwd Output (\_ -> select) "a: ⸨1⸩\nb: ⸨2⸩\n⸨3⸩"
          ]
     }
   , { file: "dependence/len.fld"
     , queries:
          [ Bwd Output (\_ -> select) "len: ⟪len⟫\nxs: ⸨[1, 2]⸩\n⸨2⸩"
          ]
     }
   , { file: "dependence/dict_lookup.fld"
     , queries:
          [ Bwd Output (\_ -> select) "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/dict_pattern.fld"
     , queries:
          [ Bwd Output (\_ -> select) "d: ⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/seq.fld"
     , queries:
          [ Bwd Output (\arg -> arg cPair f_snd select) "a: 1\nb: 2\nc: ⟪True⟫\nd: ⸨4⸩\n(1, ⸨4⸩)"
          , Fwd (Input "c") (\_ -> select) "a: 1\nb: 2\nc: ⸨True⸩\nd: 4\n⟪(⟪1⟫, ⟪4⟫)⟫"
          ]
     }
   , { file: "dependence/doc_this.fld"
     , queries:
          [ Bwd OutputDoc (\arg -> arg cParagraph f_fragments (listElement 2 select))
               "x: ⸨1⸩\ny: ⸨2⸩\n@doc(Paragraph([\"Sum\", \"is\", ⸨3⸩])) ⸨3⸩"
          , Fwd (Input "x") (\_ -> select) "x: ⸨1⸩\ny: 2\n@doc(Paragraph([\"Sum\", \"is\", ⸨3⸩])) ⸨3⸩"
          ]
     }
   , { file: "slicing/matrix/matmul.fld"
     , queries:
          [ Bwd Output (\arg -> arg cPair f_fst $ matrixElement 0 0 select)
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
          , Bwd (Intermediate 0) (\_ -> matrixElement 0 0 select)
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
          , Fwd (Intermediate 0) (\_ -> matrixElement 0 0 select)
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
          , Fwd (Input "leftMatrix") (\_ -> matrixElement 0 0 select)
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
          ]
     }
   ]
