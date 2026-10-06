module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (listElement, matrixElement, select)
import DataType (cPair, cParagraph, f_fragments, f_fst, f_snd)
import Test.Util (DepSpec, Query(..), VertexSpec(..))

dep_cases :: Array DepSpec
dep_cases =
   [ { file: "dependence/var.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 0 select) "[⸨1⸩, 2]\n[⸨1⸩, 2]"
          , Fwd (Input "x") (\_ -> listElement 1 select) "[1, ⸨2⸩]\n[1, ⸨2⸩]"
          ]
     }
   , { file: "dependence/cond.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪True⟫\n⸨1⸩\n2\n⸨1⸩"
          , Fwd (Input "b") (\_ -> select) "⸨True⸩\n1\n2\n⟪1⟫"
          , Fwd (Input "y") (\_ -> select) "True\n⸨1⸩\n2\n⸨1⸩"
          ]
     }
   , { file: "dependence/match_fallthrough.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪Bar()⟫\n⸨5⸩\n⸨5⸩"
          ]
     }
   , { file: "dependence/early_return.fld"
     , queries:
          [ Bwd Output (\_ -> select) "1\n⸨2⸩\n⟪False⟫\n⸨2⸩"
          , Fwd (Input "c") (\_ -> select) "1\n2\n⸨False⸩\n⟪2⟫"
          ]
     }
   , { file: "dependence/attribute.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪P(⸨1⸩, 2)⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/subscript.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪1⟫\n⟪[3, ⸨4⸩, 5]⟫\n⸨4⸩"
          ]
     }
   , { file: "dependence/filter.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 0 select) "⟪5⟫\n⟪[⸨8⸩, 4, 7, 3]⟫\n[⸨8⸩, 7]"
          , Fwd (Input "n") (\_ -> select) "⸨5⸩\n[8, 4, 7, 3]\n⟪[⟪8⟫, ⟪7⟫]⟫"
          , Fwd (Input "xs") (\_ -> listElement 2 select) "5\n[8, 4, ⸨7⸩, 3]\n⟪[8, ⸨7⸩]⟫"
          ]
     }
   , { file: "dependence/closure.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨1⸩\n⸨2⸩\n⸨3⸩"
          ]
     }
   , { file: "dependence/partial.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨1⸩\n⸨2⸩\n⸨3⸩"
          ]
     }
   , { file: "dependence/len.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨[1, 2]⸩\n⸨2⸩"
          ]
     }
   , { file: "dependence/dict_lookup.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/dict_pattern.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪{⟪\"a\"⟫: ⸨1⸩, \"b\": 2}⟫\n⸨1⸩"
          ]
     }
   , { file: "dependence/seq.fld"
     , queries:
          [ Bwd Output (\arg -> arg cPair f_snd select) "1\n2\n⟪True⟫\n⸨4⸩\n(1, ⸨4⸩)"
          , Fwd (Input "c") (\_ -> select) "1\n2\n⸨True⸩\n4\n⟪(⟪1⟫, ⟪4⟫)⟫"
          ]
     }
   , { file: "dependence/doc_this.fld"
     , queries:
          [ Bwd (Doc Output) (\arg -> arg cParagraph f_fragments (listElement 2 select))
               "⸨1⸩\n⸨2⸩\n@doc(Paragraph([\"Sum\", \"is\", ⸨3⸩])) ⸨3⸩"
          , Fwd (Input "x") (\_ -> select) "⸨1⸩\n2\n@doc(Paragraph([\"Sum\", \"is\", ⸨3⸩])) ⸨3⸩"
          ]
     }
   , { file: "slicing/matrix/matmul.fld"
     , queries:
          [ Bwd Output (\arg -> arg cPair f_fst $ matrixElement 0 0 select)
               """
               ⟪⸨1⸩, ⸨2⸩, ⸨3⸩,
               4, 5, 6⟫
               ⟪⸨1⸩, 2,
               ⸨3⸩, 4,
               ⸨5⸩, 6⟫
               ⸨22⸩, 28,
               49, 64
               9, 12, 15,
               19, 26, 33,
               29, 40, 51
               (⸨22⸩, 28,
               49, 64, 9, 12, 15,
               19, 26, 33,
               29, 40, 51)
               """
          , Bwd (Intermediate 0) (\_ -> matrixElement 0 0 select)
               """
               ⟪⸨1⸩, ⸨2⸩, ⸨3⸩,
               4, 5, 6⟫
               ⟪⸨1⸩, 2,
               ⸨3⸩, 4,
               ⸨5⸩, 6⟫
               ⸨22⸩, 28,
               49, 64
               9, 12, 15,
               19, 26, 33,
               29, 40, 51
               (22, 28,
               49, 64, 9, 12, 15,
               19, 26, 33,
               29, 40, 51)
               """
          , Fwd (Intermediate 0) (\_ -> matrixElement 0 0 select)
               """
               1, 2, 3,
               4, 5, 6
               1, 2,
               3, 4,
               5, 6
               ⸨22⸩, 28,
               49, 64
               9, 12, 15,
               19, 26, 33,
               29, 40, 51
               (⸨22⸩, 28,
               49, 64, 9, 12, 15,
               19, 26, 33,
               29, 40, 51)
               """
          , Fwd (Input "leftMatrix") (\_ -> matrixElement 0 0 select)
               """
               ⸨1⸩, 2, 3,
               4, 5, 6
               1, 2,
               3, 4,
               5, 6
               ⸨22⸩, ⸨28⸩,
               49, 64
               ⸨9⸩, 12, 15,
               ⸨19⸩, 26, 33,
               ⸨29⸩, 40, 51
               (⸨22⸩, ⸨28⸩,
               49, 64, ⸨9⸩, 12, 15,
               ⸨19⸩, 26, 33,
               ⸨29⸩, 40, 51)
               """
          ]
     }
   ]
