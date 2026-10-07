module Test.Specs.Dependence where

import Prelude

import App.Util.Selector (dict, dictKey, dictVal, listElement, list, matrixElement, select, tupleElement, select', (>.>))
import DataType (cParagraph, f_fragments)
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
          [ Bwd Output (const (tupleElement 1 select)) "1\n2\n⟪True⟫\n⸨4⸩\n(1, ⸨4⸩)"
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
   , { file: "dependence/matrix/matmul.fld"
     , queries:
          [ Bwd Output (const (tupleElement 0 (matrixElement 0 0 select)))
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
   , { file: "dependence/add.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨5⸩\n⸨0⸩\n⸨3⸩\n⸨8⸩"
          ]
     }
   , { file: "dependence/divide.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨362⸩\n⸨9⸩\n⸨40.22222222222222⸩"
          ]
     }
   , { file: "dependence/multiply.fld"
     , queries:
          [ Bwd Output (\_ -> select) "5\n⸨0⸩\n3\n⸨0⸩"
          ]
     }
   , { file: "dependence/nth.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪[3, ⸨4⸩, 5]⟫\n⸨4⸩"
          ]
     }
   , { file: "dependence/length.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨[1, 2, 3, 4, 5]⸩\n⸨5⸩"
          ]
     }
   , { file: "dependence/output_not_source.fld"
     , queries:
          [ Bwd Output (const (tupleElement 1 select)) "⸨3⸩\n⸨5⸩\n(3, ⸨True⸩)"
          ]
     }
   , { file: "dependence/array/lookup.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪[[1, 4, 8], [3, 2, 17], ⟪[0, ⸨14⸩, 6]⟫]⟫\n⸨14⸩"
          ]
     }
   , { file: "dependence/array/dims.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨3⸩\n⸨3⸩\n⸨(⸨3⸩, ⸨3⸩)⸩"
          ]
     }
   , { file: "dependence/filter_lambda.fld"
     , queries:
          [ Bwd Output (\_ -> list select') "⟪5⟫\n⟪[⟪8⟫, ⟪4⟫, ⟪7⟫, ⟪3⟫]⟫\n⸨[8, 7]⸩"
          ]
     }
   , { file: "dependence/list_comp.fld"
     , queries:
          [ Bwd Output (\_ -> list select')
               """
               ⟪[⟪{"country": "China", ⟪"energyType"⟫: ⟪"Bio"⟫, "output": 6.2, "year": 2013}⟫, ⟪{
                 "country": "China",
                 ⟪"energyType"⟫: ⟪"Hydro"⟫,
                 "output": 260,
                 "year": 2013
               }⟫, ⟪{
                 "country": "China",
                 ⟪"energyType"⟫: ⟪"Solar"⟫,
                 "output": 19.9,
                 "year": 2013
               }⟫, ⟪{"country": "China", ⟪"energyType"⟫: ⟪"Wind"⟫, "output": 91, "year": 2013}⟫]⟫
               ⟪[⟪"Bio"⟫, ⟪"Hydro"⟫, ⟪"Solar"⟫, ⟪"Wind"⟫]⟫
               ⸨[6.2, 260, 19.9, 91]⸩
               """
          ]
     }
   , { file: "dependence/map.fld"
     , queries:
          [ Bwd Output (\_ -> list select') "⟪[3, 4]⟫\n⸨[5, 6]⸩"
          ]
     }
   , { file: "dependence/intersperse.fld"
     , queries:
          [ Bwd Output (\_ -> list select') "⟪[1, 2, 3]⟫\n0\n⸨[1, 0, 2, 0, 3]⸩"
          ]
     }
   , { file: "dependence/zeros.fld"
     , queries:
          [ Bwd Output (\_ -> list select') "⟪[1, 2]⟫\n⸨[0, 0]⸩"
          ]
     }
   , { file: "dependence/zip_with.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 1 select') "⟪[2, ⸨3⸩, 4]⟫\n⟪[3, ⸨4⸩, 5, 6]⟫\n[13, ⸨25⸩, 41]"
          ]
     }
   , { file: "dependence/section_5_example.fld"
     , queries:
          [ Bwd Output (\_ -> list select')
               """
               ⟪[⟪{⟪"energyType"⟫: ⟪"Bio"⟫, "output": 6.2}⟫, ⟪{
                 ⟪"energyType"⟫: ⟪"Hydro"⟫,
                 "output": 260
               }⟫, ⟪{⟪"energyType"⟫: ⟪"Solar"⟫, "output": 19.9}⟫, ⟪{
                 ⟪"energyType"⟫: ⟪"Wind"⟫,
                 "output": 91
               }⟫, ⟪{⟪"energyType"⟫: ⟪"Geo"⟫, "output": 14.4}⟫]⟫
               ⟪[⟪"Hydro"⟫, ⟪"Solar"⟫, ⟪"Geo"⟫]⟫
               ⸨[88, 6, 4]⸩
               """
          ]
     }
   , { file: "dependence/section_5_example.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 1 select)
               """
               ⟪[⟪{⟪"energyType"⟫: ⟪"Bio"⟫, "output": 6.2}⟫, ⟪{
                 ⟪"energyType"⟫: ⟪"Hydro"⟫,
                 ⟪"output"⟫: ⸨260⸩
               }⟫, ⟪{⟪"energyType"⟫: ⟪"Solar"⟫, ⟪"output"⟫: ⸨19.9⸩}⟫, ⟪{
                 ⟪"energyType"⟫: ⟪"Wind"⟫,
                 "output": 91
               }⟫, ⟪{⟪"energyType"⟫: ⟪"Geo"⟫, ⟪"output"⟫: ⸨14.4⸩}⟫]⟫
               ⟪[⟪"Hydro"⟫, ⟪"Solar"⟫, ⟪"Geo"⟫]⟫
               [88, ⸨6⸩, 4]
               """
          ]
     }
   , { file: "dependence/dict/get.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪{\"a\": 5, ⟪\"ab\"⟫: ⟪{\"fst\": 6, ⟪\"snd\"⟫: ⸨0⸩}⟫}⟫\n⟪\"a\"⟫\n⸨0⸩"
          ]
     }
   , { file: "dependence/dict/create.fld"
     , queries:
          [ Bwd Output (\_ -> dictKey "ab" select') "\"a\"\n⸨\"a\"⸩\n⸨\"b\"⸩\n{\"a\": 5, ⸨\"ab\"⸩: 6}"
          ]
     }
   , { file: "dependence/dict/difference.fld"
     , queries:
          [ Bwd Output (\_ -> dict select') "⸨{\"a\": 5, \"ab\": 6}⸩\n⸨{\"ab\": 12}⸩\n⸨{\"a\": 5}⸩"
          ]
     }
   , { file: "dependence/dict/disjoint_union.fld"
     , queries:
          [ Bwd Output (\_ -> dictKey "a" select' >.> dictVal "c" select) "{⸨\"a\"⸩: 5, \"b\": 6}\n{\"c\": ⸨7⸩}\n{⸨\"a\"⸩: 5, \"b\": 6, \"c\": ⸨7⸩}"
          ]
     }
   , { file: "dependence/dict/foldl_with_index.fld"
     , queries:
          [ Bwd Output (\_ -> select) "{\"a\": ⟪[5, 6]⟫, \"b\": ⟪[⸨0⸩, 10]⟫, \"c\": ⟪[3, 4]⟫}\n⸨0⸩"
          ]
     }
   , { file: "dependence/dict/intersection_with.fld"
     , queries:
          [ Bwd Output (\_ -> dictVal "b" select >.> dictVal "c" select) "{\"a\": 5, \"b\": ⸨6⸩, \"c\": ⸨3⸩}\n{\"b\": ⸨-6⸩, \"c\": ⸨7⸩}\n{\"b\": ⸨0⸩, \"c\": ⸨20⸩}"
          ]
     }
   , { file: "dependence/dict/map.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⟪{⟪\"a\"⟫: ⟪[⸨5⸩, 6]⟫, ⟪\"b\"⟫: ⟪[⸨9⸩, 10]⟫, \"c\": [3, 4]}⟫\n⟪{\"c\": []}⟫\n⸨20⸩"
          ]
     }
   , { file: "dependence/dict/match.fld"
     , queries:
          [ Bwd Output (\_ -> select) "⸨2⸩\n⸨{⸨\"a\"⸩: ⸨2⸩}⸩"
          ]
     }
   , { file: "dependence/matrix_update.fld"
     , queries:
          [ Bwd Output (\_ -> matrixElement 1 1 select)
               """
               ⸨4000⸩
               15, 13, 6, 9, 16,
               12, ⸨4000⸩, 15, 4, 13,
               14, 9, 20, 8, 1,
               4, 10, 3, 7, 19,
               3, 11, 15, 2, 9
               """
          ]
     }
   , { file: "dependence/convolution/edge_detect.fld"
     , queries:
          [ Bwd Output (\_ -> matrixElement 0 0 select)
               """
               ⟪⸨0⸩, ⸨1⸩, ⸨0⸩,
               ⸨1⸩, ⸨-4⸩, ⸨1⸩,
               ⸨0⸩, ⸨1⸩, ⸨0⸩⟫
               ⟪⸨15⸩, ⸨13⸩, 6, 9, 16,
               ⸨12⸩, 5, 15, 4, 13,
               14, 9, 20, 8, 1,
               4, 10, 3, 7, 19,
               3, 11, 15, 2, 9⟫
               ⸨0⸩, -1, 2, 0, -1,
               0, 3, -2, 3, -2,
               -1, 1, -5, 0, 4,
               1, -1, 4, 0, -4,
               1, 0, -3, 2, 0
               """
          ]
     }
   , { file: "dependence/convolution/emboss.fld"
     , queries:
          [ Bwd Output (\_ -> matrixElement 0 0 select)
               """
               ⟪-2, -1, 0,
               -1, ⸨1⸩, ⸨1⸩,
               0, ⸨1⸩, ⸨2⸩⟫
               ⟪⸨15⸩, ⸨13⸩, 6, 9, 16,
               ⸨12⸩, ⸨5⸩, 15, 4, 13,
               14, 9, 20, 8, 1,
               4, 10, 3, 7, 19,
               3, 11, 15, 2, 9⟫
               ⸨5⸩, 4, 2, 5, 2,
               3, 1, 2, -1, -2,
               3, 0, 1, 0, -1,
               2, 1, -2, 0, 0,
               1, 0, -1, -1, -2
               """
          ]
     }
   , { file: "dependence/convolution/gaussian.fld"
     , queries:
          [ Bwd Output (\_ -> matrixElement 0 0 select)
               """
               ⟪1, 4, 1,
               4, ⸨16⸩, ⸨4⸩,
               1, ⸨4⸩, ⸨1⸩⟫
               ⟪⸨15⸩, ⸨13⸩, 6, 9, 16,
               ⸨12⸩, ⸨5⸩, 15, 4, 13,
               14, 9, 20, 8, 1,
               4, 10, 3, 7, 19,
               3, 11, 15, 2, 9⟫
               ⸨38⸩, 37, 28, 30, 38,
               38, 36, 46, 31, 34,
               37, 41, 54, 34, 20,
               21, 35, 31, 31, 42,
               13, 32, 35, 19, 26
               """
          ]
     }
   , { file: "dependence/dtw/compute_dtw.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 1 select)
               """
               ⟪[⟪3⟫, ⟪1⟫, ⟪2⟫, ⟪2⟫, ⟪1⟫]⟫
               ⟪[⟪2⟫, ⟪0⟫, ⟪0⟫, ⟪3⟫, ⟪3⟫, ⟪1⟫, 0]⟫
               ⟪2⟫
               [(0, 0), ⸨(⸨1⸩, ⸨1⸩)⸩, (1, 2), (2, 3), (3, 4), (4, 5), (4, 6)]
               """
          ]
     }
   , { file: "dependence/dtw/average_series.fld"
     , queries:
          [ Bwd Output (\_ -> listElement 2 select)
               """
               ⟪[⟪3⟫, ⸨1⸩, ⟪2⟫, ⟪2⟫, ⟪1⟫]⟫
               ⟪[⟪2⟫, ⟪0⟫, ⸨0⸩, ⟪3⟫, ⟪3⟫, ⟪1⟫, 0]⟫
               ⟪2⟫
               [2.5, 0.5, ⸨0.5⸩, 2.5, 2.5, 1.0, 0.5]
               """
          ]
     }
   , { file: "dependence/lookup.fld"
     , queries:
          [ Bwd Output (\_ -> select')
               """
               ⟪6⟫
               ⟪NonEmpty(NonEmpty(Empty(), (3, "USA"), Empty()), ⟪(⟪4⟫, "China")⟫, ⟪NonEmpty(⟪NonEmpty(Empty(), ⟪(⟪6⟫, ⸨"Germany"⸩)⟫, Empty())⟫, ⟪(⟪7⟫, "UK")⟫, Empty())⟫)⟫
               ⸨"Germany"⸩
               """
          ]
     }
   ]
