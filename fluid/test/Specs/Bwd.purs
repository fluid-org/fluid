module Test.Specs.Bwd where

import Prelude

import App.Util.Selector (barSegment, dict, dictKey, dictVal, envVal, list, listElement, matrix, matrixElement, none, select, select', topα, (>.>))
import DataType (cBarChart, cMultiView, cNonEmpty, cPair, f_fst, f_left, f_right, f_snd, f_stackedBars, f_value, f_views)
import Test.Util.Suite (TestBwdSpec)

bwd_cases :: Array TestBwdSpec
bwd_cases =
   [ { file: "add.fld"
     , bwd_expect: \_ -> envVal "a" select >.> envVal "b" select >.> envVal "c" select
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "divide.fld"
     , bwd_expect: \_ -> envVal "a" select >.> envVal "b" select
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "multiply.fld"
     , bwd_expect: \_ -> envVal "b" select
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "nth.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 1 select)
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "length.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "output_not_source.fld"
     , bwd_expect: \_ -> envVal "x" select >.> envVal "n" select
     , δv: \arg -> arg cPair f_snd select
     , inputs: []
     }
   , { file: "array/lookup.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 2 (listElement 1 select))
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "array/dims.fld"
     , bwd_expect: \_ -> envVal "x" select >.> envVal "y" select
     , δv: \_ -> select
     , inputs: [ "x", "y" ]
     }
   , { file: "filter.fld"
     , bwd_expect: \_ -> envVal "n" select >.> envVal "xs" (list select' >.> listElement 0 select >.> listElement 2 select)
     , δv: \_ -> list select'
     , inputs: [ "n", "xs" ]
     }
   , { file: "list_comp.fld"
     , bwd_expect: \_ -> envVal "data" (list select' >.> listElement 0 (dictVal "energyType" select) >.> listElement 1 (dictVal "energyType" select) >.> listElement 2 (dictVal "energyType" select) >.> listElement 3 (dictVal "energyType" select)) >.> envVal "types" select
     , δv: \_ -> list select'
     , inputs: [ "data", "types" ]
     }
   , { file: "map.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     }
   , { file: "intersperse.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     }
   , { file: "zeros.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     }
   , { file: "zip_with.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 1 select) >.> envVal "ys" (listElement 1 select)
     , δv: \_ -> listElement 1 select'
     , inputs: []
     }
   , { file: "section_5_example.fld"
     , bwd_expect: \_ -> envVal "types" select >.> envVal "data" (list select' >.> listElement 1 (dictVal "energyType" select) >.> listElement 2 (dictVal "energyType" select) >.> listElement 4 (dictVal "energyType" select))
     , δv: \_ -> list select'
     , inputs: [ "types", "data" ]
     }
   , { file: "section_5_example.fld"
     , bwd_expect: \_ -> envVal "data" (listElement 1 (dictVal "output" select) >.> listElement 2 (dictVal "output" select) >.> listElement 4 (dictVal "output" select))
     , δv: \_ -> listElement 1 select
     , inputs: [ "types", "data" ]
     }
   , { file: "dict/get.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "ab" (dictVal "snd" select))
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "dict/create.fld"
     , bwd_expect: \_ -> envVal "a_2" select >.> envVal "b" select
     , δv: \_ -> dictKey "ab" select'
     , inputs: []
     }
   , { file: "dict/difference.fld"
     , bwd_expect: \_ -> envVal "e" (dict select') >.> envVal "f" (dict select')
     , δv: \_ -> dict select'
     , inputs: []
     }
   , { file: "dict/disjoint_union.fld"
     , bwd_expect: \_ -> envVal "d1" (dictKey "a" select') >.> envVal "d2" (dictVal "c" select)
     , δv: \_ -> dictKey "a" select' >.> dictVal "c" select
     , inputs: []
     }
   , { file: "dict/foldl_with_index.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "b" (listElement 0 select))
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "dict/intersection_with.fld"
     , bwd_expect: \_ -> envVal "d1" (dictVal "b" select >.> dictVal "c" select) >.> envVal "d2" (dictVal "b" select >.> dictVal "c" select)
     , δv: \_ -> dictVal "b" select >.> dictVal "c" select
     , inputs: []
     }
   , { file: "dict/map.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "a" (listElement 0 select) >.> dictVal "b" (listElement 0 select))
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "dict/match.fld"
     , bwd_expect: \_ -> envVal "n" select
     , δv: \_ -> select
     , inputs: []
     }
   , { file: "matrix_update.fld"
     , bwd_expect: \_ -> envVal "pair" select
     , δv: \_ -> matrixElement 1 1 select
     , inputs: []
     }
   , { file: "convolution/edge_detect.fld"
     , bwd_expect:
          \_ ->
             envVal "filter"
                ( matrixElement 0 0 select >.> matrixElement 0 1 select >.> matrixElement 0 2 select
                     >.> matrixElement 1 0 select
                     >.> matrixElement 1 1 select
                     >.> matrixElement 1 2 select
                     >.> matrixElement 2 0 select
                     >.> matrixElement 2 1 select
                     >.> matrixElement 2 2 select
                )
                >.> envVal "inputImage"
                   (matrixElement 0 0 select >.> matrixElement 0 1 select >.> matrixElement 1 0 select)
     , δv: \_ -> matrixElement 0 0 select
     , inputs: [ "inputImage" ]
     }
   , { file: "convolution/emboss.fld"
     , bwd_expect:
          \_ -> envVal "convolve" (topα select')
             >.> envVal "filter"
                ( matrix select' >.> matrixElement 1 1 select >.> matrixElement 1 2 select
                     >.> matrixElement 2 1 select
                     >.> matrixElement 2 2 select
                )
             >.> envVal "inputImage"
                ( matrix select' >.> matrixElement 0 0 select >.> matrixElement 0 1 select
                     >.> matrixElement 1 0 select
                     >.> matrixElement 1 1 select
                )
     , δv: \_ -> matrixElement 0 0 select
     , inputs: [ "inputImage" ]
     }
   , { file: "convolution/gaussian.fld"
     , bwd_expect:
          \_ -> envVal "convolve" (topα select')
             >.> envVal "filter"
                ( matrix select' >.> matrixElement 1 1 select >.> matrixElement 1 2 select
                     >.> matrixElement 2 1 select
                     >.> matrixElement 2 2 select
                )
             >.> envVal "inputImage"
                ( matrix select' >.> matrixElement 0 0 select >.> matrixElement 0 1 select
                     >.> matrixElement 1 0 select
                     >.> matrixElement 1 1 select
                )
     , δv: \_ -> matrixElement 0 0 select
     , inputs: [ "inputImage" ]
     }
   , { file: "matrix/matmul.fld"
     , bwd_expect:
          \_ ->
             envVal "leftMatrix"
                (matrixElement 0 0 select >.> matrixElement 0 1 select >.> matrixElement 0 2 select)
                >.> envVal "rightMatrix"
                   (matrixElement 0 0 select >.> matrixElement 1 0 select >.> matrixElement 2 0 select)
     , δv: \arg -> arg cPair f_fst $ matrixElement 0 0 select
     , inputs: [ "leftMatrix", "rightMatrix" ]
     }
   , { file: "dtw/compute_dtw.fld"
     , bwd_expect:
          \_ ->
             envVal "seq1"
                ( listElement 0 select >.> listElement 1 select
                     >.> list select'
                )
                >.> envVal "seq2"
                   ( listElement 0 select >.> listElement 1 select >.> listElement 2 select
                        >.> list select'
                   )
                >.> envVal "window" select
     , δv: \_ -> listElement 1 select
     , inputs: [ "seq1", "seq2" ]
     }
   , { file: "dtw/average_series.fld"
     , bwd_expect:
          \_ -> envVal "seq1" (listElement 1 select)
             >.> envVal "seq2" (listElement 2 select)
     , δv: \_ -> listElement 2 select
     , inputs: [ "seq1", "seq2" ]
     }
   , { file: "lookup.fld"
     , bwd_expect:
          \arg -> envVal "tree"
             (arg cNonEmpty f_right (arg cNonEmpty f_left (arg cNonEmpty f_value (arg cPair f_snd select'))))
     , δv: \_ -> select'
     , inputs: []
     }
   , { file: "linked_outputs/bar_chart_line_chart.fld"
     , bwd_expect:
          \_ -> envVal "renewables"
             ( listElement 28 (dictVal "output" select)
                  >.> listElement 29 (dictVal "output" select)
                  >.> listElement 30 (dictVal "output" select)
                  >.> listElement 31 (dictVal "output" select)
             )
     , δv: \arg -> arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 1 0 select)))
     , inputs: [ "renewables" ]
     }
   , { file: "linked_outputs/stacked_bar_scatter_plot.fld"
     , bwd_expect:
          \_ -> envVal "nonRenewables"
             ( listElement 45 (dictVal "nuclearOut" select >.> dictVal "gasOut" select >.> dictVal "coalOut" select >.> dictVal "petrolOut" select)
                  >.> listElement 54 (dictVal "nuclearOut" select >.> dictVal "gasOut" select >.> dictVal "coalOut" select >.> dictVal "petrolOut" select)
                  >.> listElement 56 (dictVal "nuclearOut" select >.> dictVal "gasOut" select >.> dictVal "coalOut" select >.> dictVal "petrolOut" select)
             )
     , δv: \arg -> arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 3 2 select >.> barSegment arg 4 1 select >.> barSegment arg 4 3 select)))
     , inputs: [ "nonRenewables" ]
     }
   , { file: "qcut.fld"
     , bwd_expect: \_ -> none
     , δv: \_ -> none
     , inputs: []
     }
   ]
