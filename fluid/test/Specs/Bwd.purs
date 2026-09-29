module Test.Specs.Bwd where

import Prelude

import App.Util (SelectionType(..))
import App.Util.Selector (barSegment, dict, dictKey, dictVal, envVal, list, listElement, matrix, matrixElement, select, select', topα, (>.>))
import DataType (cBarChart, cMultiView, cNonEmpty, cPair, f_fst, f_left, f_right, f_snd, f_stackedBars, f_value, f_views)
import Test.Util.Suite (TestBwdSpec)
import Util ((×))

bwd_cases :: Array TestBwdSpec
bwd_cases =
   [ { file: "add.fld"
     , bwd_expect: \_ -> envVal "a" select >.> envVal "b" select >.> envVal "c" select
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨8⸩"
     }
   , { file: "divide.fld"
     , bwd_expect: \_ -> envVal "a" select >.> envVal "b" select
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨40.22222222222222⸩"
     }
   , { file: "multiply.fld"
     , bwd_expect: \_ -> envVal "b" select
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨0⸩"
     }
   , { file: "nth.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 1 select)
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨4⸩"
     }
   , { file: "length.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨5⸩"
     }
   , { file: "output_not_source.fld"
     , bwd_expect: \_ -> envVal "x" select >.> envVal "n" select
     , δv: \arg -> arg cPair f_snd select
     , inputs: []
     , fwd_expect: "(⸨3⸩, ⸨True⸩)"
     }
   , { file: "array/lookup.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 2 (listElement 1 select))
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨14⸩"
     }
   , { file: "array/dims.fld"
     , bwd_expect: \_ -> envVal "x" select >.> envVal "y" select
     , δv: \_ -> select
     , inputs: [ "x", "y" ]
     , fwd_expect: "(⸨3⸩, ⸨3⸩)"
     }
   , { file: "filter.fld"
     , bwd_expect: \_ -> envVal "n" select >.> envVal "xs" (list select' >.> listElement 0 select >.> listElement 2 select)
     , δv: \_ -> list select'
     , inputs: [ "n", "xs" ]
     , fwd_expect: "⸨[⸨8⸩, ⸨7⸩]⸩"
     }
   , { file: "list_comp.fld"
     , bwd_expect: \_ -> envVal "data" (list select' >.> listElement 0 (dictVal "energyType" select) >.> listElement 1 (dictVal "energyType" select) >.> listElement 2 (dictVal "energyType" select) >.> listElement 3 (dictVal "energyType" select)) >.> envVal "types" select
     , δv: \_ -> list select'
     , inputs: [ "data", "types" ]
     , fwd_expect: "⸨[6.2, 260, 19.9, 91]⸩"
     }
   , { file: "map.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     , fwd_expect: "⸨[5, 6]⸩"
     }
   , { file: "intersperse.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     , fwd_expect: "⸨[1, 0, 2, 0, 3]⸩"
     }
   , { file: "zeros.fld"
     , bwd_expect: \_ -> envVal "xs" (list select')
     , δv: \_ -> list select'
     , inputs: [ "xs" ]
     , fwd_expect: "⸨[⸨0⸩, ⸨0⸩]⸩"
     }
   , { file: "zip_with.fld"
     , bwd_expect: \_ -> envVal "xs" (listElement 1 select) >.> envVal "ys" (listElement 1 select)
     , δv: \_ -> listElement 1 select'
     , inputs: []
     , fwd_expect: "[13, ⸨25⸩, 41]"
     }
   , { file: "section_5_example.fld"
     , bwd_expect: \_ -> envVal "types" select >.> envVal "data" (list select' >.> listElement 1 (dictVal "energyType" select) >.> listElement 2 (dictVal "energyType" select) >.> listElement 4 (dictVal "energyType" select))
     , δv: \_ -> list select'
     , inputs: [ "types", "data" ]
     , fwd_expect: "⸨[88, 6, 4]⸩"
     }
   , { file: "section_5_example.fld"
     , bwd_expect: \_ -> envVal "data" (listElement 1 (dictVal "output" select) >.> listElement 2 (dictVal "output" select) >.> listElement 4 (dictVal "output" select))
     , δv: \_ -> listElement 1 select
     , inputs: [ "types", "data" ]
     , fwd_expect: "[⸨88⸩, ⸨6⸩, ⸨4⸩]"
     }
   , { file: "dict/get.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "ab" (dictVal "snd" select))
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨0⸩"
     }
   , { file: "dict/create.fld"
     , bwd_expect: \_ -> envVal "a_2" select >.> envVal "b" select
     , δv: \_ -> dictKey "ab" select'
     , inputs: []
     , fwd_expect: "{ a: 5, ⸨ab⸩: 6 }"
     }
   , { file: "dict/difference.fld"
     , bwd_expect: \_ -> envVal "e" (dict select') >.> envVal "f" (dict select')
     , δv: \_ -> dict select'
     , inputs: []
     , fwd_expect: "⸨{ a: 5 }⸩"
     }
   , { file: "dict/disjoint_union.fld"
     , bwd_expect: \_ -> envVal "d1" (dictKey "a" select') >.> envVal "d2" (dictVal "c" select)
     , δv: \_ -> dictKey "a" select' >.> dictVal "c" select
     , inputs: []
     , fwd_expect: "{ ⸨a⸩: 5, b: 6, c: ⸨7⸩ }"
     }
   , { file: "dict/foldl_with_index.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "b" (listElement 0 select))
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨0⸩"
     }
   , { file: "dict/intersection_with.fld"
     , bwd_expect: \_ -> envVal "d1" (dictVal "b" select >.> dictVal "c" select) >.> envVal "d2" (dictVal "b" select >.> dictVal "c" select)
     , δv: \_ -> dictVal "b" select >.> dictVal "c" select
     , inputs: []
     , fwd_expect: "{ b: ⸨0⸩, c: ⸨20⸩ }"
     }
   , { file: "dict/map.fld"
     , bwd_expect: \_ -> envVal "d" (dictVal "a" (listElement 0 select) >.> dictVal "b" (listElement 0 select))
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: "⸨20⸩"
     }
   , { file: "dict/match.fld"
     , bwd_expect: \_ -> envVal "n" select
     , δv: \_ -> select
     , inputs: []
     , fwd_expect: ""
     }
   , { file: "matrix_update.fld"
     , bwd_expect: \_ -> envVal "pair" select
     , δv: \_ -> matrixElement 1 1 select
     , inputs: []
     , fwd_expect:
          """15, 13, 6, 9, 16,
12, ⸨4000⸩, 15, 4, 13,
14, 9, 20, 8, 1,
4, 10, 3, 7, 19,
3, 11, 15, 2, 9"""
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
     , fwd_expect:
          """⸨0⸩, ⸨-1⸩, ⸨2⸩, 0, -1,
⸨0⸩, ⸨3⸩, -2, 3, -2,
⸨-1⸩, 1, -5, 0, 4,
1, -1, 4, 0, -4,
1, 0, -3, 2, 0"""
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
     , fwd_expect:
          """⸨5⸩, ⸨4⸩, ⸨2⸩, ⸨5⸩, ⸨2⸩,
⸨3⸩, ⸨1⸩, ⸨2⸩, -1, ⸨-2⸩,
⸨3⸩, ⸨0⸩, ⸨1⸩, 0, ⸨-1⸩,
⸨2⸩, 1, -2, 0, ⸨0⸩,
⸨1⸩, ⸨0⸩, ⸨-1⸩, ⸨-1⸩, ⸨-2⸩"""
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
     , fwd_expect:
          """⸨38⸩, ⸨37⸩, ⸨28⸩, ⸨30⸩, ⸨38⸩,
⸨38⸩, ⸨36⸩, ⸨46⸩, 31, ⸨34⸩,
⸨37⸩, ⸨41⸩, ⸨54⸩, 34, ⸨20⸩,
⸨21⸩, 35, 31, 31, ⸨42⸩,
⸨13⸩, ⸨32⸩, ⸨35⸩, ⸨19⸩, ⸨26⸩"""
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
     , fwd_expect:
          """(@doc(Paragraph(["Intermediate", "matrix"])) ⸨22⸩, ⸨28⸩,
⸨49⸩, 64, @doc(Paragraph(["Intermediate", "matrix"])) ⸨9⸩, ⸨12⸩, ⸨15⸩,
⸨19⸩, ⸨26⸩, ⸨33⸩,
⸨29⸩, ⸨40⸩, ⸨51⸩)"""
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
     , fwd_expect: "⸨[⸨(⸨0⸩, ⸨0⸩)⸩, ⸨(⸨1⸩, ⸨1⸩)⸩, ⸨(⸨1⸩, ⸨2⸩)⸩, ⸨(⸨2⸩, ⸨3⸩)⸩, ⸨(⸨3⸩, ⸨4⸩)⸩, ⸨(⸨4⸩, ⸨5⸩)⸩, ⸨(⸨4⸩, ⸨6⸩)⸩]⸩"
     }
   , { file: "dtw/average_series.fld"
     , bwd_expect:
          \_ -> envVal "seq1" (listElement 1 select)
             >.> envVal "seq2" (listElement 2 select)
     , δv: \_ -> listElement 2 select
     , inputs: [ "seq1", "seq2" ]
     , fwd_expect: "⸨[2.5, ⸨0.5⸩, ⸨0.5⸩, 2.5, 2.5, 1.0, 0.5]⸩"
     }
   , { file: "lookup.fld"
     , bwd_expect:
          \arg -> envVal "tree"
             (arg cNonEmpty f_right (arg cNonEmpty f_left (arg cNonEmpty f_value (arg cPair f_snd select'))))
     , δv: \_ -> select'
     , inputs: []
     , fwd_expect: "⸨\"Germany\"⸩"
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
     , fwd_expect:
          """MultiView([BarChart("Total output by country", Dimensions(275, 185), TickLabels(Default(), Default()), [StackedBar("China", [Segment("output", 295.3)]), StackedBar("USA", [Segment("output", ⸨196.7⸩)]), StackedBar("Germany", [Segment("output", 97.69999999999999)])], True), LineChart(Dimensions(330, 285), TickLabels(Default(), Default()), "Output of USA relative to China", [LinePlot("Bio", [Point(2013, 2.5483870967741935), Point(2014, 1.61), Point(2015, ⸨1.6213592233009706⸩), Point(2016, 1.4000000000000001), Point(2017, 1.1208053691275166), Point(2018, 0.9101123595505617)]), LinePlot("Hydro", [Point(2013, 0.3), Point(2014, 0.28214285714285714), Point(2015, ⸨0.8333333333333334⸩), Point(2016, 0.26229508196721313), Point(2017, 0.25559105431309903), Point(2018, 0.2484472049689441)]), LinePlot("Solar", [Point(2013, 0.6080402010050252), Point(2014, 0.6428571428571429), Point(2015, ⸨0.5909090909090909⸩), Point(2016, 0.5324675324675324), Point(2017, 0.3893129770992366), Point(2018, 0.3522727272727273)]), LinePlot("Wind", [Point(2013, 0.6703296703296703), Point(2014, 0.5739130434782609), Point(2015, ⸨0.5103448275862069⸩), Point(2016, 0.48520710059171596), Point(2017, 0.4734042553191489), Point(2018, 0.45714285714285713)])])])"""
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
     , fwd_expect:
          """MultiView([BarChart("Non-renewables by country", Dimensions(275, 185), TickLabels(Default(), Default()), [StackedBar("2014", [Segment("BRA", 151.05), Segment("EGY", 159.93), Segment("IND", 1060.1799999999998), Segment("JPN", 928.82)]), StackedBar("2015", [Segment("BRA", 142.76), Segment("EGY", 170.68), Segment("IND", 1118.8899999999999), Segment("JPN", 876.0999999999999)]), StackedBar("2016", [Segment("BRA", 108.03), Segment("EGY", 174.07999999999998), Segment("IND", 1193.53), Segment("JPN", 883.3299999999999)]), StackedBar("2017", [Segment("BRA", 116.76), Segment("EGY", 181.31), Segment("IND", ⸨1236.43⸩), Segment("JPN", 875.32)]), StackedBar("2018", [Segment("BRA", 101.48), Segment("EGY", ⸨182.31⸩), Segment("IND", 1315.57), Segment("JPN", ⸨873.39⸩)])], True), ScatterPlot("Clean energy efficiency vs proportion of renewable energy capacity", [Point(0.8723185510332055, 0.4180741155728385), Point(0.383891020964826, 0.3306374135311273), Point(0.5685559399722339, 0.2651713517303818), Point(0.39179907463864283, 0.5311676111397315), Point(0.0886691179578209, ⸨0.4125357483317445⸩), Point(0.3167847396421975, 0.2767379556904734), Point(0.3129857171819161, ⸨0.20426921772653447⸩), Point(0.29687029792356306, 0.3462200657379872), Point(0.16239390265026848, 0.4128), Point(0.2115752867627615, 0.5086651868096602)], AxisLabels("Renewables/TotalEnergyCap", "Clean Capacity Factor"))])"""
     }
   , { file: "qcut.fld"
     , bwd_expect: \_ -> (_ × Persistent)
     , δv: \_ -> (_ × Persistent)
     , inputs: []
     , fwd_expect: "[([1.01, 1.05], 0.051000000000000156), ([1.07, 1.09, 1.22, 1.23, 1.24, 1.24, 1.25, 1.32, 1.32, 1.35, 1.39, 1.47, 1.57, 1.72], 0.6639999999999999), ([1.73, 1.75, 1.76, 1.83, 1.87, 1.94, 2.04, 2.14, 2.18, 2.36, 2.37, 2.38, 2.52, 2.54], 0.8464999999999998), ([2.61, 2.67], 0.09850000000000003)]"
     }
   ]
