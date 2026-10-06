module Test.Specs.LinkedOutputs where

import App.Util.Selector (barSegment, dictVal, eachElement, envVal, listElement, matrixDims, matrixElement, none, topα, (>.>), select, select')
import Data.Maybe (Maybe(..))
import DataType (cBarChart, cLineChart, cLinePlot, cMultiView, cPair, cPoint, cScatterPlot, f_fst, f_plots, f_points, f_snd, f_stackedBars, f_views, f_y)
import Test.Util (at, fluidSrcPaths)
import Test.Util.Suite (TestLinkedOutputsSpec)

linkedOutputs_spec1 :: TestLinkedOutputsSpec
linkedOutputs_spec1 =
   { spec:
        { fluidSrcPaths
        , inputs: [ "renewables" ]
        , query: false
        , ignoreInputs: envVal "renewables" (eachElement (dictVal "year" select >.> dictVal "country" select))
        , linking: true
        , rowFilter: Nothing
        }
   , δ_out: \arg -> arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 1 0 select)))
   , out_expect: \arg ->
        arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 1 0 select)))
           >.> arg cMultiView f_views
              ( listElement 1
                   ( arg cLineChart f_plots
                        ( listElement 0 (arg cLinePlot f_points (listElement 2 (arg cPoint f_y select)))
                             >.> listElement 1 (arg cLinePlot f_points (listElement 2 (arg cPoint f_y select)))
                             >.> listElement 2 (arg cLinePlot f_points (listElement 2 (arg cPoint f_y select)))
                             >.> listElement 3 (arg cLinePlot f_points (listElement 2 (arg cPoint f_y select)))
                        )
                   )
              )
   , inert_expect: \_ -> Nothing
   , file: "slicing/linked_outputs/bar_chart_line_chart.fld"
   }

linkedOutputs_spec2 :: TestLinkedOutputsSpec
linkedOutputs_spec2 =
   { spec:
        { fluidSrcPaths
        , inputs: [ "nonRenewables" ]
        , query: false
        , ignoreInputs: envVal "nonRenewables" (eachElement (dictVal "year" select >.> dictVal "country" select))
        , linking: true
        , rowFilter: Nothing
        }
   , δ_out: \arg -> arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 3 2 select >.> barSegment arg 4 1 select >.> barSegment arg 4 3 select)))
   , out_expect: \arg ->
        arg cMultiView f_views (listElement 0 (arg cBarChart f_stackedBars (barSegment arg 3 2 select >.> barSegment arg 4 1 select >.> barSegment arg 4 3 select)))
           >.> arg cMultiView f_views
              ( listElement 1
                   ( arg cScatterPlot f_points
                        ( listElement 4 (arg cPoint f_y select)
                             >.> listElement 6 (arg cPoint f_y select)
                        )
                   )
              )
   , inert_expect: \_ -> Nothing
   , file: "slicing/linked_outputs/stacked_bar_scatter_plot.fld"
   }

movingAverages_spec :: TestLinkedOutputsSpec
movingAverages_spec =
   { spec:
        { fluidSrcPaths
        , inputs: [ "methane" ]
        , query: false
        , ignoreInputs: none
        , linking: true
        , rowFilter: Nothing
        }
   , δ_out: \_ -> none -- TODO: make this a non-trivial test
   , out_expect: \_ -> none
   , inert_expect: \_ -> Nothing
   , file: "linked_outputs/moving_average.fld"
   }

linkedOutputs_cases :: Array TestLinkedOutputsSpec
linkedOutputs_cases =
   [ { spec:
          { fluidSrcPaths
          , inputs: [ "data" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \arg -> arg cPair f_snd select
     , out_expect: \_ -> select
     , inert_expect: \_ -> Just none
     , file: "linked_outputs/pairs.fld"
     }
   , { spec:
          { fluidSrcPaths

          , inputs: [ "data" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \arg -> arg cPair f_fst (matrixElement 1 1 select)
     , out_expect: \arg ->
          arg cPair f_fst
             ( at
                  """18, 15, 10, 10, 17,
⸨14⸩, ⸨9⸩, ⸨13⸩, ⸨9⸩, ⸨12⸩,
12, 13, 19, 13, 5,
10, 9, 6, 8, 17,
6, 11, 15, 7, 8"""
             )
             >.> arg cPair f_snd
                ( at
                     """⸨18⸩, ⸨12⸩, ⸨13⸩, 9, 19,
⸨20⸩, ⸨11⸩, ⸨24⸩, 9, 14,
⸨15⸩, ⸨13⸩, ⸨20⸩, 11, 14,
7, 15, 15, 8, 20,
3, 10, 12, 3, 11"""
                )
     , inert_expect: \arg -> Just
          ( topα select'
               >.> arg cPair f_fst (topα select' >.> matrixDims select')
               >.> arg cPair f_snd (topα select' >.> matrixDims select')
          )
     , file: "linked_outputs/convolution.fld"
     }
   , { spec:
          { fluidSrcPaths
          , inputs: [ "xs", "n", "ys", "m" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \arg -> arg cPair f_fst (listElement 0 select)
     , out_expect: \_ -> at "([⸨8⸩, ⸨7⸩], [6, 9])"
     , inert_expect: \_ -> Nothing
     , file: "linked_outputs/filter.fld"
     }
   , { spec:
          { fluidSrcPaths
          , inputs: [ "types", "data" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \_ -> listElement 1 select
     , out_expect: \_ -> at "[⸨88⸩, ⸨6⸩, ⸨4⸩]"
     , inert_expect: \_ -> Nothing
     , file: "slicing/section_5_example.fld"
     }
   , { spec:
          { fluidSrcPaths
          , inputs: [ "seq1", "seq2" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \_ -> listElement 1 select
     , out_expect: \_ -> at "[⸨(⸨0⸩, ⸨0⸩)⸩, ⸨(⸨1⸩, ⸨1⸩)⸩, ⸨(⸨1⸩, ⸨2⸩)⸩, ⸨(⸨2⸩, ⸨3⸩)⸩, ⸨(⸨3⸩, ⸨4⸩)⸩, ⸨(⸨4⸩, ⸨5⸩)⸩, ⸨(⸨4⸩, ⸨6⸩)⸩]"
     , inert_expect: \_ -> Nothing
     , file: "slicing/dtw/compute_dtw.fld"
     }
   , { spec:
          { fluidSrcPaths
          , inputs: [ "x", "n" ]
          , query: false
          , ignoreInputs: none
          , linking: true
          , rowFilter: Nothing
          }
     , δ_out: \arg -> arg cPair f_snd select
     , out_expect: \_ -> at "(⸨3⸩, ⸨True⸩)"
     , inert_expect: \_ -> Nothing
     , file: "slicing/output_not_source.fld"
     }
   , linkedOutputs_spec1
   , linkedOutputs_spec2
   , movingAverages_spec
   ]
