module Test.Specs.BwdIntermediate where

import App.Fig (docQuery)
import App.Util (Selector)
import App.Util.Selector (barChart, barSegment, envVal, listElement, matrix, matrixElement, multiViewEntry, scatterPlot, scatterPoint, select, select', topα, (>.>))
import App.View.Util (Options)
import Bind (Var, (↦))
import Data.Maybe (Maybe(..))
import File (Folder(..))
import Test.Util.Suite (TestBwdIntermediateSpec)
import Val (Env)

mkSpec :: Array Var -> Options
mkSpec inputs =
   { fluidSrcPaths: [ Folder "fluid", Folder "test/fluid" ]
   , inputs
   , query: Just docQuery
   , linking: false
   , rowFilter: Nothing
   }

-- intermediate_expect is keyed by intermediate vertex address (the ι key), and
-- checked as a lower bound (≽): selecting the output must demand at least these
-- intermediate values. Only baseVal is selected — the @doc annotation's own
-- leaves are left unselected (no selector reaches them; the ≽ tolerates their
-- being additionally selected in the actual ι).

-- A demanded 3×3 convolution patch (container + all nine cells).
convPatch :: String -> Selector Env
convPatch addr = envVal addr
   ( matrix select'
        >.> matrixElement 0 0 select
        >.> matrixElement 0 1 select
        >.> matrixElement 0 2 select
        >.> matrixElement 1 0 select
        >.> matrixElement 1 1 select
        >.> matrixElement 1 2 select
        >.> matrixElement 2 0 select
        >.> matrixElement 2 1 select
        >.> matrixElement 2 2 select
   )

-- A demanded intermediate, asserted via its outer annotation (scalars, lists).
docα :: String -> Selector Env
docα addr = envVal addr (topα select')

bwdIntermediate_cases :: Array TestBwdIntermediateSpec
bwdIntermediate_cases =
   [ { file: "slicing/intermediates/conv.fld"
     , spec: mkSpec [ "inputImage", "kernel" ]
     , δv: matrixElement 1 1 select
     , δ_in: "inputImage" ↦ matrixElement 0 0 select
     , intermediate_expect: convPatch "5286"
     }
   , { file: "slicing/intermediates/edge_detect.fld"
     , spec: mkSpec [ "inputImage", "filter" ]
     , δv: matrixElement 0 0 select
     , δ_in: "inputImage" ↦ matrixElement 0 0 select
     , intermediate_expect: convPatch "4125"
     }
   , { file: "slicing/intermediates/emboss.fld"
     , spec: mkSpec [ "inputImage", "filter" ]
     , δv: matrixElement 0 0 select
     , δ_in: "inputImage" ↦ matrixElement 0 0 select
     , intermediate_expect: convPatch "4057"
     }
   , { file: "slicing/intermediates/gaussian.fld"
     , spec: mkSpec [ "inputImage", "filter" ]
     , δv: matrixElement 0 0 select
     , δ_in: "inputImage" ↦ matrixElement 0 0 select
     , intermediate_expect: convPatch "4057"
     }
   , { file: "slicing/intermediates/dtw.fld"
     , spec: mkSpec [ "seq1", "seq2", "window" ]
     , δv: listElement 0 select
     , δ_in: "seq1" ↦ listElement 0 select
     , intermediate_expect: docα "4689"
     }
   , { file: "slicing/intermediates/line_chart.fld"
     , spec: mkSpec [ "data" ]
     , δv: select
     , δ_in: "data" ↦ listElement 0 select
     , intermediate_expect: docα "1712" >.> docα "1824" >.> docα "1936" >.> docα "2048" >.> docα "2160" >.> docα "2272"
     }
   , { file: "slicing/intermediates/grouped_bar_chart.fld"
     , spec: mkSpec [ "data" ]
     , δv: select
     , δ_in: "data" ↦ listElement 0 select
     , intermediate_expect: docα "1854" >.> docα "1988" >.> docα "2122"
     }
   , { file: "slicing/intermediates/stacked_bar_chart.fld"
     , spec: mkSpec [ "data" ]
     , δv: select
     , δ_in: "data" ↦ listElement 0 select
     , intermediate_expect: docα "1744" >.> docα "1880" >.> docα "2016"
     }
   , { file: "slicing/intermediates/bar_chart_line_chart.fld"
     , spec: mkSpec [ "renewables" ]
     , δv: multiViewEntry 0 (barChart (barSegment 0 0 select))
     , δ_in: "renewables" ↦ listElement 0 select
     , intermediate_expect: docα "2506"
     }
   , { file: "slicing/intermediates/stacked_bar_scatter_plot.fld"
     , spec: mkSpec [ "renewables", "nonRenewables" ]
     , δv: multiViewEntry 1 (scatterPlot (scatterPoint 0 select))
     , δ_in: "renewables" ↦ listElement 0 select
     , intermediate_expect: docα "23952" >.> docα "24022"
     }
   ]
