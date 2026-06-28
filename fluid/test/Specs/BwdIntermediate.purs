module Test.Specs.BwdIntermediate where

import App.Util (SelectionType(..))
import App.Util.Selector (intermediateVertex, matrix, matrixElement, select, select')
import Graph (Vertex(..))
import Test.Util.Suite (TestBwdIntermediateSpec)
import Util ((×))

bwdIntermediate_cases :: Array TestBwdIntermediateSpec
bwdIntermediate_cases =
   [ { file: "conv.fld"
     , bwd_expect: (_ × Persistent)
     , δv: matrixElement 0 0 select
     , fwd_expect: ""
     , intermediate_expect: intermediateVertex (Vertex "1836") (matrix select')
     }
   ]
