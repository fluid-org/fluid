module Test.Specs.BwdIntermediate where

import App.Util.Selector (intermediateVertex, matrix, matrixElement, select, select', (>.>))
import Data.Maybe (Maybe(..))
import Graph (Vertex(..))
import Test.Util.Suite (TestBwdIntermediateSpec)

bwdIntermediate_cases :: Array TestBwdIntermediateSpec
bwdIntermediate_cases =
   [ { file: "conv.fld"
     , bwd_expect: Nothing
     , δv: matrixElement 1 1 select
     , fwd_expect: ""
     , intermediate_expect: intermediateVertex (Vertex "5286")
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
     }
   ]
