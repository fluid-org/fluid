module Test.Specs.Intermediates where

import Prelude

import App.Util.Selector (envVal, matrixElement, none, select, tupleElement, valOf, (>.>))
import Data.Maybe (Maybe(..))
import Test.Util (at, fluidSrcPaths)
import Test.Util.Suite (TestIntermediatesSpec)

intermediates_cases :: Array TestIntermediatesSpec
intermediates_cases =
   [ { spec: { fluidSrcPaths, ignoreInputs: none, linking: true, rowFilter: Nothing }
     , δ_out: \_ -> matrixElement 1 1 select
     , intermediate: 4
     , transient: matrixElement 1 1
     , in_expect:
          envVal "filter"
             ( valOf $ at
                  """
                  -2, -1, 0,
                  -1, ⸨1⸩, 1,
                  0, 1, 2
                  """
             ) >.> envVal "smallImage"
             ( valOf $ at
                  """
                  15, 13, 6,
                  12, ⸨5⸩, 15,
                  14, 9, 20
                  """
             )
     , out_expect: \_ -> at
          """
          5, 4, 0,
          3, ⸨1⸩, 0,
          1, -1, -1
          """
     , file: "dependence/convolution/intermediate.fld"
     }
   , { spec: { fluidSrcPaths, ignoreInputs: none, linking: true, rowFilter: Nothing }
     , δ_out: \_ -> tupleElement 0 (matrixElement 0 0 select)
     , intermediate: 0
     , transient: matrixElement 0 0
     , in_expect:
          envVal "leftMatrix"
             ( valOf $ at
                  """
                  ⸨1⸩, ⸨2⸩, ⸨3⸩,
                  4, 5, 6
                  """
             ) >.> envVal "rightMatrix"
             ( valOf $ at
                  """
                  ⸨1⸩, 2,
                  ⸨3⸩, 4,
                  ⸨5⸩, 6
                  """
             )
     , out_expect: \_ -> at
          """
          (⸨22⸩, 28,
          49, 64, 9, 12, 15,
          19, 26, 33,
          29, 40, 51)
          """
     , file: "dependence/matrix/matmul.fld"
     }
   ]
