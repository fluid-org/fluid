module Test.Util.Debug where

import Test.Util.Debug.Defaults

tracing :: TracingConfig
tracing = tracingDefaults
   { intermediates = true
   }

checking :: CheckingConfig
checking = checkingDefaults
   { edgeListGC = true
   , edgeListSorted = true
   , inputsAreSinks = true
   , outputsInGraph = true
   , mustEq = true
   }

testing :: TestingConfig
testing = testingDefaults
   { fwdPreservesTop = true
   , bwdDuals = true
   , fwdDuals = true
   , naiveFwd = true
   , contracted = true
   }

timing :: TimingConfig
timing = timingDefaults
