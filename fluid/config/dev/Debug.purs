module Test.Util.Debug where

import Test.Util.Debug.Defaults

tracing :: TracingConfig
tracing = tracingDefaults

checking :: CheckingConfig
checking = checkingDefaults
   { mustEq = true
   }

timing :: TimingConfig
timing = timingDefaults
