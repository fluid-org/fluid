module Test.Util.Debug.Defaults where

-- These flags considered only when Util.debug.tracing is true.
type TracingConfig =
   { mediatingData :: Boolean
   , mouseEvent :: Boolean
   }

tracingDefaults :: TracingConfig
tracingDefaults =
   { mediatingData: false
   , mouseEvent: false
   }

-- Invariants that are potentially expensive to check and that we might want to disable in production,
-- that are not covered explicitly by tests.
type CheckingConfig =
   { mustEq :: Boolean
   }

checkingDefaults :: CheckingConfig
checkingDefaults =
   { mustEq: false
   }

type TimingConfig =
   { selectionResult :: Boolean
   }

timingDefaults :: TimingConfig
timingDefaults =
   { selectionResult: false
   }
