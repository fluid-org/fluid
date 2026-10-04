module Test.Util.Debug.Defaults where

-- These flags considered only when Util.debug.tracing is true.
type TracingConfig =
   { runWithGraphT :: Boolean
   , graphBwdSlice :: Boolean
   , graphBwdSlice_vertexData :: Boolean
   , graphFwdSlice :: Boolean
   , checkEq :: Boolean
   , bwdSelection :: Boolean
   , fwdAfterBwd :: Boolean
   , mediatingData :: Boolean
   , mouseEvent :: Boolean
   , intermediates :: Boolean
   }

tracingDefaults :: TracingConfig
tracingDefaults =
   { runWithGraphT: false
   , graphBwdSlice: false
   , graphBwdSlice_vertexData: false
   , graphFwdSlice: false
   , checkEq: false
   , bwdSelection: false
   , fwdAfterBwd: false
   , mediatingData: false
   , mouseEvent: false
   , intermediates: true
   }

-- Invariants that are potentially expensive to check and that we might want to disable in production,
-- that are not covered explicitly by tests.
type CheckingConfig =
   { edgeListGC :: Boolean
   , edgeListSorted :: Boolean
   , inputsAreSinks :: Boolean
   , outputsInGraph :: Boolean
   , allocRoundTrip :: Boolean
   , mustEq :: Boolean
   }

checkingDefaults :: CheckingConfig
checkingDefaults =
   { edgeListGC: false
   , edgeListSorted: false
   , inputsAreSinks: false
   , outputsInGraph: false
   , allocRoundTrip: false
   , mustEq: false
   }

-- Should be set to false except when there are specific outstanding problems.
type TestingConfig =
   { fwdPreservesTop :: Boolean
   , bwdDuals :: Boolean
   , fwdDuals :: Boolean
   , naiveFwd :: Boolean
   }

testingDefaults :: TestingConfig
testingDefaults =
   { fwdPreservesTop: false
   , bwdDuals: false
   , fwdDuals: false
   , naiveFwd: false
   }

type TimingConfig =
   { selectionResult :: Boolean
   }

timingDefaults :: TimingConfig
timingDefaults =
   { selectionResult: false
   }
