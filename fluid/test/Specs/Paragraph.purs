module Test.Specs.Paragraph where

import Test.Util.Suite (TestSpec)

paragraph_cases :: Array TestSpec
paragraph_cases =
   [ { file: "paragraph/basic.fld"
     , fwd_expect:
          """Paragraph(["Hello", "there,", Paragraph(["Alice"]), "!"])"""
     }
   , { file: "paragraph/explicit.fld"
     , fwd_expect:
          """Paragraph([Text("Hi "), "Alice", 5, "+", "6", "is", Text("16")])"""
     }
   ]
