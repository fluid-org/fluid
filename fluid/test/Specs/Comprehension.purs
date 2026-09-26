module Test.Specs.Comprehension where

import Test.Util.Suite (TestSpec)

comprehension_cases :: Array TestSpec
comprehension_cases =
   [ { file: "comprehension/list_comp_1.fld"
     , fwd_expect: "14 :| 12 :| 10 :| 13 :| 11 :| 9 :| 12 :| 10 :| 8 :| []"
     }
   , { file: "comprehension/list_comp_2.fld"
     , fwd_expect:
          "14 :| 14 :| 14 :| 12 :| 12 :| 12 :| 10 :| 10 :| 10 :| 13 :| 13 :| 13 :| 11 :| 11 :| 11 :| 9 :| \
          \9 :| 9 :| 12 :| 12 :| 12 :| 10 :| 10 :| 10 :| 8 :| 8 :| 8 :| []"
     }
   , { file: "comprehension/list_comp_3.fld", fwd_expect: "9 :| 8 :| []" }
   , { file: "comprehension/list_comp_4.fld", fwd_expect: "5 :| 4 :| 3 :| []" }
   , { file: "comprehension/list_comp_5.fld", fwd_expect: "5 :| 4 :| 3 :| []" }
   , { file: "comprehension/list_comp_6.fld", fwd_expect: "5 :| []" }
   , { file: "comprehension/list_comp_7.fld", fwd_expect: "[] :| []" }
   , { file: "comprehension/list_comp_8.fld", fwd_expect: "5 :| 4 :| 3 :| []" }
   , { file: "comprehension/list_comp_9.fld", fwd_expect: "10 :| 19 :| []" }
   , { file: "comprehension/list_comp_10.fld", fwd_expect: "[]" }
   , { file: "comprehension/dict_comp_1.fld", fwd_expect: "{ bb: 2, ccc: 3 }" }
   , { file: "comprehension/dict_comp_2.fld", fwd_expect: "{ a: 21, b: 22 }" }
   ]
