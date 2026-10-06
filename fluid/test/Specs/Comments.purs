module Test.Specs.Comments where

import Test.Util.Suite (TestSpec)

comments_cases :: Array TestSpec
comments_cases =
   [ { file: "comments/app.fld"
     , fwd_expect: """@doc(Paragraph(["This", "function", "application", "returns", "the", "length", "of", "a", "list."])) 2"""
     }
   , { file: "comments/app_arg.fld"
     , fwd_expect: """@doc(Paragraph(["Comments", "on", "arguments", "don't", "surface", "on", "the", "outermost", "application"])) [5, 7, 13, 15, 4, 3, -3]"""
     }
   , { file: "comments/dicts.fld"
     , fwd_expect:
          """
          @doc(Paragraph(["We", "can", "have", "a", "docComment", "before", "a", "dict!"])) {
            "d": {},
            "e": {"a": 5, "ab": 6},
            "e_ab": 6,
            "f": {"a": 6, "ab": 7},
            "g": {"a": 5}
          }
          """
     }
   , { file: "comments/int.fld"
     , fwd_expect: """@doc(Paragraph(["Comment", "on", "1"])) 1"""
     }
   , { file: "comments/list_comp.fld"
     , fwd_expect: """@doc(Paragraph(["We", "can", "add", "comments", "to", "list", "comprehensions"])) [14, 12, 10, 13, 11, 9, 12, 10, 8]"""
     }
   , { file: "comments/nested_constr.fld"
     , fwd_expect: """@doc(Paragraph(["This", "is", "a", "some string", "docComment!"])) False"""
     }
   , { file: "comments/projection.fld", fwd_expect: """@doc(Paragraph(["Doc", "comment", "on", "a", "projection"])) 1""" }
   ]
