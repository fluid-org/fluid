module Test.Specs.Misc where

import Test.Util.Suite (TestSpec)

misc_cases :: Array TestSpec
misc_cases =
   [ { file: "arithmetic.fld", fwd_expect: "42" }
   , { file: "array.fld", fwd_expect: "(0, (3, 3))" }
   , { file: "assert_implicit.fld", fwd_expect: "10" }
   , { file: "bare_return.fld", fwd_expect: "None" }
   , { file: "boolean_precedence.fld", fwd_expect: "True" }
   , { file: "compose.fld", fwd_expect: "5" }
   , { file: "custom_infix.fld", fwd_expect: "True" }
   , { file: "dicts.fld"
     , fwd_expect:
          """
          {
            "d": {},
            "e": {"a": 5, "ab": 6},
            "e_ab": 6,
            "f": {"a": 6, "ab": 7},
            "g": {"a": 5}
          }
          """
     }
   , { file: "div_mod_quot_rem.fld"
     , fwd_expect: "[[1, -2, -2, 1], [2, -1, 1, -2], [1, -1, -1, 1], [2, 2, -2, -2]]"
     }
   , { file: "tuples.fld", fwd_expect: """[0, 4, 6, 2, 3, True, 3, (1, "a"), [2, 3, 4], True]""" }
   , { file: "eq_nan.fld", fwd_expect: "[False, True, False, True, False]" }
   , { file: "elif.fld", fwd_expect: """["much more", "more", "less", "much less"]""" }
   , { file: "factorial.fld", fwd_expect: "40320" }
   , { file: "filter.fld", fwd_expect: "[8, 7]" }
   , { file: "dependence/qcut.fld"
     , fwd_expect:
          """[([1.01, 1.05], 0.051000000000000156), ([1.07, 1.09, 1.22, 1.23, 1.24, 1.24, 1.25, 1.32, 1.32, 1.35, 1.39, 1.47, 1.57, 1.72], 0.6639999999999999), ([1.73, 1.75, 1.76, 1.83, 1.87, 1.94, 2.04, 2.14, 2.18, 2.36, 2.37, 2.38, 2.52, 2.54], 0.8464999999999998), ([2.61, 2.67], 0.09850000000000003)]"""
     }
   , { file: "first_class_constr.fld", fwd_expect: "[[10], [12], [20]]" }
   , { file: "flatten.fld"
     , fwd_expect: """[(3, "simon"), (4, "john"), (6, "sarah"), (7, "claire")]"""
     }
   , { file: "foldr_sum_squares.fld", fwd_expect: "661" }
   , { file: "if_no_else.fld", fwd_expect: "1" }
   , { file: "import_if_no_else.fld", fwd_expect: "1" }
   , { file: "include_input_into_output.fld"
     , fwd_expect: "(1, 1)"
     }
   , { file: "length.fld", fwd_expect: "2" }
   , { file: "lexical_scoping.fld", fwd_expect: "\"6\"" } -- avoid triple-quotes here as VSCode gets confused
   , { file: "lookup.fld", fwd_expect: "\"sarah\"" }
   , { file: "find_none.fld", fwd_expect: """[3, "none", None]""" }
   , { file: "map.fld", fwd_expect: "[5, 7, 13, 15, 4, 3, -3]" }
   , { file: "merge_sort.fld", fwd_expect: "[1, 2, 3]" }
   , { file: "match_bindings.fld", fwd_expect: "3" }
   , { file: "match_fallthrough.fld", fwd_expect: "0" }
   , { file: "match_literal.fld", fwd_expect: """["zero", "minus one", "two and a half", "greeting", "zero", "other"]""" }
   , { file: "match_as.fld", fwd_expect: "[(2, (1, 2)), (0, (3, 4))]" }
   , { file: "match_wildcard.fld", fwd_expect: "[2, -1, 0]" }
   , { file: "match_non_leaf.fld", fwd_expect: "[[1, 2, 4], [-1, 3, 5], Derived(7, 8)]" }
   , { file: "construct_non_leaf.fld", fwd_expect: "Base(1)" }
   , { file: "class_lowercase.fld", fwd_expect: "[3, 6, 9, origin()]" }
   , { file: "def_literal_pattern.fld", fwd_expect: "2" }
   , { file: "partial_application.fld", fwd_expect: "[6, 7, 3, 3, 3, 7, 7]" }
   , { file: "attr_access.fld", fwd_expect: "42" }
   , { file: "child_after_parent.fld", fwd_expect: "5" }
   , { file: "dotted_attr_access.fld", fwd_expect: "1" }
   , { file: "from_import_dataclass.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "from_import_multi.fld", fwd_expect: "3" }
   , { file: "from_import_subclass.fld", fwd_expect: "6" }
   , { file: "from_import_submodule.fld", fwd_expect: "1" }
   , { file: "from_import_value.fld", fwd_expect: "1" }
   , { file: "from_import_view.fld", fwd_expect: "MultiView([1, 2])" }
   , { file: "import_absolute_shadow.fld", fwd_expect: "2" }
   , { file: "import_dataclass.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "import_modules.fld", fwd_expect: "84" }
   , { file: "import_simple.fld", fwd_expect: "84" }
   , { file: "import_simple_unused.fld", fwd_expect: "84" }
   , { file: "import_twice.fld", fwd_expect: "1" }
   , { file: "name_member.fld", fwd_expect: "\"attr_lib\"" }
   , { file: "name_var.fld", fwd_expect: "\"__main__\"" }
   , { file: "namespace_deep.fld", fwd_expect: "3" }
   , { file: "namespace_from_import.fld", fwd_expect: "1" }
   , { file: "namespace_from_import_package.fld", fwd_expect: "1" }
   , { file: "namespace_import.fld", fwd_expect: "1" }
   , { file: "parent_after_child.fld", fwd_expect: "5" }
   , { file: "parent_uses_child.fld", fwd_expect: "6" }
   , { file: "predefined_imports.fld", fwd_expect: "5" }
   , { file: "qualified_construct.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "qualified_pattern.fld", fwd_expect: "7" }
   , { file: "same_name_classes.fld", fwd_expect: "8" }
   , { file: "sibling_submodules.fld", fwd_expect: "3" }
   , { file: "sibling_submodules_swapped.fld", fwd_expect: "3" }
   , { file: "submodule_attr.fld", fwd_expect: "5" }
   , { file: "normalise.fld", fwd_expect: "(33, 66)" }
   , { file: "not_parens_op.fld", fwd_expect: """@doc("hello") -42""" }
   , { file: "nub.fld", fwd_expect: "[1, 2, 3, 4]" }
   , { file: "paragraph.fld"
     , fwd_expect: """Paragraph([Text("As shown in Table 3, BiLSTM gives significantly  "), Text("better")])"""
     }
   , { file: "pass.fld", fwd_expect: "1" }
   , { file: "pattern_match.fld", fwd_expect: "4" }
   , { file: "piecewise_def.fld", fwd_expect: "3" }
   , { file: "prefix_op.fld", fwd_expect: "True" }
   , { file: "qualified_access.fld", fwd_expect: "1" }
   , { file: "range.fld", fwd_expect: "[[(0, 0), (0, 1), (1, 0), (1, 1)], 3, True, []]" }
   , { file: "record_lookup.fld", fwd_expect: "True" }
   , { file: "records.fld", fwd_expect: "{\"a\": 2, \"b\": 6, \"c\": 7, \"d\": [5], \"e\": 7}" }
   , { file: "reverse.fld", fwd_expect: "[2, 1]" }
   , { file: "ternary/basic_false.fld", fwd_expect: "6" }
   , { file: "ternary/basic_true.fld", fwd_expect: "5" }
   , { file: "ternary/condition_parenthesised.fld", fwd_expect: "10" }
   , { file: "ternary/in_function_body.fld", fwd_expect: "3" }
   , { file: "ternary/in_valdef_rhs.fld", fwd_expect: "3" }
   , { file: "ternary/inside_list_literal.fld", fwd_expect: "[1, 4]" }
   , { file: "ternary/lambda_body.fld", fwd_expect: "[0, 1, 2, 0]" }
   , { file: "ternary/listcomp_guard_unaffected.fld", fwd_expect: "[2, 3]" }
   , { file: "ternary/looser_than_plus.fld", fwd_expect: "7" }
   , { file: "ternary/right_assoc_false.fld", fwd_expect: "3" }
   , { file: "ternary/right_assoc_true.fld", fwd_expect: "1" }
   , { file: "ternary/untaken_branch.fld", fwd_expect: "3" }
   , { file: "zero_arg.fld", fwd_expect: "\"hello\"" }
   ]
