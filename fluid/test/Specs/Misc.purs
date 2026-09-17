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
     , fwd_expect: "{ d: {}, e: { a: 5, ab: 6 }, e_ab: 6, f: { a: 6, ab: 7 }, g: { a: 5 } }"
     }
   , { file: "div_mod_quot_rem.fld"
     , fwd_expect:
          "(1 :| -2 :| -2 :| 1 :| []) :| \
          \(2 :| -1 :| 1 :| -2 :| []) :| \
          \(1 :| -1 :| -1 :| 1 :| []) :| \
          \(2 :| 2 :| -2 :| -2 :| []) :| []"
     }
   , { file: "elif.fld", fwd_expect: """"much more" :| "more" :| "less" :| "much less" :| []""" }
   , { file: "factorial.fld", fwd_expect: "40320" }
   , { file: "filter.fld", fwd_expect: "8 :| 7 :| []" }
   , { file: "first_class_constr.fld", fwd_expect: "(10 :| []) :| (12 :| []) :| (20 :| []) :| []" }
   , { file: "flatten.fld"
     , fwd_expect: """(3, "simon") :| (4, "john") :| (6, "sarah") :| (7, "claire") :| []"""
     }
   , { file: "foldr_sum_squares.fld", fwd_expect: "661" }
   , { file: "if_no_else.fld", fwd_expect: "1" }
   , { file: "include_input_into_output.fld"
     , fwd_expect: "(1, 1)"
     }
   , { file: "length.fld", fwd_expect: "2" }
   , { file: "lexical_scoping.fld", fwd_expect: "\"6\"" } -- avoid triple-quotes here as VSCode gets confused
   , { file: "lookup.fld", fwd_expect: """Just("sarah")""" }
   , { file: "map.fld", fwd_expect: "5 :| 7 :| 13 :| 15 :| 4 :| 3 :| -3 :| []" }
   , { file: "merge_sort.fld", fwd_expect: "1 :| 2 :| 3 :| []" }
   , { file: "match_bindings.fld", fwd_expect: "3" }
   , { file: "match_fallthrough.fld", fwd_expect: "0" }
   , { file: "match_literal.fld", fwd_expect: """"zero" :| "minus one" :| "two and a half" :| "greeting" :| "zero" :| "other" :| []""" }
   , { file: "match_as.fld", fwd_expect: "(2, (1, 2)) :| (0, (3, 4)) :| []" }
   , { file: "match_wildcard.fld", fwd_expect: "2 :| -1 :| 0 :| []" }
   , { file: "module/attr_access.fld", fwd_expect: "42" }
   , { file: "module/child_after_parent.fld", fwd_expect: "5" }
   , { file: "module/dotted_attr_access.fld", fwd_expect: "1" }
   , { file: "module/from_import_dataclass.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "module/from_import_multi.fld", fwd_expect: "3" }
   , { file: "module/from_import_subclass.fld", fwd_expect: "6" }
   , { file: "module/from_import_submodule.fld", fwd_expect: "1" }
   , { file: "module/from_import_value.fld", fwd_expect: "1" }
   , { file: "module/from_import_view.fld", fwd_expect: "MultiView(1 :| 2 :| [])" }
   , { file: "module/import_absolute_shadow.fld", fwd_expect: "2" }
   , { file: "module/import_dataclass.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "module/import_modules.fld", fwd_expect: "84" }
   , { file: "module/import_simple.fld", fwd_expect: "84" }
   , { file: "module/import_simple_unused.fld", fwd_expect: "84" }
   , { file: "module/import_twice.fld", fwd_expect: "1" }
   , { file: "module/name_member.fld", fwd_expect: "\"attr_lib\"" }
   , { file: "module/name_var.fld", fwd_expect: "\"__main__\"" }
   , { file: "module/namespace_deep.fld", fwd_expect: "3" }
   , { file: "module/namespace_from_import.fld", fwd_expect: "1" }
   , { file: "module/namespace_import.fld", fwd_expect: "1" }
   , { file: "module/parent_after_child.fld", fwd_expect: "5" }
   , { file: "module/parent_uses_child.fld", fwd_expect: "6" }
   , { file: "module/predefined_imports.fld", fwd_expect: "5" }
   , { file: "module/qualified_construct.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "module/qualified_pattern.fld", fwd_expect: "7" }
   , { file: "module/same_name_classes.fld", fwd_expect: "8" }
   , { file: "module/sibling_submodules.fld", fwd_expect: "3" }
   , { file: "module/sibling_submodules_swapped.fld", fwd_expect: "3" }
   , { file: "module/submodule_attr.fld", fwd_expect: "5" }
   , { file: "normalise.fld", fwd_expect: "(33, 66)" }
   , { file: "not_parens_op.fld", fwd_expect: """@doc("hello") -42""" }
   , { file: "nub.fld", fwd_expect: "1 :| 2 :| 3 :| 4 :| []" }
   , { file: "paragraph.fld"
     , fwd_expect: """Paragraph(Text("As shown in Table 3, BiLSTM gives significantly  ") :| Text("better") :| [])"""
     }
   , { file: "pass.fld", fwd_expect: "1" }
   , { file: "pattern_match.fld", fwd_expect: "4" }
   , { file: "piecewise_def.fld", fwd_expect: "3" }
   , { file: "prefix_op.fld", fwd_expect: "True" }
   , { file: "purepy/assert_stmt.fld", fwd_expect: "10" }
   , { file: "purepy/both_branches.fld", fwd_expect: "\"smaller\"" }
   , { file: "purepy/branch_local.fld", fwd_expect: "6" }
   , { file: "purepy/closure_capture.fld", fwd_expect: "6" }
   , { file: "purepy/constr_keyword.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "purepy/constr_mixed.fld", fwd_expect: "Point(1, 2, 3)" }
   , { file: "purepy/dataclass_attr.fld", fwd_expect: "7" }
   , { file: "purepy/dataclass_construct.fld", fwd_expect: "Coord(3, 4)" }
   , { file: "purepy/dataclass_decl.fld", fwd_expect: "42" }
   , { file: "purepy/early_return.fld", fwd_expect: "\"smaller\"" }
   , { file: "purepy/expr_stmt.fld", fwd_expect: "6" }
   , { file: "purepy/implicit_none.fld", fwd_expect: "None" }
   , { file: "purepy/implicit_return.fld", fwd_expect: "None" }
   , { file: "purepy/lambda.fld", fwd_expect: "15" }
   , { file: "purepy/mutual.fld", fwd_expect: "True" }
   , { file: "purepy/mutual_after_rebind.fld", fwd_expect: "(0, 1)" }
   , { file: "purepy/mutual_def_in_branch.fld", fwd_expect: "(\"via mutual region\", \"via mutual region\")" }
   , { file: "purepy/param_reassign.fld", fwd_expect: "15" }
   , { file: "purepy/pat_class_keyword.fld", fwd_expect: "4" }
   , { file: "purepy/pat_class_mixed.fld", fwd_expect: "(2, 3)" }
   , { file: "purepy/self.fld", fwd_expect: "120" }
   , { file: "purepy/self_capture_def.fld", fwd_expect: "cl" }
   , { file: "qualified_access.fld", fwd_expect: "1" }
   , { file: "range.fld", fwd_expect: "(0, 0) :| (0, 1) :| (1, 0) :| (1, 1) :| []" }
   , { file: "record_lookup.fld", fwd_expect: "True" }
   , { file: "records.fld", fwd_expect: "{ a: 2, b: 6, c: 7, d: 5 :| [], e: 7 }" }
   , { file: "reverse.fld", fwd_expect: "2 :| 1 :| []" }
   , { file: "ternary/basic_false.fld", fwd_expect: "6" }
   , { file: "ternary/basic_true.fld", fwd_expect: "5" }
   , { file: "ternary/condition_parenthesised.fld", fwd_expect: "10" }
   , { file: "ternary/in_function_body.fld", fwd_expect: "3" }
   , { file: "ternary/in_valdef_rhs.fld", fwd_expect: "3" }
   , { file: "ternary/inside_list_literal.fld", fwd_expect: "1 :| 4 :| []" }
   , { file: "ternary/lambda_body.fld", fwd_expect: "0 :| 1 :| 2 :| 0 :| []" }
   , { file: "ternary/listcomp_guard_unaffected.fld", fwd_expect: "2 :| 3 :| []" }
   , { file: "ternary/looser_than_plus.fld", fwd_expect: "7" }
   , { file: "ternary/right_assoc_false.fld", fwd_expect: "3" }
   , { file: "ternary/right_assoc_true.fld", fwd_expect: "1" }
   , { file: "zero_arg.fld", fwd_expect: "\"hello\"" }
   ]
