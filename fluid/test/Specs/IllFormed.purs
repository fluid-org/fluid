module Test.Specs.IllFormed where

import Test.Util.Suite (IllFormedSpec)

-- Spec-derived (PurePy corpus): each entry corresponds to a test in
-- pure-py-spec/test/ill-formed/semantic.
purepy_cases :: Array IllFormedSpec
purepy_cases =
   [ { file: "purepy/attr_non_object.fld", expected_error: "Found 5, expected object" }
   , { file: "purepy/attr_unknown_member.fld", expected_error: "module qual_lib has no member unknown" }
   , { file: "purepy/assert_msg_false.fld", expected_error: "AssertionError: x should not be 5" }
   , { file: "purepy/cond_nonbool.fld", expected_error: "Found 0, expected bool" }
   , { file: "purepy/binop_operand_type.fld", expected_error: "Found \"a\", expected int or float\nIn +" }
   , { file: "purepy/unary_operand_type.fld", expected_error: "Found \"x\", expected int or float\nIn floor" }
   , { file: "purepy/dict_key_type.fld", expected_error: "Found 1, expected str" }
   , { file: "purepy/matrix_dim_type.fld", expected_error: "Found \"a\", expected int" }
   , { file: "purepy/cond_partial_def.fld", expected_error: "Not definitely assigned: x" }
   , { file: "purepy/constr_bad_keyword.fld", expected_error: "Class Coord keyword fields mismatch: expected (\"y\" : Nil), got (\"z\" : Nil)" }
   , { file: "purepy/construct_arity.fld", expected_error: "Point expects 2 argument(s); got 3" }
   , { file: "purepy/dataclass_dup_class.fld", expected_error: "Duplicate class declaration: Point" }
   , { file: "purepy/dataclass_dup_field.fld", expected_error: "Duplicate field names in class: Point" }
   , { file: "purepy/dataclass_field_default.fld", expected_error: "\"ParseError on line 5, column 10:\\nExpected EOF\"" }
   , { file: "purepy/dataclass_inherited_field_clash.fld", expected_error: "Class Sub redeclares inherited field(s): (\"x\" : Nil)" }
   , { file: "purepy/dataclass_dict_key_type.fld", expected_error: "\"ParseError on line 5, column 14:\\nExpected `str`, received `int`\"" }
   , { file: "purepy/param_type_unknown.fld", expected_error: "\"ParseError on line 1, column 13:\\nNot a type: lst\"" }
   , { file: "purepy/clauses_annotation_mismatch.fld", expected_error: "Clauses differ in parameter annotations" }
   , { file: "purepy/clauses_annotation_later.fld", expected_error: "Clauses differ in parameter annotations" }
   , { file: "purepy/annotation_unknown_class.fld", expected_error: "Unknown dataclass: Shape" }
   , { file: "purepy/dataclass_field_forward_class.fld", expected_error: "Unknown dataclass: B" }
   , { file: "purepy/dataclass_two_bases.fld", expected_error: "\"ParseError on line 12, column 10:\\nExpected ')'\"" }
   , { file: "purepy/dataclass_unknown_base.fld", expected_error: "Unknown class: Unknown" }
   , { file: "purepy/duplicate_def_in_region.fld", expected_error: "case 2 is unreachable" }
   , { file: "purepy/forward_class_in_def.fld", expected_error: "Unknown dataclass: Point" }
   , { file: "purepy/forward_class_top.fld", expected_error: "Unknown dataclass: Point" }
   , { file: "purepy/from_import_unknown_member.fld", expected_error: "Cannot import name baz from module two_vals_lib" }
   , { file: "purepy/if_nonbool.fld", expected_error: "Found 1, expected bool" }
   , { file: "purepy/nested_class.fld", expected_error: "Class declaration not at top level: C" }
   , { file: "purepy/dataclass_not_imported.fld", expected_error: "Not bound as a predefined name: dataclass" }
   , { file: "purepy/callable_not_imported.fld", expected_error: "Not bound as a predefined name: Callable" }
   , { file: "purepy/sized_not_imported.fld", expected_error: "Not bound as a predefined name: Sized" }
   , { file: "purepy/shadowed_list.fld", expected_error: "Not bound as a predefined name: list" }
   , { file: "purepy/any_not_defined.fld", expected_error: "Cannot import name Any from module typing" }
   , { file: "purepy/predefined_member_unknown.fld", expected_error: "module math has no member tau" }
   , { file: "purepy/import_in_def.fld", expected_error: "\"ParseError on line 2, column 10:\\nimports must precede statements\"" }
   , { file: "purepy/import_in_if.fld", expected_error: "\"ParseError on line 2, column 10:\\nimports must precede statements\"" }
   , { file: "purepy/import_in_match_case.fld", expected_error: "\"ParseError on line 3, column 12:\\nimports must precede statements\"" }
   , { file: "purepy/match_var_leak.fld", expected_error: "Not definitely assigned: x" }
   , { file: "purepy/match_dup_literal.fld", expected_error: "case 2 is unreachable" }
   , { file: "purepy/match_as_subsumed.fld", expected_error: "case 2 is unreachable" }
   , { file: "purepy/match_dup_list.fld", expected_error: "case 2 is unreachable" }
   , { file: "purepy/match_list_after_cons.fld", expected_error: "case 2 is unreachable" }
   , { file: "purepy/pat_dup_var.fld", expected_error: "Duplicate variable in pattern: x" }
   , { file: "purepy/pat_as_dup_var.fld", expected_error: "Duplicate variable in pattern: x" }
   , { file: "purepy/pat_dup_key.fld", expected_error: "Duplicate key in pattern: a" }
   , { file: "purepy/mutual_def_block_local.fld", expected_error: "Not definitely assigned: g" }
   , { file: "purepy/mutual_split.fld", expected_error: "Unbound name: odd" }
   , { file: "purepy/mutual_split_by_assign.fld", expected_error: "Unbound name: g" }
   , { file: "purepy/no_else.fld", expected_error: "Not definitely assigned: x" }
   , { file: "purepy/pat_class_arity.fld", expected_error: "Point expects 2 argument(s); got 0" }
   , { file: "purepy/pat_class_bad_keyword.fld", expected_error: "Class Coord keyword fields mismatch: expected (\"y\" : Nil), got (\"z\" : Nil)" }
   , { file: "purepy/pat_class_unknown.fld", expected_error: "Unknown dataclass: NotAClass" }
   , { file: "purepy/self_capture.fld", expected_error: "Variable captured by its own definition: x" }
   , { file: "purepy/self_capture_lambda.fld", expected_error: "Variable captured by its own definition: f" }
   , { file: "purepy/shadow_captured.fld", expected_error: "Captured variable reassigned: x" }
   , { file: "purepy/shadow_captured_global.fld", expected_error: "Captured variable reassigned: x" }
   , { file: "purepy/shadow_captured_mutual.fld", expected_error: "Captured variable reassigned: g" }
   , { file: "purepy/unbound_local.fld", expected_error: "Not definitely assigned: y" }
   , { file: "purepy/unreachable.fld", expected_error: "Unreachable statement" }
   ]

-- Fluid-specific ill-formed cases (no PurePy correspondent).
illFormed_cases :: Array IllFormedSpec
illFormed_cases =
   [ { file: "bare_module.fld", expected_error: "module qual_lib is not a value" }
   , { file: "capture_redefined_class.fld", expected_error: "Duplicate class declaration: C" }
   , { file: "constr_dup_keyword.fld", expected_error: "Class Coord keyword fields mismatch: expected (\"x\" : \"y\" : Nil), got (\"x\" : \"x\" : \"y\" : Nil)" }
   , { file: "construct_non_leaf.fld", expected_error: "Cannot construct non-leaf class: Base" }
   , { file: "dict_attr.fld", expected_error: "Found { a: 1 }, expected object" }
   , { file: "extend_imported_class.fld", expected_error: "Cannot extend imported class: Base" }
   , { file: "from_import_arity.fld", expected_error: "Derived expects 2 argument(s); got 1" }
   , { file: "from_import_bad_ancestor.fld", expected_error: "Unbound name: z\nChecking module bad_pkg" }
   , { file: "from_import_loads_ancestor.fld", expected_error: "AssertionError" }
   , { file: "from_import_selective.fld", expected_error: "Unbound name: bar" }
   , { file: "from_import_unassigned.fld", expected_error: "Not definitely assigned: x" }
   , { file: "import_bad_ancestor.fld", expected_error: "Unbound name: z\nChecking module bad_pkg" }
   , { file: "import_cycle.fld", expected_error: "import cycle: cyc_a -> cyc_b -> cyc_a" }
   , { file: "match_exhaustive_assign.fld", expected_error: "Not definitely assigned: result" }
   , { file: "match_non_leaf.fld", expected_error: "Cannot match non-leaf class: Base" }
   , { file: "match_partial_def.fld", expected_error: "Not definitely assigned: result" }
   , { file: "module_returns.fld", expected_error: "Module body cannot return\nChecking module return_mod" }
   , { file: "non_contiguous_def.fld", expected_error: "Non-contiguous clauses for: f" }
   , { file: "own_descendant_import.fld", expected_error: "Module od_pkg cannot import its own descendant od_pkg.sub\nChecking module od_pkg" }
   , { file: "qualified_class_unknown.fld", expected_error: "Unknown dataclass: shape_lib.Missing" }
   , { file: "reexport_from_import.fld", expected_error: "Cannot import name foo from module reexport_mid" }
   , { file: "reexport_import_alias.fld", expected_error: "Cannot import name attr_lib from module alias_mid" }
   , { file: "self_import.fld", expected_error: "import cycle: selfy -> selfy" }
   , { file: "submodule_name_clash.fld", expected_error: "Submodule name clash in module clash_pkg: sub\nChecking module clash_pkg" }
   , { file: "submodule_self_import.fld", expected_error: "import cycle: ssi.b -> ssi.b" }
   , { file: "subscript_non_dict.fld", expected_error: "Found Point(1, 2), expected dict or matrix" }
   , { file: "use_before_import.fld", expected_error: "\"ParseError on line 2, column 6:\\nimports must precede statements\"\nLoading module use_before_import_mod" }
   ]

-- Run with test/lib/predefined on search path
shadow_cases :: Array IllFormedSpec
shadow_cases =
   [ { file: "predefined_shadowed.fld", expected_error: "Predefined module cannot have a source file: math" }
   ]
