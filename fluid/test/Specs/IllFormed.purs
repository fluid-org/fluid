module Test.Specs.IllFormed where

import Test.Util.Suite (IllFormedSpec)

-- Spec-derived (PurePy corpus): each entry corresponds to a test in
-- pure-py-spec/test/ill-formed/semantic.
-- Fluid-specific ill-formed cases (no PurePy correspondent).
illFormed_cases :: Array IllFormedSpec
illFormed_cases =
   [ { file: "bare_module.fld", expected_error: "module qual_lib is not a value" }
   , { file: "capture_redefined_class.fld", expected_error: "Duplicate class declaration: C" }
   , { file: "constr_dup_keyword.fld", expected_error: "Class Coord keyword fields mismatch: expected (\"x\" : \"y\" : Nil), got (\"x\" : \"x\" : \"y\" : Nil)" }
   , { file: "dict_attr.fld", expected_error: "Found {\"a\": 1}, expected object" }
   , { file: "extend_imported_class.fld", expected_error: "Cannot extend imported class: Base" }
   , { file: "from_import_arity.fld", expected_error: "Derived expects 2 argument(s); got 1" }
   , { file: "from_import_bad_ancestor.fld", expected_error: "Unbound name: z\nChecking module bad_pkg" }
   , { file: "from_import_loads_ancestor.fld", expected_error: "AssertionError" }
   , { file: "from_import_selective.fld", expected_error: "Unbound name: bar" }
   , { file: "from_import_unassigned.fld", expected_error: "Not definitely assigned: x" }
   , { file: "import_bad_ancestor.fld", expected_error: "Unbound name: z\nChecking module bad_pkg" }
   , { file: "import_cycle.fld", expected_error: "import cycle: cyc_a -> cyc_b -> cyc_a" }
   , { file: "match_exhaustive_assign.fld", expected_error: "Not definitely assigned: result" }
   , { file: "match_partial_def.fld", expected_error: "Not definitely assigned: result" }
   , { file: "module_returns.fld", expected_error: "Module body cannot return\nChecking module return_mod" }
   , { file: "non_contiguous_def.fld", expected_error: "Non-contiguous clauses for: f" }
   , { file: "own_descendant_import.fld", expected_error: "Module od_pkg cannot import its own descendant od_pkg.sub\nChecking module od_pkg" }
   , { file: "qualified_class_unknown.fld", expected_error: "module shape_lib has no member Missing" }
   , { file: "range_pattern.fld", expected_error: "range not permitted in a constructor pattern" }
   , { file: "reexport_from_import.fld", expected_error: "Cannot import name foo from module reexport_mid" }
   , { file: "reexport_import_alias.fld", expected_error: "Cannot import name attr_lib from module alias_mid" }
   , { file: "self_import.fld", expected_error: "import cycle: selfy -> selfy" }
   , { file: "submodule_name_clash.fld", expected_error: "Submodule name clash in module clash_pkg: sub\nChecking module clash_pkg" }
   , { file: "eq_nan_container.fld", expected_error: "Cannot compare nan with nan in container\nIn ==" }
   , { file: "matrix_dim_type.fld", expected_error: "Found (2, \"a\"), expected pair of int" }
   , { file: "submodule_self_import.fld", expected_error: "import cycle: ssi.b -> ssi.b" }
   , { file: "subscript_matrix_out_of_range.fld", expected_error: "Index (2, 0) out of range" }
   , { file: "subscript_non_dict.fld", expected_error: "Found Point(1, 2), expected list, tuple, str, dict or matrix" }
   , { file: "use_before_import.fld", expected_error: "\"ParseError on line 2, column 6:\\nimports must precede statements\"\nLoading module use_before_import_mod" }
   ]

-- Run with test/lib/predefined on search path
shadow_cases :: Array IllFormedSpec
shadow_cases =
   [ { file: "predefined_shadowed.fld", expected_error: "Predefined module cannot have a source file: math" }
   ]
