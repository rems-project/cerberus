window.BENCHMARK_DATA = {
  "lastUpdate": 1727085845984,
  "repoUrl": "https://github.com/rems-project/cerberus",
  "entries": {
    "CN Benchmarks": [
      {
        "commit": {
          "author": {
            "email": "jprider63@users.noreply.github.com",
            "name": "JP",
            "username": "jprider63"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6efbb42a28aaaa046433bcec400a4268697abbe8",
          "message": "Add benchmarking CI that generates graphs on updates to master (#544)\n\nThis PR adds a CI workflow that generates performance graphs on every update to master. It stores the data as json in the `gh-pages` branch and renders the graphs on a Github Page. Here's [an example](https://galoisinc.github.io/cerberus/dev/bench/) of what this looks like with [dummy data](https://github.com/GaloisInc/cerberus/blob/gh-pages/dev/bench/data.js). \r\n\r\nThis currently runs `cn` on all the .c files in the test suite. Eventually, we probably want to make a proper benchmark suite using something like [Core_bench](https://blog.janestreet.com/core_bench-micro-benchmarking-for-ocaml/).\r\n\r\nIt relies upon the existence of the (currently empty) `gh-pages` branch.\r\n\r\nImplements part of rems-project/cn-tutorial/issues/54.",
          "timestamp": "2024-08-29T10:40:16+01:00",
          "tree_id": "c2a37af22457695bc2a9558b11bcc42aaf6e9661",
          "url": "https://github.com/rems-project/cerberus/commit/6efbb42a28aaaa046433bcec400a4268697abbe8"
        },
        "date": 1724924701577,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.98,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.8,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.89,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.9,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.24,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "e33539d0bc5773fde8525c2090a8446b9e0cc394",
          "message": "CN: Generalise cnnames\n\nThis commit generalises CN names to work with variables and predicates,\nnot just functions. It also exposes the `Alloc` allocation\ntoken/predicate and the `allocs` variable in the user-facing specs to\n(a) prepare for upcoming VIP related features and (b) test the\nimplementation of first sentence.",
          "timestamp": "2024-08-29T13:31:11+01:00",
          "tree_id": "9ca2aef6b4c5e650b73eb5c3127592b53998a58a",
          "url": "https://github.com/rems-project/cerberus/commit/e33539d0bc5773fde8525c2090a8446b9e0cc394"
        },
        "date": 1724934962782,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.85,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.94,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 17.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 13.86,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 7.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.24,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ZippeyKeys12@gmail.com",
            "name": "Zain K Aamer",
            "username": "ZippeyKeys12"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5f6325a8d3aa866a2888488c8cb0c9852c272bba",
          "message": "[CN-Exec] Minor changes to runtime library to accomodate testing (#542)\n\n* [CN-Exec] Runtime library include guards\r\n\r\n* [CN-Exec] C++ header compatibility\r\n\r\n* [CN-Exec] Allow setting exit callback\r\n\r\n* [CN-Exec] Make `cn_exit` static",
          "timestamp": "2024-08-30T17:02:07+01:00",
          "tree_id": "ce407c039d15cc9f8c1d98e355c3124e2bdadc65",
          "url": "https://github.com/rems-project/cerberus/commit/5f6325a8d3aa866a2888488c8cb0c9852c272bba"
        },
        "date": 1725034020978,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.98,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.75,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.95,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 13.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.8,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "adb1e5a768ad6fdcc2d6b8cef5f2c22646b5e13c",
          "message": "CN VIP: Add allocation history constraints\n\nThis commit enables (under the `--vip` flag) the Create memory action in\nCN adding a constraint to the `allocs` allocation history variable to\nmap the newly allocated pointer's allocation ID to the appropriate base\nand length.\n\nThis change is underneath a flag because it is not backwards compatiable\nin the presence of more than one create (of a different adress or size)\nbecause in the solver, all allocation IDs are mapped to unit, meaning\nadding the second constraint makes the context inconsistent and\nterminates type checking early.\n\nAs a result, the test suite is now run with the `--vip` flag enabled (so\nthat new features can be tested).  Note that the tutorial remains\nrunning without the `--vip` flags (and should not yet be using any of\nthe new featuers), and so any backwards compatibility issues will be\ncaught there.",
          "timestamp": "2024-09-02T12:07:34+01:00",
          "tree_id": "27703947ba4360d436beda64da2db13c58645169",
          "url": "https://github.com/rems-project/cerberus/commit/adb1e5a768ad6fdcc2d6b8cef5f2c22646b5e13c"
        },
        "date": 1725275588563,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.97,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.87,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.81,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.75,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "21b567000649aa6969696982a23e328d142a061c",
          "message": "CN VIP: Add support for ptr diff\n\nThis commit adds support for the VIP ptr diff rule, which requires that\nboth pointers come from the same live allocation.\n\nTo accommodate this without excessive annotation burden, it does so by\n(a) inferring `base <= (u64) p <= (u64) p + sizeof(ct) <= base + len`\nfor `{ base, len } = allocs[(alloc_id)p]` from `Owned<ct>(p)` and (b)\naccepting an `Owned<ct>(p)` when looking for a `Alloc(q)` if `(alloc_id)\nq == (alloc_id) p` and `(u64) p <= (u64) q <= (u64) p + sizeof(ct)`.\n\nIt only does this for pointer difference for now (later, it will be used\nfor pointer relational operators, copy_alloc_id and integer to pointer\nround-trip casts) with a special flag `alloc_or_owned` in the resource\ninference algorithm.",
          "timestamp": "2024-09-04T09:22:12+01:00",
          "tree_id": "18cfd12576d1123f5b07d7c9cab71cfb7c655fcc",
          "url": "https://github.com/rems-project/cerberus/commit/21b567000649aa6969696982a23e328d142a061c"
        },
        "date": 1725438441332,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.8,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.81,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.7,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.82,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.24,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "06271c2c1baee060dcb02319e7e5d6c05121a1f2",
          "message": "CN VIP: Generalise ptr diff support\n\nThis commit generalises the support for pointer subtraction by\n(a) working around an pointer representation quirk (b) working around\nanother Z3 bug by extending the simplifier (c) removing an unnecessary\nconstraint check from the live allocation check.\n\nSometimes we may wish to write `Owned(array_shift(p, x))`, and because\nof the solver represenation of array_shifting, the solver cannot\nconclude that `has_alloc_id(array_shift(p,x))` implies `has_alloc_id(p)`\n(e.g. p == NULL and has_alloc_id(default<Loc>) are possible). So,\nthe smart constructor for `has_alloc_id` does this for us syntactically.\nIf this happens semantically, then the user will just need to fix their\nspecs - this is mostly just so that deriving non-null constraints from\nOwneds still works as one would expect.\n\nThe Z3 bug is basically not being able to figure out that `(p + 2) - 2\n== p` for a pointer p (so the + is actually an array_shift), so the\nsimplifier takes care of that.\n\nThere is no need to do a bounds check in the resource loop since that is\nalways done in the check.ml as part of the typing rule - the previous\ncode was too restrictive (you can validly learn the allocation is live\neven in the requested pointer doesn't fall in the footprint of an Owned\nin the context).",
          "timestamp": "2024-09-04T12:37:59+01:00",
          "tree_id": "84d86f2d3820196a9e693a3e0ea8f51ac21a532d",
          "url": "https://github.com/rems-project/cerberus/commit/06271c2c1baee060dcb02319e7e5d6c05121a1f2"
        },
        "date": 1725450156709,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.98,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 15.97,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.81,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "368ac5af0c2d78d4ce18239f55791eefb8a6d003",
          "message": "CN: Refactor resourceInference.ml (#557)\n\nThis file removes a bunch of unnecessary `open Modules` from the resource inference file and also adds an `.mli` file for it.",
          "timestamp": "2024-09-04T13:43:03+01:00",
          "tree_id": "4a81ec53d3b748b68a646262a30f2690f7604dac",
          "url": "https://github.com/rems-project/cerberus/commit/368ac5af0c2d78d4ce18239f55791eefb8a6d003"
        },
        "date": 1725454085542,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.75,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 15.86,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.76,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "26858592+rbanerjee20@users.noreply.github.com",
            "name": "Rini Banerjee",
            "username": "rbanerjee20"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2c23781e7c6b012e99336b4498bacecdacc2e7ce",
          "message": "[CN-exec] Add `instrument` subcommand (#552)\n\n* CN-exec: Start work on executable spec subcommand\r\n\r\n* CN-exec: Finish adding runtime test subcommand and separate from verify subcommand\r\n\r\n* tweak\r\n\r\n* CN-exec: remove executable_spec_enabled flag set from verify subcommand\r\n\r\n* Update test gen tests to use runtime-test instead of verify\r\n\r\n* Address review comments\r\n\r\n* format\r\n\r\n* clean up Filename module usage\r\n\r\n* Update subcommand name to instrument",
          "timestamp": "2024-09-04T16:13:49+01:00",
          "tree_id": "c5fcf738fe29265a27762385a5bd9739e49d6739",
          "url": "https://github.com/rems-project/cerberus/commit/2c23781e7c6b012e99336b4498bacecdacc2e7ce"
        },
        "date": 1725463111673,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.76,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.89,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.87,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "26858592+rbanerjee20@users.noreply.github.com",
            "name": "Rini Banerjee",
            "username": "rbanerjee20"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "295a3b5ffc55c231d24af5be7cc3493243fec1d8",
          "message": "[CN-exec] Remove (some) unnecessary allocations from CN runtime library (#558)\n\nUpdate CN runtime library (runtime/libcn) to represent CN basetypes as pointers to C structs, with each C struct containing a single value of the relevant C type as its member. Previously this struct member was a *pointer* to the relevant C type, requiring some unnecessary allocations to be made throughout the runtime library. Aims to improve performance ever so slightly",
          "timestamp": "2024-09-04T18:28:06+01:00",
          "tree_id": "f9f8e16bb30174f2be2b3bd6e1515d4c2685d1f1",
          "url": "https://github.com/rems-project/cerberus/commit/295a3b5ffc55c231d24af5be7cc3493243fec1d8"
        },
        "date": 1725471176544,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.95,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.78,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.21,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "d4f79b654b85ce0e9153fa3c6d42f7c02fda9902",
          "message": "CN: Combine the base types\n\nThis commit follows-through on the previous one by removing\nsurfaceBaseTypes.ml and switching existing usages to the\n`Surface` module in `BaseTypes`.",
          "timestamp": "2024-09-04T22:09:44+01:00",
          "tree_id": "adbcc6cf8949464baacf9a3781322555224b5f4c",
          "url": "https://github.com/rems-project/cerberus/commit/d4f79b654b85ce0e9153fa3c6d42f7c02fda9902"
        },
        "date": 1725484485334,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.95,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.95,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.76,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.29,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ZippeyKeys12@gmail.com",
            "name": "Zain Aamer",
            "username": "ZippeyKeys12"
          },
          "committer": {
            "email": "ZippeyKeys12@gmail.com",
            "name": "Zain K Aamer",
            "username": "ZippeyKeys12"
          },
          "distinct": true,
          "id": "5151a4fe4af6278548c3fb79d787afcad29e820b",
          "message": "[CN] Flip `WellTyped.use_ity` default\n\nNow aligns with commit ac79195",
          "timestamp": "2024-09-06T01:18:40-04:00",
          "tree_id": "6eeace646c2d87dd326f90694012fa9b0cb6187a",
          "url": "https://github.com/rems-project/cerberus/commit/5151a4fe4af6278548c3fb79d787afcad29e820b"
        },
        "date": 1725600201119,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.76,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.86,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.2,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "cp526@cam.ac.uk",
            "name": "Christopher Pulte",
            "username": "cp526"
          },
          "committer": {
            "email": "cp526@cam.ac.uk",
            "name": "Christopher Pulte",
            "username": "cp526"
          },
          "distinct": true,
          "id": "cf6d7608d14742828c4a11339373b026f2d22ab0",
          "message": "fix formatting",
          "timestamp": "2024-09-11T14:05:25+01:00",
          "tree_id": "db79cb55726c70f2a53f6cc38a41781b3402b236",
          "url": "https://github.com/rems-project/cerberus/commit/cf6d7608d14742828c4a11339373b026f2d22ab0"
        },
        "date": 1726060256702,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.7,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 11.97,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 5.94,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.76,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 17.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.9,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.81,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.59,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.95,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.7,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.39,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ZippeyKeys12@gmail.com",
            "name": "Zain K Aamer",
            "username": "ZippeyKeys12"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dcdc0edecaaf0b160670cbeff4c792ef4503d417",
          "message": "[CN-Exec] Adding `cn_internal_to_ail.mli` (#561)\n\n* [AIL] Name `sigma` member types\r\n\r\n* [CN-Exec] Minor cleanup\r\n\r\n* [CN-Exec] Add `cn_internal_to_ail.mli`",
          "timestamp": "2024-09-11T14:42:57-04:00",
          "tree_id": "1ada19f081bd2619bc593339ddb9199c9b872219",
          "url": "https://github.com/rems-project/cerberus/commit/dcdc0edecaaf0b160670cbeff4c792ef4503d417"
        },
        "date": 1726080493337,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 13.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 18.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.96,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.83,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.89,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.45,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "iavor.diatchki@gmail.com",
            "name": "Iavor S. Diatchki",
            "username": "yav"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5df271d841dad6429f5084628116680577d5f1d8",
          "message": "Fixes #563 (#570)",
          "timestamp": "2024-09-11T14:53:54-07:00",
          "tree_id": "757d6cb9a19514d562fd7ba5e7ee41d20c628691",
          "url": "https://github.com/rems-project/cerberus/commit/5df271d841dad6429f5084628116680577d5f1d8"
        },
        "date": 1726091993399,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 13.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 11.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 1.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 18.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.96,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.7,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.82,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.48,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.54,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.46,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "cp526@cam.ac.uk",
            "name": "Christopher Pulte",
            "username": "cp526"
          },
          "committer": {
            "email": "cp526@cam.ac.uk",
            "name": "Christopher Pulte",
            "username": "cp526"
          },
          "distinct": true,
          "id": "9a71b713ce1e3034bfea88a31da3dff4f2113165",
          "message": "exclude those new tests from runtime checks, because something is going wrong",
          "timestamp": "2024-09-12T00:45:26+01:00",
          "tree_id": "6f8641ba1397eea861ed7b6e5a65deaa311f006f",
          "url": "https://github.com/rems-project/cerberus/commit/9a71b713ce1e3034bfea88a31da3dff4f2113165"
        },
        "date": 1726098640814,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.96,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 16.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.71,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1.01,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.78,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.87,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.61,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.36,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "dc_mak@outlook.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "committer": {
            "email": "dc-mak@users.noreply.github.com",
            "name": "Dhruv Makwana",
            "username": "dc-mak"
          },
          "distinct": true,
          "id": "58560003604b13df463f5ac8be9a339690d90719",
          "message": "CN VIP: Refactor live alloc bounds check",
          "timestamp": "2024-09-12T06:42:34+01:00",
          "tree_id": "fba1dc87c910bb420ff71817e6320e55162900e6",
          "url": "https://github.com/rems-project/cerberus/commit/58560003604b13df463f5ac8be9a339690d90719"
        },
        "date": 1726120042373,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 12.84,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 6.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 10.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.97,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.74,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 17.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 2.7,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 1.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.78,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 1.67,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 5.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 1.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 1.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.52,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 1.9,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.27,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.3,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 1.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 1.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 1.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 3.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.51,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 2.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 1.36,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "sainatidaniel@gmail.com",
            "name": "Daniel Sainati",
            "username": "dsainati1"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "3c931f20fb8c654fecd05a5ba6dd7f5d20383364",
          "message": "[CN] Use only one global model evaluator solver (#547)\n\n* use only one global model evaluator solver\r\n\r\n* respond to review\r\n\r\n* WIP: load and unload models\r\n\r\n* add test for hitting file descriptor limit\r\n\r\n* load and unload models as needed\r\n\r\n* increase test timeout\r\n\r\n* increase test timeout",
          "timestamp": "2024-09-12T14:04:21-07:00",
          "tree_id": "2757c9a7adceeab4186fed8899eeeb482abf502e",
          "url": "https://github.com/rems-project/cerberus/commit/3c931f20fb8c654fecd05a5ba6dd7f5d20383364"
        },
        "date": 1726175305305,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 9.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 2.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 2.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.8,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 1.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.83,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.6,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 23.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.38,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "kayvan.memarian@cl.cam.ac.uk",
            "name": "Kayvan Memarian",
            "username": "kmemarian"
          },
          "committer": {
            "email": "kmemarian@users.noreply.github.com",
            "name": "Kayvan Memarian",
            "username": "kmemarian"
          },
          "distinct": true,
          "id": "d218bd4aa01d20cc544249d1922e7e27c3eb6153",
          "message": "CHERI: adding ci tests for the new elaboration of readonly objects",
          "timestamp": "2024-09-15T01:12:34+01:00",
          "tree_id": "58d7fe9a13d267c733c317ff8a00f1ac9c64b423",
          "url": "https://github.com/rems-project/cerberus/commit/d218bd4aa01d20cc544249d1922e7e27c3eb6153"
        },
        "date": 1726359393583,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 9,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 2.46,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 2.68,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.73,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 1.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 22.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.35,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "lord@crocodile.org",
            "name": "Vadim Zaliva",
            "username": "vzaliva"
          },
          "committer": {
            "email": "kmemarian@users.noreply.github.com",
            "name": "Kayvan Memarian",
            "username": "kmemarian"
          },
          "distinct": true,
          "id": "7c826acd18a828059d0d549f88515807a62c1319",
          "message": "new UB: CHERI_UB_ZeroLength. flagged in cheri_bounds_set intrinsic",
          "timestamp": "2024-09-15T02:32:54+01:00",
          "tree_id": "c3c8612970b9b07ac455581883972000223fde99",
          "url": "https://github.com/rems-project/cerberus/commit/7c826acd18a828059d0d549f88515807a62c1319"
        },
        "date": 1726366392238,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 8.99,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 2.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 2.66,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.78,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 1.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.22,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.31,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.79,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.57,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 22.64,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.35,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ZippeyKeys12@gmail.com",
            "name": "Zain K Aamer",
            "username": "ZippeyKeys12"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2d01aed05d10524e1db00126ff026d2b7ac96661",
          "message": "[CN-Exec] Conversions from C types for CN values (#578)",
          "timestamp": "2024-09-17T11:08:10+01:00",
          "tree_id": "ca80bba0f409d3d4b467a6c109ed847a318d027b",
          "url": "https://github.com/rems-project/cerberus/commit/2d01aed05d10524e1db00126ff026d2b7ac96661"
        },
        "date": 1726567948587,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 9.29,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 3.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 3.55,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 4.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.82,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.72,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 2.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.43,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.82,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 23.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.35,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "26858592+rbanerjee20@users.noreply.github.com",
            "name": "Rini Banerjee",
            "username": "rbanerjee20"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0b1d3796f88d1733c6a744ee628b07d70f00344e",
          "message": "[CN-exec] Fix CN map set (#579)\n\nChange runtime translation of CN map set to always deep-copy the map passed in and then to update the copy of the map. Previously was an in-place update of the map, which was causing problems in swap_array.c in the CN tutorial.",
          "timestamp": "2024-09-17T11:17:12+01:00",
          "tree_id": "cbe7873516ab3d9950f6433057bceb74746c3d4a",
          "url": "https://github.com/rems-project/cerberus/commit/0b1d3796f88d1733c6a744ee628b07d70f00344e"
        },
        "date": 1726568489797,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.38,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 3.28,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 9.23,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.81,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.63,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 23.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.36,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 2.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 3.77,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.41,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.42,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.85,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.9,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.96,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.12,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "vz231@cl.cam.ac.uk",
            "name": "Vadim Zaliva",
            "username": "vzaliva"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a09536a1160f7d2ee3ba549824e15a46e0e7d583",
          "message": "CHERI: fixing last Admit with new lemmas from `coq-cheri-capabilies` (#580)\n\n* adjustements to new coq-cheri-capabilities API.\r\n\r\n* adjusted encode_decode lemma\r\n\r\n* CHERI: fixing last Admit with new lemmas from `coq-cheri-capabilies`",
          "timestamp": "2024-09-17T18:44:06+01:00",
          "tree_id": "e8247912fc1cfbaa2eafa3607fb5396b8ae38e51",
          "url": "https://github.com/rems-project/cerberus/commit/a09536a1160f7d2ee3ba549824e15a46e0e7d583"
        },
        "date": 1726597368132,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 2.49,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 8.21,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.47,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.8,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 22.83,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.16,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.44,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 1.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 2.98,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.24,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.82,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.56,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.11,
            "unit": "Seconds"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "james@galois.com",
            "name": "James Parker",
            "username": "jprider63"
          },
          "committer": {
            "email": "cp526@cam.ac.uk",
            "name": "Christopher Pulte",
            "username": "cp526"
          },
          "distinct": true,
          "id": "b9d2a5e5f33b9363acc323f47d1bf980915eebdf",
          "message": "Track total benchmark time in CI",
          "timestamp": "2024-09-23T10:59:40+01:00",
          "tree_id": "ff56a7831e85b79ff5e946e22c5949ca7f5359af",
          "url": "https://github.com/rems-project/cerberus/commit/b9d2a5e5f33b9363acc323f47d1bf980915eebdf"
        },
        "date": 1727085845274,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "Total benchmark time",
            "value": 62.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_union.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_pattern_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/block_type.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ffs.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies2.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/extract_verbose.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz.c",
            "value": 0.37,
            "unit": "Seconds"
          },
          {
            "name": "./cn/disj_nonnull.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_types_compatible.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/assert_on_toplevel.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/redundant_pattern.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_auto_mutual_dt/tree16.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_partial_map/tree16.c",
            "value": 2.53,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree16/as_mutual_dt/tree16.c",
            "value": 8.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent3.error.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent2.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_extern.c",
            "value": 0.5,
            "unit": "Seconds"
          },
          {
            "name": "./cn/increments.c",
            "value": 0.19,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_shift.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_three_opts.c",
            "value": 0.83,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_record2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.error.c",
            "value": 0.2,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_token.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.error.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_precedence.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_literal_type.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.c",
            "value": 0.58,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_type.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mask_ptr.c",
            "value": 0.17,
            "unit": "Seconds"
          },
          {
            "name": "./cn/and_or_precedence.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_sign.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_arr.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_precedence.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/match.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_pipes.error.c",
            "value": 23.65,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def03.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_function_call.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def02.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/max_min_consts.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/enum_and_and.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_case_ranges.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/merging_arrays.error.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_choose.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_array_shift.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_recursion.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/split_case.c",
            "value": 0.33,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_eq2.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies3.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arith_type.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_postcond.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args4.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simplify_add_0.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tree_rev01.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_or.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_after_curly_brace.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/simple_loop.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions1.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/f.c",
            "value": 0.45,
            "unit": "Seconds"
          },
          {
            "name": "./cn/multifile/g.c",
            "value": 0.32,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id_ptr_neq.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap_pair.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource_indirect.error.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/inconsistent.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ghost_pointer_to_bitvec_cast.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def04.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_return_size.error.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/list_rev01.c",
            "value": 0.35,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_left.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/append.c",
            "value": 1.78,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_with_constants.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pred_def01.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_typedef.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/alloc_create.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/use_enum.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args2.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/swap.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/missing_resource.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_col.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mergesort.c",
            "value": 3.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cnfunction_mismatched_args1.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_uintptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_int_cast.error.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_char_cast.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/left_shift_const.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/shift_diff_sz.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/get_from_array.c",
            "value": 0.4,
            "unit": "Seconds"
          },
          {
            "name": "./cn/memcpy.c",
            "value": 0.39,
            "unit": "Seconds"
          },
          {
            "name": "./cn/void_star_arg.c",
            "value": 0.25,
            "unit": "Seconds"
          },
          {
            "name": "./cn/previously_inconsistent_assumptions2.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_unsigned_int_cast.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/tag_defs.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/duplicate_datatype_var.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_constructor_user.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_compl_precedence.c",
            "value": 0.05,
            "unit": "Seconds"
          },
          {
            "name": "./cn/forloop_with_decl.c",
            "value": 0.12,
            "unit": "Seconds"
          },
          {
            "name": "./cn/incomplete_match.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/has_alloc_id.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/cn_inline.c",
            "value": 0.18,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_return_size.error.c",
            "value": 2.26,
            "unit": "Seconds"
          },
          {
            "name": "./cn/spec_null_shift.error.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/map_set.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unsupported_flexible_array_member.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/reverse.error.c",
            "value": 0.83,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unary_negation.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/failing_precond.error.c",
            "value": 0.03,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_casting.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/type_synonym.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_by_0.error.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/magic_comment_not_closed.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/struct_updates2.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_addrs_cn_stmt.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/lexer_hack_parse.error.c",
            "value": 0.02,
            "unit": "Seconds"
          },
          {
            "name": "./cn/doubling.c",
            "value": 0.1,
            "unit": "Seconds"
          },
          {
            "name": "./cn/copy_alloc_id.error.c",
            "value": 0.13,
            "unit": "Seconds"
          },
          {
            "name": "./cn/gnu_ctz.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/pointer_to_intptr_t_cast.c",
            "value": 0.06,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division_with_constants.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/builtin_ctz_val.c",
            "value": 0.14,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff.c",
            "value": 0.69,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ptr_diff2.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/b_xor.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/arrow_access.c",
            "value": 0.15,
            "unit": "Seconds"
          },
          {
            "name": "./cn/ownership_at_negative_index.c",
            "value": 0.07,
            "unit": "Seconds"
          },
          {
            "name": "./cn/division.c",
            "value": 0.08,
            "unit": "Seconds"
          },
          {
            "name": "./cn/fun_ptr_known.c",
            "value": 0.34,
            "unit": "Seconds"
          },
          {
            "name": "./cn/implies_associativity.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mod_precedence.c",
            "value": 0.11,
            "unit": "Seconds"
          },
          {
            "name": "./cn/mutual_rec/mutual_rec.c",
            "value": 3.62,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bitwise_and_type_right.error.c",
            "value": 0.04,
            "unit": "Seconds"
          },
          {
            "name": "./cn/unconstrained_ptr_eq2.error.c",
            "value": 0.09,
            "unit": "Seconds"
          },
          {
            "name": "./cn/bad_resource_var.error.c",
            "value": 0.12,
            "unit": "Seconds"
          }
        ]
      }
    ]
  }
}