window.BENCHMARK_DATA = {
  "lastUpdate": 1725438442600,
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
      }
    ]
  }
}