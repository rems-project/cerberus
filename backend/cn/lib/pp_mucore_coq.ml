[@@@warning "-32-27-26"] (* Disable unused value warnings and unused variable warnings *)

open Cerb_pp_prelude
open Printf
module CF = Cerb_frontend
open CF
module P = PPrint
open Mucore

(* temporary debug option to supress printing of noisy locations *)
let debug_print_locations = false (* Set to true to print actual locations *)

let pp_cn_type_args = !^"_" ^^^ !^"_"

let pp_nat n = !^(string_of_int n)

let pp_Z z =
  if Z.lt z Z.zero then !^("(" ^ Z.to_string z ^ ")%Z") else !^(Z.to_string z ^ "%Z")


let pp_string s = !^("\"" ^ String.escaped s ^ "\"")

let pp_list pp_elem xs =
  !^"["
  ^^^ List.fold_left
        (fun acc x ->
          if acc == P.empty then
            pp_elem x
          else
            acc ^^ !^";" ^^^ pp_elem x)
        P.empty
        xs
  ^^^ !^"]"


let pp_tuple l = P.parens (P.separate !^"," l)

let pp_pair p1 p2 (a, b) = pp_tuple [ p1 a; p2 b ]

let pp_option pp_elem = function
  | None -> !^"None"
  | Some x -> !^"(Some" ^^^ pp_elem x ^^ !^")"


let pp_pmap
  fromlist_fun
  (pp_key : 'a -> P.document)
  (pp_value : 'b -> P.document)
  (m : ('a, 'b) Pmap.map)
  =
  P.parens (!^fromlist_fun ^^^ pp_list (pp_pair pp_key pp_value) (Pmap.bindings_list m))


(* Helper to print Coq definitions *)
let coq_def name args body =
  !^"Definition"
  ^^^ !^name
  ^^^ args
  ^^^ !^":="
  ^^^ body
  ^^ !^"."
  ^^ P.hardline
  ^^ P.hardline


let coq_notation name args body =
  !^"Notation" ^^^ !^("\"" ^ name ^ "\"") ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."


let pp_record fields =
  !^"{|"
  ^^^ P.separate
        (!^";" ^^ P.break 1)
        (List.map (fun (name, value) -> !^(name ^ " :=") ^^^ value) fields)
  ^^^ !^"|}"


let pp_constructor name args =
  if List.length args = 0 then
    !^name
  else
    !^"(" ^^ !^name ^^^ !^"_" ^^^ P.separate_map !^" " (fun x -> x) args ^^ !^")"


let pp_undefined_behaviour = function
  | Undefined.DUMMY str -> pp_constructor "DUMMY" [ !^(sprintf "%S" str) ]
  | Undefined.UB_unspecified_lvalue -> pp_constructor "UB_unspecified_lvalue" []
  | Undefined.UB_std_omission om ->
    pp_constructor
      "UB_std_omission"
      [ (match om with
         | UB_OMIT_memcpy_non_object -> pp_constructor "UB_OMIT_memcpy_non_object" []
         | UB_OMIT_memcpy_out_of_bound -> pp_constructor "UB_OMIT_memcpy_out_of_bound" [])
      ]
  | Undefined.Invalid_format str ->
    pp_constructor "Invalid_format" [ !^(sprintf "%S" str) ]
  | Undefined.UB_CERB004_unspecified ctx ->
    pp_constructor
      "UB_CERB004_unspecified"
      [ (match ctx with
         | UB_unspec_equality_ptr_vs_NULL ->
           pp_constructor "UB_unspec_equality_ptr_vs_NULL" []
         | UB_unspec_equality_both_arith_or_ptr ->
           pp_constructor "UB_unspec_equality_both_arith_or_ptr" []
         | UB_unspec_pointer_add -> pp_constructor "UB_unspec_pointer_add" []
         | UB_unspec_pointer_sub -> pp_constructor "UB_unspec_pointer_sub" []
         | UB_unspec_conditional -> pp_constructor "UB_unspec_conditional" []
         | UB_unspec_copy_alloc_id -> pp_constructor "UB_unspec_copy_alloc_id" []
         | UB_unspec_rvalue_memberof -> pp_constructor "UB_unspec_rvalue_memberof" []
         | UB_unspec_memberofptr -> pp_constructor "UB_unspec_memberofptr" []
         | UB_unspec_do -> pp_constructor "UB_unspec_do" [])
      ]
  | Undefined.UB_CERB005_free_nullptr -> pp_constructor "UB_CERB005_free_nullptr" []
  | UB001 -> pp_constructor "UB001" []
  | UB002 -> pp_constructor "UB002" []
  | UB003 -> pp_constructor "UB003" []
  | UB004a_incorrect_main_return_type ->
    pp_constructor "UB004a_incorrect_main_return_type" []
  | UB004b_incorrect_main_argument1 -> pp_constructor "UB004b_incorrect_main_argument1" []
  | UB004c_incorrect_main_argument2 -> pp_constructor "UB004c_incorrect_main_argument2" []
  | UB004d_main_not_function -> pp_constructor "UB004d_main_not_function" []
  | UB005_data_race -> pp_constructor "UB005_data_race" []
  | UB006 -> pp_constructor "UB006" []
  | UB007 -> pp_constructor "UB007" []
  | UB008_multiple_linkage -> pp_constructor "UB008_multiple_linkage" []
  | UB009_outside_lifetime -> pp_constructor "UB009_outside_lifetime" []
  | UB010_pointer_to_dead_object -> pp_constructor "UB010_pointer_to_dead_object" []
  | UB011_use_indeterminate_automatic_object ->
    pp_constructor "UB011_use_indeterminate_automatic_object" []
  | UB_modifying_temporary_lifetime -> pp_constructor "UB_modifying_temporary_lifetime" []
  | UB012_lvalue_read_trap_representation ->
    pp_constructor "UB012_lvalue_read_trap_representation" []
  | UB013_lvalue_side_effect_trap_representation ->
    pp_constructor "UB013_lvalue_side_effect_trap_representation" []
  | UB014_unsupported_negative_zero -> pp_constructor "UB014_unsupported_negative_zero" []
  | UB015_incompatible_redeclaration ->
    pp_constructor "UB015_incompatible_redeclaration" []
  | UB016 -> pp_constructor "UB016" []
  | UB017_out_of_range_floating_integer_conversion ->
    pp_constructor "UB017_out_of_range_floating_integer_conversion" []
  | UB018 -> pp_constructor "UB018" []
  | UB019_lvalue_not_an_object -> pp_constructor "UB019_lvalue_not_an_object" []
  | UB020_nonarray_incomplete_lvalue_conversion ->
    pp_constructor "UB020_nonarray_incomplete_lvalue_conversion" []
  | UB021 -> pp_constructor "UB021" []
  | UB022_register_array_decay -> pp_constructor "UB022_register_array_decay" []
  | UB023 -> pp_constructor "UB023" []
  | UB024_out_of_range_pointer_to_integer_conversion ->
    pp_constructor "UB024_out_of_range_pointer_to_integer_conversion" []
  | UB025_misaligned_pointer_conversion ->
    pp_constructor "UB025_misaligned_pointer_conversion" []
  | UB026 -> pp_constructor "UB026" []
  | UB027 -> pp_constructor "UB027" []
  | UB028 -> pp_constructor "UB028" []
  | UB029 -> pp_constructor "UB029" []
  | UB030 -> pp_constructor "UB030" []
  | UB031 -> pp_constructor "UB031" []
  | UB032 -> pp_constructor "UB032" []
  | UB033_modifying_string_literal -> pp_constructor "UB033_modifying_string_literal" []
  | UB034 -> pp_constructor "UB034" []
  | UB035_unsequenced_race -> pp_constructor "UB035_unsequenced_race" []
  | UB036_exceptional_condition -> pp_constructor "UB036_exceptional_condition" []
  | UB037_illtyped_load -> pp_constructor "UB037_illtyped_load" []
  | UB038_number_of_args -> pp_constructor "UB038_number_of_args" []
  | UB039 -> pp_constructor "UB039" []
  | UB040 -> pp_constructor "UB040" []
  | UB041_function_not_compatible -> pp_constructor "UB041_function_not_compatible" []
  | UB042_access_atomic_structUnion_member ->
    pp_constructor "UB042_access_atomic_structUnion_member" []
  | UB043_indirection_invalid_value -> pp_constructor "UB043_indirection_invalid_value" []
  | UB044 -> pp_constructor "UB044" []
  | UB045a_division_by_zero -> pp_constructor "UB045a_division_by_zero" []
  | UB045b_modulo_by_zero -> pp_constructor "UB045b_modulo_by_zero" []
  | UB045c_quotient_not_representable ->
    pp_constructor "UB045c_quotient_not_representable" []
  | UB046_array_pointer_outside -> pp_constructor "UB046_array_pointer_outside" []
  | UB047a_array_pointer_addition_beyond_indirection ->
    pp_constructor "UB047a_array_pointer_addition_beyond_indirection" []
  | UB047b_array_pointer_subtraction_beyond_indirection ->
    pp_constructor "UB047b_array_pointer_subtraction_beyond_indirection" []
  | UB048_disjoint_array_pointers_subtraction ->
    pp_constructor "UB048_disjoint_array_pointers_subtraction" []
  | UB049 -> pp_constructor "UB049" []
  | UB050_pointers_subtraction_not_representable ->
    pp_constructor "UB050_pointers_subtraction_not_representable" []
  | UB051a_negative_shift -> pp_constructor "UB051a_negative_shift" []
  | UB51b_shift_too_large -> pp_constructor "UB51b_shift_too_large" []
  | UB052a_negative_left_shift -> pp_constructor "UB052a_negative_left_shift" []
  | UB052b_non_representable_left_shift ->
    pp_constructor "UB052b_non_representable_left_shift" []
  | UB053_distinct_aggregate_union_pointer_comparison ->
    pp_constructor "UB053_distinct_aggregate_union_pointer_comparison" []
  | UB054a_inexactly_overlapping_assignment ->
    pp_constructor "UB054a_inexactly_overlapping_assignment" []
  | UB054b_incompatible_overlapping_assignment ->
    pp_constructor "UB054b_incompatible_overlapping_assignment" []
  | UB055_invalid_integer_constant_expression ->
    pp_constructor "UB055_invalid_integer_constant_expression" []
  | UB056 -> pp_constructor "UB056" []
  | UB057 -> pp_constructor "UB057" []
  | UB058 -> pp_constructor "UB058" []
  | UB059_incomplete_no_linkage_identifier ->
    pp_constructor "UB059_incomplete_no_linkage_identifier" []
  | UB060_block_scope_function_with_storage_class ->
    pp_constructor "UB060_block_scope_function_with_storage_class" []
  | UB061_no_named_members -> pp_constructor "UB061_no_named_members" []
  | UB062 -> pp_constructor "UB062" []
  | UB063 -> pp_constructor "UB063" []
  | UB064_modifying_const -> pp_constructor "UB064_modifying_const" []
  | UB065 -> pp_constructor "UB065" []
  | UB066_qualified_function_specification ->
    pp_constructor "UB066_qualified_function_specification" []
  | UB067 -> pp_constructor "UB067" []
  | UB068 -> pp_constructor "UB068" []
  | UB069 -> pp_constructor "UB069" []
  | UB070_inline_not_defined -> pp_constructor "UB070_inline_not_defined" []
  | UB071_noreturn -> pp_constructor "UB071_noreturn" []
  | UB072_incompatible_alignment_specifiers ->
    pp_constructor "UB072_incompatible_alignment_specifiers" []
  | UB073 -> pp_constructor "UB073" []
  | UB074 -> pp_constructor "UB074" []
  | UB075 -> pp_constructor "UB075" []
  | UB076 -> pp_constructor "UB076" []
  | UB077 -> pp_constructor "UB077" []
  | UB078_modified_void_parameter -> pp_constructor "UB078_modified_void_parameter" []
  | UB079 -> pp_constructor "UB079" []
  | UB080 -> pp_constructor "UB080" []
  | UB081_scalar_initializer_not_single_expression ->
    pp_constructor "UB081_scalar_initializer_not_single_expression" []
  | UB082 -> pp_constructor "UB082" []
  | UB083 -> pp_constructor "UB083" []
  | UB084 -> pp_constructor "UB084" []
  | UB085 -> pp_constructor "UB085" []
  | UB086_incomplete_adjusted_parameter ->
    pp_constructor "UB086_incomplete_adjusted_parameter" []
  | UB087 -> pp_constructor "UB087" []
  | UB088_reached_end_of_function -> pp_constructor "UB088_reached_end_of_function" []
  | UB089_tentative_definition_internal_linkage ->
    pp_constructor "UB089_tentative_definition_internal_linkage" []
  | UB090 -> pp_constructor "UB090" []
  | UB091 -> pp_constructor "UB091" []
  | UB092 -> pp_constructor "UB092" []
  | UB093 -> pp_constructor "UB093" []
  | UB094 -> pp_constructor "UB094" []
  | UB095 -> pp_constructor "UB095" []
  | UB096 -> pp_constructor "UB096" []
  | UB097 -> pp_constructor "UB097" []
  | UB098 -> pp_constructor "UB098" []
  | UB099 -> pp_constructor "UB099" []
  | UB100 -> pp_constructor "UB100" []
  | UB101 -> pp_constructor "UB101" []
  | UB102 -> pp_constructor "UB102" []
  | UB103 -> pp_constructor "UB103" []
  | UB104 -> pp_constructor "UB104" []
  | UB105 -> pp_constructor "UB105" []
  | UB106 -> pp_constructor "UB106" []
  | UB107 -> pp_constructor "UB107" []
  | UB108 -> pp_constructor "UB108" []
  | UB109 -> pp_constructor "UB109" []
  | UB110 -> pp_constructor "UB110" []
  | UB111_illtyped_assert -> pp_constructor "UB111_illtyped_assert" []
  | UB112 -> pp_constructor "UB112" []
  | UB113 -> pp_constructor "UB113" []
  | UB114 -> pp_constructor "UB114" []
  | UB115 -> pp_constructor "UB115" []
  | UB116 -> pp_constructor "UB116" []
  | UB117 -> pp_constructor "UB117" []
  | UB118 -> pp_constructor "UB118" []
  | UB119 -> pp_constructor "UB119" []
  | UB120 -> pp_constructor "UB120" []
  | UB121 -> pp_constructor "UB121" []
  | UB122 -> pp_constructor "UB122" []
  | UB123 -> pp_constructor "UB123" []
  | UB124 -> pp_constructor "UB124" []
  | UB125 -> pp_constructor "UB125" []
  | UB126 -> pp_constructor "UB126" []
  | UB127 -> pp_constructor "UB127" []
  | UB128 -> pp_constructor "UB128" []
  | UB129 -> pp_constructor "UB129" []
  | UB130 -> pp_constructor "UB130" []
  | UB131 -> pp_constructor "UB131" []
  | UB132 -> pp_constructor "UB132" []
  | UB133 -> pp_constructor "UB133" []
  | UB134 -> pp_constructor "UB134" []
  | UB135 -> pp_constructor "UB135" []
  | UB136 -> pp_constructor "UB136" []
  | UB137 -> pp_constructor "UB137" []
  | UB138 -> pp_constructor "UB138" []
  | UB139 -> pp_constructor "UB139" []
  | UB140 -> pp_constructor "UB140" []
  | UB141 -> pp_constructor "UB141" []
  | UB142 -> pp_constructor "UB142" []
  | UB143 -> pp_constructor "UB143" []
  | UB144 -> pp_constructor "UB144" []
  | UB145 -> pp_constructor "UB145" []
  | UB146 -> pp_constructor "UB146" []
  | UB147 -> pp_constructor "UB147" []
  | UB148 -> pp_constructor "UB148" []
  | UB149 -> pp_constructor "UB149" []
  | UB150 -> pp_constructor "UB150" []
  | UB151 -> pp_constructor "UB151" []
  | UB152 -> pp_constructor "UB152" []
  | UB153a_insufficient_arguments_for_format ->
    pp_constructor "UB153a_insufficient_arguments_for_format" []
  | UB153b_illtyped_argument_for_format ->
    pp_constructor "UB153b_illtyped_argument_for_format" []
  | UB154 -> pp_constructor "UB154" []
  | UB155 -> pp_constructor "UB155" []
  | UB156 -> pp_constructor "UB156" []
  | UB157 -> pp_constructor "UB157" []
  | UB158_invalid_length_modifier -> pp_constructor "UB158_invalid_length_modifier" []
  | UB159 -> pp_constructor "UB159" []
  | UB160 -> pp_constructor "UB160" []
  | UB161 -> pp_constructor "UB161" []
  | UB162 -> pp_constructor "UB162" []
  | UB163 -> pp_constructor "UB163" []
  | UB164 -> pp_constructor "UB164" []
  | UB165 -> pp_constructor "UB165" []
  | UB166 -> pp_constructor "UB166" []
  | UB167 -> pp_constructor "UB167" []
  | UB168 -> pp_constructor "UB168" []
  | UB169 -> pp_constructor "UB169" []
  | UB170 -> pp_constructor "UB170" []
  | UB171 -> pp_constructor "UB171" []
  | UB172 -> pp_constructor "UB172" []
  | UB173 -> pp_constructor "UB173" []
  | UB174 -> pp_constructor "UB174" []
  | UB175 -> pp_constructor "UB175" []
  | UB176 -> pp_constructor "UB176" []
  | UB177 -> pp_constructor "UB177" []
  | UB178 -> pp_constructor "UB178" []
  | UB179a_non_matching_allocation_free ->
    pp_constructor "UB179a_non_matching_allocation_free" []
  | UB179b_dead_allocation_free -> pp_constructor "UB179b_dead_allocation_free" []
  | UB179c_non_matching_allocation_realloc ->
    pp_constructor "UB179c_non_matching_allocation_realloc" []
  | UB179d_dead_allocation_realloc -> pp_constructor "UB179d_dead_allocation_realloc" []
  | UB180 -> pp_constructor "UB180" []
  | UB181 -> pp_constructor "UB181" []
  | UB182 -> pp_constructor "UB182" []
  | UB183 -> pp_constructor "UB183" []
  | UB184 -> pp_constructor "UB184" []
  | UB185 -> pp_constructor "UB185" []
  | UB186 -> pp_constructor "UB186" []
  | UB187 -> pp_constructor "UB187" []
  | UB188 -> pp_constructor "UB188" []
  | UB189 -> pp_constructor "UB189" []
  | UB190 -> pp_constructor "UB190" []
  | UB191 -> pp_constructor "UB191" []
  | UB192 -> pp_constructor "UB192" []
  | UB193 -> pp_constructor "UB193" []
  | UB194 -> pp_constructor "UB194" []
  | UB195 -> pp_constructor "UB195" []
  | UB196 -> pp_constructor "UB196" []
  | UB197 -> pp_constructor "UB197" []
  | UB198 -> pp_constructor "UB198" []
  | UB199 -> pp_constructor "UB199" []
  | UB200 -> pp_constructor "UB200" []
  | UB201 -> pp_constructor "UB201" []
  | UB202 -> pp_constructor "UB202" []
  | UB203 -> pp_constructor "UB203" []
  | UB204_illtyped_Static_assert -> pp_constructor "UB204_illtyped_Static_assert" []
  | UB205_atomic_store_memorder -> pp_constructor "UB205_atomic_store_memorder" []
  | UB206_atomic_load_memorder -> pp_constructor "UB206_atomic_load_memorder" []
  | UB207_atomic_compare_exchange_memorder ->
    pp_constructor "UB207_atomic_compare_exchange_memorder" []
  | UB_CERB001_integer_to_dead_pointer ->
    pp_constructor "UB_CERB001_integer_to_dead_pointer" []
  | UB_CERB002a_out_of_bound_load -> pp_constructor "UB_CERB002a_out_of_bound_load" []
  | UB_CERB002b_out_of_bound_store -> pp_constructor "UB_CERB002b_out_of_bound_store" []
  | UB_CERB002c_out_of_bound_free -> pp_constructor "UB_CERB002c_out_of_bound_free" []
  | UB_CERB002d_out_of_bound_realloc ->
    pp_constructor "UB_CERB002d_out_of_bound_realloc" []
  | UB_CERB003_invalid_function_pointer ->
    pp_constructor "UB_CERB003_invalid_function_pointer" []
  | UB_CHERI_InvalidCap -> pp_constructor "UB_CHERI_InvalidCap" []
  | UB_CHERI_InsufficientPermissions ->
    pp_constructor "UB_CHERI_InsufficientPermissions" []
  | UB_CHERI_BoundsViolation -> pp_constructor "UB_CHERI_BoundsViolation" []
  | UB_CHERI_UndefinedTag -> pp_constructor "UB_CHERI_UndefinedTag" []
  | UB_CHERI_ZeroLength -> pp_constructor "UB_CHERI_ZeroLength" []


let pp_linux_memory_order = function
  | CF.Linux.Once -> !^"Once"
  | LAcquire -> !^"LAcquire"
  | LRelease -> !^"LRelease"
  | Rmb -> !^"Rmb"
  | Wmb -> !^"Wmb"
  | Mb -> !^"Mb"
  | RbDep -> !^"RbDep"
  | RcuLock -> !^"RcuLock"
  | RcuUnlock -> !^"RcuUnlock"
  | SyncRcu -> !^"SyncRcu"


let pp_integer_value v = Impl_mem.pp_integer_value_for_coq v

let pp_floating_value v = Impl_mem.pp_floating_value_for_coq v

let pp_pointer_value v = Impl_mem.pp_pointer_value_for_coq v

let pp_unit (_ : unit) = !^"tt"

let pp_unit_type = !^"unit"

let pp_memory_order = function
  | Cerb_frontend.Cmm_csem.NA -> !^"NA"
  | Seq_cst -> !^"Seq_cst"
  | Relaxed -> !^"Relaxed"
  | Release -> !^"Release"
  | Acquire -> !^"Acquire"
  | Consume -> !^"Consume"
  | Acq_rel -> !^"Acq_rel"


let pp_polarity = function Core.Pos -> !^"Pos" | Core.Neg -> !^"Neg"

let pp_lexing_position { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum } =
  pp_record
    [ ("pos_fname", !^(sprintf "%S" pos_fname));
      ("pos_lnum", !^(string_of_int pos_lnum));
      ("pos_bol", !^(string_of_int pos_bol));
      ("pos_cnum", !^(string_of_int pos_cnum))
    ]


let pp_location_cursor = function
  | Cerb_location.NoCursor -> !^"NoCursor"
  | Cerb_location.PointCursor pos -> !^"(PointCursor" ^^^ pp_lexing_position pos ^^ !^")"
  | Cerb_location.RegionCursor (start_pos, end_pos) ->
    !^"(RegionCursor"
    ^^^ pp_lexing_position start_pos
    ^^^ pp_lexing_position end_pos
    ^^ !^")"


let pp_location = function
  | Cerb_location.Loc_unknown -> !^"Loc_unknown"
  | _ when not debug_print_locations -> !^"Loc_unknown"
  | Cerb_location.Loc_other s -> !^"(Loc_other" ^^^ !^(sprintf "%S" s) ^^ !^")"
  | Cerb_location.Loc_point pos -> !^"(Loc_point" ^^^ pp_lexing_position pos ^^ !^")"
  | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
    !^"(Loc_region"
    ^^^ pp_lexing_position start_pos
    ^^^ pp_lexing_position end_pos
    ^^^ pp_location_cursor cursor
    ^^ !^")"
  | Cerb_location.Loc_regions (pos_list, cursor) ->
    let pp_pos_pair (start_pos, end_pos) =
      !^"("
      ^^ pp_lexing_position start_pos
      ^^ !^","
      ^^^ pp_lexing_position end_pos
      ^^ !^")"
    in
    !^"(Loc_regions"
    ^^^ !^"["
    ^^ P.separate_map (!^";" ^^ P.break 1) pp_pos_pair pos_list
    ^^ !^"]"
    ^^^ pp_location_cursor cursor
    ^^ !^")"


let pp_identifier (CF.Symbol.Identifier (loc, s)) =
  !^"(Identifier" ^^^ pp_location loc ^^^ pp_string s ^^ !^")"


let pp_digest (d : Digest.t) =
  let string_to_hex s =
    let hex_of_char c = Printf.sprintf "%02x" (Char.code c) in
    String.concat "" (List.map hex_of_char (String.to_seq s |> List.of_seq))
  in
  (* We are not using Digest.to_hex as it is gives error on invalid digest values *)
  pp_string (string_to_hex d)


let rec pp_symbol_description = function
  | CF.Symbol.SD_None -> !^"SD_None"
  | CF.Symbol.SD_unnamed_tag loc -> !^"(SD_unnamed_tag" ^^^ pp_location loc ^^ !^")"
  | CF.Symbol.SD_Id s -> !^"(SD_Id" ^^^ pp_string s ^^ !^")"
  | CF.Symbol.SD_CN_Id s -> !^"(SD_CN_Id" ^^^ pp_string s ^^ !^")"
  | CF.Symbol.SD_ObjectAddress s -> !^"(SD_ObjectAddress" ^^^ pp_string s ^^ !^")"
  | CF.Symbol.SD_Return -> !^"SD_Return"
  | CF.Symbol.SD_FunArgValue s -> !^"(SD_FunArgValue" ^^^ pp_string s ^^ !^")"
  | CF.Symbol.SD_FunArg (loc, n) ->
    !^"(SD_FunArg" ^^^ pp_location loc ^^^ !^(string_of_int n) ^^ !^")"


and pp_symbol (CF.Symbol.Symbol (d, n, sd)) =
  !^"(Symbol" ^^^ pp_digest d ^^^ pp_nat n ^^^ pp_symbol_description sd ^^ !^")"


and pp_symbol_prefix = function
  | CF.Symbol.PrefSource (loc, syms) ->
    !^"(PrefSource" ^^^ pp_location loc ^^^ pp_list pp_symbol syms ^^ !^")"
  | CF.Symbol.PrefFunArg (loc, d, z) ->
    !^"(PrefFunArg"
    ^^^ pp_location loc
    ^^^ pp_digest d
    ^^^ !^(Z.to_string (Z.of_int z))
    ^^ !^")"
  | CF.Symbol.PrefStringLiteral (loc, d) ->
    !^"(PrefStringLiteral" ^^^ pp_location loc ^^^ pp_digest d ^^ !^")"
  | CF.Symbol.PrefTemporaryLifetime (loc, d) ->
    !^"(PrefTemporaryLifetime" ^^^ pp_location loc ^^^ pp_digest d ^^ !^")"
  | CF.Symbol.PrefCompoundLiteral (loc, d) ->
    !^"(PrefCompoundLiteral" ^^^ pp_location loc ^^^ pp_digest d ^^ !^")"
  | CF.Symbol.PrefMalloc -> !^"PrefMalloc"
  | CF.Symbol.PrefOther s -> !^"(PrefOther" ^^^ !^s ^^ !^")"


let pp_sign = function
  | BaseTypes.Signed -> !^"BaseTypes.Signed"
  | BaseTypes.Unsigned -> !^"BaseTypes.Unsigned"


let rec pp_basetype pp_loc = function
  | BaseTypes.Unit -> !^"(BaseTypes.Unit unit)"
  | BaseTypes.Bool -> !^"(BaseTypes.Bool unit )"
  | BaseTypes.Integer -> !^"(BaseTypes.Integer unit)"
  | BaseTypes.MemByte -> !^"(BaseTypes.MemByte unit)"
  | BaseTypes.Bits (sign, n) ->
    !^"(BaseTypes.Bits" ^^^ !^"unit" ^^^ pp_sign sign ^^^ !^(string_of_int n) ^^ !^")"
  | BaseTypes.Real -> !^"(BaseTypes.Real unit)"
  | BaseTypes.Alloc_id -> !^"(BaseTypes.Alloc_id unit)"
  | BaseTypes.CType -> !^"(BaseTypes.CType unit)"
  | BaseTypes.Struct sym -> !^"(BaseTypes.Struct unit" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Datatype sym -> !^"(BaseTypes.Datatype unit" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Record fields ->
    !^"(BaseTypes.Record unit"
    ^^^ P.separate_map
          (!^";" ^^ P.break 1)
          (fun (id, ty) ->
            !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_basetype pp_loc ty ^^ !^")")
          fields
    ^^ !^")"
  | BaseTypes.Map (t1, t2) ->
    !^"(BaseTypes.Map unit" ^^^ pp_basetype pp_loc t1 ^^^ pp_basetype pp_loc t2 ^^ !^")"
  | BaseTypes.List t -> !^"(BaseTypes.List unit" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Tuple ts ->
    !^"(BaseTypes.Tuple unit"
    ^^^ P.separate_map (!^";" ^^ P.break 1) (pp_basetype pp_loc) ts
    ^^ !^")"
  | BaseTypes.Set t -> !^"(BaseTypes.TSet unit" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Loc x ->
    !^"(BaseTypes.Loc" ^^^ !^"unit" ^^^ pp_unit x ^^ !^")" (* NOTE hardcoded unit *)


let pp_integer_base_type = function
  | Sctypes.IntegerBaseTypes.Ichar -> !^"Ichar"
  | Sctypes.IntegerBaseTypes.Short -> !^"Short"
  | Sctypes.IntegerBaseTypes.Int_ -> !^"Int_"
  | Sctypes.IntegerBaseTypes.Long -> !^"Long"
  | Sctypes.IntegerBaseTypes.LongLong -> !^"LongLong"
  | Sctypes.IntegerBaseTypes.IntN_t n -> !^"(IntN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Int_leastN_t n ->
    !^"(Int_leastN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Int_fastN_t n ->
    !^"(Int_fastN_t" ^^^ !^(string_of_int n) ^^ !^")"
  | Sctypes.IntegerBaseTypes.Intmax_t -> !^"Intmax_t"
  | Sctypes.IntegerBaseTypes.Intptr_t -> !^"Intptr_t"


let pp_integer_type = function
  | Sctypes.IntegerTypes.Char -> !^"Char"
  | Sctypes.IntegerTypes.Bool -> !^"Bool"
  | Sctypes.IntegerTypes.Signed ibt -> !^"(Signed" ^^^ pp_integer_base_type ibt ^^ !^")"
  | Sctypes.IntegerTypes.Unsigned ibt ->
    !^"(Unsigned" ^^^ pp_integer_base_type ibt ^^ !^")"
  | Sctypes.IntegerTypes.Enum sym -> !^"(Enum" ^^^ pp_symbol sym ^^ !^")"
  | Sctypes.IntegerTypes.Wchar_t -> !^"Wchar_t"
  | Sctypes.IntegerTypes.Wint_t -> !^"Wint_t"
  | Sctypes.IntegerTypes.Size_t -> !^"Size_t"
  | Sctypes.IntegerTypes.Ptrdiff_t -> !^"Ptrdiff_t"
  | Sctypes.IntegerTypes.Ptraddr_t -> !^"Ptraddr_t"


let rec pp_annot_t = function
  | Annot.Astd s -> !^"(Astd" ^^^ !^(sprintf "%S" s) ^^ !^")"
  | Annot.Aloc loc -> !^"(Aloc" ^^^ pp_location loc ^^ !^")"
  | Annot.Auid s -> !^"(Auid" ^^^ !^(sprintf "%S" s) ^^ !^")"
  | Annot.Amarker n -> !^"(Amarker" ^^^ !^(string_of_int n) ^^ !^")"
  | Annot.Amarker_object_types n ->
    !^"(Amarker_object_types" ^^^ !^(string_of_int n) ^^ !^")"
  | Annot.Abmc bmc -> !^"(Abmc" ^^^ pp_bmc_annot bmc ^^ !^")"
  | Annot.Aattrs attrs -> !^"(Aattrs" ^^^ pp_attributes attrs ^^ !^")"
  | Annot.Atypedef sym -> !^"(Atypedef" ^^^ pp_symbol sym ^^ !^")"
  | Annot.Anot_explode -> !^"Anot_explode"
  | Annot.Alabel la -> !^"(Alabel" ^^^ pp_label_annot la ^^ !^")"
  | Annot.Acerb ca -> !^"(Acerb" ^^^ pp_cerb_attribute ca ^^ !^")"
  | Annot.Avalue va -> !^"(Avalue" ^^^ pp_value_annot va ^^ !^")"
  | Annot.Ainlined_label (loc, sym, la) ->
    !^"(Ainlined_label"
    ^^^ pp_location loc
    ^^^ pp_symbol sym
    ^^^ pp_label_annot la
    ^^ !^")"
  | Annot.Astmt -> !^"Astmt"
  | Annot.Aexpr -> !^"Aexpr"


and pp_bmc_annot = function
  | Annot.Abmc_id n -> !^"(Abmc_id" ^^^ !^(string_of_int n) ^^ !^")"


and pp_attributes (Annot.Attrs attrs) = !^"(Attrs" ^^^ pp_list pp_attribute attrs ^^ !^")"

and pp_attribute attr =
  pp_record
    [ ("attr_ns", pp_option pp_identifier attr.Annot.attr_ns);
      ("attr_id", pp_identifier attr.attr_id);
      ("attr_args", pp_list pp_attr_arg attr.attr_args)
    ]


and pp_attr_arg (loc, s, args) =
  !^"("
  ^^^ pp_location loc
  ^^ !^","
  ^^^ !^(sprintf "%S" s)
  ^^ !^","
  ^^^ pp_list
        (fun (loc, s) ->
          !^"(" ^^ pp_location loc ^^ !^"," ^^^ !^(sprintf "%S" s) ^^ !^")")
        args
  ^^ !^")"


and pp_label_annot = function
  | Annot.LAloop n -> !^"(LAloop" ^^^ !^(string_of_int n) ^^ !^")"
  | Annot.LAloop_continue n -> !^"(LAloop_continue" ^^^ !^(string_of_int n) ^^ !^")"
  | Annot.LAloop_break n -> !^"(LAloop_break" ^^^ !^(string_of_int n) ^^ !^")"
  | Annot.LAreturn -> !^"LAreturn"
  | Annot.LAswitch -> !^"LAswitch"
  | Annot.LAcase -> !^"LAcase"
  | Annot.LAdefault -> !^"LAdefault"
  | Annot.LAactual_label -> !^"LAactual_label"


and pp_cerb_attribute = function
  | Annot.ACerb_with_address n ->
    !^"(ACerb_with_address" ^^^ !^(Nat_big_num.to_string n) ^^ !^")"
  | Annot.ACerb_hidden -> !^"ACerb_hidden"


and pp_value_annot = function
  | Annot.Ainteger it -> !^"(Ainteger" ^^^ pp_integer_type it ^^ !^")"


let pp_qualifiers quals =
  pp_record
    [ ("Ctype.const", !^(string_of_bool quals.Ctype.const));
      ("Ctype.restrict", !^(string_of_bool quals.Ctype.restrict));
      ("Ctype.volatile", !^(string_of_bool quals.Ctype.volatile))
    ]


let rec pp_ctype (Ctype.Ctype (annots, ct)) =
  !^"(Ctype"
  ^^^ pp_list pp_annot_t annots
  ^^^ (match ct with
       | Ctype.Void -> !^"Ctype.Void"
       | Ctype.Basic bt -> !^"(Ctype.Basic" ^^^ pp_basic_type bt ^^ !^")"
       | Ctype.Array (ct, None) -> !^"(Ctype.Array" ^^^ pp_ctype ct ^^^ !^"None" ^^ !^")"
       | Ctype.Array (ct, Some n) ->
         !^"(Ctype.Array"
         ^^^ pp_ctype ct
         ^^^ !^"(Some"
         ^^^ !^(Z.to_string n)
         ^^ !^"))"
         ^^ !^")"
       | Ctype.Function ((quals, ret), args, variadic) ->
         !^"(Ctype.Function"
         ^^^ !^"("
         ^^^ pp_qualifiers quals
         ^^ !^","
         ^^^ pp_ctype ret
         ^^ !^")"
         ^^^ pp_list
               (fun (q, ct, is_reg) ->
                 !^"("
                 ^^ pp_qualifiers q
                 ^^ !^","
                 ^^^ pp_ctype ct
                 ^^ !^","
                 ^^^ !^(string_of_bool is_reg)
                 ^^ !^")")
               args
         ^^^ !^(string_of_bool variadic)
         ^^ !^")"
       | Ctype.FunctionNoParams (quals, ret) ->
         !^"(Ctype.FunctionNoParams"
         ^^^ !^"("
         ^^^ pp_qualifiers quals
         ^^ !^","
         ^^^ pp_ctype ret
         ^^ !^"))"
       | Ctype.Pointer (quals, ct) ->
         !^"(Ctype.Pointer" ^^^ pp_qualifiers quals ^^^ pp_ctype ct ^^ !^")"
       | Ctype.Atomic ct -> !^"(Ctype.Atomic" ^^^ pp_ctype ct ^^ !^")"
       | Ctype.Struct sym -> !^"(Ctype.Struct" ^^^ pp_symbol sym ^^ !^")"
       | Ctype.Union sym -> !^"(Ctype.Union" ^^^ pp_symbol sym ^^ !^")")
  ^^ !^")"


and pp_basic_type = function
  | Ctype.Integer it -> !^"(Ctype.Integer" ^^^ pp_integer_type it ^^ !^")"
  | Ctype.Floating ft -> !^"(Ctype.Floating" ^^^ pp_floating_type ft ^^ !^")"


and pp_floating_type = function
  | Ctype.RealFloating rft -> !^"(RealFloating" ^^^ pp_real_floating_type rft ^^ !^")"


and pp_real_floating_type = function
  | Ctype.Float -> !^"Float"
  | Ctype.Double -> !^"Double"
  | Ctype.LongDouble -> !^"LongDouble"


let rec pp_sctype = function
  | Sctypes.Void -> !^"SCtypes.Void"
  | Sctypes.Integer it -> !^"(SCtypes.Integer" ^^^ pp_integer_type it ^^ !^")"
  | Sctypes.Array (ct, None) -> !^"(SCtypes.Array" ^^^ pp_sctype ct ^^^ !^"None" ^^ !^")"
  | Sctypes.Array (ct, Some n) ->
    !^"(SCtypes.Array"
    ^^^ pp_sctype ct
    ^^^ !^"(Some"
    ^^^ !^(string_of_int n)
    ^^ !^"))"
    ^^ !^")"
  | Sctypes.Pointer ct -> !^"(SCtypes.Pointer" ^^^ pp_sctype ct ^^ !^")"
  | Sctypes.Struct sym -> !^"(SCtypes.Struct" ^^^ pp_symbol sym ^^ !^")"
  | Sctypes.Function ((quals, ret), args, variadic) ->
    !^"(SCtypes.Function"
    ^^^ !^"("
    ^^^ pp_qualifiers quals
    ^^ !^","
    ^^^ pp_sctype ret
    ^^ !^")"
    ^^^ pp_list
          (fun (ct, is_reg) ->
            !^"(" ^^ pp_sctype ct ^^ !^"," ^^^ !^(string_of_bool is_reg) ^^ !^")")
          args
    ^^^ !^(string_of_bool variadic)
    ^^ !^")"


let rec pp_core_base_type = function
  | Core.BTy_unit -> !^"BTy_unit"
  | Core.BTy_boolean -> !^"BTy_boolean"
  | Core.BTy_ctype -> !^"BTy_ctype"
  | Core.BTy_list t -> !^"(BTy_list" ^^^ pp_core_base_type t ^^ !^")"
  | Core.BTy_tuple ts ->
    !^"(BTy_tuple" ^^^ P.separate_map (!^";" ^^ P.break 1) pp_core_base_type ts ^^ !^")"
  | Core.BTy_object ot -> !^"(BTy_object" ^^^ pp_core_object_type ot ^^ !^")"
  | Core.BTy_loaded ot -> !^"(BTy_loaded" ^^^ pp_core_object_type ot ^^ !^")"
  | Core.BTy_storable -> !^"BTy_storable"


and pp_core_object_type = function
  | Core.OTy_integer -> !^"OTy_integer"
  | Core.OTy_floating -> !^"OTy_floating"
  | Core.OTy_pointer -> !^"OTy_pointer"
  | Core.OTy_array t -> !^"(OTy_array" ^^^ pp_core_object_type t ^^ !^")"
  | Core.OTy_struct sym -> !^"(OTy_struct" ^^^ pp_symbol sym ^^ !^")"
  | Core.OTy_union sym -> !^"(OTy_union" ^^^ pp_symbol sym ^^ !^")"


let pp_ctor = function
  | Mucore.Cnil bt -> !^"(Cnil" ^^^ pp_core_base_type bt ^^ !^")"
  | Mucore.Ccons -> !^"Ccons"
  | Mucore.Ctuple -> !^"Ctuple"
  | Mucore.Carray -> !^"Carray"


let pp_core_binop = function
  | Core.OpAdd -> !^"Add"
  | Core.OpSub -> !^"Sub"
  | Core.OpMul -> !^"Mul"
  | Core.OpDiv -> !^"Div"
  | Core.OpRem_t -> !^"Rem_t"
  | Core.OpRem_f -> !^"Rem_f"
  | Core.OpExp -> !^"Exp"
  | Core.OpEq -> !^"Eq"
  | Core.OpGt -> !^"Gt"
  | Core.OpLt -> !^"Lt"
  | Core.OpGe -> !^"Ge"
  | Core.OpLe -> !^"Le"
  | Core.OpAnd -> !^"And"
  | Core.OpOr -> !^"Or"


let pp_binop = function
  | Terms.And -> !^"And"
  | Terms.Or -> !^"Or"
  | Terms.Implies -> !^"Implies"
  | Terms.Add -> !^"Add"
  | Terms.Sub -> !^"Sub"
  | Terms.Mul -> !^"Mul"
  | Terms.MulNoSMT -> !^"MulNoSMT"
  | Terms.Div -> !^"Div"
  | Terms.DivNoSMT -> !^"DivNoSMT"
  | Terms.Exp -> !^"Exp"
  | Terms.ExpNoSMT -> !^"ExpNoSMT"
  | Terms.Rem -> !^"Rem"
  | Terms.RemNoSMT -> !^"RemNoSMT"
  | Terms.Mod -> !^"Mod"
  | Terms.ModNoSMT -> !^"ModNoSMT"
  | Terms.BW_Xor -> !^"BW_Xor"
  | Terms.BW_And -> !^"BW_And"
  | Terms.BW_Or -> !^"BW_Or"
  | Terms.ShiftLeft -> !^"ShiftLeft"
  | Terms.ShiftRight -> !^"ShiftRight"
  | Terms.LT -> !^"LT"
  | Terms.LE -> !^"LE"
  | Terms.Min -> !^"Min"
  | Terms.Max -> !^"Max"
  | Terms.EQ -> !^"EQ"
  | Terms.LTPointer -> !^"LTPointer"
  | Terms.LEPointer -> !^"LEPointer"
  | Terms.SetUnion -> !^"SetUnion"
  | Terms.SetIntersection -> !^"SetIntersection"
  | Terms.SetDifference -> !^"SetDifference"
  | Terms.SetMember -> !^"SetMember"
  | Terms.Subset -> !^"Subset"


let pp_bw_binop = function
  | BW_OR -> !^"BW_OR"
  | BW_AND -> !^"BW_AND"
  | BW_XOR -> !^"BW_XOR"


let pp_bw_unop = function
  | BW_COMPL -> !^"BW_COMPL"
  | BW_CTZ -> !^"BW_CTZ"
  | BW_FFS -> !^"BW_FFS"


let pp_iop = function
  | Core.IOpAdd -> !^"IOpAdd"
  | Core.IOpSub -> !^"IOpSub"
  | Core.IOpMul -> !^"IOpMul"
  | Core.IOpShl -> !^"IOpShl"
  | Core.IOpShr -> !^"IOpShr"


let rec pp_pattern_ pp_type = function
  | CaseBase (sym_opt, bt) ->
    !^"(CaseBase"
    ^^^ !^"_("
    ^^^ pp_option pp_symbol sym_opt
    ^^^ !^","
    ^^^ pp_core_base_type bt
    ^^ !^"))"
  | CaseCtor (ctor, pats) ->
    !^"(CaseCtor"
    ^^^ !^"_"
    ^^^ pp_ctor ctor
    ^^^ pp_list (pp_pattern pp_type) pats
    ^^ !^")"


and pp_pattern pp_type (Pattern (loc, annots, ty, pat)) =
  !^"(Pattern"
  ^^^ !^"_"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^ pp_pattern_ pp_type pat
  ^^ !^")"


let pp_mem_value v =
  Impl_mem.pp_mem_value_for_coq
    pp_symbol
    pp_integer_type
    pp_floating_type
    pp_ctype
    pp_identifier
    v


let rec pp_mem_constraint = function
  | Mem_common.MC_empty -> !^"MC_empty"
  | Mem_common.MC_eq (x, y) ->
    !^"(MC_eq" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_le (x, y) ->
    !^"(MC_le" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_lt (x, y) ->
    !^"(MC_lt" ^^^ pp_integer_value x ^^^ pp_integer_value y ^^ !^")"
  | Mem_common.MC_in_device x -> !^"(MC_in_device" ^^^ pp_integer_value x ^^ !^")"
  | Mem_common.MC_or (x, y) ->
    !^"(MC_or" ^^^ pp_mem_constraint x ^^^ pp_mem_constraint y ^^ !^")"
  | Mem_common.MC_conj xs -> !^"(MC_conj" ^^^ pp_list pp_mem_constraint xs ^^ !^")"
  | Mem_common.MC_not x -> !^"(MC_not" ^^^ pp_mem_constraint x ^^ !^")"


and pp_pexpr pp_type (Pexpr (loc, annots, ty, pe)) =
  !^"(Pexpr"
  ^^^ !^"_"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^ (match pe with
       | PEsym s -> !^"(PEsym" ^^^ !^"_" ^^^ pp_symbol s ^^ !^")"
       | PEval v -> !^"(PEval" ^^^ !^"_" ^^^ pp_value pp_type v ^^ !^")"
       | PEctor (c, es) ->
         !^"(PEctor" ^^^ !^"_" ^^^ pp_ctor c ^^^ pp_list (pp_pexpr pp_type) es ^^ !^")"
       | PEop (op, e1, e2) ->
         !^"(PEop"
         ^^^ !^"_"
         ^^^ pp_core_binop op
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | PEconstrained cs ->
         !^"(PEconstrained"
         ^^^ !^"_"
         ^^^ pp_list
               (fun (c, e) ->
                 !^"(" ^^ pp_mem_constraint c ^^ !^"," ^^^ pp_pexpr pp_type e ^^ !^")")
               cs
         ^^ !^")"
       | PEbitwise_unop (op, e) ->
         !^"(PEbitwise_unop" ^^^ !^"_" ^^^ pp_bw_unop op ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEbitwise_binop (op, e1, e2) ->
         !^"(PEbitwise_binop"
         ^^^ !^"_"
         ^^^ pp_bw_binop op
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | Cfvfromint e -> !^"(Cfvfromint" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
       | Civfromfloat (act, e) ->
         !^"(Civfromfloat" ^^^ !^"_" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEarray_shift (base, ct, idx) ->
         !^"(PEarray_shift"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type base
         ^^^ pp_sctype ct
         ^^^ pp_pexpr pp_type idx
         ^^ !^")"
       | PEmember_shift (e, sym, id) ->
         !^"(PEmember_shift"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type e
         ^^^ pp_symbol sym
         ^^^ pp_identifier id
         ^^ !^")"
       | PEnot e -> !^"(PEnot" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEapply_fun (f, args) ->
         !^"(PEapply_fun"
         ^^^ !^"_"
         ^^^ pp_function f
         ^^^ pp_list (pp_pexpr pp_type) args
         ^^ !^")"
       | PEstruct (sym, fields) ->
         !^"(PEstruct"
         ^^^ !^"_"
         ^^^ pp_symbol sym
         ^^^ pp_list
               (fun (id, e) ->
                 !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_pexpr pp_type e ^^ !^")")
               fields
         ^^ !^")"
       | PEunion (sym, id, e) ->
         !^"(PEunion"
         ^^^ !^"_"
         ^^^ pp_symbol sym
         ^^^ pp_identifier id
         ^^^ pp_pexpr pp_type e
         ^^ !^")"
       | PEcfunction e -> !^"(PEcfunction" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEmemberof (sym, id, e) ->
         !^"(PEmemberof"
         ^^^ !^"_"
         ^^^ pp_symbol sym
         ^^^ pp_identifier id
         ^^^ pp_pexpr pp_type e
         ^^ !^")"
       | PEbool_to_integer e ->
         !^"(PEbool_to_integer" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEconv_int (e1, e2) ->
         !^"(PEconv_int"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | PEconv_loaded_int (e1, e2) ->
         !^"(PEconv_loaded_int"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | PEwrapI (act, e) ->
         !^"(PEwrapI" ^^^ !^"_" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
       | PEcatch_exceptional_condition (act, e) ->
         !^"(PEcatch_exceptional_condition"
         ^^^ !^"_"
         ^^^ pp_act act
         ^^^ pp_pexpr pp_type e
         ^^ !^")"
       | PEbounded_binop (kind, op, e1, e2) ->
         !^"(PEbounded_binop"
         ^^^ !^"_"
         ^^^ pp_bound_kind kind
         ^^^ pp_iop op
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | PEis_representable_integer (e, act) ->
         !^"(PEis_representable_integer"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type e
         ^^^ pp_act act
         ^^ !^")"
       | PEundef (loc, ub) ->
         !^"(PEundef" ^^^ !^"_" ^^^ pp_location loc ^^^ pp_undefined_behaviour ub ^^ !^")"
       | PEerror (msg, e) ->
         !^"(PEerror" ^^^ !^"_" ^^^ !^msg ^^^ pp_pexpr pp_type e ^^ !^")"
       | PElet (pat, e1, e2) ->
         !^"(PElet"
         ^^^ !^"_"
         ^^^ pp_pattern pp_type pat
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_pexpr pp_type e2
         ^^ !^")"
       | PEif (c, t, e) ->
         !^"(PEif"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type c
         ^^^ pp_pexpr pp_type t
         ^^^ pp_pexpr pp_type e
         ^^ !^")")
  ^^ !^")"


and pp_bound_kind = function
  | Bound_Wrap act -> !^"(Bound_Wrap" ^^^ pp_act act ^^ !^")"
  | Bound_Except act -> !^"(Bound_Except" ^^^ pp_act act ^^ !^")"


and pp_action pp_type (Action (loc, act)) =
  pp_record
    [ ("action_loc", pp_location loc); ("action_content", pp_action_content pp_type act) ]


and pp_paction pp_type (Paction (pol, act)) =
  pp_record
    [ ("paction_polarity", pp_polarity pol); ("paction_action", pp_action pp_type act) ]


and pp_action_content pp_type act =
  match act with
  | Create (e, act, sym) ->
    !^"(Create"
    ^^^ !^"_"
    ^^^ pp_pexpr pp_type e
    ^^^ pp_act act
    ^^^ pp_symbol_prefix sym
    ^^ !^")"
  | CreateReadOnly (e1, act, e2, sym) ->
    !^"(CreateReadOnly"
    ^^^ !^"_"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_symbol_prefix sym
    ^^ !^")"
  | Alloc (e1, e2, sym) ->
    !^"(Alloc"
    ^^^ !^"_"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_symbol_prefix sym
    ^^ !^")"
  | Kill (kind, e) ->
    !^"(Kill" ^^^ !^"_" ^^^ pp_kill_kind kind ^^^ pp_pexpr pp_type e ^^ !^")"
  | Store (b, act, e1, e2, mo) ->
    !^"(Store"
    ^^^ !^"_"
    ^^^ pp_bool b
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_memory_order mo
    ^^ !^")"
  | Load (act, e, mo) ->
    !^"(Load"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e
    ^^^ pp_memory_order mo
    ^^ !^")"
  | RMW (act, e1, e2, e3, mo1, mo2) ->
    !^"(RMW"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | Fence mo -> !^"(Fence" ^^^ !^"_" ^^^ pp_memory_order mo ^^ !^")"
  | CompareExchangeStrong (act, e1, e2, e3, mo1, mo2) ->
    !^"(CompareExchangeStrong"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | CompareExchangeWeak (act, e1, e2, e3, mo1, mo2) ->
    !^"(CompareExchangeWeak"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | LinuxFence lmo -> !^"(LinuxFence" ^^^ !^"_" ^^^ pp_linux_memory_order lmo ^^ !^")"
  | LinuxLoad (act, e, lmo) ->
    !^"(LinuxLoad"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"
  | LinuxStore (act, e1, e2, lmo) ->
    !^"(LinuxStore"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"
  | LinuxRMW (act, e1, e2, lmo) ->
    !^"(LinuxRMW"
    ^^^ !^"_"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"


and pp_act { loc; annot; ct } =
  pp_record
    [ ("MuCore.loc", pp_location loc);
      ("MuCore.annot", pp_list pp_annot_t annot);
      ("MuCore.ct", pp_sctype ct)
    ]


and pp_kill_kind = function
  | Dynamic -> !^"Dynamic" (* constructor with no arguments *)
  | Static ct -> !^"(Static" ^^^ pp_sctype ct ^^ !^")"


and pp_bool b = if b then !^"true" else !^"false"

and pp_value pp_type (V (ty, v)) =
  !^"(V"
  ^^^ !^"_"
  ^^^ pp_type ty
  ^^^ (match v with
       | Vobject ov -> !^"(Vobject" ^^^ !^"_" ^^^ pp_object_value pp_type ov ^^ !^")"
       | Vctype t -> !^"(Vctype" ^^^ !^"_" ^^^ pp_ctype t ^^ !^")"
       | Vfunction_addr s -> !^"(Vfunction_addr" ^^^ !^"_" ^^^ pp_symbol s ^^ !^")"
       | Vunit -> !^"(Vunit" ^^^ !^"_" ^^^ !^")"
       | Vtrue -> !^"(Vtrue" ^^^ !^"_" ^^^ !^")"
       | Vfalse -> !^"(Vfalse" ^^^ !^"_" ^^^ !^")"
       | Vlist (bt, vs) ->
         !^"(Vlist"
         ^^^ !^"_"
         ^^^ pp_core_base_type bt
         ^^^ pp_list (pp_value pp_type) vs
         ^^ !^")"
       | Vtuple vs -> !^"(Vtuple" ^^^ !^"_" ^^^ pp_list (pp_value pp_type) vs ^^ !^")")
  ^^^ !^")"


and pp_object_value pp_type (OV (ty, ov)) =
  !^"OV"
  ^^^ pp_type ty
  ^^^
  match ov with
  | OVinteger i -> !^"(OVinteger" ^^^ pp_integer_value i ^^ !^")"
  | OVfloating f -> !^"(OVfloating" ^^^ pp_floating_value f ^^ !^")"
  | OVpointer p -> !^"(OVpointer" ^^^ pp_pointer_value pp_symbol p ^^ !^")"
  | OVarray vs -> !^"(OVarray" ^^^ pp_list (pp_object_value pp_type) vs ^^ !^")"
  | OVstruct (sym, fields) ->
    !^"(OVstruct"
    ^^^ pp_symbol sym
    ^^^ pp_list
          (fun (id, ty, v) ->
            !^"("
            ^^ pp_identifier id
            ^^ !^","
            ^^^ pp_sctype ty
            ^^ !^","
            ^^^ pp_mem_value v
            ^^ !^")")
          fields
    ^^ !^")"
  | OVunion (sym, id, v) ->
    !^"(OVunion" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_mem_value v ^^ !^")"


(* TODO: hardcoded None. pass `pp_type` *)
let pp_location_info (x, _) = !^"(" ^^^ pp_location x ^^^ !^"," ^^^ !^"None" ^^^ !^")"

let pp_trusted = function
  | Trusted loc -> !^"(Trusted" ^^^ pp_location loc ^^ !^")"
  | Checked -> !^"Checked"


let pp_unop = function
  | Terms.Not -> !^"Not"
  | Negate -> !^"Negate"
  | BW_CLZ_NoSMT -> !^"BW_CLZ_NoSMT"
  | BW_CTZ_NoSMT -> !^"BW_CTZ_NoSMT"
  | BW_FFS_NoSMT -> !^"BW_FFS_NoSMT"
  | BW_FLS_NoSMT -> !^"BW_FLS_NoSMT"
  | BW_Compl -> !^"BW_Compl"


let rec pp_terms_pattern (Terms.Pat (pat, bt, loc)) =
  !^"(Pat"
  ^^^ pp_terms_pattern_ pat
  ^^^ pp_basetype pp_unit bt
  ^^^ pp_location loc
  ^^ !^")"


and pp_terms_pattern_ = function
  | Terms.PSym s -> !^"(PSym" ^^^ pp_symbol s ^^ !^")"
  | Terms.PWild -> !^"PWild"
  | Terms.PConstructor (sym, args) ->
    !^"(PConstructor"
    ^^^ pp_symbol sym
    ^^^ pp_list
          (fun (id, pat) ->
            !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_terms_pattern pat ^^ !^")")
          args
    ^^ !^")"


let pp_const = function
  | Terms.Z z -> !^"(Z" ^^^ !^(Z.to_string z) ^^ !^")"
  | Bits ((sign, sz), z) ->
    !^"(Terms.Bits"
    ^^^ !^"(("
    ^^ pp_sign sign
    ^^ !^","
    ^^^ pp_nat sz
    ^^ !^"),"
    ^^^ pp_Z z
    ^^ !^"))"
  | Q q -> !^"(Q" ^^^ !^(Q.to_string q) ^^ !^")"
  | MemByte { alloc_id; value } ->
    !^"(Terms.MemByte" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string value) ^^ !^")"
  | Pointer { alloc_id; addr } ->
    !^"(Terms.Pointer" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string addr) ^^ !^")"
  | Alloc_id z -> !^"(Terms.Alloc_id" ^^^ !^(Z.to_string z) ^^ !^")"
  | Bool b -> !^"(Terms.Bool" ^^^ pp_bool b ^^ !^")"
  | Unit -> !^"Terms.Unit"
  | Null -> !^"Terms.Null"
  | CType_const t -> !^"(Terms.CType_const" ^^^ pp_sctype t ^^ !^")"
  | Default bt -> !^"(Terms.Default" ^^^ pp_basetype pp_unit bt ^^ !^")"


let rec pp_index_term (IndexTerms.IT (term, bt, loc)) =
  !^"(Terms.IT"
  ^^^ !^"_"
  ^^^ pp_index_term_content term
  ^^^ pp_basetype pp_unit bt
  ^^^ pp_location loc
  ^^ !^")"


and pp_index_term_content = function
  | IndexTerms.Const c -> !^"(Const" ^^^ !^"_" ^^^ pp_const c ^^ !^")"
  | Sym s -> !^"(Sym" ^^^ !^"_" ^^^ pp_symbol s ^^ !^")"
  | Unop (op, t) -> !^"(Unop" ^^^ !^"_" ^^^ pp_unop op ^^^ pp_index_term t ^^ !^")"
  | Binop (op, t1, t2) ->
    !^"(Binop"
    ^^^ !^"_"
    ^^^ pp_binop op
    ^^^ pp_index_term t1
    ^^^ pp_index_term t2
    ^^ !^")"
  | ITE (c, t, e) ->
    !^"(ITE"
    ^^^ !^"_"
    ^^^ pp_index_term c
    ^^^ pp_index_term t
    ^^^ pp_index_term e
    ^^ !^")"
  | EachI ((n1, (sym, bt), n2), t) ->
    !^"(EachI"
    ^^^ !^"_"
    ^^^ !^"("
    ^^^ !^(string_of_int n1)
    ^^ !^","
    ^^^ !^"("
    ^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^ !^","
    ^^^ !^(string_of_int n2)
    ^^ !^")"
    ^^^ pp_index_term t
    ^^ !^")"
  | Tuple ts -> !^"(Tuple" ^^^ pp_list pp_index_term ts ^^ !^")"
  | NthTuple (n, t) -> !^"(NthTuple" ^^^ !^(string_of_int n) ^^^ pp_index_term t ^^ !^")"
  | Struct (tag, members) ->
    !^"(Struct"
    ^^^ pp_symbol tag
    ^^^ pp_list
          (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")")
          members
    ^^ !^")"
  | StructMember (t, member) ->
    !^"(StructMember" ^^^ pp_index_term t ^^^ pp_identifier member ^^ !^")"
  | StructUpdate ((t1, member), t2) ->
    !^"(StructUpdate"
    ^^^ !^"("
    ^^^ pp_index_term t1
    ^^ !^","
    ^^^ pp_identifier member
    ^^ !^")"
    ^^^ pp_index_term t2
    ^^ !^")"
  | Record members ->
    !^"(Record"
    ^^^ pp_list
          (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")")
          members
    ^^ !^")"
  | RecordMember (t, member) ->
    !^"(RecordMember" ^^^ pp_index_term t ^^^ pp_identifier member ^^ !^")"
  | RecordUpdate ((t1, member), t2) ->
    !^"(RecordUpdate"
    ^^^ !^"("
    ^^^ pp_index_term t1
    ^^ !^","
    ^^^ pp_identifier member
    ^^ !^")"
    ^^^ pp_index_term t2
    ^^ !^")"
  | Constructor (sym, args) ->
    !^"(Constructor"
    ^^^ pp_symbol sym
    ^^^ pp_list
          (fun (id, t) -> !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_index_term t ^^ !^")")
          args
    ^^ !^")"
  | MemberShift (t, tag, id) ->
    !^"(MemberShift" ^^^ pp_index_term t ^^^ pp_symbol tag ^^^ pp_identifier id ^^ !^")"
  | ArrayShift { base; ct; index } ->
    !^"(ArrayShift"
    ^^^ pp_index_term base
    ^^^ pp_sctype ct
    ^^^ pp_index_term index
    ^^ !^")"
  | CopyAllocId { addr; loc } ->
    !^"(CopyAllocId" ^^^ pp_index_term addr ^^^ pp_index_term loc ^^ !^")"
  | HasAllocId t -> !^"(HasAllocId" ^^^ pp_index_term t ^^ !^")"
  | SizeOf ct -> !^"(SizeOf" ^^^ pp_sctype ct ^^ !^")"
  | OffsetOf (tag, member) ->
    !^"(OffsetOf" ^^^ pp_symbol tag ^^^ pp_identifier member ^^ !^")"
  | Nil bt -> !^"(Nil" ^^^ pp_basetype pp_unit bt ^^ !^")"
  | Cons (t1, t2) -> !^"(Cons" ^^^ pp_index_term t1 ^^^ pp_index_term t2 ^^ !^")"
  | Head t -> !^"(Head" ^^^ pp_index_term t ^^ !^")"
  | Tail t -> !^"(Tail" ^^^ !^"_" ^^^ pp_index_term t ^^ !^")"
  | NthList (i, xs, d) ->
    !^"(NthList"
    ^^^ !^"_"
    ^^^ pp_index_term i
    ^^^ pp_index_term xs
    ^^^ pp_index_term d
    ^^ !^")"
  | ArrayToList (arr, i, len) ->
    !^"(ArrayToList"
    ^^^ !^"_"
    ^^^ pp_index_term arr
    ^^^ pp_index_term i
    ^^^ pp_index_term len
    ^^ !^")"
  | Representable (ct, t) ->
    !^"(Representable" ^^^ !^"_" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
  | Good (ct, t) -> !^"(Good" ^^^ !^"_" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
  | Aligned { t; align } ->
    !^"(Aligned" ^^^ !^"_" ^^^ pp_index_term t ^^^ pp_index_term align ^^ !^")"
  | WrapI (ct, t) ->
    !^"(WrapI" ^^^ !^"_" ^^^ pp_integer_type ct ^^^ pp_index_term t ^^ !^")"
  | MapConst (bt, t) ->
    !^"(MapConst" ^^^ !^"_" ^^^ pp_basetype pp_unit bt ^^^ pp_index_term t ^^ !^")"
  | MapSet (m, k, v) ->
    !^"(MapSet"
    ^^^ !^"_"
    ^^^ pp_index_term m
    ^^^ pp_index_term k
    ^^^ pp_index_term v
    ^^ !^")"
  | MapGet (m, k) ->
    !^"(MapGet" ^^^ !^"_" ^^^ pp_index_term m ^^^ pp_index_term k ^^ !^")"
  | MapDef ((sym, bt), t) ->
    !^"(MapDef"
    ^^^ !^"_"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_index_term t
    ^^ !^")"
  | Apply (sym, args) ->
    !^"(Apply" ^^^ !^"_" ^^^ pp_symbol sym ^^^ pp_list pp_index_term args ^^ !^")"
  | Let ((sym, t1), t2) ->
    !^"(Let"
    ^^^ !^"_"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_index_term t1
    ^^ !^")"
    ^^^ pp_index_term t2
    ^^ !^")"
  | Match (t, cases) ->
    !^"(Match"
    ^^^ !^"_"
    ^^^ pp_index_term t
    ^^^ pp_list
          (fun (pat, body) ->
            !^"(" ^^ pp_terms_pattern pat ^^ !^"," ^^^ pp_index_term body ^^ !^")")
          cases
    ^^ !^")"
  | Cast (bt, t) ->
    !^"(Cast" ^^^ !^"_" ^^^ pp_basetype pp_unit bt ^^^ pp_index_term t ^^ !^")"


let pp_request_init = function Request.Init -> !^"Init" | Request.Uninit -> !^"Uninit"

let rec pp_request = function
  | Request.P pred -> !^"(Request.P" ^^^ pp_request_ppredicate pred ^^^ !^")"
  | Request.Q qpred -> !^"(Request.Q" ^^^ pp_request_qpredicate qpred ^^^ !^")"


and pp_request_qpredicate qpred =
  pp_record
    [ ("QPredicate.name", pp_request_name qpred.Request.QPredicate.name);
      ("QPredicate.pointer", pp_index_term qpred.pointer);
      ( "QPredicate.q",
        pp_tuple [ pp_symbol (fst qpred.q); pp_basetype pp_unit (snd qpred.q) ] );
      ("QPredicate.q_loc", pp_location qpred.q_loc);
      ("QPredicate.step", pp_index_term qpred.step);
      ("QPredicate.permission", pp_index_term qpred.permission);
      ("QPredicate.iargs", pp_list pp_index_term qpred.iargs)
    ]


and pp_request_ppredicate (pred : Request.Predicate.t) =
  pp_record
    [ ("Predicate.name", pp_request_name pred.Request.Predicate.name);
      ("Predicate.pointer", pp_index_term pred.pointer);
      ("Predicate.iargs", pp_list pp_index_term pred.iargs)
    ]


and pp_request_name = function
  | Request.PName sym -> !^"(Request.PName" ^^^ pp_symbol sym ^^ !^")"
  | Request.Owned (ct, init) ->
    !^"(Request.Owned" ^^^ pp_sctype ct ^^^ pp_request_init init ^^ !^")"


let pp_memop pp_type = function
  | PtrEq (e1, e2) ->
    !^"(PtrEq"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrNe (e1, e2) ->
    !^"(PtrNe"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrLt (e1, e2) ->
    !^"(PtrLt"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrGt (e1, e2) ->
    !^"(PtrGt"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrLe (e1, e2) ->
    !^"(PtrLe"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrGe (e1, e2) ->
    !^"(PtrGe"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | Ptrdiff (act, e1, e2) ->
    !^"(Ptrdiff"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_act act; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | IntFromPtr (act1, act2, e) ->
    !^"(IntFromPtr"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_act act1; pp_act act2; pp_pexpr pp_type e ]
    ^^ !^")"
  | PtrFromInt (act1, act2, e) ->
    !^"(PtrFromInt"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_act act1; pp_act act2; pp_pexpr pp_type e ]
    ^^ !^")"
  | PtrValidForDeref (act, e) ->
    !^"(PtrValidForDeref"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_act act; pp_pexpr pp_type e ]
    ^^ !^")"
  | PtrWellAligned (act, e) ->
    !^"(PtrWellAligned" ^^^ !^"_" ^^^ pp_tuple [ pp_act act; pp_pexpr pp_type e ] ^^ !^")"
  | PtrArrayShift (e1, act, e2) ->
    !^"(PtrArrayShift"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_act act; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | PtrMemberShift (sym, id, e) ->
    !^"(PtrMemberShift"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_symbol sym; pp_identifier id; pp_pexpr pp_type e ]
    ^^ !^")"
  | Memcpy (e1, e2, e3) ->
    !^"(Memcpy"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_pexpr pp_type e3 ]
    ^^ !^")"
  | Memcmp (e1, e2, e3) ->
    !^"(Memcmp"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_pexpr pp_type e3 ]
    ^^ !^")"
  | Realloc (e1, e2, e3) ->
    !^"(Realloc"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_pexpr pp_type e3 ]
    ^^ !^")"
  | Va_start (e1, e2) ->
    !^"(Va_start"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"
  | Va_copy e -> !^"(Va_copy" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
  | Va_arg (e, act) ->
    !^"(Va_arg" ^^^ !^"_" ^^^ pp_tuple [ pp_pexpr pp_type e; pp_act act ] ^^ !^")"
  | Va_end e -> !^"(Va_end" ^^^ !^"_" ^^^ pp_pexpr pp_type e ^^ !^")"
  | CopyAllocId (e1, e2) ->
    !^"(CopyAllocId"
    ^^^ !^"_"
    ^^^ pp_tuple [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
    ^^ !^")"


let pp_pack_unpack = function CF.Cn.Pack -> !^"Pack" | CF.Cn.Unpack -> !^"Unpack"

let pp_to_from = function CF.Cn.To -> !^"To" | CF.Cn.From -> !^"From"

let pp_cn_to_instantiate ppfa ppfty = function
  | CF.Cn.I_Function f -> !^"(I_Function" ^^^ ppfa f ^^ !^")"
  | CF.Cn.I_Good ty -> !^"(I_Good" ^^^ ppfty ty ^^ !^")"
  | CF.Cn.I_Everything -> !^"I_Everything"


let pp_logical_constraint = function
  | LogicalConstraints.T term -> !^"(T" ^^^ pp_index_term term ^^ !^")"
  | LogicalConstraints.Forall ((sym, bt), term) ->
    !^"(Forall"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_index_term term
    ^^ !^")"


let rec pp_return_type = function
  | ReturnTypes.Computational ((sym, bt), info, lrt) ->
    !^"(ReturnTypes.Computational"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"


and pp_logical_return_type = function
  | LogicalReturnTypes.Define ((sym, term), info, lrt) ->
    !^"(LogicalReturnTypes.Define"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_index_term term
    ^^ !^")"
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"
  | LogicalReturnTypes.Resource ((sym, (req, bt)), info, lrt) ->
    !^"(LogicalReturnTypes.Resource"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ !^"("
    ^^^ pp_request req
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^"))"
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"
  | LogicalReturnTypes.Constraint (lc, info, lrt) ->
    !^"(LogicalReturnTypes.Constraint"
    ^^^ pp_logical_constraint lc
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"
  | LogicalReturnTypes.I -> !^"LogicalReturnTypes.I"


let rec pp_logical_args ppf = function
  | Define ((sym, term), info, rest) ->
    !^"(MuCore.Define"
    ^^^ !^"_"
    ^^^ pp_tuple
          [ pp_tuple [ pp_symbol sym; pp_index_term term ];
            pp_location_info info;
            pp_logical_args ppf rest
          ]
    ^^ !^")"
  | Resource ((sym, (req, bt)), info, rest) ->
    !^"(MuCore.Resource"
    ^^^ !^"_"
    ^^^ !^"(("
    ^^^ pp_symbol sym
    ^^^ !^","
    ^^^ !^"("
    ^^^ pp_request req
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^"))"
    ^^ !^","
    ^^^ pp_location_info info
    ^^ !^","
    ^^^ pp_logical_args ppf rest
    ^^ !^"))"
  | Constraint (lc, info, rest) ->
    !^"(MuCore.Constraint"
    ^^^ !^"_"
    ^^^ pp_tuple
          [ pp_logical_constraint lc; pp_location_info info; pp_logical_args ppf rest ]
    ^^ !^")"
  | I i -> !^"(MuCore.I" ^^^ !^"_" ^^^ ppf i ^^ !^")"


let rec pp_arguments ppf = function
  | Mucore.Computational ((sym, bt), loc, rest) ->
    !^"(MuCore.Computational"
    ^^^ !^"_"
    ^^^ pp_tuple
          [ pp_symbol sym;
            pp_basetype pp_unit bt;
            pp_location_info loc;
            pp_arguments ppf rest
          ]
    ^^ !^")"
  | L at -> !^"(MuCore.L" ^^^ !^"_" ^^^ pp_logical_args ppf at ^^ !^")"


let pp_cn_c_kind = function
  | CF.Cn.C_kind_var -> !^"C_kind_var"
  | C_kind_enum -> !^"C_kind_enum"


let pp_cn_sign = function
  | CF.Cn.CN_unsigned -> !^"CN_unsigned"
  | CN_signed -> !^"CN_signed"


let rec pp_cn_basetype ppfa = function
  | CF.Cn.CN_unit -> !^"(CN_unit" ^^^ !^"_" ^^^ !^")"
  | CN_bool -> !^"(CN_bool" ^^^ !^"_" ^^^ !^")"
  | CN_integer -> !^"(CN_integer" ^^^ !^"_" ^^^ !^")"
  | CN_bits (sign, sz) ->
    !^"(CN_bits" ^^^ !^"_" ^^^ pp_pair pp_cn_sign pp_nat (sign, sz) ^^ !^")"
  | CN_real -> !^"(CN_real" ^^^ !^"_" ^^^ !^")"
  | CN_loc -> !^"(CN_loc" ^^^ !^"_" ^^^ !^")"
  | CN_alloc_id -> !^"(CN_alloc_id" ^^^ !^"_" ^^^ !^")"
  | CN_struct a -> !^"(CN_struct" ^^^ !^"_" ^^^ ppfa a ^^ !^")"
  | CN_record fields ->
    !^"(CN_record"
    ^^^ !^"_"
    ^^^ pp_list (pp_pair pp_identifier (pp_cn_basetype ppfa)) fields
    ^^ !^")"
  | CN_datatype a -> !^"(CN_datatype" ^^^ !^"_" ^^^ ppfa a ^^ !^")"
  | CN_map (k, v) ->
    !^"(CN_map"
    ^^^ !^"_"
    ^^^ pp_pair (pp_cn_basetype ppfa) (pp_cn_basetype ppfa) (k, v)
    ^^ !^")"
  | CN_list t -> !^"(CN_list" ^^^ !^"_" ^^^ pp_cn_basetype ppfa t ^^ !^")"
  | CN_tuple ts -> !^"(CN_tuple" ^^^ !^"_" ^^^ pp_list (pp_cn_basetype ppfa) ts ^^ !^")"
  | CN_set t -> !^"(CN_set" ^^^ !^"_" ^^^ pp_cn_basetype ppfa t ^^ !^")"
  | CN_user_type_name a -> !^"(CN_user_type_name" ^^^ !^"_" ^^^ ppfa a ^^ !^")"
  | CN_c_typedef_name a -> !^"(CN_c_typedef_name" ^^^ !^"_" ^^^ ppfa a ^^ !^")"


let pp_cn_const = function
  | CF.Cn.CNConst_NULL -> !^"CNConst_NULL"
  | CNConst_integer n -> !^"(CNConst_integer" ^^^ !^(Z.to_string n) ^^ !^")"
  | CNConst_bits (sign_sz, n) ->
    !^"(CNConst_bits" ^^^ pp_pair (pp_pair pp_cn_sign pp_nat) pp_Z (sign_sz, n) ^^ !^")"
  | CNConst_bool b -> !^"(CNConst_bool" ^^^ !^(string_of_bool b) ^^ !^")"
  | CNConst_unit -> !^"CNConst_unit"


let pp_cn_binop = function
  | CF.Cn.CN_add -> !^"CN_add"
  | CN_sub -> !^"CN_sub"
  | CN_mul -> !^"CN_mul"
  | CN_div -> !^"CN_div"
  | CN_mod -> !^"CN_mod"
  | CN_equal -> !^"CN_equal"
  | CN_inequal -> !^"CN_inequal"
  | CN_lt -> !^"CN_lt"
  | CN_le -> !^"CN_le"
  | CN_gt -> !^"CN_gt"
  | CN_ge -> !^"CN_ge"
  | CN_or -> !^"CN_or"
  | CN_and -> !^"CN_and"
  | CN_implies -> !^"CN_implies"
  | CN_map_get -> !^"CN_map_get"
  | CN_band -> !^"CN_band"
  | CN_bor -> !^"CN_bor"
  | CN_bxor -> !^"CN_bxor"


let rec pp_cn_pat ppfa = function
  | CF.Cn.CNPat (loc, pat) ->
    !^"(CNPat"
    ^^^ pp_location loc
    ^^^ (match pat with
         | CNPat_sym s -> !^"(CNPat_sym" ^^^ ppfa s ^^ !^")"
         | CNPat_wild -> !^"CNPat_wild"
         | CNPat_constructor (s, args) ->
           !^"(CNPat_constructor"
           ^^^ ppfa s
           ^^^ pp_list (pp_pair pp_identifier (pp_cn_pat ppfa)) args
           ^^ !^")")
    ^^ !^")"


let rec pp_cn_expr ppfa ppfty = function
  | CF.Cn.CNExpr (loc, e) ->
    !^"(CNExpr"
    ^^^ pp_cn_type_args
    ^^^ !^"("
    ^^^ pp_location loc
    ^^^ !^","
    ^^^ (match e with
         | CNExpr_const c ->
           !^"(CNExpr_const" ^^^ pp_cn_type_args ^^^ pp_cn_const c ^^ !^")"
         | CNExpr_var v -> !^"(CNExpr_var" ^^^ pp_cn_type_args ^^^ ppfa v ^^ !^")"
         | CNExpr_list es ->
           !^"(CNExpr_list"
           ^^^ pp_cn_type_args
           ^^^ pp_list (pp_cn_expr ppfa ppfty) es
           ^^ !^")"
         | CNExpr_memberof (e, id) ->
           !^"(CNExpr_memberof"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ pp_cn_expr ppfa ppfty e; pp_identifier id ]
           ^^ !^")"
         | CNExpr_arrow (e, id) ->
           !^"(CNExpr_arrow"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ pp_cn_expr ppfa ppfty e; pp_identifier id ]
           ^^ !^")"
         | CNExpr_record fs ->
           !^"(CNExpr_record"
           ^^^ pp_cn_type_args
           ^^^ pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) fs
           ^^ !^")"
         | CNExpr_struct (a, fs) ->
           !^"(CNExpr_struct"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ ppfa a; pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) fs ]
           ^^ !^")"
         | CNExpr_memberupdates (e, us) ->
           !^"(CNExpr_memberupdates"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_expr ppfa ppfty e;
                   pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) us
                 ]
           ^^ !^")"
         | CNExpr_arrayindexupdates (e, us) ->
           !^"(CNExpr_arrayindexupdates"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_expr ppfa ppfty e;
                   pp_list (pp_pair (pp_cn_expr ppfa ppfty) (pp_cn_expr ppfa ppfty)) us
                 ]
           ^^ !^")"
         | CNExpr_binop (op, e1, e2) ->
           !^"(CNExpr_binop"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_binop op; pp_cn_expr ppfa ppfty e1; pp_cn_expr ppfa ppfty e2 ]
           ^^ !^")"
         | CNExpr_sizeof ty ->
           !^"(CNExpr_sizeof" ^^^ pp_cn_type_args ^^^ ppfty ty ^^ !^")"
         | CNExpr_offsetof (a, id) ->
           !^"(CNExpr_offsetof"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ ppfa a; pp_identifier id ]
           ^^ !^")"
         | CNExpr_membershift (e, oa, id) ->
           !^"(CNExpr_membershift"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ pp_cn_expr ppfa ppfty e; pp_option ppfa oa; pp_identifier id ]
           ^^ !^")"
         | CNExpr_addr a -> !^"(CNExpr_addr" ^^^ pp_cn_type_args ^^^ ppfa a ^^ !^")"
         | CNExpr_cast (bt, e) ->
           !^"(CNExpr_cast"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ pp_cn_basetype ppfa bt; pp_cn_expr ppfa ppfty e ]
           ^^ !^")"
         | CNExpr_array_shift (e, oty, idx) ->
           !^"(CNExpr_array_shift"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_expr ppfa ppfty e;
                   pp_option ppfty oty;
                   pp_cn_expr ppfa ppfty idx
                 ]
           ^^ !^")"
         | CNExpr_call (a, args) ->
           !^"(CNExpr_call"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ ppfa a; pp_list (pp_cn_expr ppfa ppfty) args ]
           ^^ !^")"
         | CNExpr_cons (a, args) ->
           !^"(CNExpr_cons"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ ppfa a; pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) args ]
           ^^ !^")"
         | CNExpr_each (a, bt, rng, e) ->
           !^"(CNExpr_each"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ ppfa a;
                   pp_cn_basetype ppfa bt;
                   pp_pair pp_Z pp_Z rng;
                   pp_cn_expr ppfa ppfty e
                 ]
           ^^ !^")"
         | CNExpr_let (a, e1, e2) ->
           !^"(CNExpr_let"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ ppfa a; pp_cn_expr ppfa ppfty e1; pp_cn_expr ppfa ppfty e2 ]
           ^^ !^")"
         | CNExpr_match (e, cases) ->
           !^"(CNExpr_match"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_expr ppfa ppfty e;
                   pp_list (pp_pair (pp_cn_pat ppfa) (pp_cn_expr ppfa ppfty)) cases
                 ]
           ^^ !^")"
         | CNExpr_ite (c, t, e) ->
           !^"(CNExpr_ite"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple
                 [ pp_cn_expr ppfa ppfty c;
                   pp_cn_expr ppfa ppfty t;
                   pp_cn_expr ppfa ppfty e
                 ]
           ^^ !^")"
         | CNExpr_good (ty, e) ->
           !^"(CNExpr_good"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ ppfty ty; pp_cn_expr ppfa ppfty e ]
           ^^ !^")"
         | CNExpr_deref e ->
           !^"(CNExpr_deref" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_value_of_c_atom (a, k) ->
           !^"(CNExpr_value_of_c_atom"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ ppfa a; pp_cn_c_kind k ]
           ^^ !^")"
         | CNExpr_unchanged e ->
           !^"(CNExpr_unchanged" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_at_env (e, s) ->
           !^"(CNExpr_at_env"
           ^^^ pp_cn_type_args
           ^^^ pp_tuple [ pp_cn_expr ppfa ppfty e; pp_string s ]
           ^^ !^")"
         | CNExpr_not e ->
           !^"(CNExpr_not" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_negate e ->
           !^"(CNExpr_negate" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_default bt ->
           !^"(CNExpr_default" ^^^ pp_cn_type_args ^^^ pp_cn_basetype ppfa bt ^^ !^")"
         | CNExpr_bnot e ->
           !^"(CNExpr_bnot" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty e ^^ !^")")
    ^^ !^"))"


let rec pp_cn_resource ppfa ppfty = function
  | CF.Cn.CN_pred (loc, pred, args) ->
    !^"(CN_pred"
    ^^^ pp_cn_type_args
    ^^^ pp_location loc
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) args
    ^^ !^")"
  | CN_each (a, bt, e, loc, pred, args) ->
    !^"(CN_each"
    ^^^ pp_cn_type_args
    ^^^ ppfa a
    ^^^ pp_cn_basetype ppfa bt
    ^^^ pp_cn_expr ppfa ppfty e
    ^^^ pp_location loc
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) args
    ^^ !^")"


and pp_cn_pred ppfa ppfty = function
  | CF.Cn.CN_owned ty -> !^"(CN_owned" ^^^ pp_cn_type_args ^^^ pp_option ppfty ty ^^ !^")"
  | CN_block ty -> !^"(CN_block" ^^^ pp_cn_type_args ^^^ pp_option ppfty ty ^^ !^")"
  | CN_named a -> !^"(CN_named" ^^^ pp_cn_type_args ^^^ ppfa a ^^ !^")"


let pp_cn_to_extract ppfa ppfty = function
  | CF.Cn.E_Pred pred -> !^"(E_Pred" ^^^ pp_cn_pred ppfa ppfty pred ^^ !^")"
  | CF.Cn.E_Everything -> !^"E_Everything"


let pp_cn_assertion ppfa ppfty = function
  | CF.Cn.CN_assert_exp ex ->
    !^"(CN_assert_exp" ^^^ pp_cn_type_args ^^^ pp_cn_expr ppfa ppfty ex ^^ !^")"
  | CN_assert_qexp (sym, bt, it1, it2) ->
    !^"(CN_assert_qexp"
    ^^^ pp_cn_type_args
    ^^^ ppfa sym
    ^^^ pp_cn_basetype ppfa bt
    ^^^ pp_cn_expr ppfa ppfty it1
    ^^^ pp_cn_expr ppfa ppfty it2
    ^^ !^")"


let pp_cn_condition ppfa ppfty = function
  | CF.Cn.CN_cletResource (loc, sym, res) ->
    !^"(CN_cletResource"
    ^^^ pp_cn_type_args
    ^^^ pp_location loc
    ^^^ ppfa sym
    ^^^ pp_cn_resource ppfa ppfty res
    ^^ !^")"
  | CN_cletExpr (loc, sym, ex) ->
    !^"(CN_cletExpr"
    ^^^ pp_cn_type_args
    ^^^ pp_location loc
    ^^^ ppfa sym
    ^^^ pp_cn_expr ppfa ppfty ex
    ^^ !^")"
  | CN_cconstr (loc, assertion) ->
    !^"(CN_cconstr"
    ^^^ pp_cn_type_args
    ^^^ pp_location loc
    ^^^ pp_cn_assertion ppfa ppfty assertion
    ^^ !^")"


let pp_cnprog_statement = function
  | Cnprog.Pack_unpack (pu, pred) ->
    !^"(Pack_unpack" ^^^ pp_pack_unpack pu ^^^ pp_request_ppredicate pred ^^ !^")"
  | To_from_bytes (tf, pred) ->
    !^"(To_from_bytes" ^^^ pp_to_from tf ^^^ pp_request_ppredicate pred ^^ !^")"
  | Have lc -> !^"(Have" ^^^ pp_logical_constraint lc ^^ !^")"
  | Instantiate (inst, term) ->
    !^"(Instantiate"
    ^^^ pp_cn_to_instantiate pp_symbol pp_sctype inst
    ^^^ pp_index_term term
    ^^ !^")"
  | Split_case lc -> !^"(Split_case" ^^^ pp_logical_constraint lc ^^ !^")"
  | Extract (ids, ext, term) ->
    !^"(Extract"
    ^^^ pp_list pp_identifier ids
    ^^^ pp_cn_to_extract pp_symbol pp_sctype ext
    ^^^ pp_index_term term
    ^^ !^")"
  | Unfold (sym, terms) ->
    !^"(Unfold" ^^^ pp_symbol sym ^^^ pp_list pp_index_term terms ^^ !^")"
  | Apply (sym, terms) ->
    !^"(Apply" ^^^ pp_symbol sym ^^^ pp_list pp_index_term terms ^^ !^")"
  | Assert lc -> !^"(Assert" ^^^ pp_logical_constraint lc ^^ !^")"
  | Inline syms -> !^"(Inline" ^^^ pp_list pp_symbol syms ^^ !^")"
  | Print term -> !^"(Print" ^^^ pp_index_term term ^^ !^")"


let rec pp_cn_prog = function
  | Cnprog.Let (loc, (name, { ct; pointer }), prog) ->
    !^"(Let" ^^^ pp_location loc ^^^ pp_symbol name ^^^ pp_cn_prog prog ^^ !^")"
  | Statement (loc, stmt) ->
    !^"(Statement" ^^^ pp_location loc ^^^ pp_cnprog_statement stmt ^^ !^")"


let rec pp_cn_statement ppfa ppfty (CF.Cn.CN_statement (loc, stmt)) =
  !^"(CN_statement"
  ^^^ pp_location loc
  ^^^
  match stmt with
  | CN_pack_unpack (pu, pred, exprs) ->
    !^"(CN_pack_unpack"
    ^^^ pp_pack_unpack pu
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) exprs
    ^^ !^")"
  | CN_to_from_bytes (tf, pred, exprs) ->
    !^"(CN_to_from_bytes"
    ^^^ pp_to_from tf
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) exprs
    ^^ !^")"
  | CN_have assertion -> !^"(CN_have" ^^^ pp_cn_assertion ppfa ppfty assertion ^^ !^")"
  | CN_instantiate (inst, expr) ->
    !^"(CN_instantiate"
    ^^^ pp_cn_to_instantiate ppfa ppfty inst
    ^^^ pp_cn_expr ppfa ppfty expr
    ^^ !^")"
  | CN_split_case assertion ->
    !^"(CN_split_case" ^^^ pp_cn_assertion ppfa ppfty assertion ^^ !^")"
  | CN_extract (ids, extract, expr) ->
    !^"(CN_extract"
    ^^^ pp_list pp_identifier ids
    ^^^ pp_cn_to_extract ppfa ppfty extract
    ^^^ pp_cn_expr ppfa ppfty expr
    ^^ !^")"
  | CN_unfold (sym, exprs) ->
    !^"(CN_unfold" ^^^ ppfa sym ^^^ pp_list (pp_cn_expr ppfa ppfty) exprs ^^ !^")"
  | CN_assert_stmt assertion ->
    !^"(CN_assert_stmt" ^^^ pp_cn_assertion ppfa ppfty assertion ^^ !^")"
  | CN_apply (sym, exprs) ->
    !^"(CN_apply" ^^^ ppfa sym ^^^ pp_list (pp_cn_expr ppfa ppfty) exprs ^^ !^")"
  | CN_inline syms -> !^"(CN_inline" ^^^ pp_list ppfa syms ^^ !^")"
  | CN_print expr -> !^"(CN_print" ^^^ pp_cn_expr ppfa ppfty expr ^^ !^")" ^^ !^")"


and pp_expr pp_type (Expr (loc, annots, ty, e)) =
  !^"(Expr"
  ^^^ !^"_"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^ (match e with
       | Epure pe -> !^"(Epure" ^^^ !^"_" ^^^ pp_pexpr pp_type pe ^^ !^")"
       | Ememop m -> !^"(Ememop" ^^^ !^"_" ^^^ pp_memop pp_type m ^^ !^")"
       | Eaction pa -> !^"(Eaction" ^^^ !^"_" ^^^ pp_paction pp_type pa ^^ !^")"
       | Eskip -> !^"(Eskip" ^^^ !^"_)"
       | Eccall (act, f, args) ->
         !^"(Eccall"
         ^^^ !^"_"
         ^^^ pp_act act
         ^^^ pp_pexpr pp_type f
         ^^^ pp_list (pp_pexpr pp_type) args
         ^^ !^")"
       | Elet (pat, e1, e2) ->
         !^"(Elet"
         ^^^ !^"_"
         ^^^ pp_pattern pp_type pat
         ^^^ pp_pexpr pp_type e1
         ^^^ pp_expr pp_type e2
         ^^ !^")"
       | Eunseq exprs ->
         !^"(Eunseq" ^^^ !^"_" ^^^ pp_list (pp_expr pp_type) exprs ^^ !^")"
       | Ewseq (pat, e1, e2) ->
         !^"(Ewseq"
         ^^^ !^"_"
         ^^^ pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
         ^^ !^")"
       | Esseq (pat, e1, e2) ->
         !^"(Esseq"
         ^^^ !^"_"
         ^^^ pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
         ^^ !^")"
       | Eif (c, t, e) ->
         !^"(Eif"
         ^^^ !^"_"
         ^^^ pp_pexpr pp_type c
         ^^^ pp_expr pp_type t
         ^^^ pp_expr pp_type e
         ^^ !^")"
       | Ebound e -> !^"(Ebound" ^^^ !^"_" ^^^ pp_expr pp_type e ^^ !^")"
       | End exprs -> !^"(End" ^^^ !^"_" ^^^ pp_list (pp_expr pp_type) exprs ^^ !^")"
       | Erun (sym, args) ->
         !^"(Erun"
         ^^^ !^"_"
         ^^^ pp_tuple [ pp_symbol sym; pp_list (pp_pexpr pp_type) args ]
         ^^ !^")"
       | CN_progs (stmts, progs) ->
         !^"(CN_progs"
         ^^^ !^"_"
         ^^^ pp_list (pp_cn_statement pp_symbol pp_ctype) stmts
         ^^^ pp_list pp_cn_prog progs
         ^^ !^")")
  ^^^ !^")"


let pp_parse_ast_label_spec (s : parse_ast_label_spec) =
  pp_record [ ("label_spec", pp_list (pp_cn_condition pp_symbol pp_ctype) s.label_spec) ]


let pp_label_def pp_type = function
  | Return loc -> !^"(Return" ^^^ !^"_" ^^^ pp_location loc ^^ !^")"
  | Label (loc, args, annots, spec, `Loop loop_locs) ->
    !^"(Label"
    ^^^ pp_location loc
    ^^^ pp_arguments (pp_expr pp_type) args
    ^^^ pp_list pp_annot_t annots
    ^^^ pp_parse_ast_label_spec spec
    ^^^ pp_pair pp_location pp_location loop_locs
    ^^ !^")"


let pp_args_and_body pp_type (args : 'a args_and_body) =
  pp_arguments
    (fun (body, (labels : (Symbol.sym, 'a label_def) Pmap.map), (rt : ReturnTypes.t)) ->
      !^"("
      ^^^ pp_expr pp_type body
      ^^ !^","
      ^^^ pp_pmap "Sym.map_from_list" pp_symbol (pp_label_def pp_type) labels
      ^^ !^","
      ^^^ pp_return_type rt
      ^^ !^")")
    args


let pp_desugared_spec { accesses; requires; ensures } =
  pp_record
    [ ("accesses", pp_list (pp_pair pp_symbol pp_ctype) accesses);
      ("requires", pp_list (pp_cn_condition pp_symbol pp_ctype) requires);
      ("ensures", pp_list (pp_cn_condition pp_symbol pp_ctype) ensures)
    ]


let rec pp_logical_argument_types pp_type = function
  | LogicalArgumentTypes.I i -> !^"(I" ^^^ pp_type i ^^ !^")"
  | Resource ((sym, (req, bt)), info, at) ->
    !^"(LogicalArgumentTypes.Resource"
    ^^^ pp_tuple [ pp_symbol sym; pp_tuple [ pp_request req; pp_basetype pp_unit bt ] ]
    ^^^ pp_location_info info
    ^^^ pp_logical_argument_types pp_type at
    ^^ !^")"
  | Constraint (lc, info, at) ->
    !^"(LogicalArgumentTypes.Constraint"
    ^^^ pp_logical_constraint lc
    ^^^ pp_location_info info
    ^^^ pp_logical_argument_types pp_type at
    ^^ !^")"
  | LogicalArgumentTypes.Define (si, info, at) ->
    !^"(LogicalArgumentTypes.Define"
    ^^^ (pp_pair pp_symbol pp_index_term) si
    ^^^ pp_location_info info
    ^^^ pp_logical_argument_types pp_type at
    ^^ !^")"


let rec pp_argument_types pp_type = function
  | ArgumentTypes.Computational ((sym, bt), info, at) ->
    !^"(ArgumentTypes.Computational"
    ^^^ !^"_"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_location_info info
    ^^^ pp_argument_types pp_type at
    ^^^ !^")"
  | L at ->
    !^"(ArgumentTypes.L" ^^^ !^"_" ^^^ pp_logical_argument_types pp_type at ^^ !^")"


let coq_prologue =
  !^"From MuCore Require Import Annot ArgumentTypes Core BaseTypes CN CNProgs Ctype \
     False Id ImplMem IndexTerms IntegerType Location Locations LogicalArgumentTypes \
     LogicalConstraints LogicalReturnTypes Memory MuCore Request ReturnTypes SCtypes Sym \
     Symbol Terms Undefined Utils."
  ^^ P.hardline
  ^^ !^"Require Import Coq.Lists.List."
  ^^ P.hardline
  ^^ !^"Import ListNotations."
  ^^ P.hardline
  ^^ !^"Require Import Coq.Strings.String."
  ^^ P.hardline
  ^^ !^"Open Scope string_scope."
  ^^ P.hardline
  ^^ !^"Require Import ZArith."
  ^^ P.hardline


let pp_file pp_type pp_type_name file =
  coq_prologue
  ^^ P.hardline
  ^^ P.hardline
  (* Print globals *)
  ^^ !^"(* Global definitions *)"
  ^^ P.hardline
  ^^ List.fold_left
       (fun acc (sym, glob) ->
         acc
         ^^
         match glob with
         | GlobalDef (ct, e) ->
           coq_def
             (Pp_symbol.to_string sym)
             P.empty
             (!^"GlobalDef" ^^^ pp_sctype ct ^^^ pp_expr pp_type e)
           ^^ P.hardline
         | GlobalDecl ct ->
           coq_def (Pp_symbol.to_string sym) P.empty (!^"GlobalDecl" ^^^ pp_sctype ct)
           ^^ P.hardline)
       P.empty
       file.globs
  (* Print functions *)
  ^^ !^"(* Function definitions *)"
  ^^ P.hardline
  ^^ Pmap.fold
       (fun sym decl acc ->
         acc
         ^^
         match decl with
         | ProcDecl (loc, ft) ->
           coq_def
             (Pp_symbol.to_string_pretty_cn sym)
             P.empty
             (!^"ProcDecl"
              ^^^ pp_type_name
              ^^^ pp_location loc
              ^^^ pp_option (pp_argument_types pp_return_type) ft)
         | Proc { loc; args_and_body; trusted; desugared_spec } ->
           coq_def
             (Pp_symbol.to_string_pretty_cn sym)
             P.empty
             (!^"Proc"
              ^^^ pp_type_name
              ^^^ pp_location loc
              ^^^ pp_args_and_body pp_type args_and_body
              ^^^ pp_trusted trusted
              ^^^ pp_desugared_spec desugared_spec))
       file.funs
       P.empty


(* let pp_file_string file = Pp_utils.to_plain_string (pp_file file) *)

let pp_unit_file (f : unit file) = pp_file pp_unit pp_unit_type f
