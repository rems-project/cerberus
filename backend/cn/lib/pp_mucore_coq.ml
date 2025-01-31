[@@@warning "-32-27-26"] (* Disable unused value warnings and unused variable warnings *)

open Cerb_pp_prelude
module CF = Cerb_frontend
open CF
module P = PPrint
open Mucore

(* temporary debug option to supress printing of noisy locations *)
let debug_print_locations = false (* Set to true to print actual locations *)

let pp_underscore = !^"_"

let pp_Z z =
  let s = Z.to_string z in
  if Z.lt z Z.zero then !^("(" ^ s ^ ")%Z") else !^(s ^ "%Z")


let pp_Q q = !^("(" ^ Q.to_string q ^ ")%Q")

(* Prints int as a Coq `nat` *)
let pp_nat n = !^(string_of_int n)

let pp_Z_as_nat z = pp_nat (Z.to_int z)

(* Prints int as a Coq `Z` *)
let pp_int i = pp_Z (Z.of_int i)

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


let pp_tuple l =
  P.group
    (!^"("
     ^^ P.nest
          2
          (P.break 0 ^^ P.separate_map (P.break 1 ^^ !^"," ^^ P.break 1) (fun x -> x) l)
     ^^ P.break 0
     ^^ !^")")


let pp_pair p1 p2 (a, b) = pp_tuple [ p1 a; p2 b ]

let pp_triple p1 p2 p3 (a, b, c) = pp_tuple [ p1 a; p2 b; p3 c ]

let pp_pmap
  fromlist_fun
  (pp_key : 'a -> P.document)
  (pp_value : 'b -> P.document)
  (m : ('a, 'b) Pmap.map)
  =
  P.parens (!^fromlist_fun ^^^ pp_list (pp_pair pp_key pp_value) (Pmap.bindings_list m))


let pp_bool b = if b then !^"true" else !^"false"

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


let pp_comment s = !^("(* " ^ s ^ " *)")

let coq_notation name args body =
  !^"Notation" ^^^ !^("\"" ^ name ^ "\"") ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."


let pp_record fields =
  P.group
    (!^"{|"
     ^^ P.nest
          2
          (P.break 1
           ^^ P.separate_map
                (!^";" ^^ P.break 1)
                (fun (name, value) ->
                  P.group (!^(name ^ " :=") ^^ P.nest 2 (P.break 1 ^^ value)))
                fields)
     ^^ P.break 1
     ^^ !^"|}")


let pp_constructor name args =
  if List.length args = 0 then
    !^name
  else
    P.group
      (!^"("
       ^^ !^name
       ^^ P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1) (fun x -> x) args)
       ^^ !^")")


let pp_option pp_elem = function
  | None -> pp_constructor "None" []
  | Some x -> pp_constructor "Some" [ pp_elem x ]


let pp_undefined_behaviour = function
  | Undefined.DUMMY str -> pp_constructor "DUMMY" [ pp_string str ]
  | Undefined.UB_unspecified_lvalue -> pp_constructor "UB_unspecified_lvalue" []
  | Undefined.UB_std_omission om ->
    pp_constructor
      "UB_std_omission"
      [ (match om with
         | UB_OMIT_memcpy_non_object -> pp_constructor "UB_OMIT_memcpy_non_object" []
         | UB_OMIT_memcpy_out_of_bound -> pp_constructor "UB_OMIT_memcpy_out_of_bound" [])
      ]
  | Undefined.Invalid_format str -> pp_constructor "Invalid_format" [ pp_string str ]
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
  | CF.Linux.Once -> pp_constructor "Once" []
  | LAcquire -> pp_constructor "LAcquire" []
  | LRelease -> pp_constructor "LRelease" []
  | Rmb -> pp_constructor "Rmb" []
  | Wmb -> pp_constructor "Wmb" []
  | Mb -> pp_constructor "Mb" []
  | RbDep -> pp_constructor "RbDep" []
  | RcuLock -> pp_constructor "RcuLock" []
  | RcuUnlock -> pp_constructor "RcuUnlock" []
  | SyncRcu -> pp_constructor "SyncRcu" []


let pp_floating_value v = Impl_mem.pp_floating_value_for_coq v

let pp_pointer_value v = Impl_mem.pp_pointer_value_for_coq v

let pp_unit (_ : unit) = !^"tt"

let pp_unit_type = !^"unit"

let pp_memory_order = function
  | Cerb_frontend.Cmm_csem.NA -> pp_constructor "NA" []
  | Seq_cst -> pp_constructor "Seq_cst" []
  | Relaxed -> pp_constructor "Relaxed" []
  | Release -> pp_constructor "Release" []
  | Acquire -> pp_constructor "Acquire" []
  | Consume -> pp_constructor "Consume" []
  | Acq_rel -> pp_constructor "Acq_rel" []


let pp_polarity = function Core.Pos -> !^"Pos" | Core.Neg -> !^"Neg"

let pp_lexing_position { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum } =
  pp_record
    [ ("pos_fname", pp_string pos_fname);
      ("pos_lnum", pp_nat pos_lnum);
      ("pos_bol", pp_nat pos_bol);
      ("pos_cnum", pp_nat pos_cnum)
    ]


let pp_location_cursor = function
  | Cerb_location.NoCursor -> pp_constructor "NoCursor" []
  | Cerb_location.PointCursor pos ->
    pp_constructor "PointCursor" [ pp_lexing_position pos ]
  | Cerb_location.RegionCursor (start_pos, end_pos) ->
    pp_constructor
      "RegionCursor"
      [ pp_lexing_position start_pos; pp_lexing_position end_pos ]


let pp_location = function
  | Cerb_location.Loc_unknown -> pp_constructor "Loc_unknown" []
  | _ when not debug_print_locations -> pp_constructor "Loc_unknown" []
  | Cerb_location.Loc_other s -> pp_constructor "Loc_other" [ pp_string s ]
  | Cerb_location.Loc_point pos -> pp_constructor "Loc_point" [ pp_lexing_position pos ]
  | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
    pp_constructor
      "Loc_region"
      [ pp_lexing_position start_pos;
        pp_lexing_position end_pos;
        pp_location_cursor cursor
      ]
  | Cerb_location.Loc_regions (pos_list, cursor) ->
    let pp_pos_pair ppair = pp_pair pp_lexing_position pp_lexing_position ppair in
    pp_constructor
      "Loc_regions"
      [ pp_list pp_pos_pair pos_list; pp_location_cursor cursor ]


let pp_identifier (CF.Symbol.Identifier (loc, s)) =
  pp_constructor "Identifier" [ pp_location loc; pp_string s ]


let pp_digest (d : Digest.t) =
  let string_to_hex s =
    let hex_of_char c = Printf.sprintf "%02x" (Char.code c) in
    String.concat "" (List.map hex_of_char (String.to_seq s |> List.of_seq))
  in
  (* We are not using Digest.to_hex as it is gives error on invalid digest values *)
  pp_string (string_to_hex d)


let rec pp_symbol_description = function
  | CF.Symbol.SD_None -> pp_constructor "SD_None" []
  | CF.Symbol.SD_unnamed_tag loc -> pp_constructor "SD_unnamed_tag" [ pp_location loc ]
  | CF.Symbol.SD_Id s -> pp_constructor "SD_Id" [ pp_string s ]
  | CF.Symbol.SD_CN_Id s -> pp_constructor "SD_CN_Id" [ pp_string s ]
  | CF.Symbol.SD_ObjectAddress s -> pp_constructor "SD_ObjectAddress" [ pp_string s ]
  | CF.Symbol.SD_Return -> pp_constructor "SD_Return" []
  | CF.Symbol.SD_FunArgValue s -> pp_constructor "SD_FunArgValue" [ pp_string s ]
  | CF.Symbol.SD_FunArg (loc, n) ->
    pp_constructor "SD_FunArg" [ pp_location loc; pp_nat n ]


and pp_symbol (CF.Symbol.Symbol (d, n, sd)) =
  pp_constructor "Symbol" [ pp_digest d; pp_nat n; pp_symbol_description sd ]


and pp_symbol_prefix = function
  | CF.Symbol.PrefSource (loc, syms) ->
    pp_constructor "PrefSource" [ pp_location loc; pp_list pp_symbol syms ]
  | CF.Symbol.PrefFunArg (loc, d, z) ->
    pp_constructor "PrefFunArg" [ pp_location loc; pp_digest d; pp_int z ]
  | CF.Symbol.PrefStringLiteral (loc, d) ->
    pp_constructor "PrefStringLiteral" [ pp_location loc; pp_digest d ]
  | CF.Symbol.PrefTemporaryLifetime (loc, d) ->
    pp_constructor "PrefTemporaryLifetime" [ pp_location loc; pp_digest d ]
  | CF.Symbol.PrefCompoundLiteral (loc, d) ->
    pp_constructor "PrefCompoundLiteral" [ pp_location loc; pp_digest d ]
  | CF.Symbol.PrefMalloc -> pp_constructor "PrefMalloc" []
  | CF.Symbol.PrefOther s -> pp_constructor "PrefOther" [ !^s ]


let pp_sign = function
  | BaseTypes.Signed -> pp_constructor "BaseTypes.Signed" []
  | BaseTypes.Unsigned -> pp_constructor "BaseTypes.Unsigned" []


(* Unit type is hardcoded bacause `BaseTypes.t` is defined as `t_gen unit` *)
let rec pp_basetype pp_loc = function
  | BaseTypes.Unit -> pp_constructor "BaseTypes.Unit" [ !^"unit" ]
  | BaseTypes.Bool -> pp_constructor "BaseTypes.Bool" [ !^"unit" ]
  | BaseTypes.Integer -> pp_constructor "BaseTypes.Integer" [ !^"unit" ]
  | BaseTypes.MemByte -> pp_constructor "BaseTypes.MemByte" [ !^"unit" ]
  | BaseTypes.Bits (sign, n) ->
    pp_constructor "BaseTypes.Bits" [ !^"unit"; pp_sign sign; pp_nat n ]
  | BaseTypes.Real -> pp_constructor "BaseTypes.Real" [ !^"unit" ]
  | BaseTypes.Alloc_id -> pp_constructor "BaseTypes.Alloc_id" [ !^"unit" ]
  | BaseTypes.CType -> pp_constructor "BaseTypes.CType" [ !^"unit" ]
  | BaseTypes.Struct sym -> pp_constructor "BaseTypes.Struct" [ !^"unit"; pp_symbol sym ]
  | BaseTypes.Datatype sym ->
    pp_constructor "BaseTypes.Datatype" [ !^"unit"; pp_symbol sym ]
  | BaseTypes.Record fields ->
    pp_constructor
      "BaseTypes.Record"
      [ !^"unit"; pp_list (pp_pair pp_identifier (pp_basetype pp_loc)) fields ]
  | BaseTypes.Map (t1, t2) ->
    pp_constructor
      "BaseTypes.Map"
      [ !^"unit"; pp_basetype pp_loc t1; pp_basetype pp_loc t2 ]
  | BaseTypes.List t -> pp_constructor "BaseTypes.List" [ !^"unit"; pp_basetype pp_loc t ]
  | BaseTypes.Tuple ts ->
    pp_constructor "BaseTypes.Tuple" [ !^"unit"; pp_list (pp_basetype pp_loc) ts ]
  | BaseTypes.Set t -> pp_constructor "BaseTypes.Set" [ !^"unit"; pp_basetype pp_loc t ]
  | BaseTypes.Loc x -> pp_constructor "BaseTypes.Loc" [ !^"unit"; pp_unit x ]


let pp_integer_base_type = function
  | Sctypes.IntegerBaseTypes.Ichar -> pp_constructor "Ichar" []
  | Sctypes.IntegerBaseTypes.Short -> pp_constructor "Short" []
  | Sctypes.IntegerBaseTypes.Int_ -> pp_constructor "Int_" []
  | Sctypes.IntegerBaseTypes.Long -> pp_constructor "Long" []
  | Sctypes.IntegerBaseTypes.LongLong -> pp_constructor "LongLong" []
  | Sctypes.IntegerBaseTypes.IntN_t n -> pp_constructor "IntN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Int_leastN_t n -> pp_constructor "Int_leastN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Int_fastN_t n -> pp_constructor "Int_fastN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Intmax_t -> pp_constructor "Intmax_t" []
  | Sctypes.IntegerBaseTypes.Intptr_t -> pp_constructor "Intptr_t" []


let pp_integer_type = function
  | Sctypes.IntegerTypes.Char -> pp_constructor "Char" []
  | Sctypes.IntegerTypes.Bool -> pp_constructor "Bool" []
  | Sctypes.IntegerTypes.Signed ibt ->
    pp_constructor "Signed" [ pp_integer_base_type ibt ]
  | Sctypes.IntegerTypes.Unsigned ibt ->
    pp_constructor "Unsigned" [ pp_integer_base_type ibt ]
  | Sctypes.IntegerTypes.Enum sym -> pp_constructor "Enum" [ pp_symbol sym ]
  | Sctypes.IntegerTypes.Wchar_t -> pp_constructor "Wchar_t" []
  | Sctypes.IntegerTypes.Wint_t -> pp_constructor "Wint_t" []
  | Sctypes.IntegerTypes.Size_t -> pp_constructor "Size_t" []
  | Sctypes.IntegerTypes.Ptrdiff_t -> pp_constructor "Ptrdiff_t" []
  | Sctypes.IntegerTypes.Ptraddr_t -> pp_constructor "Ptraddr_t" []


let rec pp_annot_t = function
  | Annot.Astd s -> pp_constructor "Astd" [ pp_string s ]
  | Annot.Aloc loc -> pp_constructor "Aloc" [ pp_location loc ]
  | Annot.Auid s -> pp_constructor "Auid" [ pp_string s ]
  | Annot.Amarker n -> pp_constructor "Amarker" [ pp_nat n ]
  | Annot.Amarker_object_types n -> pp_constructor "Amarker_object_types" [ pp_nat n ]
  | Annot.Abmc bmc -> pp_constructor "Abmc" [ pp_bmc_annot bmc ]
  | Annot.Aattrs attrs -> pp_constructor "Aattrs" [ pp_attributes attrs ]
  | Annot.Atypedef sym -> pp_constructor "Atypedef" [ pp_symbol sym ]
  | Annot.Anot_explode -> pp_constructor "Anot_explode" []
  | Annot.Alabel la -> pp_constructor "Alabel" [ pp_label_annot la ]
  | Annot.Acerb ca -> pp_constructor "Acerb" [ pp_cerb_attribute ca ]
  | Annot.Avalue va -> pp_constructor "Avalue" [ pp_value_annot va ]
  | Annot.Ainlined_label (loc, sym, la) ->
    pp_constructor "Ainlined_label" [ pp_location loc; pp_symbol sym; pp_label_annot la ]
  | Annot.Astmt -> pp_constructor "Astmt" []
  | Annot.Aexpr -> pp_constructor "Aexpr" []


and pp_bmc_annot = function Annot.Abmc_id n -> pp_constructor "Abmc_id" [ pp_nat n ]

and pp_attributes (Annot.Attrs attrs) =
  pp_constructor "Attrs" [ pp_list pp_attribute attrs ]


and pp_attribute attr =
  pp_record
    [ ("attr_ns", pp_option pp_identifier attr.Annot.attr_ns);
      ("attr_id", pp_identifier attr.attr_id);
      ("attr_args", pp_list pp_attr_arg attr.attr_args)
    ]


and pp_attr_arg (loc, s, args) =
  pp_tuple [ pp_location loc; pp_string s; pp_list (pp_pair pp_location pp_string) args ]


and pp_label_annot = function
  | Annot.LAloop n -> pp_constructor "LAloop" [ pp_nat n ]
  | Annot.LAloop_continue n -> pp_constructor "LAloop_continue" [ pp_nat n ]
  | Annot.LAloop_break n -> pp_constructor "LAloop_break" [ pp_nat n ]
  | Annot.LAreturn -> pp_constructor "LAreturn" []
  | Annot.LAswitch -> pp_constructor "LAswitch" []
  | Annot.LAcase -> pp_constructor "LAcase" []
  | Annot.LAdefault -> pp_constructor "LAdefault" []
  | Annot.LAactual_label -> pp_constructor "LAactual_label" []


and pp_cerb_attribute = function
  | Annot.ACerb_with_address n -> pp_constructor "ACerb_with_address" [ pp_Z_as_nat n ]
  | Annot.ACerb_hidden -> pp_constructor "ACerb_hidden" []


and pp_value_annot = function
  | Annot.Ainteger it -> pp_constructor "Ainteger" [ pp_integer_type it ]


let pp_qualifiers quals =
  pp_record
    [ ("Ctype.const", pp_bool quals.Ctype.const);
      ("Ctype.restrict", pp_bool quals.Ctype.restrict);
      ("Ctype.volatile", pp_bool quals.Ctype.volatile)
    ]


let rec pp_ctype (Ctype.Ctype (annots, ct)) =
  pp_constructor
    "Ctype"
    [ pp_list pp_annot_t annots;
      (match ct with
       | Ctype.Void -> pp_constructor "Ctype.Void" []
       | Ctype.Basic bt -> pp_constructor "Ctype.Basic" [ pp_basic_type bt ]
       | Ctype.Array (ct, on) ->
         pp_constructor "Ctype.Array" [ pp_ctype ct; pp_option pp_Z_as_nat on ]
       | Ctype.Function ((quals, ret), args, variadic) ->
         pp_constructor
           "Ctype.Function"
           [ pp_pair pp_qualifiers pp_ctype (quals, ret);
             pp_list (pp_triple pp_qualifiers pp_ctype pp_bool) args;
             pp_bool variadic
           ]
       | Ctype.FunctionNoParams (quals, ret) ->
         pp_constructor
           "Ctype.FunctionNoParams"
           [ pp_pair pp_qualifiers pp_ctype (quals, ret) ]
       | Ctype.Pointer (quals, ct) ->
         pp_constructor "Ctype.Pointer" [ pp_qualifiers quals; pp_ctype ct ]
       | Ctype.Atomic ct -> pp_constructor "Ctype.Atomic" [ pp_ctype ct ]
       | Ctype.Struct sym -> pp_constructor "Ctype.Struct" [ pp_symbol sym ]
       | Ctype.Union sym -> pp_constructor "Ctype.Union" [ pp_symbol sym ])
    ]


and pp_basic_type = function
  | Ctype.Integer it -> pp_constructor "Ctype.Integer" [ pp_integer_type it ]
  | Ctype.Floating ft -> pp_constructor "Ctype.Floating" [ pp_floating_type ft ]


and pp_floating_type = function
  | Ctype.RealFloating rft -> pp_constructor "RealFloating" [ pp_real_floating_type rft ]


and pp_real_floating_type = function
  | Ctype.Float -> pp_constructor "Float" []
  | Ctype.Double -> pp_constructor "Double" []
  | Ctype.LongDouble -> pp_constructor "LongDouble" []


let rec pp_sctype = function
  | Sctypes.Void -> pp_constructor "SCtypes.Void" []
  | Sctypes.Integer it -> pp_constructor "SCtypes.Integer" [ pp_integer_type it ]
  | Sctypes.Array (ct, on) ->
    pp_constructor "SCtypes.Array" [ pp_tuple [ pp_sctype ct; pp_option pp_nat on ] ]
  | Sctypes.Pointer ct -> pp_constructor "SCtypes.Pointer" [ pp_sctype ct ]
  | Sctypes.Struct sym -> pp_constructor "SCtypes.Struct" [ pp_symbol sym ]
  | Sctypes.Function ((quals, ret), args, variadic) ->
    pp_constructor
      "SCtypes.SCFunction"
      [ pp_tuple
          [ pp_pair pp_qualifiers pp_sctype (quals, ret);
            pp_list (pp_pair pp_sctype pp_bool) args;
            pp_bool variadic
          ]
      ]


let rec pp_core_base_type = function
  | Core.BTy_unit -> pp_constructor "BTy_unit" []
  | Core.BTy_boolean -> pp_constructor "BTy_boolean" []
  | Core.BTy_ctype -> pp_constructor "BTy_ctype" []
  | Core.BTy_list t -> pp_constructor "BTy_list" [ pp_core_base_type t ]
  | Core.BTy_tuple ts -> pp_constructor "BTy_tuple" [ pp_list pp_core_base_type ts ]
  | Core.BTy_object ot -> pp_constructor "BTy_object" [ pp_core_object_type ot ]
  | Core.BTy_loaded ot -> pp_constructor "BTy_loaded" [ pp_core_object_type ot ]
  | Core.BTy_storable -> pp_constructor "BTy_storable" []


and pp_core_object_type = function
  | Core.OTy_integer -> pp_constructor "OTy_integer" []
  | Core.OTy_floating -> pp_constructor "OTy_floating" []
  | Core.OTy_pointer -> pp_constructor "OTy_pointer" []
  | Core.OTy_array t -> pp_constructor "OTy_array" [ pp_core_object_type t ]
  | Core.OTy_struct sym -> pp_constructor "OTy_struct" [ pp_symbol sym ]
  | Core.OTy_union sym -> pp_constructor "OTy_union" [ pp_symbol sym ]


let pp_ctor = function
  | Mucore.Cnil bt -> pp_constructor "Cnil" [ pp_core_base_type bt ]
  | Mucore.Ccons -> pp_constructor "Ccons" []
  | Mucore.Ctuple -> pp_constructor "Ctuple" []
  | Mucore.Carray -> pp_constructor "Carray" []


let pp_core_binop = function
  | Core.OpAdd -> pp_constructor "Core.OpAdd" []
  | Core.OpSub -> pp_constructor "Core.OpSub" []
  | Core.OpMul -> pp_constructor "Core.OpMul" []
  | Core.OpDiv -> pp_constructor "Core.OpDiv" []
  | Core.OpRem_t -> pp_constructor "Core.OpRem_t" []
  | Core.OpRem_f -> pp_constructor "Core.OpRem_f" []
  | Core.OpExp -> pp_constructor "Core.OpExp" []
  | Core.OpEq -> pp_constructor "Core.OpEq" []
  | Core.OpGt -> pp_constructor "Core.OpGt" []
  | Core.OpLt -> pp_constructor "Core.OpLt" []
  | Core.OpGe -> pp_constructor "Core.OpGe" []
  | Core.OpLe -> pp_constructor "Core.OpLe" []
  | Core.OpAnd -> pp_constructor "Core.OpAnd" []
  | Core.OpOr -> pp_constructor "Core.OpOr" []


let pp_binop = function
  | Terms.And -> pp_constructor "Terms.And" []
  | Terms.Or -> pp_constructor "Terms.Or" []
  | Terms.Implies -> pp_constructor "Terms.Implies" []
  | Terms.Add -> pp_constructor "Terms.Add" []
  | Terms.Sub -> pp_constructor "Terms.Sub" []
  | Terms.Mul -> pp_constructor "Terms.Mul" []
  | Terms.MulNoSMT -> pp_constructor "Terms.MulNoSMT" []
  | Terms.Div -> pp_constructor "Terms.Div" []
  | Terms.DivNoSMT -> pp_constructor "Terms.DivNoSMT" []
  | Terms.Exp -> pp_constructor "Terms.Exp" []
  | Terms.ExpNoSMT -> pp_constructor "Terms.ExpNoSMT" []
  | Terms.Rem -> pp_constructor "Terms.Rem" []
  | Terms.RemNoSMT -> pp_constructor "Terms.RemNoSMT" []
  | Terms.Mod -> pp_constructor "Terms.Mod" []
  | Terms.ModNoSMT -> pp_constructor "Terms.ModNoSMT" []
  | Terms.BW_Xor -> pp_constructor "Terms.BW_Xor" []
  | Terms.BW_And -> pp_constructor "Terms.BW_And" []
  | Terms.BW_Or -> pp_constructor "Terms.BW_Or" []
  | Terms.ShiftLeft -> pp_constructor "Terms.ShiftLeft" []
  | Terms.ShiftRight -> pp_constructor "Terms.ShiftRight" []
  | Terms.LT -> pp_constructor "Terms.LT" []
  | Terms.LE -> pp_constructor "Terms.LE" []
  | Terms.Min -> pp_constructor "Terms.Min" []
  | Terms.Max -> pp_constructor "Terms.Max" []
  | Terms.EQ -> pp_constructor "Terms.EQ" []
  | Terms.LTPointer -> pp_constructor "Terms.LTPointer" []
  | Terms.LEPointer -> pp_constructor "Terms.LEPointer" []
  | Terms.SetUnion -> pp_constructor "Terms.SetUnion" []
  | Terms.SetIntersection -> pp_constructor "Terms.SetIntersection" []
  | Terms.SetDifference -> pp_constructor "Terms.SetDifference" []
  | Terms.SetMember -> pp_constructor "Terms.SetMember" []
  | Terms.Subset -> pp_constructor "Terms.Subset" []


let pp_bw_binop = function
  | BW_OR -> pp_constructor "BW_OR" []
  | BW_AND -> pp_constructor "BW_AND" []
  | BW_XOR -> pp_constructor "BW_XOR" []


let pp_bw_unop = function
  | BW_COMPL -> pp_constructor "BW_COMPL" []
  | BW_CTZ -> pp_constructor "BW_CTZ" []
  | BW_FFS -> pp_constructor "BW_FFS" []


let pp_core_iop = function
  | Core.IOpAdd -> pp_constructor "Core.IOpAdd" []
  | Core.IOpSub -> pp_constructor "Core.IOpSub" []
  | Core.IOpMul -> pp_constructor "Core.IOpMul" []
  | Core.IOpShl -> pp_constructor "Core.IOpShl" []
  | Core.IOpShr -> pp_constructor "Core.IOpShr" []


let rec pp_pattern_ pp_type = function
  | CaseBase (sym_opt, bt) ->
    pp_constructor
      "CaseBase"
      [ pp_underscore; pp_tuple [ pp_option pp_symbol sym_opt; pp_core_base_type bt ] ]
  | CaseCtor (ctor, pats) ->
    pp_constructor
      "CaseCtor"
      [ pp_underscore; pp_ctor ctor; pp_list (pp_pattern pp_type) pats ]


and pp_pattern pp_type (Pattern (loc, annots, ty, pat)) =
  pp_constructor
    "Pattern"
    [ pp_underscore;
      pp_location loc;
      pp_list pp_annot_t annots;
      pp_type ty;
      pp_pattern_ pp_type pat
    ]


let pp_mem_value v =
  Impl_mem.pp_mem_value_for_coq
    pp_symbol
    pp_integer_type
    pp_floating_type
    pp_ctype
    pp_identifier
    v


let rec pp_mem_constraint = function
  | Mem_common.MC_empty -> pp_constructor "MC_empty" []
  | Mem_common.MC_eq (x, y) ->
    pp_constructor
      "MC_eq"
      [ Impl_mem.pp_integer_value_for_coq x; Impl_mem.pp_integer_value_for_coq y ]
  | Mem_common.MC_le (x, y) ->
    pp_constructor
      "MC_le"
      [ Impl_mem.pp_integer_value_for_coq x; Impl_mem.pp_integer_value_for_coq y ]
  | Mem_common.MC_lt (x, y) ->
    pp_constructor
      "MC_lt"
      [ Impl_mem.pp_integer_value_for_coq x; Impl_mem.pp_integer_value_for_coq y ]
  | Mem_common.MC_in_device x ->
    pp_constructor "MC_in_device" [ Impl_mem.pp_integer_value_for_coq x ]
  | Mem_common.MC_or (x, y) ->
    pp_constructor "MC_or" [ pp_mem_constraint x; pp_mem_constraint y ]
  | Mem_common.MC_conj xs -> pp_constructor "MC_conj" [ pp_list pp_mem_constraint xs ]
  | Mem_common.MC_not x -> pp_constructor "MC_not" [ pp_mem_constraint x ]


and pp_pexpr pp_type (Pexpr (loc, annots, ty, pe)) =
  pp_constructor
    "Pexpr"
    [ pp_underscore;
      pp_location loc;
      pp_list pp_annot_t annots;
      pp_type ty;
      (match pe with
       | PEsym s -> pp_constructor "PEsym" [ pp_underscore; pp_symbol s ]
       | PEval v -> pp_constructor "PEval" [ pp_underscore; pp_value pp_type v ]
       | PEctor (c, es) ->
         pp_constructor
           "PEctor"
           [ pp_underscore; pp_ctor c; pp_list (pp_pexpr pp_type) es ]
       | PEop (op, e1, e2) ->
         pp_constructor
           "PEop"
           [ pp_underscore; pp_core_binop op; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEconstrained cs ->
         pp_constructor
           "PEconstrained"
           [ pp_underscore; pp_list (pp_pair pp_mem_constraint (pp_pexpr pp_type)) cs ]
       | PEbitwise_unop (op, e) ->
         pp_constructor
           "PEbitwise_unop"
           [ pp_underscore; pp_bw_unop op; pp_pexpr pp_type e ]
       | PEbitwise_binop (op, e1, e2) ->
         pp_constructor
           "PEbitwise_binop"
           [ pp_underscore; pp_bw_binop op; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | Cfvfromint e -> pp_constructor "Cfvfromint" [ pp_underscore; pp_pexpr pp_type e ]
       | Civfromfloat (act, e) ->
         pp_constructor "Civfromfloat" [ pp_underscore; pp_act act; pp_pexpr pp_type e ]
       | PEarray_shift (base, ct, idx) ->
         pp_constructor
           "PEarray_shift"
           [ pp_underscore; pp_pexpr pp_type base; pp_sctype ct; pp_pexpr pp_type idx ]
       | PEmember_shift (e, sym, id) ->
         pp_constructor
           "PEmember_shift"
           [ pp_underscore; pp_pexpr pp_type e; pp_symbol sym; pp_identifier id ]
       | PEnot e -> pp_constructor "PEnot" [ pp_underscore; pp_pexpr pp_type e ]
       | PEapply_fun (f, args) ->
         pp_constructor
           "PEapply_fun"
           [ pp_underscore; pp_function f; pp_list (pp_pexpr pp_type) args ]
       | PEstruct (sym, fields) ->
         pp_constructor
           "PEstruct"
           [ pp_underscore;
             pp_symbol sym;
             pp_list (pp_pair pp_identifier (pp_pexpr pp_type)) fields
           ]
       | PEunion (sym, id, e) ->
         pp_constructor
           "PEunion"
           [ pp_underscore; pp_symbol sym; pp_identifier id; pp_pexpr pp_type e ]
       | PEcfunction e ->
         pp_constructor "PEcfunction" [ pp_underscore; pp_pexpr pp_type e ]
       | PEmemberof (sym, id, e) ->
         pp_constructor
           "PEmemberof"
           [ pp_underscore; pp_symbol sym; pp_identifier id; pp_pexpr pp_type e ]
       | PEbool_to_integer e ->
         pp_constructor "PEbool_to_integer" [ pp_underscore; pp_pexpr pp_type e ]
       | PEconv_int (e1, e2) ->
         pp_constructor
           "PEconv_int"
           [ pp_underscore; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEconv_loaded_int (e1, e2) ->
         pp_constructor
           "PEconv_loaded_int"
           [ pp_underscore; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEwrapI (act, e) ->
         pp_constructor "PEwrapI" [ pp_underscore; pp_act act; pp_pexpr pp_type e ]
       | PEcatch_exceptional_condition (act, e) ->
         pp_constructor
           "PEcatch_exceptional_condition"
           [ pp_underscore; pp_act act; pp_pexpr pp_type e ]
       | PEbounded_binop (kind, op, e1, e2) ->
         pp_constructor
           "PEbounded_binop"
           [ pp_underscore;
             pp_bound_kind kind;
             pp_core_iop op;
             pp_pexpr pp_type e1;
             pp_pexpr pp_type e2
           ]
       | PEis_representable_integer (e, act) ->
         pp_constructor
           "PEis_representable_integer"
           [ pp_underscore; pp_pexpr pp_type e; pp_act act ]
       | PEundef (loc, ub) ->
         pp_constructor
           "PEundef"
           [ pp_underscore; pp_location loc; pp_undefined_behaviour ub ]
       | PEerror (msg, e) ->
         pp_constructor "PEerror" [ pp_underscore; pp_string msg; pp_pexpr pp_type e ]
       | PElet (pat, e1, e2) ->
         pp_constructor
           "PElet"
           [ pp_underscore;
             pp_pattern pp_type pat;
             pp_pexpr pp_type e1;
             pp_pexpr pp_type e2
           ]
       | PEif (c, t, e) ->
         pp_constructor
           "PEif"
           [ pp_underscore; pp_pexpr pp_type c; pp_pexpr pp_type t; pp_pexpr pp_type e ])
    ]


and pp_bound_kind = function
  | Bound_Wrap act -> pp_constructor "Bound_Wrap" [ pp_act act ]
  | Bound_Except act -> pp_constructor "Bound_Except" [ pp_act act ]


and pp_action pp_type (Action (loc, act)) =
  pp_record
    [ ("action_loc", pp_location loc); ("action_content", pp_action_content pp_type act) ]


and pp_paction pp_type (Paction (pol, act)) =
  pp_record
    [ ("paction_polarity", pp_polarity pol); ("paction_action", pp_action pp_type act) ]


and pp_action_content pp_type act =
  match act with
  | Create (e, act, sym) ->
    pp_constructor
      "Create"
      [ pp_underscore; pp_pexpr pp_type e; pp_act act; pp_symbol_prefix sym ]
  | CreateReadOnly (e1, act, e2, sym) ->
    pp_constructor
      "CreateReadOnly"
      [ pp_underscore;
        pp_pexpr pp_type e1;
        pp_act act;
        pp_pexpr pp_type e2;
        pp_symbol_prefix sym
      ]
  | Alloc (e1, e2, sym) ->
    pp_constructor
      "Alloc"
      [ pp_underscore; pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_symbol_prefix sym ]
  | Kill (kind, e) ->
    pp_constructor "Kill" [ pp_underscore; pp_kill_kind kind; pp_pexpr pp_type e ]
  | Store (b, act, e1, e2, mo) ->
    pp_constructor
      "Store"
      [ pp_underscore;
        pp_bool b;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_memory_order mo
      ]
  | Load (act, e, mo) ->
    pp_constructor
      "Load"
      [ pp_underscore; pp_act act; pp_pexpr pp_type e; pp_memory_order mo ]
  | RMW (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor
      "RMW"
      [ pp_underscore;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | Fence mo -> pp_constructor "Fence" [ pp_underscore; pp_memory_order mo ]
  | CompareExchangeStrong (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor
      "CompareExchangeStrong"
      [ pp_underscore;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | CompareExchangeWeak (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor
      "CompareExchangeWeak"
      [ pp_underscore;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | LinuxFence lmo ->
    pp_constructor "LinuxFence" [ pp_underscore; pp_linux_memory_order lmo ]
  | LinuxLoad (act, e, lmo) ->
    pp_constructor
      "LinuxLoad"
      [ pp_act act; pp_pexpr pp_type e; pp_linux_memory_order lmo ]
  | LinuxStore (act, e1, e2, lmo) ->
    pp_constructor
      "LinuxStore"
      [ pp_underscore;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_linux_memory_order lmo
      ]
  | LinuxRMW (act, e1, e2, lmo) ->
    pp_constructor
      "LinuxRMW"
      [ pp_underscore;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_linux_memory_order lmo
      ]


and pp_act { loc; annot; ct } =
  pp_record
    [ ("MuCore.loc", pp_location loc);
      ("MuCore.annot", pp_list pp_annot_t annot);
      ("MuCore.ct", pp_sctype ct)
    ]


and pp_kill_kind = function
  | Dynamic -> pp_constructor "Dynamic" []
  | Static ct -> pp_constructor "Static" [ pp_sctype ct ]


and pp_value pp_type (V (ty, v)) =
  pp_constructor
    "V"
    [ pp_underscore;
      pp_type ty;
      (match v with
       | Vobject ov ->
         pp_constructor "Vobject" [ pp_underscore; pp_object_value pp_type ov ]
       | Vctype t -> pp_constructor "Vctype" [ pp_underscore; pp_ctype t ]
       | Vfunction_addr s ->
         pp_constructor "Vfunction_addr" [ pp_underscore; pp_symbol s ]
       | Vunit -> pp_constructor "Vunit" [ pp_underscore ]
       | Vtrue -> pp_constructor "Vtrue" [ pp_underscore ]
       | Vfalse -> pp_constructor "Vfalse" [ pp_underscore ]
       | Vlist (bt, vs) ->
         pp_constructor
           "Vlist"
           [ pp_underscore; pp_core_base_type bt; pp_list (pp_value pp_type) vs ]
       | Vtuple vs ->
         pp_constructor "Vtuple" [ pp_underscore; pp_list (pp_value pp_type) vs ])
    ]


and pp_object_value pp_type (OV (ty, ov)) =
  pp_constructor
    "OV"
    [ pp_underscore;
      pp_type ty;
      (match ov with
       | OVinteger i ->
         pp_constructor "OVinteger" [ pp_underscore; Impl_mem.pp_integer_value_for_coq i ]
       | OVfloating f ->
         pp_constructor "OVfloating" [ pp_underscore; pp_floating_value f ]
       | OVpointer p ->
         pp_constructor "OVpointer" [ pp_underscore; pp_pointer_value pp_symbol p ]
       | OVarray vs ->
         pp_constructor "OVarray" [ pp_underscore; pp_list (pp_object_value pp_type) vs ]
       | OVstruct (sym, fields) ->
         pp_constructor
           "OVstruct"
           [ pp_underscore;
             pp_symbol sym;
             pp_list (pp_triple pp_identifier pp_sctype pp_mem_value) fields
           ]
       | OVunion (sym, id, v) ->
         pp_constructor
           "OVunion"
           [ pp_underscore; pp_symbol sym; pp_identifier id; pp_mem_value v ])
    ]


(* TODO: hardcoded None. pass `pp_type` *)
let pp_location_info = pp_pair pp_location (fun _ -> !^"None")

let pp_trusted = function
  | Trusted loc -> pp_constructor "Trusted" [ pp_location loc ]
  | Checked -> pp_constructor "Checked" []


let pp_unop = function
  | Terms.Not -> pp_constructor "Not" []
  | Negate -> pp_constructor "Negate" []
  | BW_CLZ_NoSMT -> pp_constructor "BW_CLZ_NoSMT" []
  | BW_CTZ_NoSMT -> pp_constructor "BW_CTZ_NoSMT" []
  | BW_FFS_NoSMT -> pp_constructor "BW_FFS_NoSMT" []
  | BW_FLS_NoSMT -> pp_constructor "BW_FLS_NoSMT" []
  | BW_Compl -> pp_constructor "BW_Compl" []


let rec pp_terms_pattern (Terms.Pat (pat, bt, loc)) =
  pp_constructor "Pat" [ pp_terms_pattern_ pat; pp_basetype pp_unit bt; pp_location loc ]


and pp_terms_pattern_ = function
  | Terms.PSym s -> pp_constructor "PSym" [ pp_symbol s ]
  | Terms.PWild -> pp_constructor "PWild" []
  | Terms.PConstructor (sym, args) ->
    pp_constructor
      "PConstructor"
      [ pp_symbol sym; pp_list (pp_pair pp_identifier pp_terms_pattern) args ]


let pp_const = function
  | Terms.Z z -> pp_constructor "Z" [ pp_Z z ]
  | Terms.Bits (x, z) ->
    pp_constructor "Bits" [ pp_pair (pp_pair pp_sign pp_nat) pp_Z (x, z) ]
  | Q q -> pp_constructor "Q" [ pp_Q q ]
  | MemByte { alloc_id; value } -> pp_constructor "MemByte" [ pp_Z alloc_id; pp_Z value ]
  | Pointer { alloc_id; addr } -> pp_constructor "Pointer" [ pp_Z alloc_id; pp_Z addr ]
  | Alloc_id z -> pp_constructor "Alloc_id" [ pp_Z z ]
  | Bool b -> pp_constructor "Bool" [ pp_bool b ]
  | Unit -> pp_constructor "Unit" []
  | Null -> pp_constructor "Null" []
  | CType_const t -> pp_constructor "CType_const" [ pp_sctype t ]
  | Default bt -> pp_constructor "Default" [ pp_basetype pp_unit bt ]


let rec pp_index_term (IndexTerms.IT (term, bt, loc)) =
  pp_constructor
    "IT"
    [ pp_underscore; pp_index_term_content term; pp_basetype pp_unit bt; pp_location loc ]


and pp_index_term_content = function
  | IndexTerms.Const c -> pp_constructor "Const" [ pp_underscore; pp_const c ]
  | Sym s -> pp_constructor "Sym" [ pp_underscore; pp_symbol s ]
  | Unop (op, t) -> pp_constructor "Unop" [ pp_underscore; pp_unop op; pp_index_term t ]
  | Binop (op, t1, t2) ->
    pp_constructor
      "Binop"
      [ pp_underscore; pp_binop op; pp_index_term t1; pp_index_term t2 ]
  | ITE (c, t, e) ->
    pp_constructor
      "ITE"
      [ pp_underscore; pp_index_term c; pp_index_term t; pp_index_term e ]
  | EachI ((n1, (sym, bt), n2), t) ->
    pp_constructor
      "EachI"
      [ pp_underscore;
        pp_tuple
          [ pp_nat n1; pp_pair pp_symbol (pp_basetype pp_unit) (sym, bt); pp_nat n2 ];
        pp_index_term t
      ]
  | Tuple ts -> pp_constructor "Tuple" [ pp_underscore; pp_list pp_index_term ts ]
  | NthTuple (n, t) ->
    pp_constructor "NthTuple" [ pp_underscore; pp_nat n; pp_index_term t ]
  | Struct (tag, members) ->
    pp_constructor
      "Struct"
      [ pp_underscore;
        pp_symbol tag;
        pp_list (pp_pair pp_identifier pp_index_term) members
      ]
  | StructMember (t, member) ->
    pp_constructor "StructMember" [ pp_underscore; pp_index_term t; pp_identifier member ]
  | StructUpdate ((t1, member), t2) ->
    pp_constructor
      "StructUpdate"
      [ pp_underscore;
        pp_pair pp_index_term pp_identifier (t1, member);
        pp_index_term t2
      ]
  | Record members ->
    pp_constructor
      "Record"
      [ pp_underscore; pp_list (pp_pair pp_identifier pp_index_term) members ]
  | RecordMember (t, member) ->
    pp_constructor "RecordMember" [ pp_underscore; pp_index_term t; pp_identifier member ]
  | RecordUpdate ((t1, member), t2) ->
    pp_constructor
      "RecordUpdate"
      [ pp_underscore;
        pp_pair pp_index_term pp_identifier (t1, member);
        pp_index_term t2
      ]
  | Constructor (sym, args) ->
    pp_constructor
      "Constructor"
      [ pp_symbol sym; pp_list (pp_pair pp_identifier pp_index_term) args ]
  | MemberShift (t, tag, id) ->
    pp_constructor
      "MemberShift"
      [ pp_underscore; pp_index_term t; pp_symbol tag; pp_identifier id ]
  | ArrayShift { base; ct; index } ->
    pp_constructor
      "ArrayShift"
      [ pp_underscore; pp_index_term base; pp_sctype ct; pp_index_term index ]
  | CopyAllocId { addr; loc } ->
    pp_constructor "CopyAllocId" [ pp_underscore; pp_index_term addr; pp_index_term loc ]
  | HasAllocId t -> pp_constructor "HasAllocId" [ pp_underscore; pp_index_term t ]
  | SizeOf ct -> pp_constructor "SizeOf" [ pp_underscore; pp_sctype ct ]
  | OffsetOf (tag, member) ->
    pp_constructor "OffsetOf" [ pp_underscore; pp_symbol tag; pp_identifier member ]
  | Nil bt -> pp_constructor "Nil" [ pp_underscore; pp_basetype pp_unit bt ]
  | Cons (t1, t2) ->
    pp_constructor "Cons" [ pp_underscore; pp_index_term t1; pp_index_term t2 ]
  | Head t -> pp_constructor "Head" [ pp_underscore; pp_index_term t ]
  | Tail t -> pp_constructor "Tail" [ pp_underscore; pp_index_term t ]
  | NthList (i, xs, d) ->
    pp_constructor
      "NthList"
      [ pp_underscore; pp_index_term i; pp_index_term xs; pp_index_term d ]
  | ArrayToList (arr, i, len) ->
    pp_constructor
      "ArrayToList"
      [ pp_underscore; pp_index_term arr; pp_index_term i; pp_index_term len ]
  | Representable (ct, t) ->
    pp_constructor "Representable" [ pp_underscore; pp_sctype ct; pp_index_term t ]
  | Good (ct, t) -> pp_constructor "Good" [ pp_underscore; pp_sctype ct; pp_index_term t ]
  | Aligned { t; align } ->
    pp_constructor "Aligned" [ pp_underscore; pp_index_term t; pp_index_term align ]
  | WrapI (ct, t) ->
    pp_constructor "WrapI" [ pp_underscore; pp_integer_type ct; pp_index_term t ]
  | MapConst (bt, t) ->
    pp_constructor "MapConst" [ pp_underscore; pp_basetype pp_unit bt; pp_index_term t ]
  | MapSet (m, k, v) ->
    pp_constructor
      "MapSet"
      [ pp_underscore; pp_index_term m; pp_index_term k; pp_index_term v ]
  | MapGet (m, k) ->
    pp_constructor "MapGet" [ pp_underscore; pp_index_term m; pp_index_term k ]
  | MapDef ((sym, bt), t) ->
    pp_constructor
      "MapDef"
      [ pp_underscore;
        pp_pair pp_symbol (pp_basetype pp_unit) (sym, bt);
        pp_index_term t
      ]
  | Apply (sym, args) ->
    pp_constructor "Apply" [ pp_underscore; pp_symbol sym; pp_list pp_index_term args ]
  | Let ((sym, t1), t2) ->
    pp_constructor
      "TLet"
      [ pp_underscore; pp_pair pp_symbol pp_index_term (sym, t1); pp_index_term t2 ]
  | Match (t, cases) ->
    pp_constructor
      "Match"
      [ pp_underscore;
        pp_index_term t;
        pp_list (pp_pair pp_terms_pattern pp_index_term) cases
      ]
  | Cast (bt, t) ->
    pp_constructor "Cast" [ pp_underscore; pp_basetype pp_unit bt; pp_index_term t ]


let pp_request_init = function
  | Request.Init -> pp_constructor "Init" []
  | Request.Uninit -> pp_constructor "Uninit" []


let rec pp_request = function
  | Request.P pred -> pp_constructor "P" [ pp_request_ppredicate pred ]
  | Request.Q qpred -> pp_constructor "Q" [ pp_request_qpredicate qpred ]


and pp_request_qpredicate qpred =
  pp_record
    [ ("QPredicate.name", pp_request_name qpred.Request.QPredicate.name);
      ("QPredicate.pointer", pp_index_term qpred.pointer);
      ("QPredicate.q", pp_pair pp_symbol (pp_basetype pp_unit) qpred.q);
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
  | Request.PName sym -> pp_constructor "PName" [ pp_symbol sym ]
  | Request.Owned (ct, init) ->
    pp_constructor "Owned" [ pp_sctype ct; pp_request_init init ]


let pp_memop pp_type m =
  let pte = pp_pexpr pp_type in
  match m with
  | PtrEq e12 -> pp_constructor "PtrEq" [ pp_underscore; pp_pair pte pte e12 ]
  | PtrNe e12 -> pp_constructor "PtrNe" [ pp_underscore; pp_pair pte pte e12 ]
  | PtrLt e12 -> pp_constructor "PtrLt" [ pp_underscore; pp_pair pte pte e12 ]
  | PtrGt e12 -> pp_constructor "PtrGt" [ pp_underscore; pp_pair pte pte e12 ]
  | PtrLe e12 -> pp_constructor "PtrLe" [ pp_underscore; pp_pair pte pte e12 ]
  | PtrGe e12 -> pp_constructor "PtrGe" [ pp_underscore; pp_pair pte pte e12 ]
  | Ptrdiff e123 ->
    pp_constructor "Ptrdiff" [ pp_underscore; pp_triple pp_act pte pte e123 ]
  | IntFromPtr e123 ->
    pp_constructor "IntFromPtr" [ pp_underscore; pp_triple pp_act pp_act pte e123 ]
  | PtrFromInt e123 ->
    pp_constructor "PtrFromInt" [ pp_underscore; pp_triple pp_act pp_act pte e123 ]
  | PtrValidForDeref e12 ->
    pp_constructor "PtrValidForDeref" [ pp_underscore; pp_pair pp_act pte e12 ]
  | PtrWellAligned e12 ->
    pp_constructor "PtrWellAligned" [ pp_underscore; pp_pair pp_act pte e12 ]
  | PtrArrayShift e123 ->
    pp_constructor "PtrArrayShift" [ pp_underscore; pp_triple pte pp_act pte e123 ]
  | PtrMemberShift e123 ->
    pp_constructor
      "PtrMemberShift"
      [ pp_underscore; pp_triple pp_symbol pp_identifier pte e123 ]
  | Memcpy e123 -> pp_constructor "Memcpy" [ pp_underscore; pp_triple pte pte pte e123 ]
  | Memcmp e123 -> pp_constructor "Memcmp" [ pp_underscore; pp_triple pte pte pte e123 ]
  | Realloc e123 -> pp_constructor "Realloc" [ pp_underscore; pp_triple pte pte pte e123 ]
  | Va_start e12 -> pp_constructor "Va_start" [ pp_underscore; pp_pair pte pte e12 ]
  | Va_copy e -> pp_constructor "Va_copy" [ pp_underscore; pte e ]
  | Va_arg e12 -> pp_constructor "Va_arg" [ pp_underscore; pp_pair pte pp_act e12 ]
  | Va_end e -> pp_constructor "Va_end" [ pp_underscore; pte e ]
  | CopyAllocId e12 -> pp_constructor "CopyAllocId" [ pp_underscore; pp_pair pte pte e12 ]


let pp_pack_unpack = function
  | CF.Cn.Pack -> pp_constructor "Pack" []
  | CF.Cn.Unpack -> pp_constructor "Unpack" []


let pp_to_from = function
  | CF.Cn.To -> pp_constructor "To" []
  | CF.Cn.From -> pp_constructor "From" []


let pp_cn_to_instantiate ppfa ppfty = function
  | CF.Cn.I_Function f -> pp_constructor "I_Function" [ ppfa f ]
  | CF.Cn.I_Good ty -> pp_constructor "I_Good" [ ppfty ty ]
  | CF.Cn.I_Everything -> pp_constructor "I_Everything" []


let pp_logical_constraint = function
  | LogicalConstraints.T term -> pp_constructor "T" [ pp_index_term term ]
  | LogicalConstraints.Forall ((sym, bt), term) ->
    pp_constructor
      "Forall"
      [ pp_pair pp_symbol (pp_basetype pp_unit) (sym, bt); pp_index_term term ]


let rec pp_return_type = function
  | ReturnTypes.Computational (sbt, info, lrt) ->
    pp_constructor
      "ReturnTypes.Computational"
      [ pp_pair pp_symbol (pp_basetype pp_unit) sbt;
        pp_location_info info;
        pp_logical_return_type lrt
      ]


and pp_logical_return_type = function
  | LogicalReturnTypes.Define (st, info, lrt) ->
    pp_constructor
      "LogicalReturnTypes.Define"
      [ pp_pair pp_symbol pp_index_term st;
        pp_location_info info;
        pp_logical_return_type lrt
      ]
  | LogicalReturnTypes.Resource (x, info, lrt) ->
    pp_constructor
      "LogicalReturnTypes.Resource"
      [ pp_pair pp_symbol (pp_pair pp_request (pp_basetype pp_unit)) x;
        pp_location_info info;
        pp_logical_return_type lrt
      ]
  | LogicalReturnTypes.Constraint (lc, info, lrt) ->
    pp_constructor
      "LogicalReturnTypes.Constraint"
      [ pp_logical_constraint lc; pp_location_info info; pp_logical_return_type lrt ]
  | LogicalReturnTypes.I -> pp_constructor "LogicalReturnTypes.I" []


let rec pp_logical_args ppf = function
  | Define (st, info, rest) ->
    pp_constructor
      "MuCore.Define"
      [ pp_underscore;
        pp_tuple
          [ pp_pair pp_symbol pp_index_term st;
            pp_location_info info;
            pp_logical_args ppf rest
          ]
      ]
  | Resource ((sym, rbt), info, rest) ->
    pp_constructor
      "MuCore.Resource"
      [ pp_underscore;
        pp_tuple
          [ pp_symbol sym;
            pp_pair pp_request (pp_basetype pp_unit) rbt;
            pp_location_info info;
            pp_logical_args ppf rest
          ]
      ]
  | Constraint (lc, info, rest) ->
    pp_constructor
      "MuCore.Constraint"
      [ pp_underscore;
        pp_triple
          pp_logical_constraint
          pp_location_info
          (pp_logical_args ppf)
          (lc, info, rest)
      ]
  | I i -> pp_constructor "MuCore.I" [ pp_underscore; ppf i ]


let rec pp_arguments ppf = function
  | Mucore.Computational (sbt, loc, rest) ->
    pp_constructor
      "MuCore.Computational"
      [ pp_underscore;
        pp_tuple
          [ pp_pair pp_symbol (pp_basetype pp_unit) sbt;
            pp_location_info loc;
            pp_arguments ppf rest
          ]
      ]
  | L at -> pp_constructor "MuCore.L" [ pp_underscore; pp_logical_args ppf at ]


let pp_cn_c_kind = function
  | CF.Cn.C_kind_var -> pp_constructor "C_kind_var" []
  | C_kind_enum -> pp_constructor "C_kind_enum" []


let pp_cn_sign = function
  | CF.Cn.CN_unsigned -> pp_constructor "CN_unsigned" []
  | CN_signed -> pp_constructor "CN_signed" []


let rec pp_cn_basetype ppfa = function
  | CF.Cn.CN_unit -> pp_constructor "CN_unit" [ pp_underscore ]
  | CN_bool -> pp_constructor "CN_bool" [ pp_underscore ]
  | CN_integer -> !^"(CN_integer" ^^^ pp_underscore ^^^ !^")"
  | CN_bits (sign, sz) ->
    pp_constructor "CN_bits" [ pp_underscore; pp_pair pp_cn_sign pp_nat (sign, sz) ]
  | CN_real -> pp_constructor "CN_real" [ pp_underscore ]
  | CN_loc -> pp_constructor "CN_loc" [ pp_underscore ]
  | CN_alloc_id -> pp_constructor "CN_alloc_id" [ pp_underscore ]
  | CN_struct a -> pp_constructor "CN_struct" [ pp_underscore; ppfa a ]
  | CN_record fields ->
    pp_constructor
      "CN_record"
      [ pp_underscore; pp_list (pp_pair pp_identifier (pp_cn_basetype ppfa)) fields ]
  | CN_datatype a -> pp_constructor "CN_datatype" [ pp_underscore; ppfa a ]
  | CN_map (k, v) ->
    pp_constructor
      "CN_map"
      [ pp_underscore; pp_pair (pp_cn_basetype ppfa) (pp_cn_basetype ppfa) (k, v) ]
  | CN_list t -> pp_constructor "CN_list" [ pp_underscore; pp_cn_basetype ppfa t ]
  | CN_tuple ts ->
    pp_constructor "CN_tuple" [ pp_underscore; pp_list (pp_cn_basetype ppfa) ts ]
  | CN_set t -> pp_constructor "CN_set" [ pp_underscore; pp_cn_basetype ppfa t ]
  | CN_user_type_name a -> pp_constructor "CN_user_type_name" [ pp_underscore; ppfa a ]
  | CN_c_typedef_name a -> pp_constructor "CN_c_typedef_name" [ pp_underscore; ppfa a ]


let pp_cn_const = function
  | CF.Cn.CNConst_NULL -> pp_constructor "CNConst_NULL" []
  | CNConst_integer n -> pp_constructor "CNConst_integer" [ pp_Z n ]
  | CNConst_bits (sign_sz, n) ->
    pp_constructor
      "CNConst_bits"
      [ pp_pair (pp_pair pp_cn_sign pp_nat) pp_Z (sign_sz, n) ]
  | CNConst_bool b -> pp_constructor "CNConst_bool" [ pp_bool b ]
  | CNConst_unit -> pp_constructor "CNConst_unit" []


let pp_cn_binop = function
  | CF.Cn.CN_add -> pp_constructor "CN_add" []
  | CN_sub -> pp_constructor "CN_sub" []
  | CN_mul -> pp_constructor "CN_mul" []
  | CN_div -> pp_constructor "CN_div" []
  | CN_mod -> pp_constructor "CN_mod" []
  | CN_equal -> pp_constructor "CN_equal" []
  | CN_inequal -> pp_constructor "CN_inequal" []
  | CN_lt -> pp_constructor "CN_lt" []
  | CN_le -> pp_constructor "CN_le" []
  | CN_gt -> pp_constructor "CN_gt" []
  | CN_ge -> pp_constructor "CN_ge" []
  | CN_or -> pp_constructor "CN_or" []
  | CN_and -> pp_constructor "CN_and" []
  | CN_implies -> pp_constructor "CN_implies" []
  | CN_map_get -> pp_constructor "CN_map_get" []
  | CN_band -> pp_constructor "CN_band" []
  | CN_bor -> pp_constructor "CN_bor" []
  | CN_bxor -> pp_constructor "CN_bxor" []


let rec pp_cn_pat ppfa = function
  | CF.Cn.CNPat (loc, pat) ->
    pp_constructor
      "CNPat"
      [ pp_location loc;
        (match pat with
         | CNPat_sym s -> pp_constructor "CNPat_sym" [ ppfa s ]
         | CNPat_wild -> pp_constructor "CNPat_wild" []
         | CNPat_constructor (s, args) ->
           pp_constructor
             "CNPat_constructor"
             [ ppfa s; pp_list (pp_pair pp_identifier (pp_cn_pat ppfa)) args ])
      ]


let rec pp_cn_expr ppfa ppfty = function
  | CF.Cn.CNExpr (loc, e) ->
    pp_constructor
      "CNExpr"
      [ pp_underscore;
        pp_underscore;
        pp_tuple
          [ pp_location loc;
            (match e with
             | CNExpr_const c ->
               pp_constructor
                 "CNExpr_const"
                 [ pp_underscore; pp_underscore; pp_cn_const c ]
             | CNExpr_var v ->
               pp_constructor "CNExpr_var" [ pp_underscore; pp_underscore; ppfa v ]
             | CNExpr_list es ->
               pp_constructor
                 "CNExpr_list"
                 [ pp_underscore; pp_underscore; pp_list (pp_cn_expr ppfa ppfty) es ]
             | CNExpr_memberof (e, id) ->
               pp_constructor
                 "CNExpr_memberof"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id)
                 ]
             | CNExpr_arrow (e, id) ->
               pp_constructor
                 "CNExpr_arrow"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id)
                 ]
             | CNExpr_record fs ->
               pp_constructor
                 "CNExpr_record"
                 [ pp_underscore;
                   pp_underscore;
                   pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) fs
                 ]
             | CNExpr_struct (id, fs) ->
               pp_constructor
                 "CNExpr_struct"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair
                     ppfa
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (id, fs)
                 ]
             | CNExpr_memberupdates (e, us) ->
               pp_constructor
                 "CNExpr_memberupdates"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (e, us)
                 ]
             | CNExpr_arrayindexupdates (e, us) ->
               pp_constructor
                 "CNExpr_arrayindexupdates"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair (pp_cn_expr ppfa ppfty) (pp_cn_expr ppfa ppfty)))
                     (e, us)
                 ]
             | CNExpr_binop (op, e1, e2) ->
               pp_constructor
                 "CNExpr_binop"
                 [ pp_underscore;
                   pp_underscore;
                   pp_triple
                     pp_cn_binop
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (op, e1, e2)
                 ]
             | CNExpr_sizeof ty ->
               pp_constructor "CNExpr_sizeof" [ pp_underscore; pp_underscore; ppfty ty ]
             | CNExpr_offsetof (a, id) ->
               pp_constructor
                 "CNExpr_offsetof"
                 [ pp_underscore; pp_underscore; pp_pair ppfa pp_identifier (a, id) ]
             | CNExpr_membershift (e, oa, id) ->
               pp_constructor
                 "CNExpr_membershift"
                 [ pp_underscore;
                   pp_underscore;
                   pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_option ppfa)
                     pp_identifier
                     (e, oa, id)
                 ]
             | CNExpr_addr a ->
               pp_constructor "CNExpr_addr" [ pp_underscore; pp_underscore; ppfa a ]
             | CNExpr_cast (bt, e) ->
               pp_constructor
                 "CNExpr_cast"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair (pp_cn_basetype ppfa) (pp_cn_expr ppfa ppfty) (bt, e)
                 ]
             | CNExpr_array_shift (e, ty, idx) ->
               pp_constructor
                 "CNExpr_array_shift"
                 [ pp_underscore;
                   pp_underscore;
                   pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_option ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (e, ty, idx)
                 ]
             | CNExpr_call (f, args) ->
               pp_constructor
                 "CNExpr_call"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair ppfa (pp_list (pp_cn_expr ppfa ppfty)) (f, args)
                 ]
             | CNExpr_cons (id, e) ->
               pp_constructor
                 "CNExpr_cons"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair
                     ppfa
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (id, e)
                 ]
             | CNExpr_each (a, bt, n12, e) ->
               pp_constructor
                 "CNExpr_each"
                 [ pp_underscore;
                   pp_underscore;
                   pp_tuple
                     [ ppfa a;
                       pp_cn_basetype ppfa bt;
                       pp_pair pp_Z pp_Z n12;
                       pp_cn_expr ppfa ppfty e
                     ]
                 ]
             | CNExpr_let (a, e1, e2) ->
               pp_constructor
                 "CNExpr_let"
                 [ pp_underscore;
                   pp_underscore;
                   pp_triple
                     ppfa
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (a, e1, e2)
                 ]
             | CNExpr_match (e, cases) ->
               pp_constructor
                 "CNExpr_match"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair (pp_cn_pat ppfa) (pp_cn_expr ppfa ppfty)))
                     (e, cases)
                 ]
             | CNExpr_ite (c, t, e) ->
               pp_constructor
                 "CNExpr_ite"
                 [ pp_underscore;
                   pp_underscore;
                   pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (c, t, e)
                 ]
             | CNExpr_good (ty, e) ->
               pp_constructor
                 "CNExpr_good"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair ppfty (pp_cn_expr ppfa ppfty) (ty, e)
                 ]
             | CNExpr_deref e ->
               pp_constructor
                 "CNExpr_deref"
                 [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty e ]
             | CNExpr_value_of_c_atom (a, k) ->
               pp_constructor
                 "CNExpr_value_of_c_atom"
                 [ pp_underscore; pp_underscore; pp_pair ppfa pp_cn_c_kind (a, k) ]
             | CNExpr_unchanged e ->
               pp_constructor
                 "CNExpr_unchanged"
                 [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty e ]
             | CNExpr_at_env (e, s) ->
               pp_constructor
                 "CNExpr_at_env"
                 [ pp_underscore;
                   pp_underscore;
                   pp_pair (pp_cn_expr ppfa ppfty) pp_string (e, s)
                 ]
             | CNExpr_not e ->
               pp_constructor
                 "CNExpr_not"
                 [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty e ]
             | CNExpr_negate e ->
               pp_constructor
                 "CNExpr_negate"
                 [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty e ]
             | CNExpr_default bt ->
               pp_constructor
                 "CNExpr_default"
                 [ pp_underscore; pp_underscore; pp_cn_basetype ppfa bt ]
             | CNExpr_bnot e ->
               pp_constructor
                 "CNExpr_bnot"
                 [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty e ])
          ]
      ]


let rec pp_cn_resource ppfa ppfty = function
  | CF.Cn.CN_pred (loc, pred, args) ->
    pp_constructor
      "CN_pred"
      [ pp_underscore;
        pp_underscore;
        pp_location loc;
        pp_cn_pred ppfa ppfty pred;
        pp_list (pp_cn_expr ppfa ppfty) args
      ]
  | CN_each (a, bt, e, loc, pred, args) ->
    pp_constructor
      "CN_each"
      [ pp_underscore;
        pp_underscore;
        ppfa a;
        pp_cn_basetype ppfa bt;
        pp_cn_expr ppfa ppfty e;
        pp_location loc;
        pp_cn_pred ppfa ppfty pred;
        pp_list (pp_cn_expr ppfa ppfty) args
      ]


and pp_cn_pred ppfa ppfty = function
  | CF.Cn.CN_owned ty ->
    pp_constructor "CN_owned" [ pp_underscore; pp_underscore; pp_option ppfty ty ]
  | CN_block ty ->
    pp_constructor "CN_block" [ pp_underscore; pp_underscore; pp_option ppfty ty ]
  | CN_named a -> pp_constructor "CN_named" [ pp_underscore; pp_underscore; ppfa a ]


let pp_cn_to_extract ppfa ppfty = function
  | CF.Cn.E_Pred pred ->
    pp_constructor "E_Pred" [ pp_underscore; pp_underscore; pp_cn_pred ppfa ppfty pred ]
  | CF.Cn.E_Everything -> pp_constructor "E_Everything" [ pp_underscore; pp_underscore ]


let pp_cn_assertion ppfa ppfty = function
  | CF.Cn.CN_assert_exp ex ->
    pp_constructor
      "CN_assert_exp"
      [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty ex ]
  | CN_assert_qexp (sym, bt, it1, it2) ->
    pp_constructor
      "CN_assert_qexp"
      [ pp_underscore;
        pp_underscore;
        ppfa sym;
        pp_cn_basetype ppfa bt;
        pp_cn_expr ppfa ppfty it1;
        pp_cn_expr ppfa ppfty it2
      ]


let pp_cn_condition ppfa ppfty = function
  | CF.Cn.CN_cletResource (loc, sym, res) ->
    pp_constructor
      "CN_cletResource"
      [ pp_underscore;
        pp_underscore;
        pp_location loc;
        ppfa sym;
        pp_cn_resource ppfa ppfty res
      ]
  | CN_cletExpr (loc, sym, ex) ->
    pp_constructor
      "CN_cletExpr"
      [ pp_underscore;
        pp_underscore;
        pp_location loc;
        ppfa sym;
        pp_cn_expr ppfa ppfty ex
      ]
  | CN_cconstr (loc, assertion) ->
    pp_constructor
      "CN_cconstr"
      [ pp_underscore;
        pp_underscore;
        pp_location loc;
        pp_cn_assertion ppfa ppfty assertion
      ]


let pp_cnprog_statement = function
  | Cnprog.Pack_unpack (pu, pred) ->
    pp_constructor "Pack_unpack" [ pp_pack_unpack pu; pp_request_ppredicate pred ]
  | To_from_bytes (tf, pred) ->
    pp_constructor "To_from_bytes" [ pp_to_from tf; pp_request_ppredicate pred ]
  | Have lc -> pp_constructor "Have" [ pp_logical_constraint lc ]
  | Instantiate (inst, term) ->
    pp_constructor
      "Instantiate"
      [ pp_cn_to_instantiate pp_symbol pp_sctype inst; pp_index_term term ]
  | Split_case lc -> pp_constructor "Split_case" [ pp_logical_constraint lc ]
  | Extract (ids, ext, term) ->
    pp_constructor
      "Extract"
      [ pp_list pp_identifier ids;
        pp_cn_to_extract pp_symbol pp_sctype ext;
        pp_index_term term
      ]
  | Unfold (sym, terms) ->
    pp_constructor "Unfold" [ pp_symbol sym; pp_list pp_index_term terms ]
  | Apply (sym, terms) ->
    pp_constructor "Apply" [ pp_symbol sym; pp_list pp_index_term terms ]
  | Assert lc -> pp_constructor "Assert" [ pp_logical_constraint lc ]
  | Inline syms -> pp_constructor "Inline" [ pp_list pp_symbol syms ]
  | Print term -> pp_constructor "Print" [ pp_index_term term ]


let pp_cnprog_load (r : Cnprog.load) =
  pp_record [ ("CNProgs.ct", pp_sctype r.ct); ("CNProgs.pointer", pp_index_term r.pointer) ]


let rec pp_cn_prog = function
  | Cnprog.Let (loc, (name, l), prog) ->
    pp_constructor
      "CLet"
      [ pp_location loc; pp_tuple [ pp_symbol name; pp_cnprog_load l ]; pp_cn_prog prog ]
  | Statement (loc, stmt) ->
    pp_constructor "Statement" [ pp_location loc; pp_cnprog_statement stmt ]


let rec pp_cn_statement ppfa ppfty (CF.Cn.CN_statement (loc, stmt)) =
  pp_constructor
    "CN_statement"
    [ pp_underscore;
      pp_underscore;
      pp_location loc;
      (match stmt with
       | CN_pack_unpack (pu, pred, exprs) ->
         pp_constructor
           "CN_pack_unpack"
           [ pp_underscore;
             pp_underscore;
             pp_pack_unpack pu;
             pp_cn_pred ppfa ppfty pred;
             pp_list (pp_cn_expr ppfa ppfty) exprs
           ]
       | CN_to_from_bytes (tf, pred, exprs) ->
         pp_constructor
           "CN_to_from_bytes"
           [ pp_underscore;
             pp_underscore;
             pp_to_from tf;
             pp_cn_pred ppfa ppfty pred;
             pp_list (pp_cn_expr ppfa ppfty) exprs
           ]
       | CN_have assertion ->
         pp_constructor
           "CN_have"
           [ pp_underscore; pp_underscore; pp_cn_assertion ppfa ppfty assertion ]
       | CN_instantiate (inst, expr) ->
         pp_constructor
           "CN_instantiate"
           [ pp_underscore;
             pp_underscore;
             pp_cn_to_instantiate ppfa ppfty inst;
             pp_cn_expr ppfa ppfty expr
           ]
       | CN_split_case assertion ->
         pp_constructor
           "CN_split_case"
           [ pp_underscore; pp_underscore; pp_cn_assertion ppfa ppfty assertion ]
       | CN_extract (ids, extract, expr) ->
         pp_constructor
           "CN_extract"
           [ pp_underscore;
             pp_underscore;
             pp_list pp_identifier ids;
             pp_cn_to_extract ppfa ppfty extract;
             pp_cn_expr ppfa ppfty expr
           ]
       | CN_unfold (sym, exprs) ->
         pp_constructor
           "CN_unfold"
           [ pp_underscore;
             pp_underscore;
             ppfa sym;
             pp_list (pp_cn_expr ppfa ppfty) exprs
           ]
       | CN_assert_stmt assertion ->
         pp_constructor
           "CN_assert_stmt"
           [ pp_underscore; pp_underscore; pp_cn_assertion ppfa ppfty assertion ]
       | CN_apply (sym, exprs) ->
         pp_constructor
           "CN_apply"
           [ pp_underscore;
             pp_underscore;
             ppfa sym;
             pp_list (pp_cn_expr ppfa ppfty) exprs
           ]
       | CN_inline syms ->
         pp_constructor "CN_inline" [ pp_underscore; pp_underscore; pp_list ppfa syms ]
       | CN_print expr ->
         pp_constructor
           "CN_print"
           [ pp_underscore; pp_underscore; pp_cn_expr ppfa ppfty expr ])
    ]


and pp_expr pp_type = function
  | Expr (loc, annots, ty, e) ->
    pp_constructor
      "Expr"
      [ pp_underscore;
        pp_location loc;
        pp_list pp_annot_t annots;
        pp_type ty;
        (match e with
         | Epure pe -> pp_constructor "Epure" [ pp_underscore; pp_pexpr pp_type pe ]
         | Ememop m -> pp_constructor "Ememop" [ pp_underscore; pp_memop pp_type m ]
         | Eaction pa -> pp_constructor "Eaction" [ pp_underscore; pp_paction pp_type pa ]
         | Eskip -> pp_constructor "Eskip" [ pp_underscore ]
         | Eccall (act, f, args) ->
           pp_constructor
             "Eccall"
             [ pp_underscore;
               pp_tuple
                 [ pp_act act; pp_pexpr pp_type f; pp_list (pp_pexpr pp_type) args ]
             ]
         | Elet (pat, e1, e2) ->
           pp_constructor
             "Elet"
             [ pp_underscore;
               pp_tuple
                 [ pp_pattern pp_type pat; pp_pexpr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Eunseq exprs ->
           pp_constructor "Eunseq" [ pp_underscore; pp_list (pp_expr pp_type) exprs ]
         | Ewseq (pat, e1, e2) ->
           pp_constructor
             "Ewseq"
             [ pp_underscore;
               pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Esseq (pat, e1, e2) ->
           pp_constructor
             "Esseq"
             [ pp_underscore;
               pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Eif (c, t, e) ->
           pp_constructor
             "Eif"
             [ pp_underscore;
               pp_tuple [ pp_pexpr pp_type c; pp_expr pp_type t; pp_expr pp_type e ]
             ]
         | Ebound e -> pp_constructor "Ebound" [ pp_underscore; pp_expr pp_type e ]
         | End exprs ->
           pp_constructor "End" [ pp_underscore; pp_list (pp_expr pp_type) exprs ]
         | Erun (sym, args) ->
           pp_constructor
             "Erun"
             [ pp_underscore;
               pp_tuple [ pp_symbol sym; pp_list (pp_pexpr pp_type) args ]
             ]
         | CN_progs (stmts, progs) ->
           pp_constructor
             "CN_progs"
             [ pp_underscore;
               pp_tuple
                 [ pp_list (pp_cn_statement pp_symbol pp_ctype) stmts;
                   pp_list pp_cn_prog progs
                 ]
             ])
      ]


let pp_parse_ast_label_spec (s : parse_ast_label_spec) =
  pp_record [ ("label_spec", pp_list (pp_cn_condition pp_symbol pp_ctype) s.label_spec) ]


let pp_label_def pp_type = function
  | Return loc -> pp_constructor "Return" [ pp_underscore; pp_location loc ]
  | Label (loc, args, annots, spec, `Loop loop_locs) ->
    pp_constructor
      "Label"
      [ pp_location loc;
        pp_arguments (pp_expr pp_type) args;
        pp_list pp_annot_t annots;
        pp_parse_ast_label_spec spec;
        pp_pair pp_location pp_location loop_locs
      ]


let pp_args_and_body pp_type =
  pp_arguments
    (fun (body, (labels : (Symbol.sym, 'a label_def) Pmap.map), (rt : ReturnTypes.t)) ->
       pp_tuple
         [ pp_expr pp_type body;
           pp_pmap "Sym.map_from_list" pp_symbol (pp_label_def pp_type) labels;
           pp_return_type rt
         ])


let pp_desugared_spec { accesses; requires; ensures } =
  pp_record
    [ ("accesses", pp_list (pp_pair pp_symbol pp_ctype) accesses);
      ("requires", pp_list (pp_cn_condition pp_symbol pp_ctype) requires);
      ("ensures", pp_list (pp_cn_condition pp_symbol pp_ctype) ensures)
    ]


let rec pp_logical_argument_types pp_type = function
  | LogicalArgumentTypes.I i -> !^"(I" ^^^ pp_type i ^^ !^")"
  | Resource ((sym, (req, bt)), info, at) ->
    pp_constructor
      "LogicalArgumentTypes.Resource"
      [ pp_symbol sym;
        pp_tuple [ pp_request req; pp_basetype pp_unit bt ];
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]
  | Constraint (lc, info, at) ->
    pp_constructor
      "LogicalArgumentTypes.Constraint"
      [ pp_logical_constraint lc;
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]
  | LogicalArgumentTypes.Define (si, info, at) ->
    pp_constructor
      "LogicalArgumentTypes.Define"
      [ pp_pair pp_symbol pp_index_term si;
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]


let rec pp_argument_types pp_type = function
  | ArgumentTypes.Computational (sbt, info, at) ->
    pp_constructor
      "ArgumentTypes.Computational"
      [ pp_underscore;
        pp_pair pp_symbol (pp_basetype pp_unit) sbt;
        pp_location_info info;
        pp_argument_types pp_type at
      ]
  | L at ->
    pp_constructor
      "ArgumentTypes.L"
      [ pp_underscore; pp_logical_argument_types pp_type at ]


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
  ^^ pp_comment "Global definitions"
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
             (pp_constructor "GlobalDef" [ pp_sctype ct; pp_expr pp_type e ])
           ^^ P.hardline
         | GlobalDecl ct ->
           coq_def
             (Pp_symbol.to_string sym)
             P.empty
             (pp_constructor "GlobalDecl" [ pp_sctype ct ])
           ^^ P.hardline)
       P.empty
       file.globs
  (* Print functions *)
  ^^ pp_comment "Function definitions"
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
             (pp_constructor
                "ProcDecl"
                [ pp_type_name;
                  pp_location loc;
                  pp_option (pp_argument_types pp_return_type) ft
                ])
         | Proc { loc; args_and_body; trusted; desugared_spec } ->
           coq_def
             (Pp_symbol.to_string_pretty_cn sym)
             P.empty
             (pp_constructor
                "Proc"
                [ pp_type_name;
                  pp_location loc;
                  pp_args_and_body pp_type args_and_body;
                  pp_trusted trusted;
                  pp_desugared_spec desugared_spec
                ]))
       file.funs
       P.empty


let pp_unit_file (f : unit file) = pp_file pp_unit pp_unit_type f
