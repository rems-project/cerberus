[@@@warning "-32-27-26"] (* Disable unused value warnings and unused variable warnings *)

open Cerb_pp_prelude
open Printf
module CF = Cerb_frontend
open CF
module P = PPrint
open Mucore

(* temporary debug option to supress printing of noisy locations *)
let debug_print_locations = false (* Set to true to print actual locations *)

let pp_nat n = !^(string_of_int n)

let pp_Z z = !^(Z.to_string z)

let pp_pair p1 p2 (a, b) = P.parens (p1 a ^^ !^"," ^^ p2 b)

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
  !^"Definition" ^^^ !^name ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."


let coq_notation name args body =
  !^"Notation" ^^^ !^("\"" ^ name ^ "\"") ^^^ args ^^^ !^":=" ^^^ body ^^ !^"."


let pp_undefined_behaviour = function
  | Undefined.DUMMY str -> !^"(DUMMY" ^^^ !^(sprintf "%S" str) ^^ !^")"
  | Undefined.UB_unspecified_lvalue -> !^"UB_unspecified_lvalue"
  | Undefined.UB_std_omission om ->
    !^"(UB_std_omission"
    ^^^ (match om with
         | UB_OMIT_memcpy_non_object -> !^"UB_OMIT_memcpy_non_object"
         | UB_OMIT_memcpy_out_of_bound -> !^"UB_OMIT_memcpy_out_of_bound")
    ^^ !^")"
  | Undefined.Invalid_format str -> !^"(Invalid_format" ^^^ !^(sprintf "%S" str) ^^ !^")"
  | Undefined.UB_CERB004_unspecified ctx ->
    !^"(UB_CERB004_unspecified"
    ^^^ (match ctx with
         | UB_unspec_equality_ptr_vs_NULL -> !^"UB_unspec_equality_ptr_vs_NULL"
         | UB_unspec_equality_both_arith_or_ptr ->
           !^"UB_unspec_equality_both_arith_or_ptr"
         | UB_unspec_pointer_add -> !^"UB_unspec_pointer_add"
         | UB_unspec_pointer_sub -> !^"UB_unspec_pointer_sub"
         | UB_unspec_conditional -> !^"UB_unspec_conditional"
         | UB_unspec_copy_alloc_id -> !^"UB_unspec_copy_alloc_id"
         | UB_unspec_rvalue_memberof -> !^"UB_unspec_rvalue_memberof"
         | UB_unspec_memberofptr -> !^"UB_unspec_memberofptr"
         | UB_unspec_do -> !^"UB_unspec_do")
    ^^ !^")"
  | Undefined.UB_CERB005_free_nullptr -> !^"UB_CERB005_free_nullptr"
  | UB001 -> !^"UB001"
  | UB002 -> !^"UB002"
  | UB003 -> !^"UB003"
  | UB004a_incorrect_main_return_type -> !^"UB004a_incorrect_main_return_type"
  | UB004b_incorrect_main_argument1 -> !^"UB004b_incorrect_main_argument1"
  | UB004c_incorrect_main_argument2 -> !^"UB004c_incorrect_main_argument2"
  | UB004d_main_not_function -> !^"UB004d_main_not_function"
  | UB005_data_race -> !^"UB005_data_race"
  | UB006 -> !^"UB006"
  | UB007 -> !^"UB007"
  | UB008_multiple_linkage -> !^"UB008_multiple_linkage"
  | UB009_outside_lifetime -> !^"UB009_outside_lifetime"
  | UB010_pointer_to_dead_object -> !^"UB010_pointer_to_dead_object"
  | UB011_use_indeterminate_automatic_object ->
    !^"UB011_use_indeterminate_automatic_object"
  | UB_modifying_temporary_lifetime -> !^"UB_modifying_temporary_lifetime"
  | UB012_lvalue_read_trap_representation -> !^"UB012_lvalue_read_trap_representation"
  | UB013_lvalue_side_effect_trap_representation ->
    !^"UB013_lvalue_side_effect_trap_representation"
  | UB014_unsupported_negative_zero -> !^"UB014_unsupported_negative_zero"
  | UB015_incompatible_redeclaration -> !^"UB015_incompatible_redeclaration"
  | UB016 -> !^"UB016"
  | UB017_out_of_range_floating_integer_conversion ->
    !^"UB017_out_of_range_floating_integer_conversion"
  | UB018 -> !^"UB018"
  | UB019_lvalue_not_an_object -> !^"UB019_lvalue_not_an_object"
  | UB020_nonarray_incomplete_lvalue_conversion ->
    !^"UB020_nonarray_incomplete_lvalue_conversion"
  | UB021 -> !^"UB021"
  | UB022_register_array_decay -> !^"UB022_register_array_decay"
  | UB023 -> !^"UB023"
  | UB024_out_of_range_pointer_to_integer_conversion ->
    !^"UB024_out_of_range_pointer_to_integer_conversion"
  | UB025_misaligned_pointer_conversion -> !^"UB025_misaligned_pointer_conversion"
  | UB026 -> !^"UB026"
  | UB027 -> !^"UB027"
  | UB028 -> !^"UB028"
  | UB029 -> !^"UB029"
  | UB030 -> !^"UB030"
  | UB031 -> !^"UB031"
  | UB032 -> !^"UB032"
  | UB033_modifying_string_literal -> !^"UB033_modifying_string_literal"
  | UB034 -> !^"UB034"
  | UB035_unsequenced_race -> !^"UB035_unsequenced_race"
  | UB036_exceptional_condition -> !^"UB036_exceptional_condition"
  | UB037_illtyped_load -> !^"UB037_illtyped_load"
  | UB038_number_of_args -> !^"UB038_number_of_args"
  | UB039 -> !^"UB039"
  | UB040 -> !^"UB040"
  | UB041_function_not_compatible -> !^"UB041_function_not_compatible"
  | UB042_access_atomic_structUnion_member -> !^"UB042_access_atomic_structUnion_member"
  | UB043_indirection_invalid_value -> !^"UB043_indirection_invalid_value"
  | UB044 -> !^"UB044"
  | UB045a_division_by_zero -> !^"UB045a_division_by_zero"
  | UB045b_modulo_by_zero -> !^"UB045b_modulo_by_zero"
  | UB045c_quotient_not_representable -> !^"UB045c_quotient_not_representable"
  | UB046_array_pointer_outside -> !^"UB046_array_pointer_outside"
  | UB047a_array_pointer_addition_beyond_indirection ->
    !^"UB047a_array_pointer_addition_beyond_indirection"
  | UB047b_array_pointer_subtraction_beyond_indirection ->
    !^"UB047b_array_pointer_subtraction_beyond_indirection"
  | UB048_disjoint_array_pointers_subtraction ->
    !^"UB048_disjoint_array_pointers_subtraction"
  | UB049 -> !^"UB049"
  | UB050_pointers_subtraction_not_representable ->
    !^"UB050_pointers_subtraction_not_representable"
  | UB051a_negative_shift -> !^"UB051a_negative_shift"
  | UB51b_shift_too_large -> !^"UB51b_shift_too_large"
  | UB052a_negative_left_shift -> !^"UB052a_negative_left_shift"
  | UB052b_non_representable_left_shift -> !^"UB052b_non_representable_left_shift"
  | UB053_distinct_aggregate_union_pointer_comparison ->
    !^"UB053_distinct_aggregate_union_pointer_comparison"
  | UB054a_inexactly_overlapping_assignment -> !^"UB054a_inexactly_overlapping_assignment"
  | UB054b_incompatible_overlapping_assignment ->
    !^"UB054b_incompatible_overlapping_assignment"
  | UB055_invalid_integer_constant_expression ->
    !^"UB055_invalid_integer_constant_expression"
  | UB056 -> !^"UB056"
  | UB057 -> !^"UB057"
  | UB058 -> !^"UB058"
  | UB059_incomplete_no_linkage_identifier -> !^"UB059_incomplete_no_linkage_identifier"
  | UB060_block_scope_function_with_storage_class ->
    !^"UB060_block_scope_function_with_storage_class"
  | UB061_no_named_members -> !^"UB061_no_named_members"
  | UB062 -> !^"UB062"
  | UB063 -> !^"UB063"
  | UB064_modifying_const -> !^"UB064_modifying_const"
  | UB065 -> !^"UB065"
  | UB066_qualified_function_specification -> !^"UB066_qualified_function_specification"
  | UB067 -> !^"UB067"
  | UB068 -> !^"UB068"
  | UB069 -> !^"UB069"
  | UB070_inline_not_defined -> !^"UB070_inline_not_defined"
  | UB071_noreturn -> !^"UB071_noreturn"
  | UB072_incompatible_alignment_specifiers -> !^"UB072_incompatible_alignment_specifiers"
  | UB073 -> !^"UB073"
  | UB074 -> !^"UB074"
  | UB075 -> !^"UB075"
  | UB076 -> !^"UB076"
  | UB077 -> !^"UB077"
  | UB078_modified_void_parameter -> !^"UB078_modified_void_parameter"
  | UB079 -> !^"UB079"
  | UB080 -> !^"UB080"
  | UB081_scalar_initializer_not_single_expression ->
    !^"UB081_scalar_initializer_not_single_expression"
  | UB082 -> !^"UB082"
  | UB083 -> !^"UB083"
  | UB084 -> !^"UB084"
  | UB085 -> !^"UB085"
  | UB086_incomplete_adjusted_parameter -> !^"UB086_incomplete_adjusted_parameter"
  | UB087 -> !^"UB087"
  | UB088_reached_end_of_function -> !^"UB088_reached_end_of_function"
  | UB089_tentative_definition_internal_linkage ->
    !^"UB089_tentative_definition_internal_linkage"
  | UB090 -> !^"UB090"
  | UB091 -> !^"UB091"
  | UB092 -> !^"UB092"
  | UB093 -> !^"UB093"
  | UB094 -> !^"UB094"
  | UB095 -> !^"UB095"
  | UB096 -> !^"UB096"
  | UB097 -> !^"UB097"
  | UB098 -> !^"UB098"
  | UB099 -> !^"UB099"
  | UB100 -> !^"UB100"
  | UB101 -> !^"UB101"
  | UB102 -> !^"UB102"
  | UB103 -> !^"UB103"
  | UB104 -> !^"UB104"
  | UB105 -> !^"UB105"
  | UB106 -> !^"UB106"
  | UB107 -> !^"UB107"
  | UB108 -> !^"UB108"
  | UB109 -> !^"UB109"
  | UB110 -> !^"UB110"
  | UB111_illtyped_assert -> !^"UB111_illtyped_assert"
  | UB112 -> !^"UB112"
  | UB113 -> !^"UB113"
  | UB114 -> !^"UB114"
  | UB115 -> !^"UB115"
  | UB116 -> !^"UB116"
  | UB117 -> !^"UB117"
  | UB118 -> !^"UB118"
  | UB119 -> !^"UB119"
  | UB120 -> !^"UB120"
  | UB121 -> !^"UB121"
  | UB122 -> !^"UB122"
  | UB123 -> !^"UB123"
  | UB124 -> !^"UB124"
  | UB125 -> !^"UB125"
  | UB126 -> !^"UB126"
  | UB127 -> !^"UB127"
  | UB128 -> !^"UB128"
  | UB129 -> !^"UB129"
  | UB130 -> !^"UB130"
  | UB131 -> !^"UB131"
  | UB132 -> !^"UB132"
  | UB133 -> !^"UB133"
  | UB134 -> !^"UB134"
  | UB135 -> !^"UB135"
  | UB136 -> !^"UB136"
  | UB137 -> !^"UB137"
  | UB138 -> !^"UB138"
  | UB139 -> !^"UB139"
  | UB140 -> !^"UB140"
  | UB141 -> !^"UB141"
  | UB142 -> !^"UB142"
  | UB143 -> !^"UB143"
  | UB144 -> !^"UB144"
  | UB145 -> !^"UB145"
  | UB146 -> !^"UB146"
  | UB147 -> !^"UB147"
  | UB148 -> !^"UB148"
  | UB149 -> !^"UB149"
  | UB150 -> !^"UB150"
  | UB151 -> !^"UB151"
  | UB152 -> !^"UB152"
  | UB153a_insufficient_arguments_for_format ->
    !^"UB153a_insufficient_arguments_for_format"
  | UB153b_illtyped_argument_for_format -> !^"UB153b_illtyped_argument_for_format"
  | UB154 -> !^"UB154"
  | UB155 -> !^"UB155"
  | UB156 -> !^"UB156"
  | UB157 -> !^"UB157"
  | UB158_invalid_length_modifier -> !^"UB158_invalid_length_modifier"
  | UB159 -> !^"UB159"
  | UB160 -> !^"UB160"
  | UB161 -> !^"UB161"
  | UB162 -> !^"UB162"
  | UB163 -> !^"UB163"
  | UB164 -> !^"UB164"
  | UB165 -> !^"UB165"
  | UB166 -> !^"UB166"
  | UB167 -> !^"UB167"
  | UB168 -> !^"UB168"
  | UB169 -> !^"UB169"
  | UB170 -> !^"UB170"
  | UB171 -> !^"UB171"
  | UB172 -> !^"UB172"
  | UB173 -> !^"UB173"
  | UB174 -> !^"UB174"
  | UB175 -> !^"UB175"
  | UB176 -> !^"UB176"
  | UB177 -> !^"UB177"
  | UB178 -> !^"UB178"
  | UB179a_non_matching_allocation_free -> !^"UB179a_non_matching_allocation_free"
  | UB179b_dead_allocation_free -> !^"UB179b_dead_allocation_free"
  | UB179c_non_matching_allocation_realloc -> !^"UB179c_non_matching_allocation_realloc"
  | UB179d_dead_allocation_realloc -> !^"UB179d_dead_allocation_realloc"
  | UB180 -> !^"UB180"
  | UB181 -> !^"UB181"
  | UB182 -> !^"UB182"
  | UB183 -> !^"UB183"
  | UB184 -> !^"UB184"
  | UB185 -> !^"UB185"
  | UB186 -> !^"UB186"
  | UB187 -> !^"UB187"
  | UB188 -> !^"UB188"
  | UB189 -> !^"UB189"
  | UB190 -> !^"UB190"
  | UB191 -> !^"UB191"
  | UB192 -> !^"UB192"
  | UB193 -> !^"UB193"
  | UB194 -> !^"UB194"
  | UB195 -> !^"UB195"
  | UB196 -> !^"UB196"
  | UB197 -> !^"UB197"
  | UB198 -> !^"UB198"
  | UB199 -> !^"UB199"
  | UB200 -> !^"UB200"
  | UB201 -> !^"UB201"
  | UB202 -> !^"UB202"
  | UB203 -> !^"UB203"
  | UB204_illtyped_Static_assert -> !^"UB204_illtyped_Static_assert"
  | UB205_atomic_store_memorder -> !^"UB205_atomic_store_memorder"
  | UB206_atomic_load_memorder -> !^"UB206_atomic_load_memorder"
  | UB207_atomic_compare_exchange_memorder -> !^"UB207_atomic_compare_exchange_memorder"
  | UB_CERB001_integer_to_dead_pointer -> !^"UB_CERB001_integer_to_dead_pointer"
  | UB_CERB002a_out_of_bound_load -> !^"UB_CERB002a_out_of_bound_load"
  | UB_CERB002b_out_of_bound_store -> !^"UB_CERB002b_out_of_bound_store"
  | UB_CERB002c_out_of_bound_free -> !^"UB_CERB002c_out_of_bound_free"
  | UB_CERB002d_out_of_bound_realloc -> !^"UB_CERB002d_out_of_bound_realloc"
  | UB_CERB003_invalid_function_pointer -> !^"UB_CERB003_invalid_function_pointer"
  | UB_CHERI_InvalidCap -> !^"UB_CHERI_InvalidCap"
  | UB_CHERI_InsufficientPermissions -> !^"UB_CHERI_InsufficientPermissions"
  | UB_CHERI_BoundsViolation -> !^"UB_CHERI_BoundsViolation"
  | UB_CHERI_UndefinedTag -> !^"UB_CHERI_UndefinedTag"
  | UB_CHERI_ZeroLength -> !^"UB_CHERI_ZeroLength"


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


(*
let pp_address n = !^(N.to_string n)

let pp_provenance = function
  | Prov_empty -> !^"Prov_empty"
  | Prov_some n -> !^"(Prov_some" ^^^ !^(N.to_string n) ^^ !^")"

let pp_integer_value = function
  | CF.Impl_mem.IVloc (prov, addr) ->
    !^"(IVloc" ^^^ pp_pair pp_provenance pp_address (prov, addr) ^^ !^")"
  | IVint n -> !^"(IVint" ^^^ !^(N.to_string n) ^^ !^")"
*)

let pp_integer_value _ = !^"integer_value placeholder" (* TODO *)

let pp_floating_value _ = !^"floating_value placeholder" (* TODO *)

let pp_pointer_value _ = !^"pointer_value placeholder" (* TODO *)

let pp_mem_value _ = !^"mem_value placeholder" (* TODO *)

let pp_unit (_ : unit) = !^"tt"

let pp_floating_value f = !^"floating_value placeholder" (* TODO *)

let pp_pointer_value p = !^"pointer_value placeholder" (* TODO *)

let pp_mem_value m = !^"mem_value placeholder" (* TODO *)

let pp_unit (_ : unit) = !^"tt"

let pp_unit_type _ = !^"unit"

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
  !^"{"
  ^^ !^"pos_fname :="
  ^^ !^(sprintf "%S" pos_fname)
  ^^ !^";"
  ^^ !^"pos_lnum :="
  ^^ !^(string_of_int pos_lnum)
  ^^ !^";"
  ^^ !^"pos_bol :="
  ^^ !^(string_of_int pos_bol)
  ^^ !^";"
  ^^ !^"pos_cnum :="
  ^^ !^(string_of_int pos_cnum)
  ^^ !^"}"


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


let rec pp_symbol_description = function
  | CF.Symbol.SD_None -> !^"SD_None"
  | CF.Symbol.SD_unnamed_tag loc -> !^"(SD_unnamed_tag" ^^^ pp_location loc ^^ !^")"
  | CF.Symbol.SD_Id s -> !^"(SD_Id" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_CN_Id s -> !^"(SD_CN_Id" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_ObjectAddress s -> !^"(SD_ObjectAddress" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_Return -> !^"SD_Return"
  | CF.Symbol.SD_FunArgValue s -> !^"(SD_FunArgValue" ^^^ !^s ^^ !^")"
  | CF.Symbol.SD_FunArg (loc, n) ->
    !^"(SD_FunArg" ^^^ pp_location loc ^^^ !^(string_of_int n) ^^ !^")"


and pp_symbol (CF.Symbol.Symbol (d, n, sd)) =
  !^"(Symbol" ^^^ pp_string d ^^^ pp_nat n ^^^ pp_symbol_description sd ^^ !^")"


and pp_symbol_prefix = function
  | CF.Symbol.PrefSource (loc, syms) ->
    !^"(PrefSource" ^^^ pp_location loc ^^^ pp_list pp_symbol syms ^^ !^")"
  | CF.Symbol.PrefFunArg (loc, d, z) ->
    let d = "arg" in
    (* TODO: it looks like `d` contains some garbage*)
    !^"(PrefFunArg"
    ^^^ pp_location loc
    ^^^ !^("\"" ^ d ^ "\"")
    ^^^ !^(Z.to_string (Z.of_int z))
    ^^ !^")"
  | CF.Symbol.PrefStringLiteral (loc, d) ->
    !^"(PrefStringLiteral" ^^^ pp_location loc ^^^ !^("\"" ^ d ^ "\"") ^^ !^")"
  | CF.Symbol.PrefTemporaryLifetime (loc, d) ->
    !^"(PrefTemporaryLifetime" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefCompoundLiteral (loc, d) ->
    !^"(PrefCompoundLiteral" ^^^ pp_location loc ^^^ !^d ^^ !^")"
  | CF.Symbol.PrefMalloc -> !^"PrefMalloc"
  | CF.Symbol.PrefOther s -> !^"(PrefOther" ^^^ !^s ^^ !^")"


let rec pp_basetype pp_loc = function
  | BaseTypes.Unit -> !^"Unit"
  | BaseTypes.Bool -> !^"Bool"
  | BaseTypes.Integer -> !^"Integer"
  | BaseTypes.MemByte -> !^"MemByte"
  | BaseTypes.Bits (sign, n) ->
    !^"(Bits"
    ^^^ (match sign with
         | BaseTypes.Signed -> !^"Signed"
         | BaseTypes.Unsigned -> !^"Unsigned")
    ^^^ !^(string_of_int n)
    ^^ !^")"
  | BaseTypes.Real -> !^"Real"
  | BaseTypes.Alloc_id -> !^"Alloc_id"
  | BaseTypes.CType -> !^"CType"
  | BaseTypes.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Datatype sym -> !^"(Datatype" ^^^ pp_symbol sym ^^ !^")"
  | BaseTypes.Record fields ->
    !^"(Record"
    ^^^ P.separate_map
          (!^";" ^^ P.break 1)
          (fun (id, ty) ->
            !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_basetype pp_loc ty ^^ !^")")
          fields
    ^^ !^")"
  | BaseTypes.Map (t1, t2) ->
    !^"(Map" ^^^ pp_basetype pp_loc t1 ^^^ pp_basetype pp_loc t2 ^^ !^")"
  | BaseTypes.List t -> !^"(List" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Tuple ts ->
    !^"(Tuple" ^^^ P.separate_map (!^";" ^^ P.break 1) (pp_basetype pp_loc) ts ^^ !^")"
  | BaseTypes.Set t -> !^"(TSet" ^^^ pp_basetype pp_loc t ^^ !^")"
  | BaseTypes.Loc x -> pp_loc x


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
  !^"{|"
  ^^^ !^"attr_ns :="
  ^^^ pp_option pp_identifier attr.Annot.attr_ns
  ^^ !^";"
  ^^^ !^"attr_id :="
  ^^^ pp_identifier attr.attr_id
  ^^ !^";"
  ^^^ !^"attr_args :="
  ^^^ pp_list pp_attr_arg attr.attr_args
  ^^^ !^"|}"


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


let rec pp_ctype (Ctype.Ctype (annots, ct)) =
  !^"(Ctype"
  ^^^ pp_list pp_annot_t annots
  ^^^ (match ct with
       | Ctype.Void -> !^"Void"
       | Ctype.Basic bt -> !^"(Basic" ^^^ pp_basic_type bt ^^ !^")"
       | Ctype.Array (ct, None) -> !^"(Array" ^^^ pp_ctype ct ^^^ !^"None" ^^ !^")"
       | Ctype.Array (ct, Some n) ->
         !^"(Array" ^^^ pp_ctype ct ^^^ !^"(Some" ^^^ !^(Z.to_string n) ^^ !^"))" ^^ !^")"
       | Ctype.Function ((quals, ret), args, variadic) ->
         !^"(Function"
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
         !^"(FunctionNoParams"
         ^^^ !^"("
         ^^^ pp_qualifiers quals
         ^^ !^","
         ^^^ pp_ctype ret
         ^^ !^"))"
       | Ctype.Pointer (quals, ct) ->
         !^"(Pointer" ^^^ pp_qualifiers quals ^^^ pp_ctype ct ^^ !^")"
       | Ctype.Atomic ct -> !^"(Atomic" ^^^ pp_ctype ct ^^ !^")"
       | Ctype.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
       | Ctype.Union sym -> !^"(Union" ^^^ pp_symbol sym ^^ !^")")
  ^^ !^")"


and pp_basic_type = function
  | Ctype.Integer it -> !^"(Integer" ^^^ pp_integer_type it ^^ !^")"
  | Ctype.Floating ft -> !^"(Floating" ^^^ pp_floating_type ft ^^ !^")"


and pp_floating_type = function
  | Ctype.RealFloating rft -> !^"(RealFloating" ^^^ pp_real_floating_type rft ^^ !^")"


and pp_real_floating_type = function
  | Ctype.Float -> !^"Float"
  | Ctype.Double -> !^"Double"
  | Ctype.LongDouble -> !^"LongDouble"


and pp_qualifiers quals =
  !^"{|"
  ^^^ !^"const :="
  ^^^ !^(string_of_bool quals.Ctype.const)
  ^^ !^";"
  ^^^ !^"restrict :="
  ^^^ !^(string_of_bool quals.Ctype.restrict)
  ^^ !^";"
  ^^^ !^"volatile :="
  ^^^ !^(string_of_bool quals.Ctype.volatile)
  ^^^ !^"|}"


let rec pp_sctype = function
  | Sctypes.Void -> !^"Void"
  | Sctypes.Integer it -> !^"(Integer" ^^^ pp_integer_type it ^^ !^")"
  | Sctypes.Array (ct, None) -> !^"(Array" ^^^ pp_sctype ct ^^^ !^"None" ^^ !^")"
  | Sctypes.Array (ct, Some n) ->
    !^"(Array" ^^^ pp_sctype ct ^^^ !^"(Some" ^^^ !^(string_of_int n) ^^ !^"))" ^^ !^")"
  | Sctypes.Pointer ct -> !^"(Pointer" ^^^ pp_sctype ct ^^ !^")"
  | Sctypes.Struct sym -> !^"(Struct" ^^^ pp_symbol sym ^^ !^")"
  | Sctypes.Function ((quals, ret), args, variadic) ->
    !^"(SCFunction"
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


and pp_qualifiers quals =
  !^"{|"
  ^^^ !^"const :="
  ^^^ !^(string_of_bool quals.Ctype.const)
  ^^ !^";"
  ^^^ !^"restrict :="
  ^^^ !^(string_of_bool quals.Ctype.restrict)
  ^^ !^";"
  ^^^ !^"volatile :="
  ^^^ !^(string_of_bool quals.Ctype.volatile)
  ^^^ !^"|}"


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
    !^"(CaseBase" ^^^ pp_option pp_symbol sym_opt ^^^ pp_core_base_type bt ^^ !^")"
  | CaseCtor (ctor, pats) ->
    !^"(CaseCtor" ^^^ pp_ctor ctor ^^^ pp_list (pp_pattern pp_type) pats ^^ !^")"


and pp_pattern pp_type (Pattern (loc, annots, ty, pat)) =
  !^"(Pattern"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^ pp_pattern_ pp_type pat
  ^^ !^")"


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
  !^"Pexpr"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^
  match pe with
  | PEsym s -> !^"(PEsym" ^^^ pp_symbol s ^^ !^")"
  | PEval v -> !^"(PEval" ^^^ pp_value pp_type v ^^ !^")"
  | PEctor (c, es) -> !^"(PEctor" ^^^ pp_ctor c ^^^ pp_list (pp_pexpr pp_type) es ^^ !^")"
  | PEop (op, e1, e2) ->
    !^"(PEop"
    ^^^ pp_core_binop op
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^ !^")"
  | PEconstrained cs ->
    !^"(PEconstrained"
    ^^^ pp_list
          (fun (c, e) ->
            !^"(" ^^ pp_mem_constraint c ^^ !^"," ^^^ pp_pexpr pp_type e ^^ !^")")
          cs
    ^^ !^")"
  | PEbitwise_unop (op, e) ->
    !^"(PEbitwise_unop" ^^^ pp_bw_unop op ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEbitwise_binop (op, e1, e2) ->
    !^"(PEbitwise_binop"
    ^^^ pp_bw_binop op
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^ !^")"
  | Cfvfromint e -> !^"(Cfvfromint" ^^^ pp_pexpr pp_type e ^^ !^")"
  | Civfromfloat (act, e) ->
    !^"(Civfromfloat" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEarray_shift (base, ct, idx) ->
    !^"(PEarray_shift"
    ^^^ pp_pexpr pp_type base
    ^^^ pp_sctype ct
    ^^^ pp_pexpr pp_type idx
    ^^ !^")"
  | PEmember_shift (e, sym, id) ->
    !^"(PEmember_shift"
    ^^^ pp_pexpr pp_type e
    ^^^ pp_symbol sym
    ^^^ pp_identifier id
    ^^ !^")"
  | PEnot e -> !^"(PEnot" ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEapply_fun (f, args) ->
    !^"(PEapply_fun" ^^^ pp_function f ^^^ pp_list (pp_pexpr pp_type) args ^^ !^")"
  | PEstruct (sym, fields) ->
    !^"(PEstruct"
    ^^^ pp_symbol sym
    ^^^ pp_list
          (fun (id, e) ->
            !^"(" ^^ pp_identifier id ^^ !^"," ^^^ pp_pexpr pp_type e ^^ !^")")
          fields
    ^^ !^")"
  | PEunion (sym, id, e) ->
    !^"(PEunion" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEcfunction e -> !^"(PEcfunction" ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEmemberof (sym, id, e) ->
    !^"(PEmemberof" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEbool_to_integer e -> !^"(PEbool_to_integer" ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEconv_int (e1, e2) ->
    !^"(PEconv_int" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PEconv_loaded_int (e1, e2) ->
    !^"(PEconv_loaded_int" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PEwrapI (act, e) -> !^"(PEwrapI" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEcatch_exceptional_condition (act, e) ->
    !^"(PEcatch_exceptional_condition" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
  | PEbounded_binop (kind, op, e1, e2) ->
    !^"(PEbounded_binop"
    ^^^ pp_bound_kind kind
    ^^^ pp_iop op
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^ !^")"
  | PEis_representable_integer (e, act) ->
    !^"(PEis_representable_integer" ^^^ pp_pexpr pp_type e ^^^ pp_act act ^^ !^")"
  | PEundef (loc, ub) ->
    !^"(PEundef" ^^^ pp_location loc ^^^ pp_undefined_behaviour ub ^^ !^")"
  | PEerror (msg, e) -> !^"(PEerror" ^^^ !^msg ^^^ pp_pexpr pp_type e ^^ !^")"
  | PElet (pat, e1, e2) ->
    !^"(PElet"
    ^^^ pp_pattern pp_type pat
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^ !^")"
  | PEif (c, t, e) ->
    !^"(PEif"
    ^^^ pp_pexpr pp_type c
    ^^^ pp_pexpr pp_type t
    ^^^ pp_pexpr pp_type e
    ^^ !^")"


and pp_bound_kind = function
  | Bound_Wrap act -> !^"(Bound_Wrap" ^^^ pp_act act ^^ !^")"
  | Bound_Except act -> !^"(Bound_Except" ^^^ pp_act act ^^ !^")"


and pp_action pp_type (Action (loc, act)) =
  !^"{|"
  ^^^ !^"action_location :="
  ^^^ pp_location loc
  ^^ !^";"
  ^^^ !^"action_content :="
  ^^^ pp_action_content pp_type act
  ^^^ !^"|}"


and pp_paction pp_type (Paction (pol, act)) =
  !^"{|"
  ^^^ !^"paction_polarity :="
  ^^^ pp_polarity pol
  ^^ !^";"
  ^^^ !^"paction_action :="
  ^^^ pp_action pp_type act
  ^^^ !^"|}"


and pp_action_content pp_type act =
  match act with
  | Create (e, act, sym) ->
    !^"(Create" ^^^ pp_pexpr pp_type e ^^^ pp_act act ^^^ pp_symbol_prefix sym ^^ !^")"
  | CreateReadOnly (e1, act, e2, sym) ->
    !^"(CreateReadOnly"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_symbol_prefix sym
    ^^ !^")"
  | Alloc (e1, e2, sym) ->
    !^"(Alloc"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_symbol_prefix sym
    ^^ !^")"
  | Kill (kind, e) -> !^"(Kill" ^^^ pp_kill_kind kind ^^^ pp_pexpr pp_type e ^^ !^")"
  | Store (b, act, e1, e2, mo) ->
    !^"(Store"
    ^^^ pp_bool b
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_memory_order mo
    ^^ !^")"
  | Load (act, e, mo) ->
    !^"(Load" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^^ pp_memory_order mo ^^ !^")"
  | RMW (act, e1, e2, e3, mo1, mo2) ->
    !^"(RMW"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | Fence mo -> !^"(Fence" ^^^ pp_memory_order mo ^^ !^")"
  | CompareExchangeStrong (act, e1, e2, e3, mo1, mo2) ->
    !^"(CompareExchangeStrong"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | CompareExchangeWeak (act, e1, e2, e3, mo1, mo2) ->
    !^"(CompareExchangeWeak"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^^ pp_memory_order mo1
    ^^^ pp_memory_order mo2
    ^^ !^")"
  | LinuxFence lmo -> !^"(LinuxFence" ^^^ pp_linux_memory_order lmo ^^ !^")"
  | LinuxLoad (act, e, lmo) ->
    !^"(LinuxLoad"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"
  | LinuxStore (act, e1, e2, lmo) ->
    !^"(LinuxStore"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"
  | LinuxRMW (act, e1, e2, lmo) ->
    !^"(LinuxRMW"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_linux_memory_order lmo
    ^^ !^")"


and pp_act { loc; annot; ct } =
  !^"{|"
  ^^^ !^"loc :="
  ^^^ pp_location loc
  ^^ !^";"
  ^^^ !^"annot :="
  ^^^ pp_list pp_annot_t annot
  ^^ !^";"
  ^^^ !^"ct :="
  ^^^ pp_sctype ct
  ^^^ !^"|}"


and pp_kill_kind = function
  | Dynamic -> !^"Dynamic" (* constructor with no arguments *)
  | Static ct -> !^"(Static" ^^^ pp_sctype ct ^^ !^")"


and pp_bool b = if b then !^"true" else !^"false"

and pp_value pp_type (V (ty, v)) =
  !^"V"
  ^^^ pp_type ty
  ^^^
  match v with
  | Vobject ov -> !^"(Vobject" ^^^ pp_object_value pp_type ov ^^ !^")"
  | Vctype t -> !^"(Vctype" ^^^ pp_ctype t ^^ !^")"
  | Vfunction_addr s -> !^"(Vfunction_addr" ^^^ pp_symbol s ^^ !^")"
  | Vunit -> !^"Vunit"
  | Vtrue -> !^"Vtrue"
  | Vfalse -> !^"Vfalse"
  | Vlist (bt, vs) ->
    !^"(Vlist" ^^^ pp_core_base_type bt ^^^ pp_list (pp_value pp_type) vs ^^ !^")"
  | Vtuple vs -> !^"(Vtuple" ^^^ pp_list (pp_value pp_type) vs ^^ !^")"


and pp_object_value pp_type (OV (ty, ov)) =
  !^"OV"
  ^^^ pp_type ty
  ^^^
  match ov with
  | OVinteger i -> !^"(OVinteger" ^^^ pp_integer_value i ^^ !^")"
  | OVfloating f -> !^"(OVfloating" ^^^ pp_floating_value f ^^ !^")"
  | OVpointer p -> !^"(OVpointer" ^^^ pp_pointer_value p ^^ !^")"
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


let pp_location_info (loc, _) = pp_location loc

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


let pp_sign = function
  | BaseTypes.Signed -> !^"Signed"
  | BaseTypes.Unsigned -> !^"Unsigned"


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
    !^"(Bits"
    ^^^ !^"("
    ^^ pp_sign sign
    ^^ !^","
    ^^^ !^(string_of_int sz)
    ^^ !^")"
    ^^^ !^(Z.to_string z)
    ^^ !^")"
  | Q q -> !^"(Q" ^^^ !^(Q.to_string q) ^^ !^")"
  | MemByte { alloc_id; value } ->
    !^"(MemByte" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string value) ^^ !^")"
  | Pointer { alloc_id; addr } ->
    !^"(Pointer" ^^^ !^(Z.to_string alloc_id) ^^^ !^(Z.to_string addr) ^^ !^")"
  | Alloc_id z -> !^"(Alloc_id" ^^^ !^(Z.to_string z) ^^ !^")"
  | Bool b -> !^"(Bool" ^^^ pp_bool b ^^ !^")"
  | Unit -> !^"Unit"
  | Null -> !^"Null"
  | CType_const t -> !^"(CType_const" ^^^ pp_sctype t ^^ !^")"
  | Default bt -> !^"(Default" ^^^ pp_basetype pp_unit bt ^^ !^")"


let rec pp_index_term (IndexTerms.IT (term, bt, loc)) =
  !^"(IT"
  ^^^ pp_index_term_content term
  ^^^ pp_basetype pp_unit bt
  ^^^ pp_location loc
  ^^ !^")"


and pp_index_term_content = function
  | IndexTerms.Const c -> !^"(Const" ^^^ pp_const c ^^ !^")"
  | Sym s -> !^"(Sym" ^^^ pp_symbol s ^^ !^")"
  | Unop (op, t) -> !^"(Unop" ^^^ pp_unop op ^^^ pp_index_term t ^^ !^")"
  | Binop (op, t1, t2) ->
    !^"(Binop" ^^^ pp_binop op ^^^ pp_index_term t1 ^^^ pp_index_term t2 ^^ !^")"
  | ITE (c, t, e) ->
    !^"(ITE" ^^^ pp_index_term c ^^^ pp_index_term t ^^^ pp_index_term e ^^ !^")"
  | EachI ((n1, (sym, bt), n2), t) ->
    !^"(EachI"
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
  | Tail t -> !^"(Tail" ^^^ pp_index_term t ^^ !^")"
  | NthList (i, xs, d) ->
    !^"(NthList" ^^^ pp_index_term i ^^^ pp_index_term xs ^^^ pp_index_term d ^^ !^")"
  | ArrayToList (arr, i, len) ->
    !^"(ArrayToList"
    ^^^ pp_index_term arr
    ^^^ pp_index_term i
    ^^^ pp_index_term len
    ^^ !^")"
  | Representable (ct, t) ->
    !^"(Representable" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
  | Good (ct, t) -> !^"(Good" ^^^ pp_sctype ct ^^^ pp_index_term t ^^ !^")"
  | Aligned { t; align } ->
    !^"(Aligned" ^^^ pp_index_term t ^^^ pp_index_term align ^^ !^")"
  | WrapI (ct, t) -> !^"(WrapI" ^^^ pp_integer_type ct ^^^ pp_index_term t ^^ !^")"
  | MapConst (bt, t) ->
    !^"(MapConst" ^^^ pp_basetype pp_unit bt ^^^ pp_index_term t ^^ !^")"
  | MapSet (m, k, v) ->
    !^"(MapSet" ^^^ pp_index_term m ^^^ pp_index_term k ^^^ pp_index_term v ^^ !^")"
  | MapGet (m, k) -> !^"(MapGet" ^^^ pp_index_term m ^^^ pp_index_term k ^^ !^")"
  | MapDef ((sym, bt), t) ->
    !^"(MapDef"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_index_term t
    ^^ !^")"
  | Apply (sym, args) ->
    !^"(Apply" ^^^ pp_symbol sym ^^^ pp_list pp_index_term args ^^ !^")"
  | Let ((sym, t1), t2) ->
    !^"(Let"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_index_term t1
    ^^ !^")"
    ^^^ pp_index_term t2
    ^^ !^")"
  | Match (t, cases) ->
    !^"(Match"
    ^^^ pp_index_term t
    ^^^ pp_list
          (fun (pat, body) ->
            !^"(" ^^ pp_terms_pattern pat ^^ !^"," ^^^ pp_index_term body ^^ !^")")
          cases
    ^^ !^")"
  | Cast (bt, t) -> !^"(Cast" ^^^ pp_basetype pp_unit bt ^^^ pp_index_term t ^^ !^")"


let pp_request_init = function Request.Init -> !^"Init" | Request.Uninit -> !^"Uninit"

let rec pp_request = function
  | Request.P pred ->
    !^"(P"
    ^^^ !^"{|"
    ^^^ !^"name :="
    ^^^ pp_request_name pred.Request.Predicate.name
    ^^ !^";"
    ^^^ !^"pointer :="
    ^^^ pp_index_term pred.pointer
    ^^ !^";"
    ^^^ !^"iargs :="
    ^^^ pp_list pp_index_term pred.iargs
    ^^^ !^"|}"
    ^^ !^")"
  | Request.Q qpred ->
    !^"(Q"
    ^^^ !^"{|"
    ^^^ !^"name :="
    ^^^ pp_request_name qpred.Request.QPredicate.name
    ^^ !^";"
    ^^^ !^"pointer :="
    ^^^ pp_index_term qpred.pointer
    ^^ !^";"
    ^^^ !^"q :="
    ^^^ !^"("
    ^^ pp_symbol (fst qpred.q)
    ^^ !^","
    ^^^ pp_basetype pp_unit (snd qpred.q)
    ^^ !^")"
    ^^ !^";"
    ^^^ !^"q_loc :="
    ^^^ pp_location qpred.q_loc
    ^^ !^";"
    ^^^ !^"step :="
    ^^^ pp_index_term qpred.step
    ^^ !^";"
    ^^^ !^"permission :="
    ^^^ pp_index_term qpred.permission
    ^^ !^";"
    ^^^ !^"iargs :="
    ^^^ pp_list pp_index_term qpred.iargs
    ^^^ !^"|}"
    ^^ !^")"


and pp_request_name = function
  | Request.PName sym -> !^"(PName" ^^^ pp_symbol sym ^^ !^")"
  | Request.Owned (ct, init) ->
    (* TODO
       !^"(Owned" ^^^ pp_sctype ct ^^^ pp_request_init init ^^ !^")"
    *)
    P.empty


let pp_memop pp_type op =
  match op with
  | PtrEq (e1, e2) -> !^"(PtrEq" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PtrNe (e1, e2) -> !^"(PtrNe" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PtrLt (e1, e2) -> !^"(PtrLt" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PtrGt (e1, e2) -> !^"(PtrGt" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PtrLe (e1, e2) -> !^"(PtrLe" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | PtrGe (e1, e2) -> !^"(PtrGe" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | Ptrdiff (act, e1, e2) ->
    !^"(Ptrdiff" ^^^ pp_act act ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | IntFromPtr (act1, act2, e) ->
    !^"(IntFromPtr" ^^^ pp_act act1 ^^^ pp_act act2 ^^^ pp_pexpr pp_type e ^^ !^")"
  | PtrFromInt (act1, act2, e) ->
    !^"(PtrFromInt" ^^^ pp_act act1 ^^^ pp_act act2 ^^^ pp_pexpr pp_type e ^^ !^")"
  | PtrValidForDeref (act, e) ->
    !^"(PtrValidForDeref" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
  | PtrWellAligned (act, e) ->
    !^"(PtrWellAligned" ^^^ pp_act act ^^^ pp_pexpr pp_type e ^^ !^")"
  | PtrArrayShift (e1, act, e2) ->
    !^"(PtrArrayShift"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type e2
    ^^ !^")"
  | PtrMemberShift (sym, id, e) ->
    !^"(PtrMemberShift"
    ^^^ pp_symbol sym
    ^^^ pp_identifier id
    ^^^ pp_pexpr pp_type e
    ^^ !^")"
  | Memcpy (e1, e2, e3) ->
    !^"(Memcpy"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^ !^")"
  | Memcmp (e1, e2, e3) ->
    !^"(Memcmp"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^ !^")"
  | Realloc (e1, e2, e3) ->
    !^"(Realloc"
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_pexpr pp_type e2
    ^^^ pp_pexpr pp_type e3
    ^^ !^")"
  | Va_start (e1, e2) ->
    !^"(Va_start" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"
  | Va_copy e -> !^"(Va_copy" ^^^ pp_pexpr pp_type e ^^ !^")"
  | Va_arg (e, act) -> !^"(Va_arg" ^^^ pp_pexpr pp_type e ^^^ pp_act act ^^ !^")"
  | Va_end e -> !^"(Va_end" ^^^ pp_pexpr pp_type e ^^ !^")"
  | CopyAllocId (e1, e2) ->
    !^"(CopyAllocId" ^^^ pp_pexpr pp_type e1 ^^^ pp_pexpr pp_type e2 ^^ !^")"


let rec pp_expr pp_type (Expr (loc, annots, ty, e)) =
  !^"Expr"
  ^^^ pp_location loc
  ^^^ pp_list pp_annot_t annots
  ^^^ pp_type ty
  ^^^
  match e with
  | Epure pe -> !^"(Epure" ^^^ pp_pexpr pp_type pe ^^ !^")"
  | Ememop m -> !^"(Ememop" ^^^ pp_memop pp_type m ^^ !^")"
  | Eaction pa -> !^"(Eaction" ^^^ pp_paction pp_type pa ^^ !^")"
  | Eskip -> !^"Eskip"
  | Eccall (act, f, args) ->
    !^"(Eccall"
    ^^^ pp_act act
    ^^^ pp_pexpr pp_type f
    ^^^ pp_list (pp_pexpr pp_type) args
    ^^ !^")"
  | Elet (pat, e1, e2) ->
    !^"(Elet"
    ^^^ pp_pattern pp_type pat
    ^^^ pp_pexpr pp_type e1
    ^^^ pp_expr pp_type e2
    ^^ !^")"
  | Eunseq exprs -> !^"(Eunseq" ^^^ pp_list (pp_expr pp_type) exprs ^^ !^")"
  | Ewseq (pat, e1, e2) ->
    !^"(Ewseq"
    ^^^ pp_pattern pp_type pat
    ^^^ pp_expr pp_type e1
    ^^^ pp_expr pp_type e2
    ^^ !^")"
  | Esseq (pat, e1, e2) ->
    !^"(Esseq"
    ^^^ pp_pattern pp_type pat
    ^^^ pp_expr pp_type e1
    ^^^ pp_expr pp_type e2
    ^^ !^")"
  | Eif (c, t, e) ->
    !^"(Eif" ^^^ pp_pexpr pp_type c ^^^ pp_expr pp_type t ^^^ pp_expr pp_type e ^^ !^")"
  | Ebound e -> !^"(Ebound" ^^^ pp_expr pp_type e ^^ !^")"
  | End exprs -> !^"(End" ^^^ pp_list (pp_expr pp_type) exprs ^^ !^")"
  | Erun (sym, args) ->
    !^"(Erun" ^^^ pp_symbol sym ^^^ pp_list (pp_pexpr pp_type) args ^^ !^")"
  | CN_progs (stmts, progs) ->
    (* TODO: this constructor was omitted from the original code *)
    P.empty


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
    !^"(Computational"
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
    !^"(Define"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_index_term term
    ^^ !^")"
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"
  | LogicalReturnTypes.Resource ((sym, (req, bt)), info, lrt) ->
    !^"(Resource"
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
    !^"(Constraint"
    ^^^ pp_logical_constraint lc
    ^^^ pp_location_info info
    ^^^ pp_logical_return_type lrt
    ^^^ !^")"
  | LogicalReturnTypes.I -> !^"I"


let rec pp_logical_args ppf = function
  | Define ((sym, term), info, rest) ->
    !^"(Define"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_index_term term
    ^^ !^")"
    ^^^ pp_location_info info
    ^^^ pp_logical_args ppf rest
    ^^ !^")"
  | Resource ((sym, (req, bt)), info, rest) ->
    !^"(Resource"
    ^^^ !^"("
    ^^^ pp_request req
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^"))"
    ^^^ pp_location_info info
    ^^^ pp_logical_args ppf rest
    ^^ !^")"
  | Constraint (lc, info, rest) ->
    !^"(Constraint"
    ^^^ pp_logical_constraint lc
    ^^^ pp_location_info info
    ^^^ pp_logical_args ppf rest
    ^^ !^")"
  | I i -> !^"(I" ^^^ ppf i ^^ !^")"


let rec pp_arguments ppf = function
  | Computational ((sym, bt), loc, rest) ->
    !^"(Computational"
    ^^^ !^"("
    ^^^ pp_symbol sym
    ^^ !^","
    ^^^ pp_basetype pp_unit bt
    ^^ !^")"
    ^^^ pp_location_info loc
    ^^^ pp_arguments ppf rest
    ^^ !^")"
  | L logical_args -> pp_logical_args ppf logical_args


let pp_cn_c_kind = function
  | CF.Cn.C_kind_var -> !^"C_kind_var"
  | C_kind_enum -> !^"C_kind_enum"


let pp_cn_sign = function
  | CF.Cn.CN_unsigned -> !^"CN_unsigned"
  | CN_signed -> !^"CN_signed"


let rec pp_cn_basetype ppfa = function
  | CF.Cn.CN_unit -> !^"CN_unit"
  | CN_bool -> !^"CN_bool"
  | CN_integer -> !^"CN_integer"
  | CN_bits (sign, sz) -> !^"(CN_bits" ^^^ pp_pair pp_cn_sign pp_nat (sign, sz) ^^ !^")"
  | CN_real -> !^"CN_real"
  | CN_loc -> !^"CN_loc"
  | CN_alloc_id -> !^"CN_alloc_id"
  | CN_struct a -> !^"(CN_struct" ^^^ ppfa a ^^ !^")"
  | CN_record fields ->
    !^"(CN_record"
    ^^^ pp_list (pp_pair pp_identifier (pp_cn_basetype ppfa)) fields
    ^^ !^")"
  | CN_datatype a -> !^"(CN_datatype" ^^^ ppfa a ^^ !^")"
  | CN_map (k, v) ->
    !^"(CN_map" ^^^ pp_pair (pp_cn_basetype ppfa) (pp_cn_basetype ppfa) (k, v) ^^ !^")"
  | CN_list t -> !^"(CN_list" ^^^ pp_cn_basetype ppfa t ^^ !^")"
  | CN_tuple ts -> !^"(CN_tuple" ^^^ pp_list (pp_cn_basetype ppfa) ts ^^ !^")"
  | CN_set t -> !^"(CN_set" ^^^ pp_cn_basetype ppfa t ^^ !^")"
  | CN_user_type_name a -> !^"(CN_user_type_name" ^^^ ppfa a ^^ !^")"
  | CN_c_typedef_name a -> !^"(CN_c_typedef_name" ^^^ ppfa a ^^ !^")"


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
    ^^^ pp_location loc
    ^^^ (match e with
         | CNExpr_const c -> !^"(CNExpr_const" ^^^ pp_cn_const c ^^ !^")"
         | CNExpr_var v -> !^"(CNExpr_var" ^^^ ppfa v ^^ !^")"
         | CNExpr_list es ->
           !^"(CNExpr_list" ^^^ pp_list (pp_cn_expr ppfa ppfty) es ^^ !^")"
         | CNExpr_memberof (e, id) ->
           !^"(CNExpr_memberof"
           ^^^ pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id)
           ^^ !^")"
         | CNExpr_arrow (e, id) ->
           !^"(CNExpr_arrow"
           ^^^ pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id)
           ^^ !^")"
         | CNExpr_record fs ->
           !^"(CNExpr_record"
           ^^^ pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) fs
           ^^ !^")"
         | CNExpr_struct (a, fs) ->
           !^"(CNExpr_struct"
           ^^^ pp_pair
                 ppfa
                 (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                 (a, fs)
           ^^ !^")"
         | CNExpr_memberupdates (e, us) ->
           !^"(CNExpr_memberupdates"
           ^^^ pp_pair
                 (pp_cn_expr ppfa ppfty)
                 (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                 (e, us)
           ^^ !^")"
         | CNExpr_arrayindexupdates (e, us) ->
           !^"(CNExpr_arrayindexupdates"
           ^^^ pp_pair
                 (pp_cn_expr ppfa ppfty)
                 (pp_list (pp_pair (pp_cn_expr ppfa ppfty) (pp_cn_expr ppfa ppfty)))
                 (e, us)
           ^^ !^")"
         | CNExpr_binop (op, e1, e2) ->
           !^"(CNExpr_binop"
           ^^^ pp_cn_binop op
           ^^^ pp_cn_expr ppfa ppfty e1
           ^^^ pp_cn_expr ppfa ppfty e2
           ^^ !^")"
         | CNExpr_sizeof ty -> !^"(CNExpr_sizeof" ^^^ ppfty ty ^^ !^")"
         | CNExpr_offsetof (a, id) ->
           !^"(CNExpr_offsetof" ^^^ pp_pair ppfa pp_identifier (a, id) ^^ !^")"
         | CNExpr_membershift (e, oa, id) ->
           !^"(CNExpr_membershift"
           ^^^ pp_cn_expr ppfa ppfty e
           ^^^ pp_option ppfa oa
           ^^^ pp_identifier id
           ^^ !^")"
         | CNExpr_addr a -> !^"(CNExpr_addr" ^^^ ppfa a ^^ !^")"
         | CNExpr_cast (bt, e) ->
           !^"(CNExpr_cast"
           ^^^ pp_pair (pp_cn_basetype ppfa) (pp_cn_expr ppfa ppfty) (bt, e)
           ^^ !^")"
         | CNExpr_array_shift (e, oty, idx) ->
           !^"(CNExpr_array_shift"
           ^^^ pp_cn_expr ppfa ppfty e
           ^^^ pp_option ppfty oty
           ^^^ pp_cn_expr ppfa ppfty idx
           ^^ !^")"
         | CNExpr_call (a, args) ->
           !^"(CNExpr_call"
           ^^^ pp_pair ppfa (pp_list (pp_cn_expr ppfa ppfty)) (a, args)
           ^^ !^")"
         | CNExpr_cons (a, args) ->
           !^"(CNExpr_cons"
           ^^^ pp_pair
                 ppfa
                 (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                 (a, args)
           ^^ !^")"
         | CNExpr_each (a, bt, rng, e) ->
           !^"(CNExpr_each"
           ^^^ ppfa a
           ^^^ pp_cn_basetype ppfa bt
           ^^^ pp_pair pp_Z pp_Z rng
           ^^^ pp_cn_expr ppfa ppfty e
           ^^ !^")"
         | CNExpr_let (a, e1, e2) ->
           !^"(CNExpr_let"
           ^^^ ppfa a
           ^^^ pp_cn_expr ppfa ppfty e1
           ^^^ pp_cn_expr ppfa ppfty e2
           ^^ !^")"
         | CNExpr_match (e, cases) ->
           !^"(CNExpr_match"
           ^^^ pp_cn_expr ppfa ppfty e
           ^^^ pp_list (pp_pair (pp_cn_pat ppfa) (pp_cn_expr ppfa ppfty)) cases
           ^^ !^")"
         | CNExpr_ite (c, t, e) ->
           !^"(CNExpr_ite"
           ^^^ pp_cn_expr ppfa ppfty c
           ^^^ pp_cn_expr ppfa ppfty t
           ^^^ pp_cn_expr ppfa ppfty e
           ^^ !^")"
         | CNExpr_good (ty, e) ->
           !^"(CNExpr_good" ^^^ pp_pair ppfty (pp_cn_expr ppfa ppfty) (ty, e) ^^ !^")"
         | CNExpr_deref e -> !^"(CNExpr_deref" ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_value_of_c_atom (a, k) ->
           !^"(CNExpr_value_of_c_atom" ^^^ pp_pair ppfa pp_cn_c_kind (a, k) ^^ !^")"
         | CNExpr_unchanged e ->
           !^"(CNExpr_unchanged" ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_at_env (e, s) ->
           !^"(CNExpr_at_env"
           ^^^ pp_pair (pp_cn_expr ppfa ppfty) pp_string (e, s)
           ^^ !^")"
         | CNExpr_not e -> !^"(CNExpr_not" ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_negate e -> !^"(CNExpr_negate" ^^^ pp_cn_expr ppfa ppfty e ^^ !^")"
         | CNExpr_default bt -> !^"(CNExpr_default" ^^^ pp_cn_basetype ppfa bt ^^ !^")"
         | CNExpr_bnot e -> !^"(CNExpr_bnot" ^^^ pp_cn_expr ppfa ppfty e ^^ !^")")
    ^^ !^")"


let rec pp_cn_resource ppfa ppfty = function
  | CF.Cn.CN_pred (loc, pred, args) ->
    !^"(CN_pred"
    ^^^ pp_location loc
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) args
    ^^ !^")"
  | CN_each (a, bt, e, loc, pred, args) ->
    !^"(CN_each"
    ^^^ ppfa a
    ^^^ pp_cn_basetype ppfa bt
    ^^^ pp_cn_expr ppfa ppfty e
    ^^^ pp_location loc
    ^^^ pp_cn_pred ppfa ppfty pred
    ^^^ pp_list (pp_cn_expr ppfa ppfty) args
    ^^ !^")"


and pp_cn_pred ppfa ppfty = function
  | CF.Cn.CN_owned ty -> !^"(CN_owned" ^^^ pp_option ppfty ty ^^ !^")"
  | CN_block ty -> !^"(CN_block" ^^^ pp_option ppfty ty ^^ !^")"
  | CN_named a -> !^"(CN_named" ^^^ ppfa a ^^ !^")"


let pp_cn_assertion ppfa ppfty = function
  | CF.Cn.CN_assert_exp ex -> !^"(CN_assert_exp" ^^^ pp_cn_expr ppfa ppfty ex ^^ !^")"
  | CN_assert_qexp (sym, bt, it1, it2) ->
    !^"(CN_assert_qexp"
    ^^^ ppfa sym
    ^^^ pp_cn_basetype ppfa bt
    ^^^ pp_cn_expr ppfa ppfty it1
    ^^^ pp_cn_expr ppfa ppfty it2
    ^^ !^")"


let pp_cn_condition ppfa ppfty = function
  | CF.Cn.CN_cletResource (loc, sym, res) ->
    !^"(CN_cletResource"
    ^^^ pp_location loc
    ^^^ ppfa sym
    ^^^ pp_cn_resource ppfa ppfty res
    ^^ !^")"
  | CN_cletExpr (loc, sym, ex) ->
    !^"(CN_cletExpr"
    ^^^ pp_location loc
    ^^^ ppfa sym
    ^^^ pp_cn_expr ppfa ppfty ex
    ^^ !^")"
  | CN_cconstr (loc, assertion) ->
    !^"(CN_cconstr" ^^^ pp_location loc ^^^ pp_cn_assertion ppfa ppfty assertion ^^ !^")"


let pp_parse_ast_label_spec (s : parse_ast_label_spec) =
  (* TODO double check this: *)
  !^"{|"
  ^^^ !^"label_spec :="
  ^^^ pp_list (pp_cn_condition pp_symbol pp_ctype) s.label_spec
  ^^^ !^"|}"


let pp_label_def pp_type = function
  | Return loc -> !^"(Return" ^^^ pp_location loc ^^ !^")"
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
      ^^^ pp_pmap "SymMap.from_list" pp_symbol (pp_label_def pp_type) labels
      ^^ !^","
      ^^^ pp_return_type rt
      ^^ !^"))")
    args


let pp_desugared_spec { accesses; requires; ensures } =
  !^"{|"
  ^^^ !^"accesses :="
  ^^^ pp_list
        (fun (sym, ty) -> !^"(" ^^ pp_symbol sym ^^ !^"," ^^^ pp_ctype ty ^^ !^")")
        accesses
  ^^ !^";"
  ^^^ !^"requires :="
  ^^^ pp_list (pp_cn_condition pp_symbol pp_ctype) requires
  ^^ !^";"
  ^^^ !^"ensures :="
  ^^^ pp_list (pp_cn_condition pp_symbol pp_ctype) ensures
  ^^^ !^"|}"


(* Top-level file printer *)
let pp_file pp_type pp_type_name file =
  !^"Require Import MuCore."
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
         (* TODO: handle ProcDecl *)
         | ProcDecl (loc, ft) ->
           (*
              coq_def (Pp_symbol.to_string_pretty_cn sym) P.empty
              (!^"ProcDecl" ^^^ pp_location loc ^^^
              match ft with None -> !^"None" | Some ft -> !^"(Some" ^^^ pp_ft ft ^^ !^")")
           *)
           P.empty
         | Proc { loc; args_and_body; trusted; desugared_spec } ->
           coq_def
             (Pp_symbol.to_string_pretty_cn sym)
             P.empty
             (!^"Proc"
              ^^^ pp_location loc
              ^^^ pp_args_and_body pp_type args_and_body
              ^^^ pp_trusted trusted
              ^^^ pp_desugared_spec desugared_spec))
       file.funs
       P.empty


(* let pp_file_string file = Pp_utils.to_plain_string (pp_file file) *)

let pp_unit_file (f : unit file) = pp_file pp_unit pp_unit_type f
