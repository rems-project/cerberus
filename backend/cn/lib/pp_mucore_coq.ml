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


let pp_lines (lines : string list) : P.document =
  List.fold_left (fun acc s -> acc ^^ !^s ^^ P.hardline) P.empty lines


let pp_bool b = if b then !^"true" else !^"false"

(* Some user-defined names can clash with existing Coq identifiers so we need to quote them *)
let quote_coq_name name = "_cn_" ^ name

(* Helper to print Coq definitions *)
let coq_def name args body =
  !^"Definition"
  ^^^ !^(quote_coq_name name)
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


(* Emits constrctor without arguments *)
let pp_constructor0 name = pp_constructor name []

(* Emits constrctor with implicit 1st wildcard (underscore) argument for type parameter *)
let pp_constructor1 name args = pp_constructor name (pp_underscore :: args)

(* Emits constrctor with implicit 1st and 2nd wildcard (underscore) arguments for 2 type parameters *)
let pp_constructor2 name args = pp_constructor1 name (pp_underscore :: args)

let pp_option pp_elem = function
  | None -> pp_constructor0 "None"
  | Some x -> pp_constructor "Some" [ pp_elem x ]


let pp_undefined_behaviour = function
  | Undefined.DUMMY str -> pp_constructor "DUMMY" [ pp_string str ]
  | Undefined.UB_unspecified_lvalue -> pp_constructor0 "UB_unspecified_lvalue"
  | Undefined.UB_std_omission om ->
    pp_constructor
      "UB_std_omission"
      [ (match om with
         | UB_OMIT_memcpy_non_object -> pp_constructor0 "UB_OMIT_memcpy_non_object"
         | UB_OMIT_memcpy_out_of_bound -> pp_constructor0 "UB_OMIT_memcpy_out_of_bound")
      ]
  | Undefined.Invalid_format str -> pp_constructor "Invalid_format" [ pp_string str ]
  | Undefined.UB_CERB004_unspecified ctx ->
    pp_constructor
      "UB_CERB004_unspecified"
      [ (match ctx with
         | UB_unspec_equality_ptr_vs_NULL ->
           pp_constructor0 "UB_unspec_equality_ptr_vs_NULL"
         | UB_unspec_equality_both_arith_or_ptr ->
           pp_constructor0 "UB_unspec_equality_both_arith_or_ptr"
         | UB_unspec_pointer_add -> pp_constructor0 "UB_unspec_pointer_add"
         | UB_unspec_pointer_sub -> pp_constructor0 "UB_unspec_pointer_sub"
         | UB_unspec_conditional -> pp_constructor0 "UB_unspec_conditional"
         | UB_unspec_copy_alloc_id -> pp_constructor0 "UB_unspec_copy_alloc_id"
         | UB_unspec_rvalue_memberof -> pp_constructor0 "UB_unspec_rvalue_memberof"
         | UB_unspec_memberofptr -> pp_constructor0 "UB_unspec_memberofptr"
         | UB_unspec_do -> pp_constructor0 "UB_unspec_do")
      ]
  | Undefined.UB_CERB005_free_nullptr -> pp_constructor0 "UB_CERB005_free_nullptr"
  | UB001 -> pp_constructor0 "UB001"
  | UB002 -> pp_constructor0 "UB002"
  | UB003 -> pp_constructor0 "UB003"
  | UB004a_incorrect_main_return_type ->
    pp_constructor0 "UB004a_incorrect_main_return_type"
  | UB004b_incorrect_main_argument1 -> pp_constructor0 "UB004b_incorrect_main_argument1"
  | UB004c_incorrect_main_argument2 -> pp_constructor0 "UB004c_incorrect_main_argument2"
  | UB004d_main_not_function -> pp_constructor0 "UB004d_main_not_function"
  | UB005_data_race -> pp_constructor0 "UB005_data_race"
  | UB006 -> pp_constructor0 "UB006"
  | UB007 -> pp_constructor0 "UB007"
  | UB008_multiple_linkage -> pp_constructor0 "UB008_multiple_linkage"
  | UB009_outside_lifetime -> pp_constructor0 "UB009_outside_lifetime"
  | UB010_pointer_to_dead_object -> pp_constructor0 "UB010_pointer_to_dead_object"
  | UB011_use_indeterminate_automatic_object ->
    pp_constructor0 "UB011_use_indeterminate_automatic_object"
  | UB_modifying_temporary_lifetime -> pp_constructor0 "UB_modifying_temporary_lifetime"
  | UB012_lvalue_read_trap_representation ->
    pp_constructor0 "UB012_lvalue_read_trap_representation"
  | UB013_lvalue_side_effect_trap_representation ->
    pp_constructor0 "UB013_lvalue_side_effect_trap_representation"
  | UB014_unsupported_negative_zero -> pp_constructor0 "UB014_unsupported_negative_zero"
  | UB015_incompatible_redeclaration -> pp_constructor0 "UB015_incompatible_redeclaration"
  | UB016 -> pp_constructor0 "UB016"
  | UB017_out_of_range_floating_integer_conversion ->
    pp_constructor0 "UB017_out_of_range_floating_integer_conversion"
  | UB018 -> pp_constructor0 "UB018"
  | UB019_lvalue_not_an_object -> pp_constructor0 "UB019_lvalue_not_an_object"
  | UB020_nonarray_incomplete_lvalue_conversion ->
    pp_constructor0 "UB020_nonarray_incomplete_lvalue_conversion"
  | UB021 -> pp_constructor0 "UB021"
  | UB022_register_array_decay -> pp_constructor0 "UB022_register_array_decay"
  | UB023 -> pp_constructor0 "UB023"
  | UB024_out_of_range_pointer_to_integer_conversion ->
    pp_constructor0 "UB024_out_of_range_pointer_to_integer_conversion"
  | UB025_misaligned_pointer_conversion ->
    pp_constructor0 "UB025_misaligned_pointer_conversion"
  | UB026 -> pp_constructor0 "UB026"
  | UB027 -> pp_constructor0 "UB027"
  | UB028 -> pp_constructor0 "UB028"
  | UB029 -> pp_constructor0 "UB029"
  | UB030 -> pp_constructor0 "UB030"
  | UB031 -> pp_constructor0 "UB031"
  | UB032 -> pp_constructor0 "UB032"
  | UB033_modifying_string_literal -> pp_constructor0 "UB033_modifying_string_literal"
  | UB034 -> pp_constructor0 "UB034"
  | UB035_unsequenced_race -> pp_constructor0 "UB035_unsequenced_race"
  | UB036_exceptional_condition -> pp_constructor0 "UB036_exceptional_condition"
  | UB037_illtyped_load -> pp_constructor0 "UB037_illtyped_load"
  | UB038_number_of_args -> pp_constructor0 "UB038_number_of_args"
  | UB039 -> pp_constructor0 "UB039"
  | UB040 -> pp_constructor0 "UB040"
  | UB041_function_not_compatible -> pp_constructor0 "UB041_function_not_compatible"
  | UB042_access_atomic_structUnion_member ->
    pp_constructor0 "UB042_access_atomic_structUnion_member"
  | UB043_indirection_invalid_value -> pp_constructor0 "UB043_indirection_invalid_value"
  | UB044 -> pp_constructor0 "UB044"
  | UB045a_division_by_zero -> pp_constructor0 "UB045a_division_by_zero"
  | UB045b_modulo_by_zero -> pp_constructor0 "UB045b_modulo_by_zero"
  | UB045c_quotient_not_representable ->
    pp_constructor0 "UB045c_quotient_not_representable"
  | UB046_array_pointer_outside -> pp_constructor0 "UB046_array_pointer_outside"
  | UB047a_array_pointer_addition_beyond_indirection ->
    pp_constructor0 "UB047a_array_pointer_addition_beyond_indirection"
  | UB047b_array_pointer_subtraction_beyond_indirection ->
    pp_constructor0 "UB047b_array_pointer_subtraction_beyond_indirection"
  | UB048_disjoint_array_pointers_subtraction ->
    pp_constructor0 "UB048_disjoint_array_pointers_subtraction"
  | UB049 -> pp_constructor0 "UB049"
  | UB050_pointers_subtraction_not_representable ->
    pp_constructor0 "UB050_pointers_subtraction_not_representable"
  | UB051a_negative_shift -> pp_constructor0 "UB051a_negative_shift"
  | UB51b_shift_too_large -> pp_constructor0 "UB51b_shift_too_large"
  | UB052a_negative_left_shift -> pp_constructor0 "UB052a_negative_left_shift"
  | UB052b_non_representable_left_shift ->
    pp_constructor0 "UB052b_non_representable_left_shift"
  | UB053_distinct_aggregate_union_pointer_comparison ->
    pp_constructor0 "UB053_distinct_aggregate_union_pointer_comparison"
  | UB054a_inexactly_overlapping_assignment ->
    pp_constructor0 "UB054a_inexactly_overlapping_assignment"
  | UB054b_incompatible_overlapping_assignment ->
    pp_constructor0 "UB054b_incompatible_overlapping_assignment"
  | UB055_invalid_integer_constant_expression ->
    pp_constructor0 "UB055_invalid_integer_constant_expression"
  | UB056 -> pp_constructor0 "UB056"
  | UB057 -> pp_constructor0 "UB057"
  | UB058 -> pp_constructor0 "UB058"
  | UB059_incomplete_no_linkage_identifier ->
    pp_constructor0 "UB059_incomplete_no_linkage_identifier"
  | UB060_block_scope_function_with_storage_class ->
    pp_constructor0 "UB060_block_scope_function_with_storage_class"
  | UB061_no_named_members -> pp_constructor0 "UB061_no_named_members"
  | UB062 -> pp_constructor0 "UB062"
  | UB063 -> pp_constructor0 "UB063"
  | UB064_modifying_const -> pp_constructor0 "UB064_modifying_const"
  | UB065 -> pp_constructor0 "UB065"
  | UB066_qualified_function_specification ->
    pp_constructor0 "UB066_qualified_function_specification"
  | UB067 -> pp_constructor0 "UB067"
  | UB068 -> pp_constructor0 "UB068"
  | UB069 -> pp_constructor0 "UB069"
  | UB070_inline_not_defined -> pp_constructor0 "UB070_inline_not_defined"
  | UB071_noreturn -> pp_constructor0 "UB071_noreturn"
  | UB072_incompatible_alignment_specifiers ->
    pp_constructor0 "UB072_incompatible_alignment_specifiers"
  | UB073 -> pp_constructor0 "UB073"
  | UB074 -> pp_constructor0 "UB074"
  | UB075 -> pp_constructor0 "UB075"
  | UB076 -> pp_constructor0 "UB076"
  | UB077 -> pp_constructor0 "UB077"
  | UB078_modified_void_parameter -> pp_constructor0 "UB078_modified_void_parameter"
  | UB079 -> pp_constructor0 "UB079"
  | UB080 -> pp_constructor0 "UB080"
  | UB081_scalar_initializer_not_single_expression ->
    pp_constructor0 "UB081_scalar_initializer_not_single_expression"
  | UB082 -> pp_constructor0 "UB082"
  | UB083 -> pp_constructor0 "UB083"
  | UB084 -> pp_constructor0 "UB084"
  | UB085 -> pp_constructor0 "UB085"
  | UB086_incomplete_adjusted_parameter ->
    pp_constructor0 "UB086_incomplete_adjusted_parameter"
  | UB087 -> pp_constructor0 "UB087"
  | UB088_reached_end_of_function -> pp_constructor0 "UB088_reached_end_of_function"
  | UB089_tentative_definition_internal_linkage ->
    pp_constructor0 "UB089_tentative_definition_internal_linkage"
  | UB090 -> pp_constructor0 "UB090"
  | UB091 -> pp_constructor0 "UB091"
  | UB092 -> pp_constructor0 "UB092"
  | UB093 -> pp_constructor0 "UB093"
  | UB094 -> pp_constructor0 "UB094"
  | UB095 -> pp_constructor0 "UB095"
  | UB096 -> pp_constructor0 "UB096"
  | UB097 -> pp_constructor0 "UB097"
  | UB098 -> pp_constructor0 "UB098"
  | UB099 -> pp_constructor0 "UB099"
  | UB100 -> pp_constructor0 "UB100"
  | UB101 -> pp_constructor0 "UB101"
  | UB102 -> pp_constructor0 "UB102"
  | UB103 -> pp_constructor0 "UB103"
  | UB104 -> pp_constructor0 "UB104"
  | UB105 -> pp_constructor0 "UB105"
  | UB106 -> pp_constructor0 "UB106"
  | UB107 -> pp_constructor0 "UB107"
  | UB108 -> pp_constructor0 "UB108"
  | UB109 -> pp_constructor0 "UB109"
  | UB110 -> pp_constructor0 "UB110"
  | UB111_illtyped_assert -> pp_constructor0 "UB111_illtyped_assert"
  | UB112 -> pp_constructor0 "UB112"
  | UB113 -> pp_constructor0 "UB113"
  | UB114 -> pp_constructor0 "UB114"
  | UB115 -> pp_constructor0 "UB115"
  | UB116 -> pp_constructor0 "UB116"
  | UB117 -> pp_constructor0 "UB117"
  | UB118 -> pp_constructor0 "UB118"
  | UB119 -> pp_constructor0 "UB119"
  | UB120 -> pp_constructor0 "UB120"
  | UB121 -> pp_constructor0 "UB121"
  | UB122 -> pp_constructor0 "UB122"
  | UB123 -> pp_constructor0 "UB123"
  | UB124 -> pp_constructor0 "UB124"
  | UB125 -> pp_constructor0 "UB125"
  | UB126 -> pp_constructor0 "UB126"
  | UB127 -> pp_constructor0 "UB127"
  | UB128 -> pp_constructor0 "UB128"
  | UB129 -> pp_constructor0 "UB129"
  | UB130 -> pp_constructor0 "UB130"
  | UB131 -> pp_constructor0 "UB131"
  | UB132 -> pp_constructor0 "UB132"
  | UB133 -> pp_constructor0 "UB133"
  | UB134 -> pp_constructor0 "UB134"
  | UB135 -> pp_constructor0 "UB135"
  | UB136 -> pp_constructor0 "UB136"
  | UB137 -> pp_constructor0 "UB137"
  | UB138 -> pp_constructor0 "UB138"
  | UB139 -> pp_constructor0 "UB139"
  | UB140 -> pp_constructor0 "UB140"
  | UB141 -> pp_constructor0 "UB141"
  | UB142 -> pp_constructor0 "UB142"
  | UB143 -> pp_constructor0 "UB143"
  | UB144 -> pp_constructor0 "UB144"
  | UB145 -> pp_constructor0 "UB145"
  | UB146 -> pp_constructor0 "UB146"
  | UB147 -> pp_constructor0 "UB147"
  | UB148 -> pp_constructor0 "UB148"
  | UB149 -> pp_constructor0 "UB149"
  | UB150 -> pp_constructor0 "UB150"
  | UB151 -> pp_constructor0 "UB151"
  | UB152 -> pp_constructor0 "UB152"
  | UB153a_insufficient_arguments_for_format ->
    pp_constructor0 "UB153a_insufficient_arguments_for_format"
  | UB153b_illtyped_argument_for_format ->
    pp_constructor0 "UB153b_illtyped_argument_for_format"
  | UB154 -> pp_constructor0 "UB154"
  | UB155 -> pp_constructor0 "UB155"
  | UB156 -> pp_constructor0 "UB156"
  | UB157 -> pp_constructor0 "UB157"
  | UB158_invalid_length_modifier -> pp_constructor0 "UB158_invalid_length_modifier"
  | UB159 -> pp_constructor0 "UB159"
  | UB160 -> pp_constructor0 "UB160"
  | UB161 -> pp_constructor0 "UB161"
  | UB162 -> pp_constructor0 "UB162"
  | UB163 -> pp_constructor0 "UB163"
  | UB164 -> pp_constructor0 "UB164"
  | UB165 -> pp_constructor0 "UB165"
  | UB166 -> pp_constructor0 "UB166"
  | UB167 -> pp_constructor0 "UB167"
  | UB168 -> pp_constructor0 "UB168"
  | UB169 -> pp_constructor0 "UB169"
  | UB170 -> pp_constructor0 "UB170"
  | UB171 -> pp_constructor0 "UB171"
  | UB172 -> pp_constructor0 "UB172"
  | UB173 -> pp_constructor0 "UB173"
  | UB174 -> pp_constructor0 "UB174"
  | UB175 -> pp_constructor0 "UB175"
  | UB176 -> pp_constructor0 "UB176"
  | UB177 -> pp_constructor0 "UB177"
  | UB178 -> pp_constructor0 "UB178"
  | UB179a_non_matching_allocation_free ->
    pp_constructor0 "UB179a_non_matching_allocation_free"
  | UB179b_dead_allocation_free -> pp_constructor0 "UB179b_dead_allocation_free"
  | UB179c_non_matching_allocation_realloc ->
    pp_constructor0 "UB179c_non_matching_allocation_realloc"
  | UB179d_dead_allocation_realloc -> pp_constructor0 "UB179d_dead_allocation_realloc"
  | UB180 -> pp_constructor0 "UB180"
  | UB181 -> pp_constructor0 "UB181"
  | UB182 -> pp_constructor0 "UB182"
  | UB183 -> pp_constructor0 "UB183"
  | UB184 -> pp_constructor0 "UB184"
  | UB185 -> pp_constructor0 "UB185"
  | UB186 -> pp_constructor0 "UB186"
  | UB187 -> pp_constructor0 "UB187"
  | UB188 -> pp_constructor0 "UB188"
  | UB189 -> pp_constructor0 "UB189"
  | UB190 -> pp_constructor0 "UB190"
  | UB191 -> pp_constructor0 "UB191"
  | UB192 -> pp_constructor0 "UB192"
  | UB193 -> pp_constructor0 "UB193"
  | UB194 -> pp_constructor0 "UB194"
  | UB195 -> pp_constructor0 "UB195"
  | UB196 -> pp_constructor0 "UB196"
  | UB197 -> pp_constructor0 "UB197"
  | UB198 -> pp_constructor0 "UB198"
  | UB199 -> pp_constructor0 "UB199"
  | UB200 -> pp_constructor0 "UB200"
  | UB201 -> pp_constructor0 "UB201"
  | UB202 -> pp_constructor0 "UB202"
  | UB203 -> pp_constructor0 "UB203"
  | UB204_illtyped_Static_assert -> pp_constructor0 "UB204_illtyped_Static_assert"
  | UB205_atomic_store_memorder -> pp_constructor0 "UB205_atomic_store_memorder"
  | UB206_atomic_load_memorder -> pp_constructor0 "UB206_atomic_load_memorder"
  | UB207_atomic_compare_exchange_memorder ->
    pp_constructor0 "UB207_atomic_compare_exchange_memorder"
  | UB_CERB001_integer_to_dead_pointer ->
    pp_constructor0 "UB_CERB001_integer_to_dead_pointer"
  | UB_CERB002a_out_of_bound_load -> pp_constructor0 "UB_CERB002a_out_of_bound_load"
  | UB_CERB002b_out_of_bound_store -> pp_constructor0 "UB_CERB002b_out_of_bound_store"
  | UB_CERB002c_out_of_bound_free -> pp_constructor0 "UB_CERB002c_out_of_bound_free"
  | UB_CERB002d_out_of_bound_realloc -> pp_constructor0 "UB_CERB002d_out_of_bound_realloc"
  | UB_CERB003_invalid_function_pointer ->
    pp_constructor0 "UB_CERB003_invalid_function_pointer"
  | UB_CHERI_InvalidCap -> pp_constructor0 "UB_CHERI_InvalidCap"
  | UB_CHERI_InsufficientPermissions -> pp_constructor0 "UB_CHERI_InsufficientPermissions"
  | UB_CHERI_BoundsViolation -> pp_constructor0 "UB_CHERI_BoundsViolation"
  | UB_CHERI_UndefinedTag -> pp_constructor0 "UB_CHERI_UndefinedTag"
  | UB_CHERI_ZeroLength -> pp_constructor0 "UB_CHERI_ZeroLength"


let pp_linux_memory_order = function
  | CF.Linux.Once -> pp_constructor0 "Once"
  | LAcquire -> pp_constructor0 "LAcquire"
  | LRelease -> pp_constructor0 "LRelease"
  | Rmb -> pp_constructor0 "Rmb"
  | Wmb -> pp_constructor0 "Wmb"
  | Mb -> pp_constructor0 "Mb"
  | RbDep -> pp_constructor0 "RbDep"
  | RcuLock -> pp_constructor0 "RcuLock"
  | RcuUnlock -> pp_constructor0 "RcuUnlock"
  | SyncRcu -> pp_constructor0 "SyncRcu"


let pp_floating_value v = Impl_mem.pp_floating_value_for_coq v

let pp_unit (_ : unit) = !^"tt"

let pp_unit_type = !^"unit"

let pp_memory_order = function
  | Cerb_frontend.Cmm_csem.NA -> pp_constructor0 "NA"
  | Seq_cst -> pp_constructor0 "Seq_cst"
  | Relaxed -> pp_constructor0 "Relaxed"
  | Release -> pp_constructor0 "Release"
  | Acquire -> pp_constructor0 "Acquire"
  | Consume -> pp_constructor0 "Consume"
  | Acq_rel -> pp_constructor0 "Acq_rel"


let pp_polarity = function Core.Pos -> !^"Pos" | Core.Neg -> !^"Neg"

(* XXX: use the original source locations? *)
let pp_lexing_position pos =
  let { Lexing.pos_fname; pos_lnum; pos_bol; pos_cnum } =
    Cerb_position.to_file_lexing pos
  in
  pp_record
    [ ("pos_fname", pp_string pos_fname);
      ("pos_lnum", pp_nat pos_lnum);
      ("pos_bol", pp_nat pos_bol);
      ("pos_cnum", pp_nat pos_cnum)
    ]


let pp_location_cursor = function
  | Cerb_location.NoCursor -> pp_constructor0 "NoCursor"
  | Cerb_location.PointCursor pos ->
    pp_constructor "PointCursor" [ pp_lexing_position pos ]
  | Cerb_location.RegionCursor (start_pos, end_pos) ->
    pp_constructor
      "RegionCursor"
      [ pp_lexing_position start_pos; pp_lexing_position end_pos ]


let pp_location = function
  | Cerb_location.Loc_unknown -> pp_constructor0 "Loc_unknown"
  | _ when not debug_print_locations -> pp_constructor0 "Loc_unknown"
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
  | CF.Symbol.SD_None -> pp_constructor0 "SD_None"
  | CF.Symbol.SD_unnamed_tag loc -> pp_constructor "SD_unnamed_tag" [ pp_location loc ]
  | CF.Symbol.SD_Id s -> pp_constructor "SD_Id" [ pp_string s ]
  | CF.Symbol.SD_CN_Id s -> pp_constructor "SD_CN_Id" [ pp_string s ]
  | CF.Symbol.SD_ObjectAddress s -> pp_constructor "SD_ObjectAddress" [ pp_string s ]
  | CF.Symbol.SD_Return -> pp_constructor0 "SD_Return"
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
  | CF.Symbol.PrefMalloc -> pp_constructor0 "PrefMalloc"
  | CF.Symbol.PrefOther s -> pp_constructor "PrefOther" [ !^s ]


let pp_sign = function
  | BaseTypes.Signed -> pp_constructor0 "BaseTypes.Signed"
  | BaseTypes.Unsigned -> pp_constructor0 "BaseTypes.Unsigned"


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
      "BaseTypes.TRecord"
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
  | Sctypes.IntegerBaseTypes.Ichar -> pp_constructor0 "Ichar"
  | Sctypes.IntegerBaseTypes.Short -> pp_constructor0 "Short"
  | Sctypes.IntegerBaseTypes.Int_ -> pp_constructor0 "Int_"
  | Sctypes.IntegerBaseTypes.Long -> pp_constructor0 "Long"
  | Sctypes.IntegerBaseTypes.LongLong -> pp_constructor0 "LongLong"
  | Sctypes.IntegerBaseTypes.IntN_t n -> pp_constructor "IntN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Int_leastN_t n -> pp_constructor "Int_leastN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Int_fastN_t n -> pp_constructor "Int_fastN_t" [ pp_nat n ]
  | Sctypes.IntegerBaseTypes.Intmax_t -> pp_constructor0 "Intmax_t"
  | Sctypes.IntegerBaseTypes.Intptr_t -> pp_constructor0 "Intptr_t"


let pp_integer_type = function
  | Sctypes.IntegerTypes.Char -> pp_constructor0 "IntegerType.Char"
  | Sctypes.IntegerTypes.Bool -> pp_constructor0 "IntegerType.Bool"
  | Sctypes.IntegerTypes.Signed ibt ->
    pp_constructor "IntegerType.Signed" [ pp_integer_base_type ibt ]
  | Sctypes.IntegerTypes.Unsigned ibt ->
    pp_constructor "IntegerType.Unsigned" [ pp_integer_base_type ibt ]
  | Sctypes.IntegerTypes.Enum sym -> pp_constructor "IntegerType.Enum" [ pp_symbol sym ]
  | Sctypes.IntegerTypes.Wchar_t -> pp_constructor0 "IntegerType.Wchar_t"
  | Sctypes.IntegerTypes.Wint_t -> pp_constructor0 "IntegerType.Wint_t"
  | Sctypes.IntegerTypes.Size_t -> pp_constructor0 "IntegerType.Size_t"
  | Sctypes.IntegerTypes.Ptrdiff_t -> pp_constructor0 "IntegerType.Ptrdiff_t"
  | Sctypes.IntegerTypes.Ptraddr_t -> pp_constructor0 "IntegerType.Ptraddr_t"


let rec pp_annot_t = function
  | Annot.Astd s -> pp_constructor "Astd" [ pp_string s ]
  | Annot.Aloc loc -> pp_constructor "Aloc" [ pp_location loc ]
  | Annot.Auid s -> pp_constructor "Auid" [ pp_string s ]
  | Annot.Amarker n -> pp_constructor "Amarker" [ pp_nat n ]
  | Annot.Amarker_object_types n -> pp_constructor "Amarker_object_types" [ pp_nat n ]
  | Annot.Abmc bmc -> pp_constructor "Abmc" [ pp_bmc_annot bmc ]
  | Annot.Aattrs attrs -> pp_constructor "Aattrs" [ pp_attributes attrs ]
  | Annot.Atypedef sym -> pp_constructor "Atypedef" [ pp_symbol sym ]
  | Annot.Anot_explode -> pp_constructor0 "Anot_explode"
  | Annot.Alabel la -> pp_constructor "Alabel" [ pp_label_annot la ]
  | Annot.Acerb ca -> pp_constructor "Acerb" [ pp_cerb_attribute ca ]
  | Annot.Avalue va -> pp_constructor "Avalue" [ pp_value_annot va ]
  | Annot.Ainlined_label (loc, sym, la) ->
    pp_constructor "Ainlined_label" [ pp_location loc; pp_symbol sym; pp_label_annot la ]
  | Annot.Astmt -> pp_constructor0 "Astmt"
  | Annot.Aexpr -> pp_constructor0 "Aexpr"


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
  | Annot.LAreturn -> pp_constructor0 "LAreturn"
  | Annot.LAswitch -> pp_constructor0 "LAswitch"
  | Annot.LAcase -> pp_constructor0 "LAcase"
  | Annot.LAdefault -> pp_constructor0 "LAdefault"
  | Annot.LAactual_label -> pp_constructor0 "LAactual_label"


and pp_cerb_attribute = function
  | Annot.ACerb_with_address n -> pp_constructor "ACerb_with_address" [ pp_Z_as_nat n ]
  | Annot.ACerb_hidden -> pp_constructor0 "ACerb_hidden"


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
       | Ctype.Void -> pp_constructor0 "Ctype.Void"
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
  | Ctype.Float -> pp_constructor0 "Float"
  | Ctype.Double -> pp_constructor0 "Double"
  | Ctype.LongDouble -> pp_constructor0 "LongDouble"


let rec pp_sctype = function
  | Sctypes.Void -> pp_constructor0 "SCtypes.Void"
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
  | Core.BTy_unit -> pp_constructor0 "BTy_unit"
  | Core.BTy_boolean -> pp_constructor0 "BTy_boolean"
  | Core.BTy_ctype -> pp_constructor0 "BTy_ctype"
  | Core.BTy_list t -> pp_constructor "BTy_list" [ pp_core_base_type t ]
  | Core.BTy_tuple ts -> pp_constructor "BTy_tuple" [ pp_list pp_core_base_type ts ]
  | Core.BTy_object ot -> pp_constructor "BTy_object" [ pp_core_object_type ot ]
  | Core.BTy_loaded ot -> pp_constructor "BTy_loaded" [ pp_core_object_type ot ]
  | Core.BTy_storable -> pp_constructor0 "BTy_storable"


and pp_core_object_type = function
  | Core.OTy_integer -> pp_constructor0 "OTy_integer"
  | Core.OTy_floating -> pp_constructor0 "OTy_floating"
  | Core.OTy_pointer -> pp_constructor0 "OTy_pointer"
  | Core.OTy_array t -> pp_constructor "OTy_array" [ pp_core_object_type t ]
  | Core.OTy_struct sym -> pp_constructor "OTy_struct" [ pp_symbol sym ]
  | Core.OTy_union sym -> pp_constructor "OTy_union" [ pp_symbol sym ]


let pp_ctor = function
  | Mucore.Cnil bt -> pp_constructor "Cnil" [ pp_core_base_type bt ]
  | Mucore.Ccons -> pp_constructor0 "Ccons"
  | Mucore.Ctuple -> pp_constructor0 "Ctuple"
  | Mucore.Carray -> pp_constructor0 "Carray"


let pp_core_binop = function
  | Core.OpAdd -> pp_constructor0 "Core.OpAdd"
  | Core.OpSub -> pp_constructor0 "Core.OpSub"
  | Core.OpMul -> pp_constructor0 "Core.OpMul"
  | Core.OpDiv -> pp_constructor0 "Core.OpDiv"
  | Core.OpRem_t -> pp_constructor0 "Core.OpRem_t"
  | Core.OpRem_f -> pp_constructor0 "Core.OpRem_f"
  | Core.OpExp -> pp_constructor0 "Core.OpExp"
  | Core.OpEq -> pp_constructor0 "Core.OpEq"
  | Core.OpGt -> pp_constructor0 "Core.OpGt"
  | Core.OpLt -> pp_constructor0 "Core.OpLt"
  | Core.OpGe -> pp_constructor0 "Core.OpGe"
  | Core.OpLe -> pp_constructor0 "Core.OpLe"
  | Core.OpAnd -> pp_constructor0 "Core.OpAnd"
  | Core.OpOr -> pp_constructor0 "Core.OpOr"


let pp_binop = function
  | Terms.And -> pp_constructor0 "Terms.And"
  | Terms.Or -> pp_constructor0 "Terms.Or"
  | Terms.Implies -> pp_constructor0 "Terms.Implies"
  | Terms.Add -> pp_constructor0 "Terms.Add"
  | Terms.Sub -> pp_constructor0 "Terms.Sub"
  | Terms.Mul -> pp_constructor0 "Terms.Mul"
  | Terms.MulNoSMT -> pp_constructor0 "Terms.MulNoSMT"
  | Terms.Div -> pp_constructor0 "Terms.Div"
  | Terms.DivNoSMT -> pp_constructor0 "Terms.DivNoSMT"
  | Terms.Exp -> pp_constructor0 "Terms.Exp"
  | Terms.ExpNoSMT -> pp_constructor0 "Terms.ExpNoSMT"
  | Terms.Rem -> pp_constructor0 "Terms.Rem"
  | Terms.RemNoSMT -> pp_constructor0 "Terms.RemNoSMT"
  | Terms.Mod -> pp_constructor0 "Terms.Mod"
  | Terms.ModNoSMT -> pp_constructor0 "Terms.ModNoSMT"
  | Terms.BW_Xor -> pp_constructor0 "Terms.BW_Xor"
  | Terms.BW_And -> pp_constructor0 "Terms.BW_And"
  | Terms.BW_Or -> pp_constructor0 "Terms.BW_Or"
  | Terms.ShiftLeft -> pp_constructor0 "Terms.ShiftLeft"
  | Terms.ShiftRight -> pp_constructor0 "Terms.ShiftRight"
  | Terms.LT -> pp_constructor0 "Terms.LT"
  | Terms.LE -> pp_constructor0 "Terms.LE"
  | Terms.Min -> pp_constructor0 "Terms.Min"
  | Terms.Max -> pp_constructor0 "Terms.Max"
  | Terms.EQ -> pp_constructor0 "Terms.EQ"
  | Terms.LTPointer -> pp_constructor0 "Terms.LTPointer"
  | Terms.LEPointer -> pp_constructor0 "Terms.LEPointer"
  | Terms.SetUnion -> pp_constructor0 "Terms.SetUnion"
  | Terms.SetIntersection -> pp_constructor0 "Terms.SetIntersection"
  | Terms.SetDifference -> pp_constructor0 "Terms.SetDifference"
  | Terms.SetMember -> pp_constructor0 "Terms.SetMember"
  | Terms.Subset -> pp_constructor0 "Terms.Subset"


let pp_bw_binop = function
  | BW_OR -> pp_constructor0 "BW_OR"
  | BW_AND -> pp_constructor0 "BW_AND"
  | BW_XOR -> pp_constructor0 "BW_XOR"


let pp_bw_unop = function
  | BW_COMPL -> pp_constructor0 "BW_COMPL"
  | BW_CTZ -> pp_constructor0 "BW_CTZ"
  | BW_FFS -> pp_constructor0 "BW_FFS"


let pp_core_iop = function
  | Core.IOpAdd -> pp_constructor0 "Core.IOpAdd"
  | Core.IOpSub -> pp_constructor0 "Core.IOpSub"
  | Core.IOpMul -> pp_constructor0 "Core.IOpMul"
  | Core.IOpShl -> pp_constructor0 "Core.IOpShl"
  | Core.IOpShr -> pp_constructor0 "Core.IOpShr"


let rec pp_pattern_ pp_type = function
  | CaseBase (sym_opt, bt) ->
    pp_constructor1
      "CaseBase"
      [ pp_tuple [ pp_option pp_symbol sym_opt; pp_core_base_type bt ] ]
  | CaseCtor (ctor, pats) ->
    pp_constructor1 "CaseCtor" [ pp_ctor ctor; pp_list (pp_pattern pp_type) pats ]


and pp_pattern pp_type (Pattern (loc, annots, ty, pat)) =
  pp_constructor1
    "Pattern"
    [ pp_location loc; pp_list pp_annot_t annots; pp_type ty; pp_pattern_ pp_type pat ]


let pp_mem_value v =
  Impl_mem.pp_mem_value_for_coq
    pp_symbol
    pp_integer_type
    pp_floating_type
    pp_ctype
    pp_identifier
    v


let rec pp_mem_constraint = function
  | Mem_common.MC_empty -> pp_constructor0 "MC_empty"
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
  pp_constructor1
    "Pexpr"
    [ pp_location loc;
      pp_list pp_annot_t annots;
      pp_type ty;
      (match pe with
       | PEsym s -> pp_constructor1 "PEsym" [ pp_symbol s ]
       | PEval v -> pp_constructor1 "PEval" [ pp_value pp_type v ]
       | PEctor (c, es) ->
         pp_constructor1 "PEctor" [ pp_ctor c; pp_list (pp_pexpr pp_type) es ]
       | PEop (op, e1, e2) ->
         pp_constructor1
           "PEop"
           [ pp_core_binop op; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEconstrained cs ->
         pp_constructor1
           "PEconstrained"
           [ pp_list (pp_pair pp_mem_constraint (pp_pexpr pp_type)) cs ]
       | PEbitwise_unop (op, e) ->
         pp_constructor1 "PEbitwise_unop" [ pp_bw_unop op; pp_pexpr pp_type e ]
       | PEbitwise_binop (op, e1, e2) ->
         pp_constructor1
           "PEbitwise_binop"
           [ pp_bw_binop op; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | Cfvfromint e -> pp_constructor1 "Cfvfromint" [ pp_pexpr pp_type e ]
       | Civfromfloat (act, e) ->
         pp_constructor1 "Civfromfloat" [ pp_act act; pp_pexpr pp_type e ]
       | PEarray_shift (base, ct, idx) ->
         pp_constructor1
           "PEarray_shift"
           [ pp_pexpr pp_type base; pp_sctype ct; pp_pexpr pp_type idx ]
       | PEmember_shift (e, sym, id) ->
         pp_constructor1
           "PEmember_shift"
           [ pp_pexpr pp_type e; pp_symbol sym; pp_identifier id ]
       | PEnot e -> pp_constructor1 "PEnot" [ pp_pexpr pp_type e ]
       | PEapply_fun (f, args) ->
         pp_constructor1 "PEapply_fun" [ pp_function f; pp_list (pp_pexpr pp_type) args ]
       | PEstruct (sym, fields) ->
         pp_constructor1
           "PEstruct"
           [ pp_symbol sym; pp_list (pp_pair pp_identifier (pp_pexpr pp_type)) fields ]
       | PEunion (sym, id, e) ->
         pp_constructor1 "PEunion" [ pp_symbol sym; pp_identifier id; pp_pexpr pp_type e ]
       | PEcfunction e -> pp_constructor1 "PEcfunction" [ pp_pexpr pp_type e ]
       | PEmemberof (sym, id, e) ->
         pp_constructor1
           "PEmemberof"
           [ pp_symbol sym; pp_identifier id; pp_pexpr pp_type e ]
       | PEbool_to_integer e -> pp_constructor1 "PEbool_to_integer" [ pp_pexpr pp_type e ]
       | PEconv_int (e1, e2) ->
         pp_constructor1 "PEconv_int" [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEconv_loaded_int (e1, e2) ->
         pp_constructor1 "PEconv_loaded_int" [ pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEwrapI (act, e) -> pp_constructor1 "PEwrapI" [ pp_act act; pp_pexpr pp_type e ]
       | PEcatch_exceptional_condition (act, e) ->
         pp_constructor1
           "PEcatch_exceptional_condition"
           [ pp_act act; pp_pexpr pp_type e ]
       | PEbounded_binop (kind, op, e1, e2) ->
         pp_constructor1
           "PEbounded_binop"
           [ pp_bound_kind kind;
             pp_core_iop op;
             pp_pexpr pp_type e1;
             pp_pexpr pp_type e2
           ]
       | PEis_representable_integer (e, act) ->
         pp_constructor1 "PEis_representable_integer" [ pp_pexpr pp_type e; pp_act act ]
       | PEundef (loc, ub) ->
         pp_constructor1 "PEundef" [ pp_location loc; pp_undefined_behaviour ub ]
       | PEerror (msg, e) ->
         pp_constructor1 "PEerror" [ pp_string msg; pp_pexpr pp_type e ]
       | PElet (pat, e1, e2) ->
         pp_constructor1
           "PElet"
           [ pp_pattern pp_type pat; pp_pexpr pp_type e1; pp_pexpr pp_type e2 ]
       | PEif (c, t, e) ->
         pp_constructor1
           "PEif"
           [ pp_pexpr pp_type c; pp_pexpr pp_type t; pp_pexpr pp_type e ])
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
    pp_constructor1 "Create" [ pp_pexpr pp_type e; pp_act act; pp_symbol_prefix sym ]
  | CreateReadOnly (e1, act, e2, sym) ->
    pp_constructor1
      "CreateReadOnly"
      [ pp_pexpr pp_type e1; pp_act act; pp_pexpr pp_type e2; pp_symbol_prefix sym ]
  | Alloc (e1, e2, sym) ->
    pp_constructor1
      "Alloc"
      [ pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_symbol_prefix sym ]
  | Kill (kind, e) -> pp_constructor1 "Kill" [ pp_kill_kind kind; pp_pexpr pp_type e ]
  | Store (b, act, e1, e2, mo) ->
    pp_constructor1
      "Store"
      [ pp_bool b;
        pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_memory_order mo
      ]
  | Load (act, e, mo) ->
    pp_constructor1 "Load" [ pp_act act; pp_pexpr pp_type e; pp_memory_order mo ]
  | RMW (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor1
      "RMW"
      [ pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | Fence mo -> pp_constructor1 "Fence" [ pp_memory_order mo ]
  | CompareExchangeStrong (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor1
      "CompareExchangeStrong"
      [ pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | CompareExchangeWeak (act, e1, e2, e3, mo1, mo2) ->
    pp_constructor1
      "CompareExchangeWeak"
      [ pp_act act;
        pp_pexpr pp_type e1;
        pp_pexpr pp_type e2;
        pp_pexpr pp_type e3;
        pp_memory_order mo1;
        pp_memory_order mo2
      ]
  | LinuxFence lmo -> pp_constructor1 "LinuxFence" [ pp_linux_memory_order lmo ]
  | LinuxLoad (act, e, lmo) ->
    pp_constructor1
      "LinuxLoad"
      [ pp_act act; pp_pexpr pp_type e; pp_linux_memory_order lmo ]
  | LinuxStore (act, e1, e2, lmo) ->
    pp_constructor1
      "LinuxStore"
      [ pp_act act; pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_linux_memory_order lmo ]
  | LinuxRMW (act, e1, e2, lmo) ->
    pp_constructor1
      "LinuxRMW"
      [ pp_act act; pp_pexpr pp_type e1; pp_pexpr pp_type e2; pp_linux_memory_order lmo ]


and pp_act { loc; annot; ct } =
  pp_record
    [ ("MuCore.loc", pp_location loc);
      ("MuCore.annot", pp_list pp_annot_t annot);
      ("MuCore.ct", pp_sctype ct)
    ]


and pp_kill_kind = function
  | Dynamic -> pp_constructor0 "Dynamic"
  | Static ct -> pp_constructor "Static" [ pp_sctype ct ]


and pp_value pp_type (V (ty, v)) =
  pp_constructor1
    "V"
    [ pp_type ty;
      (match v with
       | Vobject ov -> pp_constructor1 "Vobject" [ pp_object_value pp_type ov ]
       | Vctype t -> pp_constructor1 "Vctype" [ pp_ctype t ]
       | Vfunction_addr s -> pp_constructor1 "Vfunction_addr" [ pp_symbol s ]
       | Vunit -> pp_constructor1 "Vunit" []
       | Vtrue -> pp_constructor1 "Vtrue" []
       | Vfalse -> pp_constructor1 "Vfalse" []
       | Vlist (bt, vs) ->
         pp_constructor1 "Vlist" [ pp_core_base_type bt; pp_list (pp_value pp_type) vs ]
       | Vtuple vs -> pp_constructor1 "Vtuple" [ pp_list (pp_value pp_type) vs ])
    ]


and pp_object_value pp_type (OV (ty, ov)) =
  pp_constructor1
    "OV"
    [ pp_type ty;
      (match ov with
       | OVinteger i ->
         pp_constructor1 "OVinteger" [ Impl_mem.pp_integer_value_for_coq i ]
       | OVfloating f -> pp_constructor1 "OVfloating" [ pp_floating_value f ]
       | OVpointer p ->
         pp_constructor1 "OVpointer" [ Impl_mem.pp_pointer_value_for_coq pp_symbol p ]
       | OVarray vs -> pp_constructor1 "OVarray" [ pp_list (pp_object_value pp_type) vs ]
       | OVstruct (sym, fields) ->
         pp_constructor1
           "OVstruct"
           [ pp_symbol sym;
             pp_list (pp_triple pp_identifier pp_sctype pp_mem_value) fields
           ]
       | OVunion (sym, id, v) ->
         pp_constructor1 "OVunion" [ pp_symbol sym; pp_identifier id; pp_mem_value v ])
    ]


let pp_location_info = pp_pair pp_location (pp_option pp_string)

let pp_trusted = function
  | Trusted loc -> pp_constructor "Trusted" [ pp_location loc ]
  | Checked -> pp_constructor0 "Checked"


let pp_unop = function
  | Terms.Not -> pp_constructor0 "Not"
  | Negate -> pp_constructor0 "Negate"
  | BW_CLZ_NoSMT -> pp_constructor0 "BW_CLZ_NoSMT"
  | BW_CTZ_NoSMT -> pp_constructor0 "BW_CTZ_NoSMT"
  | BW_FFS_NoSMT -> pp_constructor0 "BW_FFS_NoSMT"
  | BW_FLS_NoSMT -> pp_constructor0 "BW_FLS_NoSMT"
  | BW_Compl -> pp_constructor0 "BW_Compl"


let rec pp_terms_pattern (Terms.Pat (pat, bt, loc)) =
  pp_constructor1 "Pat" [ pp_terms_pattern_ pat; pp_basetype pp_unit bt; pp_location loc ]


and pp_terms_pattern_ = function
  | Terms.PSym s -> pp_constructor1 "PSym" [ pp_symbol s ]
  | Terms.PWild -> pp_constructor1 "PWild" []
  | Terms.PConstructor (sym, args) ->
    pp_constructor1
      "PConstructor"
      [ pp_symbol sym; pp_list (pp_pair pp_identifier pp_terms_pattern) args ]


let pp_const = function
  | Terms.Z z -> pp_constructor "Terms.Z" [ pp_Z z ]
  | Terms.Bits (x, z) ->
    pp_constructor "Terms.Bits" [ pp_pair (pp_pair pp_sign pp_nat) pp_Z (x, z) ]
  | Terms.Q q -> pp_constructor "Terms.Q" [ pp_Q q ]
  | Terms.MemByte { alloc_id; value } ->
    pp_constructor "Terms.MemByte" [ pp_Z alloc_id; pp_Z value ]
  | Terms.Pointer { alloc_id; addr } ->
    pp_constructor "Terms.Pointer" [ pp_Z alloc_id; pp_Z addr ]
  | Terms.Alloc_id z -> pp_constructor "Terms.Alloc_id" [ pp_Z z ]
  | Terms.Bool b -> pp_constructor "Terms.Bool" [ pp_bool b ]
  | Terms.Unit -> pp_constructor0 "Terms.Unit"
  | Terms.Null -> pp_constructor0 "Terms.Null"
  | Terms.CType_const t -> pp_constructor "Terms.CType_const" [ pp_sctype t ]
  | Terms.Default bt -> pp_constructor "Terms.Default" [ pp_basetype pp_unit bt ]


let rec pp_index_term (IndexTerms.IT (term, bt, loc)) =
  pp_constructor1
    "IT"
    [ pp_index_term_content term; pp_basetype pp_unit bt; pp_location loc ]


and pp_index_term_content = function
  | IndexTerms.Const c -> pp_constructor1 "Const" [ pp_const c ]
  | Sym s -> pp_constructor1 "Sym" [ pp_symbol s ]
  | Unop (op, t) -> pp_constructor1 "Unop" [ pp_unop op; pp_index_term t ]
  | Binop (op, t1, t2) ->
    pp_constructor1 "Binop" [ pp_binop op; pp_index_term t1; pp_index_term t2 ]
  | ITE (c, t, e) ->
    pp_constructor1 "ITE" [ pp_index_term c; pp_index_term t; pp_index_term e ]
  | EachI ((n1, (sym, bt), n2), t) ->
    pp_constructor1
      "EachI"
      [ pp_tuple
          [ pp_nat n1; pp_pair pp_symbol (pp_basetype pp_unit) (sym, bt); pp_nat n2 ];
        pp_index_term t
      ]
  | Tuple ts -> pp_constructor1 "Tuple" [ pp_list pp_index_term ts ]
  | NthTuple (n, t) -> pp_constructor1 "NthTuple" [ pp_nat n; pp_index_term t ]
  | Struct (tag, members) ->
    pp_constructor1
      "Struct"
      [ pp_symbol tag; pp_list (pp_pair pp_identifier pp_index_term) members ]
  | StructMember (t, member) ->
    pp_constructor1 "StructMember" [ pp_index_term t; pp_identifier member ]
  | StructUpdate ((t1, member), t2) ->
    pp_constructor1
      "StructUpdate"
      [ pp_index_term t1; pp_identifier member; pp_index_term t2 ]
  | Record members ->
    pp_constructor1 "TRecord" [ pp_list (pp_pair pp_identifier pp_index_term) members ]
  | RecordMember (t, member) ->
    pp_constructor1 "RecordMember" [ pp_index_term t; pp_identifier member ]
  | RecordUpdate ((t1, member), t2) ->
    pp_constructor1
      "RecordUpdate"
      [ pp_index_term t1; pp_identifier member; pp_index_term t2 ]
  | Constructor (sym, args) ->
    pp_constructor1
      "Constructor"
      [ pp_symbol sym; pp_list (pp_pair pp_identifier pp_index_term) args ]
  | MemberShift (t, tag, id) ->
    pp_constructor1 "MemberShift" [ pp_index_term t; pp_symbol tag; pp_identifier id ]
  | ArrayShift { base; ct; index } ->
    pp_constructor1 "ArrayShift" [ pp_index_term base; pp_sctype ct; pp_index_term index ]
  | CopyAllocId { addr; loc } ->
    pp_constructor1 "CopyAllocId" [ pp_index_term addr; pp_index_term loc ]
  | HasAllocId t -> pp_constructor1 "HasAllocId" [ pp_index_term t ]
  | SizeOf ct -> pp_constructor1 "SizeOf" [ pp_sctype ct ]
  | OffsetOf (tag, member) ->
    pp_constructor1 "OffsetOf" [ pp_symbol tag; pp_identifier member ]
  | Nil bt -> pp_constructor1 "Nil" [ pp_basetype pp_unit bt ]
  | Cons (t1, t2) -> pp_constructor1 "Cons" [ pp_index_term t1; pp_index_term t2 ]
  | Head t -> pp_constructor1 "Head" [ pp_index_term t ]
  | Tail t -> pp_constructor1 "Tail" [ pp_index_term t ]
  | NthList (i, xs, d) ->
    pp_constructor1 "NthList" [ pp_index_term i; pp_index_term xs; pp_index_term d ]
  | ArrayToList (arr, i, len) ->
    pp_constructor1
      "ArrayToList"
      [ pp_index_term arr; pp_index_term i; pp_index_term len ]
  | Representable (ct, t) ->
    pp_constructor1 "Representable" [ pp_sctype ct; pp_index_term t ]
  | Good (ct, t) -> pp_constructor1 "Good" [ pp_sctype ct; pp_index_term t ]
  | Aligned { t; align } ->
    pp_constructor1 "Aligned" [ pp_index_term t; pp_index_term align ]
  | WrapI (ct, t) -> pp_constructor1 "WrapI" [ pp_integer_type ct; pp_index_term t ]
  | MapConst (bt, t) ->
    pp_constructor1 "MapConst" [ pp_basetype pp_unit bt; pp_index_term t ]
  | MapSet (m, k, v) ->
    pp_constructor1 "MapSet" [ pp_index_term m; pp_index_term k; pp_index_term v ]
  | MapGet (m, k) -> pp_constructor1 "MapGet" [ pp_index_term m; pp_index_term k ]
  | MapDef ((sym, bt), t) ->
    pp_constructor1
      "MapDef"
      [ pp_pair pp_symbol (pp_basetype pp_unit) (sym, bt); pp_index_term t ]
  | Apply (sym, args) ->
    pp_constructor1 "Apply" [ pp_symbol sym; pp_list pp_index_term args ]
  | Let ((sym, t1), t2) ->
    pp_constructor1 "TLet" [ pp_pair pp_symbol pp_index_term (sym, t1); pp_index_term t2 ]
  | Match (t, cases) ->
    pp_constructor1
      "TMatch"
      [ pp_index_term t; pp_list (pp_pair pp_terms_pattern pp_index_term) cases ]
  | Cast (bt, t) -> pp_constructor1 "Cast" [ pp_basetype pp_unit bt; pp_index_term t ]


let pp_request_init = function
  | Request.Init -> pp_constructor0 "Init"
  | Request.Uninit -> pp_constructor0 "Uninit"


let rec pp_request = function
  | Request.P pred -> pp_constructor "Request.P" [ pp_request_ppredicate pred ]
  | Request.Q qpred -> pp_constructor "Request.Q" [ pp_request_qpredicate qpred ]


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
  | PtrEq e12 -> pp_constructor1 "MuCore.PtrEq" [ pp_pair pte pte e12 ]
  | PtrNe e12 -> pp_constructor1 "MuCore.PtrNe" [ pp_pair pte pte e12 ]
  | PtrLt e12 -> pp_constructor1 "MuCore.PtrLt" [ pp_pair pte pte e12 ]
  | PtrGt e12 -> pp_constructor1 "MuCore.PtrGt" [ pp_pair pte pte e12 ]
  | PtrLe e12 -> pp_constructor1 "MuCore.PtrLe" [ pp_pair pte pte e12 ]
  | PtrGe e12 -> pp_constructor1 "MuCore.PtrGe" [ pp_pair pte pte e12 ]
  | Ptrdiff e123 -> pp_constructor1 "MuCore.Ptrdiff" [ pp_triple pp_act pte pte e123 ]
  | IntFromPtr e123 ->
    pp_constructor1 "MuCore.IntFromPtr" [ pp_triple pp_act pp_act pte e123 ]
  | PtrFromInt e123 ->
    pp_constructor1 "MuCore.PtrFromInt" [ pp_triple pp_act pp_act pte e123 ]
  | PtrValidForDeref e12 ->
    pp_constructor1 "MuCore.PtrValidForDeref" [ pp_pair pp_act pte e12 ]
  | PtrWellAligned e12 ->
    pp_constructor1 "MuCore.PtrWellAligned" [ pp_pair pp_act pte e12 ]
  | PtrArrayShift e123 ->
    pp_constructor1 "MuCore.PtrArrayShift" [ pp_triple pte pp_act pte e123 ]
  | PtrMemberShift e123 ->
    pp_constructor1 "MuCore.PtrMemberShift" [ pp_triple pp_symbol pp_identifier pte e123 ]
  | Memcpy e123 -> pp_constructor1 "MuCore.Memcpy" [ pp_triple pte pte pte e123 ]
  | Memcmp e123 -> pp_constructor1 "MuCore.Memcmp" [ pp_triple pte pte pte e123 ]
  | Realloc e123 -> pp_constructor1 "MuCore.Realloc" [ pp_triple pte pte pte e123 ]
  | Va_start e12 -> pp_constructor1 "MuCore.Va_start" [ pp_pair pte pte e12 ]
  | Va_copy e -> pp_constructor1 "MuCore.Va_copy" [ pte e ]
  | Va_arg e12 -> pp_constructor1 "MuCore.Va_arg" [ pp_pair pte pp_act e12 ]
  | Va_end e -> pp_constructor1 "MuCore.Va_end" [ pte e ]
  | CopyAllocId e12 -> pp_constructor1 "MuCore.CopyAllocId" [ pp_pair pte pte e12 ]


let pp_pack_unpack = function
  | CF.Cn.Pack -> pp_constructor0 "Pack"
  | CF.Cn.Unpack -> pp_constructor0 "Unpack"


let pp_to_from = function
  | CF.Cn.To -> pp_constructor0 "To"
  | CF.Cn.From -> pp_constructor0 "From"


let pp_cn_to_instantiate ppfa ppfty = function
  | CF.Cn.I_Function f -> pp_constructor2 "I_Function" [ ppfa f ]
  | CF.Cn.I_Good ty -> pp_constructor2 "I_Good" [ ppfty ty ]
  | CF.Cn.I_Everything -> pp_constructor2 "I_Everything" []


let pp_logical_constraint = function
  | LogicalConstraints.T term ->
    pp_constructor "LogicalConstraints.T" [ pp_index_term term ]
  | LogicalConstraints.Forall ((sym, bt), term) ->
    pp_constructor
      "LogicalConstraints.Forall"
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
  | LogicalReturnTypes.I -> pp_constructor0 "LogicalReturnTypes.I"


let rec pp_logical_args ppf = function
  | Define (st, info, rest) ->
    pp_constructor1
      "MuCore.Define"
      [ pp_tuple
          [ pp_pair pp_symbol pp_index_term st;
            pp_location_info info;
            pp_logical_args ppf rest
          ]
      ]
  | Resource ((sym, rbt), info, rest) ->
    pp_constructor1
      "MuCore.Resource"
      [ pp_tuple
          [ pp_symbol sym;
            pp_pair pp_request (pp_basetype pp_unit) rbt;
            pp_location_info info;
            pp_logical_args ppf rest
          ]
      ]
  | Constraint (lc, info, rest) ->
    pp_constructor1
      "MuCore.Constraint"
      [ pp_tuple
          [ pp_logical_constraint lc; pp_location_info info; pp_logical_args ppf rest ]
      ]
  | I i -> pp_constructor1 "MuCore.I" [ ppf i ]


let rec pp_arguments ppf = function
  | Computational (sbt, loc, rest) ->
    pp_constructor1
      "MuCore.Computational"
      [ pp_tuple
          [ pp_pair pp_symbol (pp_basetype pp_unit) sbt;
            pp_location_info loc;
            pp_arguments ppf rest
          ]
      ]
  | L at -> pp_constructor1 "MuCore.L" [ pp_logical_args ppf at ]


let pp_cn_c_kind = function
  | CF.Cn.C_kind_var -> pp_constructor0 "C_kind_var"
  | C_kind_enum -> pp_constructor0 "C_kind_enum"


let pp_cn_sign = function
  | CF.Cn.CN_unsigned -> pp_constructor0 "CN_unsigned"
  | CN_signed -> pp_constructor0 "CN_signed"


let rec pp_cn_basetype ppfa = function
  | CF.Cn.CN_unit -> pp_constructor1 "CN_unit" []
  | CN_bool -> pp_constructor1 "CN_bool" []
  | CN_integer -> pp_constructor1 "CN_integer" []
  | CN_bits (sign, sz) ->
    pp_constructor1 "CN_bits" [ pp_pair pp_cn_sign pp_nat (sign, sz) ]
  | CN_real -> pp_constructor1 "CN_real" []
  | CN_loc -> pp_constructor1 "CN_loc" []
  | CN_alloc_id -> pp_constructor1 "CN_alloc_id" []
  | CN_struct a -> pp_constructor1 "CN_struct" [ ppfa a ]
  | CN_record fields ->
    pp_constructor1
      "CN_record"
      [ pp_list (pp_pair pp_identifier (pp_cn_basetype ppfa)) fields ]
  | CN_datatype a -> pp_constructor1 "CN_datatype" [ ppfa a ]
  | CN_map (k, v) ->
    pp_constructor1
      "CN_map"
      [ pp_pair (pp_cn_basetype ppfa) (pp_cn_basetype ppfa) (k, v) ]
  | CN_list t -> pp_constructor1 "CN_list" [ pp_cn_basetype ppfa t ]
  | CN_tuple ts -> pp_constructor1 "CN_tuple" [ pp_list (pp_cn_basetype ppfa) ts ]
  | CN_set t -> pp_constructor1 "CN_set" [ pp_cn_basetype ppfa t ]
  | CN_user_type_name a -> pp_constructor1 "CN_user_type_name" [ ppfa a ]
  | CN_c_typedef_name a -> pp_constructor1 "CN_c_typedef_name" [ ppfa a ]


let pp_cn_const = function
  | CF.Cn.CNConst_NULL -> pp_constructor0 "CNConst_NULL"
  | CNConst_integer n -> pp_constructor "CNConst_integer" [ pp_Z n ]
  | CNConst_bits (sign_sz, n) ->
    pp_constructor
      "CNConst_bits"
      [ pp_pair (pp_pair pp_cn_sign pp_nat) pp_Z (sign_sz, n) ]
  | CNConst_bool b -> pp_constructor "CNConst_bool" [ pp_bool b ]
  | CNConst_unit -> pp_constructor0 "CNConst_unit"


let pp_cn_binop = function
  | CF.Cn.CN_add -> pp_constructor0 "CN_add"
  | CN_sub -> pp_constructor0 "CN_sub"
  | CN_mul -> pp_constructor0 "CN_mul"
  | CN_div -> pp_constructor0 "CN_div"
  | CN_mod -> pp_constructor0 "CN_mod"
  | CN_equal -> pp_constructor0 "CN_equal"
  | CN_inequal -> pp_constructor0 "CN_inequal"
  | CN_lt -> pp_constructor0 "CN_lt"
  | CN_le -> pp_constructor0 "CN_le"
  | CN_gt -> pp_constructor0 "CN_gt"
  | CN_ge -> pp_constructor0 "CN_ge"
  | CN_or -> pp_constructor0 "CN_or"
  | CN_and -> pp_constructor0 "CN_and"
  | CN_implies -> pp_constructor0 "CN_implies"
  | CN_map_get -> pp_constructor0 "CN_map_get"
  | CN_band -> pp_constructor0 "CN_band"
  | CN_bor -> pp_constructor0 "CN_bor"
  | CN_bxor -> pp_constructor0 "CN_bxor"


let rec pp_cn_pat ppfa = function
  | CF.Cn.CNPat (loc, pat) ->
    pp_constructor
      "CNPat"
      [ pp_location loc;
        (match pat with
         | CNPat_sym s -> pp_constructor "CNPat_sym" [ ppfa s ]
         | CNPat_wild -> pp_constructor0 "CNPat_wild"
         | CNPat_constructor (s, args) ->
           pp_constructor
             "CNPat_constructor"
             [ ppfa s; pp_list (pp_pair pp_identifier (pp_cn_pat ppfa)) args ])
      ]


let rec pp_cn_expr ppfa ppfty = function
  | CF.Cn.CNExpr (loc, e) ->
    pp_constructor2
      "CNExpr"
      [ pp_tuple
          [ pp_location loc;
            (match e with
             | CNExpr_const c -> pp_constructor2 "CNExpr_const" [ pp_cn_const c ]
             | CNExpr_var v -> pp_constructor2 "CNExpr_var" [ ppfa v ]
             | CNExpr_list es ->
               pp_constructor2 "CNExpr_list" [ pp_list (pp_cn_expr ppfa ppfty) es ]
             | CNExpr_memberof (e, id) ->
               pp_constructor2
                 "CNExpr_memberof"
                 [ pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id) ]
             | CNExpr_arrow (e, id) ->
               pp_constructor2
                 "CNExpr_arrow"
                 [ pp_pair (pp_cn_expr ppfa ppfty) pp_identifier (e, id) ]
             | CNExpr_record fs ->
               pp_constructor2
                 "CNExpr_record"
                 [ pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)) fs ]
             | CNExpr_struct (id, fs) ->
               pp_constructor2
                 "CNExpr_struct"
                 [ pp_pair
                     ppfa
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (id, fs)
                 ]
             | CNExpr_memberupdates (e, us) ->
               pp_constructor2
                 "CNExpr_memberupdates"
                 [ pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (e, us)
                 ]
             | CNExpr_arrayindexupdates (e, us) ->
               pp_constructor2
                 "CNExpr_arrayindexupdates"
                 [ pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair (pp_cn_expr ppfa ppfty) (pp_cn_expr ppfa ppfty)))
                     (e, us)
                 ]
             | CNExpr_binop (op, e1, e2) ->
               pp_constructor2
                 "CNExpr_binop"
                 [ pp_triple
                     pp_cn_binop
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (op, e1, e2)
                 ]
             | CNExpr_sizeof ty -> pp_constructor2 "CNExpr_sizeof" [ ppfty ty ]
             | CNExpr_offsetof (a, id) ->
               pp_constructor2 "CNExpr_offsetof" [ pp_pair ppfa pp_identifier (a, id) ]
             | CNExpr_membershift (e, oa, id) ->
               pp_constructor2
                 "CNExpr_membershift"
                 [ pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_option ppfa)
                     pp_identifier
                     (e, oa, id)
                 ]
             | CNExpr_addr a -> pp_constructor2 "CNExpr_addr" [ ppfa a ]
             | CNExpr_cast (bt, e) ->
               pp_constructor2
                 "CNExpr_cast"
                 [ pp_pair (pp_cn_basetype ppfa) (pp_cn_expr ppfa ppfty) (bt, e) ]
             | CNExpr_array_shift (e, ty, idx) ->
               pp_constructor2
                 "CNExpr_array_shift"
                 [ pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_option ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (e, ty, idx)
                 ]
             | CNExpr_call (f, args) ->
               pp_constructor2
                 "CNExpr_call"
                 [ pp_pair ppfa (pp_list (pp_cn_expr ppfa ppfty)) (f, args) ]
             | CNExpr_cons (id, e) ->
               pp_constructor2
                 "CNExpr_cons"
                 [ pp_pair
                     ppfa
                     (pp_list (pp_pair pp_identifier (pp_cn_expr ppfa ppfty)))
                     (id, e)
                 ]
             | CNExpr_each (a, bt, n12, e) ->
               pp_constructor2
                 "CNExpr_each"
                 [ pp_tuple
                     [ ppfa a;
                       pp_cn_basetype ppfa bt;
                       pp_pair pp_Z pp_Z n12;
                       pp_cn_expr ppfa ppfty e
                     ]
                 ]
             | CNExpr_let (a, e1, e2) ->
               pp_constructor2
                 "CNExpr_let"
                 [ pp_triple
                     ppfa
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (a, e1, e2)
                 ]
             | CNExpr_match (e, cases) ->
               pp_constructor2
                 "CNExpr_match"
                 [ pp_pair
                     (pp_cn_expr ppfa ppfty)
                     (pp_list (pp_pair (pp_cn_pat ppfa) (pp_cn_expr ppfa ppfty)))
                     (e, cases)
                 ]
             | CNExpr_ite (c, t, e) ->
               pp_constructor2
                 "CNExpr_ite"
                 [ pp_triple
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (pp_cn_expr ppfa ppfty)
                     (c, t, e)
                 ]
             | CNExpr_good (ty, e) ->
               pp_constructor2
                 "CNExpr_good"
                 [ pp_pair ppfty (pp_cn_expr ppfa ppfty) (ty, e) ]
             | CNExpr_deref e ->
               pp_constructor2 "CNExpr_deref" [ pp_cn_expr ppfa ppfty e ]
             | CNExpr_value_of_c_atom (a, k) ->
               pp_constructor2
                 "CNExpr_value_of_c_atom"
                 [ pp_pair ppfa pp_cn_c_kind (a, k) ]
             | CNExpr_unchanged e ->
               pp_constructor2 "CNExpr_unchanged" [ pp_cn_expr ppfa ppfty e ]
             | CNExpr_at_env (e, s) ->
               pp_constructor2
                 "CNExpr_at_env"
                 [ pp_pair (pp_cn_expr ppfa ppfty) pp_string (e, s) ]
             | CNExpr_not e -> pp_constructor2 "CNExpr_not" [ pp_cn_expr ppfa ppfty e ]
             | CNExpr_negate e ->
               pp_constructor2 "CNExpr_negate" [ pp_cn_expr ppfa ppfty e ]
             | CNExpr_default bt ->
               pp_constructor2 "CNExpr_default" [ pp_cn_basetype ppfa bt ]
             | CNExpr_bnot e -> pp_constructor2 "CNExpr_bnot" [ pp_cn_expr ppfa ppfty e ])
          ]
      ]


let rec pp_cn_resource ppfa ppfty = function
  | CF.Cn.CN_pred (loc, pred, args) ->
    pp_constructor2
      "CN_pred"
      [ pp_location loc;
        pp_cn_pred ppfa ppfty pred;
        pp_list (pp_cn_expr ppfa ppfty) args
      ]
  | CN_each (a, bt, e, loc, pred, args) ->
    pp_constructor2
      "CN_each"
      [ ppfa a;
        pp_cn_basetype ppfa bt;
        pp_cn_expr ppfa ppfty e;
        pp_location loc;
        pp_cn_pred ppfa ppfty pred;
        pp_list (pp_cn_expr ppfa ppfty) args
      ]


and pp_cn_pred ppfa ppfty = function
  | CF.Cn.CN_owned ty -> pp_constructor2 "CN_owned" [ pp_option ppfty ty ]
  | CN_block ty -> pp_constructor2 "CN_block" [ pp_option ppfty ty ]
  | CN_named a -> pp_constructor2 "CN_named" [ ppfa a ]


let pp_cn_to_extract ppfa ppfty = function
  | CF.Cn.E_Pred pred -> pp_constructor2 "E_Pred" [ pp_cn_pred ppfa ppfty pred ]
  | CF.Cn.E_Everything -> pp_constructor2 "E_Everything" []


let pp_cn_assertion ppfa ppfty = function
  | CF.Cn.CN_assert_exp ex -> pp_constructor2 "CN_assert_exp" [ pp_cn_expr ppfa ppfty ex ]
  | CN_assert_qexp (sym, bt, it1, it2) ->
    pp_constructor2
      "CN_assert_qexp"
      [ ppfa sym;
        pp_cn_basetype ppfa bt;
        pp_cn_expr ppfa ppfty it1;
        pp_cn_expr ppfa ppfty it2
      ]


let pp_cn_condition ppfa ppfty = function
  | CF.Cn.CN_cletResource (loc, sym, res) ->
    pp_constructor2
      "CN_cletResource"
      [ pp_location loc; ppfa sym; pp_cn_resource ppfa ppfty res ]
  | CN_cletExpr (loc, sym, ex) ->
    pp_constructor2 "CN_cletExpr" [ pp_location loc; ppfa sym; pp_cn_expr ppfa ppfty ex ]
  | CN_cconstr (loc, assertion) ->
    pp_constructor2 "CN_cconstr" [ pp_location loc; pp_cn_assertion ppfa ppfty assertion ]


let pp_cnprogs_extract (ids, extract, term) =
  pp_tuple
    [ pp_list pp_identifier ids;
      pp_cn_to_extract pp_symbol pp_sctype extract;
      pp_index_term term
    ]


let pp_cnprog_statement = function
  | Cnprog.Pack_unpack (pu, pred) ->
    pp_constructor "CNProgs.Pack_unpack" [ pp_pack_unpack pu; pp_request_ppredicate pred ]
  | To_from_bytes (tf, pred) ->
    pp_constructor "CNProgs.To_from_bytes" [ pp_to_from tf; pp_request_ppredicate pred ]
  | Have lc -> pp_constructor "CNProgs.Have" [ pp_logical_constraint lc ]
  | Instantiate (inst, term) ->
    pp_constructor
      "CNProgs.Instantiate"
      [ pp_cn_to_instantiate pp_symbol pp_sctype inst; pp_index_term term ]
  | Split_case lc -> pp_constructor "CNProgs.Split_case" [ pp_logical_constraint lc ]
  | Extract extract -> pp_constructor "CNProgs.Extract" [ pp_cnprogs_extract extract ]
  | Unfold (sym, terms) ->
    pp_constructor "CNProgs.Unfold" [ pp_symbol sym; pp_list pp_index_term terms ]
  | Apply (sym, terms) ->
    pp_constructor "CNProgs.Apply" [ pp_symbol sym; pp_list pp_index_term terms ]
  | Assert lc -> pp_constructor "CNProgs.Assert" [ pp_logical_constraint lc ]
  | Inline syms -> pp_constructor "CNProgs.Inline" [ pp_list pp_symbol syms ]
  | Print term -> pp_constructor "CNProgs.Print" [ pp_index_term term ]


let pp_cnprog_load (r : Cnprog.load) =
  pp_record
    [ ("CNProgs.ct", pp_sctype r.ct); ("CNProgs.pointer", pp_index_term r.pointer) ]


let rec pp_cn_prog = function
  | Cnprog.Let (loc, (name, l), prog) ->
    pp_constructor
      "CNProgs.CLet"
      [ pp_location loc; pp_tuple [ pp_symbol name; pp_cnprog_load l ]; pp_cn_prog prog ]
  | Statement (loc, stmt) ->
    pp_constructor "CNProgs.Statement" [ pp_location loc; pp_cnprog_statement stmt ]


let rec pp_cn_statement ppfa ppfty (CF.Cn.CN_statement (loc, stmt)) =
  pp_constructor2
    "CN_statement"
    [ pp_location loc;
      (match stmt with
       | CN_pack_unpack (pu, pred, exprs) ->
         pp_constructor2
           "CN_pack_unpack"
           [ pp_tuple
               [ pp_pack_unpack pu;
                 pp_cn_pred ppfa ppfty pred;
                 pp_list (pp_cn_expr ppfa ppfty) exprs
               ]
           ]
       | CN_to_from_bytes (tf, pred, exprs) ->
         pp_constructor2
           "CN_to_from_bytes"
           [ pp_tuple
               [ pp_to_from tf;
                 pp_cn_pred ppfa ppfty pred;
                 pp_list (pp_cn_expr ppfa ppfty) exprs
               ]
           ]
       | CN_have assertion ->
         pp_constructor2 "CN_have" [ pp_cn_assertion ppfa ppfty assertion ]
       | CN_instantiate (inst, expr) ->
         pp_constructor2
           "CN_instantiate"
           [ pp_tuple [ pp_cn_to_instantiate ppfa ppfty inst; pp_cn_expr ppfa ppfty expr ]
           ]
       | CN_split_case assertion ->
         pp_constructor2 "CN_split_case" [ pp_cn_assertion ppfa ppfty assertion ]
       | CN_extract (ids, extract, expr) ->
         pp_constructor2
           "CN_extract"
           [ pp_tuple
               [ pp_list pp_identifier ids;
                 pp_cn_to_extract ppfa ppfty extract;
                 pp_cn_expr ppfa ppfty expr
               ]
           ]
       | CN_unfold (sym, exprs) ->
         pp_constructor2
           "CN_unfold"
           [ pp_tuple [ ppfa sym; pp_list (pp_cn_expr ppfa ppfty) exprs ] ]
       | CN_assert_stmt assertion ->
         pp_constructor2 "CN_assert_stmt" [ pp_cn_assertion ppfa ppfty assertion ]
       | CN_apply (sym, exprs) ->
         pp_constructor2
           "CN_apply"
           [ pp_tuple [ ppfa sym; pp_list (pp_cn_expr ppfa ppfty) exprs ] ]
       | CN_inline syms -> pp_constructor2 "CN_inline" [ pp_list ppfa syms ]
       | CN_print expr -> pp_constructor2 "CN_print" [ pp_cn_expr ppfa ppfty expr ])
    ]


and pp_expr pp_type = function
  | Expr (loc, annots, ty, e) ->
    pp_constructor1
      "Expr"
      [ pp_location loc;
        pp_list pp_annot_t annots;
        pp_type ty;
        (match e with
         | Epure pe -> pp_constructor1 "Epure" [ pp_pexpr pp_type pe ]
         | Ememop m -> pp_constructor1 "Ememop" [ pp_memop pp_type m ]
         | Eaction pa -> pp_constructor1 "Eaction" [ pp_paction pp_type pa ]
         | Eskip -> pp_constructor1 "Eskip" []
         | Eccall (act, f, args) ->
           pp_constructor1
             "Eccall"
             [ pp_tuple
                 [ pp_act act; pp_pexpr pp_type f; pp_list (pp_pexpr pp_type) args ]
             ]
         | Elet (pat, e1, e2) ->
           pp_constructor1
             "Elet"
             [ pp_tuple
                 [ pp_pattern pp_type pat; pp_pexpr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Eunseq exprs -> pp_constructor1 "Eunseq" [ pp_list (pp_expr pp_type) exprs ]
         | Ewseq (pat, e1, e2) ->
           pp_constructor1
             "Ewseq"
             [ pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Esseq (pat, e1, e2) ->
           pp_constructor1
             "Esseq"
             [ pp_tuple [ pp_pattern pp_type pat; pp_expr pp_type e1; pp_expr pp_type e2 ]
             ]
         | Eif (c, t, e) ->
           pp_constructor1
             "Eif"
             [ pp_tuple [ pp_pexpr pp_type c; pp_expr pp_type t; pp_expr pp_type e ] ]
         | Ebound e -> pp_constructor1 "Ebound" [ pp_expr pp_type e ]
         | End exprs -> pp_constructor1 "End" [ pp_list (pp_expr pp_type) exprs ]
         | Erun (sym, args) ->
           pp_constructor1
             "Erun"
             [ pp_tuple [ pp_symbol sym; pp_list (pp_pexpr pp_type) args ] ]
         | CN_progs (stmts, progs) ->
           pp_constructor1
             "CN_progs"
             [ pp_tuple
                 [ pp_list (pp_cn_statement pp_symbol pp_ctype) stmts;
                   pp_list pp_cn_prog progs
                 ]
             ])
      ]


let pp_parse_ast_label_spec (s : parse_ast_label_spec) =
  pp_record [ ("label_spec", pp_list (pp_cn_condition pp_symbol pp_ctype) s.label_spec) ]


let pp_label_def pp_type = function
  | Return loc -> pp_constructor1 "Return" [ pp_location loc ]
  | Label (loc, args, annots, spec, `Loop (cond_loc, loop_loc, _)) ->
    pp_constructor1
      "Label"
      [ pp_location loc;
        pp_arguments (pp_expr pp_type) args;
        pp_list pp_annot_t annots;
        pp_parse_ast_label_spec spec;
        pp_pair pp_location pp_location (cond_loc, loop_loc)
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
  | LogicalArgumentTypes.I i -> pp_constructor1 "LogicalArgumentTypes.I" [ pp_type i ]
  | Resource ((sym, (req, bt)), info, at) ->
    pp_constructor1
      "LogicalArgumentTypes.Resource"
      [ pp_tuple [ pp_symbol sym; pp_tuple [ pp_request req; pp_basetype pp_unit bt ] ];
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]
  | Constraint (lc, info, at) ->
    pp_constructor1
      "LogicalArgumentTypes.Constraint"
      [ pp_logical_constraint lc;
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]
  | LogicalArgumentTypes.Define (si, info, at) ->
    pp_constructor1
      "LogicalArgumentTypes.Define"
      [ pp_pair pp_symbol pp_index_term si;
        pp_location_info info;
        pp_logical_argument_types pp_type at
      ]


let rec pp_argument_types pp_type = function
  | ArgumentTypes.Computational (sbt, info, at) ->
    pp_constructor1
      "ArgumentTypes.Computational"
      [ pp_pair pp_symbol (pp_basetype pp_unit) sbt;
        pp_location_info info;
        pp_argument_types pp_type at
      ]
  | L at -> pp_constructor1 "ArgumentTypes.L" [ pp_logical_argument_types pp_type at ]


let coq_prologue =
  pp_lines
    [ "Require Import Coq.Lists.List.";
      "Import ListNotations.";
      "Require Import Coq.Strings.String.";
      "Open Scope string_scope.";
      "Require Import ZArith.";
      "From Cerberus Require Import Annot Core Ctype ImplMem IntegerType Location Memory \
       Symbol Undefined Utils.";
      "From Cn Require Import ArgumentTypes BaseTypes CN CNProgs ErrorCommon False Id \
       IndexTerms Locations LogicalArgumentTypes LogicalConstraints LogicalReturnTypes \
       MuCore Prooflog Request ReturnTypes Resource SCtypes Sym Terms."
    ]


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
             (pp_constructor1 "GlobalDef" [ pp_sctype ct; pp_expr pp_type e ])
           ^^ P.hardline
         | GlobalDecl ct ->
           coq_def
             (Pp_symbol.to_string sym)
             P.empty
             (pp_constructor1 "GlobalDecl" [ pp_sctype ct ])
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


(* Functions to pretty print the Explain.log types *)

let pp_access = function
  | Error_common.Load -> pp_constructor "ErrorCommon.Load" []
  | Error_common.Store -> pp_constructor "ErrorCommon.Store" []
  | Error_common.Deref -> pp_constructor "ErrorCommon.Deref" []
  | Error_common.Kill -> pp_constructor "ErrorCommon.Kill" []
  | Error_common.Free -> pp_constructor "ErrorCommon.Free" []
  | Error_common.To_bytes -> pp_constructor "ErrorCommon.To_bytes" []
  | Error_common.From_bytes -> pp_constructor "ErrorCommon.From_bytes" []


let pp_call_situation = function
  | Error_common.FunctionCall s ->
    pp_constructor "ErrorCommon.FunctionCall" [ pp_symbol s ]
  | Error_common.LemmaApplication s ->
    pp_constructor "ErrorCommon.LemmaApplication" [ pp_symbol s ]
  | Error_common.LabelCall l ->
    pp_constructor "ErrorCommon.LabelCall" [ pp_label_annot l ]
  | Error_common.Subtyping -> pp_constructor "ErrorCommon.Subtyping" []


let pp_situation (s : Error_common.situation) =
  match s with
  | Error_common.Access a -> pp_constructor "ErrorCommon.Access" [ pp_access a ]
  | Error_common.Call c -> pp_constructor "ErrorCommon.Call" [ pp_call_situation c ]


let pp_init = function
  | Request.Init -> pp_constructor "Init" []
  | Request.Uninit -> pp_constructor "Uninit" []


let pp_request_name = function
  | Request.Owned (ct, init) ->
    pp_constructor "Request.Owned" [ pp_sctype ct; pp_init init ]
  | Request.PName s -> pp_constructor "Request.PName" [ pp_symbol s ]


let pp_predicate (p : Request.Predicate.t) =
  pp_record
    [ ("Request.Predicate.name", pp_request_name p.name);
      ("Request.Predicate.pointer", pp_index_term p.pointer);
      ("Request.Predicate.iargs", pp_list pp_index_term p.iargs)
    ]


let pp_sym_map (pp_value : 'a -> P.document) (m : 'a Sym.Map.t) =
  P.parens
    (!^"Sym.map_from_list" ^^^ pp_list (pp_pair pp_symbol pp_value) (Sym.Map.bindings m))


let pp_basetype_or_value = function
  | Context.BaseType bt -> pp_constructor "Context.BaseType" [ pp_basetype pp_unit bt ]
  | Context.Value v -> pp_constructor "Context.Value" [ pp_index_term v ]


let pp_output (o : Resource.output) =
  match o with Resource.O i -> pp_constructor "Resource.O" [ pp_index_term i ]


let pp_resource_predicate (p : Resource.predicate) = pp_pair pp_predicate pp_output p

let pp_lazy_document_as_string (x : P.document Lazy.t) = !^"\"" ^^ Lazy.force x ^^ !^"\""

let pp_context_l_info (x : Context.l_info) =
  pp_pair pp_location pp_lazy_document_as_string x


let pp_resource (r : Resource.t) = pp_pair pp_request pp_output r

let pp_struct_piece (p : Memory.struct_piece) =
  pp_record
    [ ("Cn.Memory.piece_offset", pp_int p.offset);
      ("Cn.Memory.piece_size", pp_int p.size);
      ( "Cn.Memory.piece_member_or_padding",
        pp_option (pp_pair pp_identifier pp_sctype) p.member_or_padding )
    ]


let pp_struct_layout (l : Memory.struct_layout) = pp_list pp_struct_piece l

let pp_struct_decls (s : Memory.struct_decls) = pp_sym_map pp_struct_layout s

let pp_member_types_gen (mt : unit BaseTypes.member_types_gen) =
  pp_list (pp_pair pp_identifier (pp_basetype pp_unit)) mt


let pp_basetype_dt_info (dt : BaseTypes.dt_info) =
  pp_record
    [ ("BaseTypes.Datatype.constrs", pp_list pp_symbol dt.constrs);
      ("BaseTypes.Datatype.all_params", pp_member_types_gen dt.all_params)
    ]


let pp_basetype_constr_info (ci : BaseTypes.constr_info) =
  pp_record
    [ ("BaseTypes.Datatype.params", pp_member_types_gen ci.params);
      ("BaseTypes.Datatype.datatype_tag", pp_symbol ci.datatype_tag)
    ]


let pp_argument_types_ft (ft : ArgumentTypes.ft) = pp_argument_types pp_return_type ft

let pp_c_concrete_sig (c : Sctypes.c_concrete_sig) =
  pp_record
    [ ("SCtypes.sig_return_ty", pp_ctype c.sig_return_ty);
      ("SCtypes.sig_arg_tys", pp_list pp_ctype c.sig_arg_tys);
      ("SCtypes.sig_variadic", pp_bool c.sig_variadic);
      ("SCtypes.sig_has_proto", pp_bool c.sig_has_proto)
    ]


let pp_clause (c : Definition.Clause.t) =
  pp_record
    [ ("CNDefinition.clause_loc", pp_location c.loc);
      ("CNDefinition.clause_guard", pp_index_term c.guard);
      ( "CNDefinition.clause_packing_ft",
        pp_logical_argument_types pp_index_term c.packing_ft )
    ]


let pp_definition_predicate (p : Definition.Predicate.t) =
  pp_record
    [ ("CNDefinition.def_predicate_loc", pp_location p.loc);
      ("CNDefinition.def_predicate_pointer", pp_symbol p.pointer);
      ( "CNDefinition.def_predicate_iargs",
        pp_list (pp_pair pp_symbol (pp_basetype pp_unit)) p.iargs );
      ("CNDefinition.def_predicate_oarg_bt", pp_basetype pp_unit p.oarg_bt);
      ("CNDefinition.def_predicate_clauses", pp_option (pp_list pp_clause) p.clauses)
    ]


let pp_definition_function_body (b : Definition.Function.body) =
  match b with
  | Def i -> pp_constructor "CNDefinition.Function.Def" [ pp_index_term i ]
  | Rec_Def i -> pp_constructor "CNDefinition.Function.Rec_Def" [ pp_index_term i ]
  | Uninterp -> pp_constructor "CNDefinition.Function.Uninterp" []


let pp_definition_function (f : Definition.Function.t) =
  pp_record
    [ ("CNDefinition.Function.def_function_loc", pp_location f.loc);
      ( "CNDefinition.Function.def_function_args",
        pp_list (pp_pair pp_symbol (pp_basetype pp_unit)) f.args );
      ("CNDefinition.Function.def_function_return_bt", pp_basetype pp_unit f.return_bt);
      ("CNDefinition.Function.def_function_emit_coq", pp_bool f.emit_coq);
      ("CNDefinition.Function.def_function_body", pp_definition_function_body f.body)
    ]


let pp_global (g : Global.t) =
  pp_record
    [ ("Global.struct_decls", pp_struct_decls g.struct_decls);
      ("Global.datatypes", pp_sym_map pp_basetype_dt_info g.datatypes);
      ("Global.datatype_constrs", pp_sym_map pp_basetype_constr_info g.datatype_constrs);
      ("Global.datatype_order", pp_option (pp_list (pp_list pp_symbol)) g.datatype_order);
      ( "Global.fun_decls",
        pp_sym_map
          (fun (l, a, s) ->
            pp_tuple
              [ pp_location l; pp_option pp_argument_types_ft a; pp_c_concrete_sig s ])
          g.fun_decls );
      ( "Global.resource_predicates",
        pp_sym_map pp_definition_predicate g.resource_predicates );
      ( "Global.resource_predicate_order",
        pp_option (pp_list (pp_list pp_symbol)) g.resource_predicate_order );
      ("Global.logical_functions", pp_sym_map pp_definition_function g.logical_functions);
      ( "Global.logical_function_order",
        pp_option (pp_list (pp_list pp_symbol)) g.logical_function_order )
      (* TODO: add lemmata *)
    ]


let pp_context (c : Context.t) =
  pp_record
    [ ( "Context.computational",
        pp_sym_map (pp_pair pp_basetype_or_value pp_context_l_info) c.computational );
      ( "Context.logical",
        pp_sym_map (pp_pair pp_basetype_or_value pp_context_l_info) c.logical );
      ( "Context.resources",
        pp_pair (pp_list (pp_pair pp_resource pp_int)) pp_int c.resources );
      (*      ("resource_history", pp_map pp_int pp_resource_history c.resource_history); Ignore for now *)
      ( "Context.constraints",
        let l = LogicalConstraints.Set.elements c.constraints in
        pp_constructor
          "LogicalConstraints.set_from_list"
          [ pp_list pp_logical_constraint l ] );
      ("Context.global", pp_global c.global)
      (*      ("where", pp_where c.where) Ignore for now *)
    ]


let pp_resource_inference_type = function
  | Prooflog.PredicateRequest (s, p, o, ri) ->
    pp_constructor
      "PredicateRequest"
      [ pp_situation s;
        pp_predicate p;
        pp_option (pp_pair pp_location pp_string) o;
        pp_pair pp_resource_predicate (pp_list pp_int) ri
      ]
  | Prooflog.UnfoldResources loc -> pp_constructor "UnfoldResources" [ pp_location loc ]


(* Add this definition before its use in `pp_unit_file_with_resource_inference` *)
let pp_resource_inference_step = function
  | Prooflog.ResourceInferenceStep (c1, ri, c2) ->
    pp_constructor
      "ResourceInferenceStep"
      [ pp_context c1; pp_resource_inference_type ri; pp_context c2 ]


let coq_steps_var_name = "ResourceInferenceSteps"

(* Helper function that prints a list of strings, each followed by a hardline *)
(* Usage in your code *)
let coq_inference_proof =
  !^"From Reasoning Require Import ResourceInference ProofAutomation."
  ^^ P.hardline
  ^^ !^"Theorem resource_inference_steps_valid: prooflog_valid"
  ^^^ !^(quote_coq_name coq_steps_var_name)
  ^^^ !^"."
  ^^ P.hardline
  ^^ pp_lines
       [ "Proof.";
         "  unfold prooflog_valid.";
         "  unfold _cn_ResourceInferenceSteps.";
         "  ltac2:(prove_log_entry_list_valid ()).";
         "Admitted."
       ]


let pp_unit_file_with_resource_inference
  (prog : unit file)
  (osteps : Prooflog.log option)
  (generate_proof : bool)
  =
  pp_file pp_unit pp_unit_type prog
  ^^ P.hardline
  ^^
  match osteps with
  | Some steps ->
    pp_comment "Resource Inference Steps"
    ^^ P.hardline
    ^^ coq_def
         (coq_steps_var_name ^ ":Prooflog.log")
         P.empty
         (pp_list pp_resource_inference_step steps)
    ^^ P.hardline
    ^^
    if generate_proof then
      pp_comment "Resource Inference Proof" ^^ P.hardline ^^ coq_inference_proof
    else
      P.empty
  | None -> P.empty
