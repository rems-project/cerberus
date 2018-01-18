open Memory_model

(* we need to do this because of Lem's renaming not understanding modules... *)
module Defacto : Memory = struct
  type pointer_value = Defacto_memory_types.impl_pointer_value
  type integer_value = Defacto_memory_types.impl_integer_value
  type floating_value = Defacto_memory_types.impl_floating_value
  type mem_value = Defacto_memory_types.impl_mem_value
  type mem_iv_constraint = integer_value Mem_common.mem_constraint

  let cs_module = (module struct
    type t = mem_iv_constraint
    let negate x = Mem_common.MC_not x
    
    type 'a eff = 'a
    let return a = a
    let bind ma f = f ma
    let foldlM f a bs = List.fold_left f a bs
    
    let runEff a = a
    
(*    let init_solver = return () *)
    let string_of_solver = return []
    let check_sat = return `SAT
    
    let with_constraints _ _ a = a
  end : Constraints with type t = mem_iv_constraint)
  
  type footprint = Defacto_memory_types.impl_footprint
  let do_overlap _ _ = false (* TODO *)
  type mem_state = Defacto_memory.impl_mem_state
  let initial_mem_state = Defacto_memory.impl_initial_mem_state
  type 'a memM =
    ('a, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM
  let return = Defacto_memory.impl_return
  let bind = Nondeterminism.bind2
  let allocate_static = Defacto_memory.impl_allocate_static

  let allocate_dynamic = Defacto_memory.impl_allocate_dynamic
  let kill = Defacto_memory.impl_kill
  let load = Defacto_memory.impl_load
  let store = Defacto_memory.impl_store
  let null_ptrval = Defacto_memory.impl_null_ptrval
  let fun_ptrval = Defacto_memory.impl_fun_ptrval
  let eq_ptrval = Defacto_memory.impl_eq_ptrval
  let ne_ptrval = Defacto_memory.impl_ne_ptrval
  let lt_ptrval = Defacto_memory.impl_lt_ptrval
  let gt_ptrval = Defacto_memory.impl_gt_ptrval
  let le_ptrval = Defacto_memory.impl_le_ptrval
  let ge_ptrval = Defacto_memory.impl_ge_ptrval
  let diff_ptrval = Defacto_memory.impl_diff_ptrval
  let validForDeref_ptrval = Defacto_memory.impl_validForDeref_ptrval
  let ptrcast_ival = Defacto_memory.impl_ptrcast_ival
  let intcast_ptrval = Defacto_memory.impl_intcast_ptrval
  let array_shift_ptrval = Defacto_memory.impl_array_shift_ptrval
  let member_shift_ptrval = Defacto_memory.impl_member_shift_ptrval
  let memcmp = Defacto_memory.impl_memcmp
  let concurRead_ival = Defacto_memory.impl_concurRead_ival
  let integer_ival = Defacto_memory.impl_integer_ival
  let max_ival = Defacto_memory.impl_max_ival
  let min_ival = Defacto_memory.impl_min_ival
  let op_ival = Defacto_memory.impl_op_ival
  let offsetof_ival = Defacto_memory.impl_offsetof_ival
  let sizeof_ival = Defacto_memory.impl_sizeof_ival
  let alignof_ival = Defacto_memory.impl_alignof_ival
  let bitwise_complement_ival = Defacto_memory.impl_bitwise_complement_ival
  let bitwise_and_ival = Defacto_memory.impl_bitwise_and_ival
  let bitwise_or_ival = Defacto_memory.impl_bitwise_or_ival
  let bitwise_xor_ival = Defacto_memory.impl_bitwise_xor_ival
  let case_integer_value = Defacto_memory.impl_case_integer_value
  let is_specified_ival = Defacto_memory.impl_is_specified_ival
  let eq_ival = Defacto_memory.impl_eq_ival
  let lt_ival = Defacto_memory.impl_lt_ival
  let le_ival = Defacto_memory.impl_le_ival
  let eval_integer_value = Defacto_memory.impl_eval_integer_value
  let zero_fval = Defacto_memory.impl_zero_fval
  let str_fval = Defacto_memory.impl_str_fval
  let case_fval = Defacto_memory.impl_case_fval
  let op_fval = Defacto_memory.impl_op_fval
  let eq_fval = Defacto_memory.impl_eq_fval
  let lt_fval = Defacto_memory.impl_lt_fval
  let le_fval = Defacto_memory.impl_le_fval
  let fvfromint = Defacto_memory.impl_fvfromint
  let ivfromfloat = Defacto_memory.impl_ivfromfloat
  let unspecified_mval = Defacto_memory.impl_unspecified_mval
  let integer_value_mval = Defacto_memory.impl_integer_value_mval
  let floating_value_mval = Defacto_memory.impl_floating_value_mval
  let pointer_mval = Defacto_memory.impl_pointer_mval
  let array_mval = Defacto_memory.impl_array_mval
  let struct_mval = Defacto_memory.impl_struct_mval
  let union_mval = Defacto_memory.impl_union_mval
  let case_mem_value = Defacto_memory.impl_case_mem_value
  let sequencePoint = Defacto_memory.impl_sequencePoint
  
  include Pp_defacto_memory
end


type mem_setting =
  [ `MemDefacto | `MemConcrete ]
(* TODO: I hate that *)
let switch : mem_setting ref =
  ref `MemDefacto

module Mem = (
  val match !switch with
    | `MemDefacto  -> (module Defacto : Memory_model.Memory)
    | `MemConcrete -> (module Concrete : Memory_model.Memory)
)

include Mem

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)



let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Colour.do_colour in
    Colour.do_colour := false;
    let ret = pp_mem_value mval in
    Colour.do_colour := saved;
    ret
  end
