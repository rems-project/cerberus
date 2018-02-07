module type Constraints = sig
  type t
  val negate: t -> t

  type 'a eff
  val return: 'a -> 'a eff
  val bind: 'a eff -> ('a -> 'b eff) -> 'b eff
  val foldlM : ('a -> 'b -> 'a eff) -> 'a -> 'b list -> 'a eff
  
  val runEff: 'a eff -> 'a
  
(*  val init_solver: unit eff *) (* TODO: this can be internal to runEff *)
  val string_of_solver: string list eff
  val check_sat: [ `SAT | `UNSAT ] eff
  
  val with_constraints: string -> t -> 'a eff -> 'a eff
end

module type Memory = sig
  val name: string
(*  include (module type of Mem_common) *)
  
  type pointer_value
  type integer_value
  type floating_value
  
  type mem_value
  
  type mem_iv_constraint = integer_value Mem_common.mem_constraint
  val cs_module : (module Constraints with type t = mem_iv_constraint)
  
  type footprint
  val do_overlap: footprint -> footprint -> bool
  
  type mem_state
  val initial_mem_state: mem_state
  
  type 'a memM =
    ('a, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM
  val return: 'a -> 'a memM
  val bind: 'a memM -> ('a -> 'b memM) -> 'b memM
  
  (* Memory actions *)
  val allocate_static:
       Cthread.thread_id  (* the allocating thread *)
    -> Symbol.prefix      (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value      (* alignment constraint *)
    -> Core_ctype.ctype0  (* type of the allocation *)
    -> pointer_value memM
  
  val allocate_dynamic:
       Cthread.thread_id (* the allocating thread *)
    -> Symbol.prefix     (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value     (* alignment constraint *)
    -> integer_value     (* size *)
    -> pointer_value memM
  
  val kill: pointer_value -> unit memM
  
  val load: Location_ocaml.t -> Core_ctype.ctype0 -> pointer_value -> (footprint * mem_value) memM
  val store: Location_ocaml.t -> Core_ctype.ctype0 -> pointer_value -> mem_value -> footprint memM
  
  (* Pointer value constructors *)
  val null_ptrval: Core_ctype.ctype0 -> pointer_value
  val fun_ptrval: Symbol.sym -> pointer_value
  
  (* Operations on pointer values *)
  val eq_ptrval: pointer_value -> pointer_value -> bool memM
  val ne_ptrval: pointer_value -> pointer_value -> bool memM
  val lt_ptrval: pointer_value -> pointer_value -> bool memM
  val gt_ptrval: pointer_value -> pointer_value -> bool memM
  val le_ptrval: pointer_value -> pointer_value -> bool memM
  val ge_ptrval: pointer_value -> pointer_value -> bool memM
  val diff_ptrval: Core_ctype.ctype0 -> pointer_value -> pointer_value -> integer_value memM
  
  val validForDeref_ptrval: pointer_value -> bool
  val isWellAligned_ptrval: Core_ctype.ctype0 -> pointer_value -> bool memM
  
  (* Casting operations *)
  (* the first ctype is the original integer type, the second is the target referenced type *)
  val ptrcast_ival: Core_ctype.ctype0 -> Core_ctype.ctype0 -> integer_value -> pointer_value memM
  (* the first ctype is the original referenced type, the integerType is the target integer type *)
  val intcast_ptrval: Core_ctype.ctype0 -> AilTypes.integerType -> pointer_value -> integer_value memM
  
  (* Pointer shifting constructors *)
  val array_shift_ptrval:  pointer_value -> Core_ctype.ctype0 -> integer_value -> pointer_value
  val member_shift_ptrval: pointer_value -> Symbol.sym -> Cabs.cabs_identifier -> pointer_value
  
  val memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM
  
  (* Integer value constructors *)
  val concurRead_ival: AilTypes.integerType -> Symbol.sym -> integer_value
  val integer_ival: Nat_big_num.num -> integer_value
  val max_ival: AilTypes.integerType -> integer_value
  val min_ival: AilTypes.integerType -> integer_value
  val op_ival: Mem_common.integer_operator -> integer_value -> integer_value -> integer_value
  val offsetof_ival: Symbol.sym -> Cabs.cabs_identifier -> integer_value
  
  val sizeof_ival: Core_ctype.ctype0 -> integer_value
  val alignof_ival: Core_ctype.ctype0 -> integer_value
  
  val bitwise_complement_ival: AilTypes.integerType -> integer_value -> integer_value
  val bitwise_and_ival: AilTypes.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_or_ival: AilTypes.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_xor_ival: AilTypes.integerType -> integer_value -> integer_value -> integer_value
  
  val case_integer_value: (* TODO: expose more ctors *)
    integer_value ->
    (Nat_big_num.num -> 'a) ->
    (unit -> 'a) ->
    'a
  
  val is_specified_ival: integer_value -> bool
  
  (* Predicats on integer values *)
  val eq_ival: mem_state option -> integer_value -> integer_value -> bool option
  val lt_ival: mem_state option -> integer_value -> integer_value -> bool option
  val le_ival: mem_state option -> integer_value -> integer_value -> bool option
  
  val eval_integer_value: integer_value -> Nat_big_num.num option
  
  (* Floating value constructors *)
  val zero_fval: floating_value
  val str_fval: string -> floating_value
  
  (* Floating value destructors *)
  val case_fval: floating_value -> (unit -> 'a) -> (float -> 'a) -> 'a
  
  (* Predicates on floating values *)
  val op_fval: Mem_common.floating_operator -> floating_value -> floating_value -> floating_value
  val eq_fval: floating_value -> floating_value -> bool
  val lt_fval: floating_value -> floating_value -> bool
  val le_fval: floating_value -> floating_value -> bool
  
  (* Integer <-> Floating casting constructors *)
  val fvfromint: integer_value -> floating_value
  val ivfromfloat: AilTypes.integerType -> floating_value -> integer_value
  
  
  
  (* Memory value constructors *)
  (*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
  val unspecified_mval: Core_ctype.ctype0 -> mem_value
  val integer_value_mval: AilTypes.integerType -> integer_value -> mem_value
  val floating_value_mval: AilTypes.floatingType -> floating_value -> mem_value
  val pointer_mval: Core_ctype.ctype0 -> pointer_value -> mem_value
  val array_mval: mem_value list -> mem_value
  val struct_mval: Symbol.sym -> (Cabs.cabs_identifier * mem_value) list -> mem_value
  val union_mval: Symbol.sym -> Cabs.cabs_identifier -> mem_value -> mem_value
  
  (* Memory value destructor *)
  val case_mem_value:
    mem_value ->
    (Core_ctype.ctype0 -> 'a) -> (* unspecified case *)
    (AilTypes.integerType -> Symbol.sym -> 'a) -> (* concurrency read case *)
    (AilTypes.integerType -> integer_value -> 'a) ->
    (AilTypes.floatingType -> floating_value -> 'a) ->
    (Core_ctype.ctype0 -> pointer_value -> 'a) ->
    (mem_value list -> 'a) ->
    (Symbol.sym -> (Cabs.cabs_identifier * mem_value) list -> 'a) ->
    (Symbol.sym -> Cabs.cabs_identifier -> mem_value -> 'a) ->
    'a
  
  
  (* For race detection *)
  val sequencePoint: unit memM
  
  (* pretty printing *)
  val pp_pointer_value: pointer_value -> PPrint.document
  val pp_integer_value: integer_value -> PPrint.document
  val pp_integer_value_for_core: integer_value -> PPrint.document
  val pp_mem_value: mem_value -> PPrint.document
  val pp_pretty_pointer_value: pointer_value -> PPrint.document
  val pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document
  val pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document
  
(*
  val string_of_pointer_value: pointer_value -> string
  val string_of_integer_value: integer_value -> string
  val string_of_mem_value: mem_value -> string
*)

  (* JSON serialisation *)
  val serialise_pointer_value: pointer_value -> Json.json
  val parse_pointer_value: Json.json -> pointer_value
  val serialise_integer_value: integer_value -> Json.json
  val parse_integer_value: Json.json -> integer_value
  val serialise_floating_value: floating_value -> Json.json
  val parse_floating_value: Json.json -> floating_value
  val serialise_mem_value: mem_value -> Json.json
  val parse_mem_value: Json.json -> mem_value
  
  
  
  
  
(*  
  val runND:
    Driver.driver_result Driver.driverM ->
    Driver.driver_state ->
    ( (Driver.driver_result, Driver.driver_error) Nondeterminism.nd_status
    * string list
    * Driver.driver_state ) list
*)
end
