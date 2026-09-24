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
  
  val with_constraints: 'b -> t -> 'a eff -> 'a eff
end

type basis =
  [ `Octal | `Decimal | `Hexadecimal | `Binary ]

module type Memory = sig
  val name: string
(*  include (module type of Mem_common) *)
  
  type pointer_value
  type integer_value
  
  type mem_value
  
  type mem_iv_constraint = integer_value Mem_common.mem_constraint
  val cs_module : (module Constraints with type t = mem_iv_constraint)
  
  type footprint
  val overlapping: footprint -> footprint -> bool
  
  type mem_state
  val initial_mem_state: mem_state
  
  type 'a memM =
    ('a, string, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM
  val return: 'a -> 'a memM
  val bind: 'a memM -> ('a -> 'b memM) -> 'b memM
  
  (* Memory actions *)
  val allocate_object:
       Mem_common.thread_id      (* the allocating thread *)
    -> Cerb_symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
(*    -> bool           (* whether to zero init the allocated bytes *) *)
    -> integer_value  (* alignment constraint *)
    -> Ctype.ctype    (* type of the allocation *)
    -> Z.t option     (* potential requested address (see Cerb_attributes: cerb::with_address()) *)
    -> mem_value option   (* optional initialisation value (if provided the allocation is made read-only) *)
    -> pointer_value memM
  
  val allocate_region:
       Mem_common.thread_id      (* the allocating thread *)
    -> Cerb_symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value  (* alignment constraint *)
    -> integer_value  (* size *)
    -> pointer_value memM
  
  val kill: Cerb_location.t -> bool -> pointer_value -> unit memM
  
  val load: Cerb_location.t -> Ctype.ctype -> pointer_value -> (footprint * mem_value) memM
  val store: Cerb_location.t -> Ctype.ctype -> (* is_locking *)bool -> pointer_value -> mem_value -> footprint memM
  
  (* Pointer value constructors *)
  val null_ptrval: Ctype.ctype -> pointer_value
  val fun_ptrval: Cerb_symbol.Sym.t -> pointer_value

  (*TODO: revise that, just a hack for codegen*)
  val concrete_ptrval: Z.t -> Z.t -> pointer_value
  val case_ptrval: pointer_value ->
   (* null pointer *) (Ctype.ctype -> 'a) ->
   (* function pointer *) (Cerb_symbol.Sym.t option -> 'a) ->
   (* concrete pointer *) (Z.t option -> Z.t -> 'a) -> 'a
  val case_funsym_opt: mem_state -> pointer_value -> Cerb_symbol.Sym.t option

  (* Operations on pointer values *)
  val eq_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val ne_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val lt_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val gt_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val le_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val ge_ptrval: Cerb_location.t -> pointer_value -> pointer_value -> bool memM
  val diff_ptrval: Cerb_location.t -> Ctype.ctype -> pointer_value -> pointer_value -> integer_value memM

  val update_prefix: (Cerb_symbol.prefix * mem_value) -> unit memM
  val prefix_of_pointer: pointer_value -> string option memM
  
  val validForDeref_ptrval: Ctype.ctype -> pointer_value -> bool memM
  val isWellAligned_ptrval: Ctype.ctype -> pointer_value -> bool memM
  
  (* Casting operations *)
  (* the first ctype is the original integer type, the second is the target referenced type *)
  val ptrfromint: Cerb_location.t -> Ctype.integerType -> Ctype.ctype -> integer_value -> pointer_value memM
  (* the first ctype is the original referenced type, the integerType is the target integer type *)
  val intfromptr: Cerb_location.t -> Ctype.ctype -> Ctype.integerType -> pointer_value -> integer_value memM

  (* New operations for CHERI *)
  val derive_cap : bool(* is_signed *) -> Mem_common.derivecap_op -> integer_value -> integer_value -> integer_value
  val cap_assign_value: Cerb_location.t -> integer_value -> integer_value -> integer_value
  val ptr_t_int_value: integer_value -> integer_value
  val null_cap : bool(* is_signed *) -> integer_value

  (* Pointer shifting constructors *)
  val array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value
  val member_shift_ptrval: pointer_value -> Cerb_symbol.Sym.t -> Cerb_symbol.Identifier.t -> pointer_value
  
  val eff_array_shift_ptrval: Cerb_location.t -> pointer_value -> Ctype.ctype -> integer_value -> pointer_value memM
  val eff_member_shift_ptrval: Cerb_location.t -> pointer_value -> Cerb_symbol.Sym.t -> Cerb_symbol.Identifier.t -> pointer_value memM
  
  val memcpy: Cerb_location.t -> pointer_value -> pointer_value -> integer_value -> pointer_value memM
  val memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM
  val realloc: Cerb_location.t -> Mem_common.thread_id -> integer_value -> pointer_value -> integer_value -> pointer_value memM

  val va_start: (Ctype.ctype * pointer_value) list -> integer_value memM
  val va_copy: integer_value -> integer_value memM
  val va_arg: integer_value -> Ctype.ctype -> pointer_value memM
  val va_end: integer_value -> unit memM
  val va_list: Z.t -> ((Ctype.ctype * pointer_value) list) memM

  val copy_alloc_id: integer_value -> pointer_value -> pointer_value memM

  (* Byte casting operations *)
  val bytefromint: integer_value -> integer_value
  val intfrombyte: integer_value -> integer_value

  
  (* Integer value constructors *)
  val integer_ival: Z.t -> integer_value
  val max_ival: Ctype.integerType -> integer_value
  val min_ival: Ctype.integerType -> integer_value
  val op_ival: Mem_common.integer_operator -> integer_value -> integer_value -> integer_value
  val offsetof_ival: (Cerb_symbol.Sym.t, Cerb_location.t * Ctype.tag_definition) Pmap.map -> Cerb_symbol.Sym.t -> Cerb_symbol.Identifier.t -> integer_value
  
  val bitwise_complement_ival: Ctype.integerType -> integer_value -> integer_value
  val bitwise_and_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_or_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_xor_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  
  val case_integer_value: (* TODO: expose more ctors *)
    integer_value ->
    (Z.t -> 'a) ->
    (unit -> 'a) ->
    'a
  
  (* Predicats on integer values *)
  val eq_ival: integer_value -> integer_value -> bool option
  val lt_ival: integer_value -> integer_value -> bool option
  val le_ival: integer_value -> integer_value -> bool option

  (* Integer <-> Floating casting constructors *)
  val fvfromint: integer_value -> Float.t
  val ivfromfloat: Ctype.integerType -> Float.t -> integer_value
  
  
  
  (* Memory value constructors *)
  val unspecified_mval: Ctype.ctype -> mem_value
  val integer_value_mval: Ctype.integerType -> integer_value -> mem_value
  val floating_value_mval: Ctype.floatingType -> Float.t -> mem_value
  val pointer_mval: Ctype.ctype -> pointer_value -> mem_value
  val array_mval: mem_value list -> mem_value
  val struct_mval: Cerb_symbol.Sym.t -> (Cerb_symbol.Identifier.t * Ctype.ctype * mem_value) list -> mem_value
  val union_mval: Cerb_symbol.Sym.t -> Cerb_symbol.Identifier.t -> mem_value -> mem_value
  
  (* Memory value destructor *)
  val case_mem_value:
    mem_value ->
    (Ctype.ctype -> 'a) -> (* unspecified case *)
    (Ctype.integerType -> Cerb_symbol.Sym.t -> 'a) -> (* concurrency read case *)
    (Ctype.integerType -> integer_value -> 'a) ->
    (Ctype.floatingType -> Float.t -> 'a) ->
    (Ctype.ctype -> pointer_value -> 'a) ->
    (mem_value list -> 'a) ->
    (Cerb_symbol.Sym.t -> (Cerb_symbol.Identifier.t * Ctype.ctype * mem_value) list -> 'a) ->
    (Cerb_symbol.Sym.t -> Cerb_symbol.Identifier.t -> mem_value -> 'a) ->
    'a


  (* Memory intrinsics (currently used in CHERI) *)
  val call_intrinsic: Cerb_location.t -> string -> (mem_value list) -> (mem_value option) memM
  val get_intrinsic_type_spec: string -> Mem_common.intrinsics_signature option


  (* Only used by cn-coq *)
  val pp_integer_value_for_coq: integer_value -> PPrint.document
  (* val pp_floating_value_for_coq: floating_value -> PPrint.document *)
  val pp_pointer_value_for_coq: (Cerb_symbol.Sym.t -> PPrint.document) -> pointer_value -> PPrint.document
  (* This is a bit ugly as we need to pass all the pretty printers for the different types *)
  val pp_mem_value_for_coq: 
    (Cerb_symbol.Sym.t -> PPrint.document) ->
    (Ctype.integerType -> PPrint.document) ->
    (Ctype.floatingType -> PPrint.document) ->
    (Ctype.ctype -> PPrint.document) ->
    (Cerb_symbol.Identifier.t -> PPrint.document) ->
    mem_value -> PPrint.document

  (* pretty printing *)
  val pp_integer_value: integer_value -> PPrint.document
  val pp_pretty_integer_value: ?basis:basis -> use_upper:bool -> integer_value -> PPrint.document
  val pp_integer_value_for_core: integer_value -> PPrint.document

  val pp_pointer_value: ?is_verbose:bool -> pointer_value -> PPrint.document
  val pp_pretty_pointer_value: pointer_value -> PPrint.document

  val pp_mem_value: mem_value -> PPrint.document
  val pp_pretty_mem_value: ?basis:basis -> use_upper:bool -> mem_value -> PPrint.document

  (* JSON serialisation *)
  val serialise_mem_state: Digest.t -> mem_state -> Cerb_json.json
end
