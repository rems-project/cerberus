[@@@warning "+8-37"]
open Ctype

(*open Ocaml_implementation*)
open Memory_model
open Mem_common
open CheriMemory
open CoqImplementation
open Morello

module MM = CheriMemory(MorelloCapability)(MorelloImpl)
module C = MorelloCapability

module Z = struct
  include Nat_big_num
  let format = Z.format
end

module L = struct
  include List
  include Lem_list
end


module CHERIMorello : Memory = struct
  let name = MM.name

  type pointer_value = MM.pointer_value
  type integer_value = MM.integer_value
  type floating_value = MM.floating_value
  type mem_value = MM.mem_value

  type mem_iv_constraint = integer_value Mem_common.mem_constraint
  type footprint = MM.footprint
  type mem_state = MM.mem_state

  let check_overlap = MM.check_overlap

  let initial_mem_state = MM.initial_mem_state

  let cs_module = (module struct
                     type t = mem_iv_constraint
                     let negate x = MC_not x

                     type 'a eff = Eff of (bool -> ('a * bool))
                     let return a = Eff (fun b -> (a, b))
                     let bind (Eff ma) f =
                       Eff (fun b -> let (a, b') = ma b in let Eff mb = f a in mb b')
                     let rec foldlM f a = function
                       | [] ->
                          return a
                       | x::xs ->
                          bind (f a x) (fun fax -> foldlM f fax xs)

                     let runEff (Eff ma) = fst (ma true)

                     let string_of_solver = return []
                     let check_sat =
                       Eff (fun b -> ((if b then `SAT else `UNSAT), b))

                     let with_constraints _ cs (Eff ma) =
                       Debug_ocaml.print_debug 1 [] (fun () -> "HELLO: Concrete.with_constraints");
                       let rec eval_cs = function
                         | MC_empty ->
                            true
                         | MC_eq (ival1, ival2) ->
                            Stdlib.Option.value (MM.eq_ival None ival1 ival2) ~default:false
                         | MC_le (ival1, ival2) ->
                            Stdlib.Option.value (MM.le_ival None ival1 ival2) ~default:false
                         | MC_lt (ival1, ival2) ->
                            Stdlib.Option.value (MM.lt_ival None ival1 ival2) ~default:false
                         | MC_in_device _ ->
                            failwith "TODO: Concrete, with_constraints: MC_in_device"
                         | MC_or (cs1, cs2) ->
                            eval_cs cs1 || eval_cs cs2
                         | MC_conj css ->
                            List.for_all (fun z -> eval_cs z) css
                         | MC_not cs ->
                            not (eval_cs cs)
                       in
                       Eff (fun b -> ma (b && eval_cs cs))
                   end : Constraints with type t = mem_iv_constraint)

  type 'a memM =
    ('a, string, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM

  let return = Nondeterminism.nd_return
  let bind = Nondeterminism.nd_bind

  let lift_coq_memM (m:'a MM.memM): 'a memM =
    ND (fun st ->
        match m st with
        | (st', Coq_inl e) ->
           let e' = translateMemError e in
           (ND.NDkilled e', st')
        | (st',Coq_inr a) -> (ND.NDactive a, st')
      )


(* Types from Coq-extracted code:

     type 'a memM = (mem_state, memMError, 'a) errS

     type ('st, 'errT, 'a) errS = 'st -> 'st * ('errT, 'a) sum

     type ('a, 'b) sum =
     | Coq_inl of 'a
     | Coq_inr of 'b

   *)

(*
  val allocate_object:
       Mem_common.thread_id      (* the allocating thread *)
    -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value  (* alignment constraint *)
    -> Ctype.ctype    (* type of the allocation *)
    -> mem_value option   (* optional initialisation value (if provided the allocation is made read-only) *)
    -> pointer_value memM =
    lift_coq_memM (MM.allocate_object _ _ _)
 *)
  
  (*

  let cs_module : (module Constraints with type t = mem_iv_constraint)

  type 'a memM =
    ('a, string, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM
  val return: 'a -> 'a memM
  val bind: 'a memM -> ('a -> 'b memM) -> 'b memM

  (* Memory actions *)
  val allocate_object:
       Mem_common.thread_id      (* the allocating thread *)
    -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value  (* alignment constraint *)
    -> Ctype.ctype    (* type of the allocation *)
    -> mem_value option   (* optional initialisation value (if provided the allocation is made read-only) *)
    -> pointer_value memM

  val allocate_region:
       Mem_common.thread_id      (* the allocating thread *)
    -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
    -> integer_value  (* alignment constraint *)
    -> integer_value  (* size *)
    -> pointer_value memM

  val kill: Location_ocaml.t -> bool -> pointer_value -> unit memM

  val load: Location_ocaml.t -> Ctype.ctype -> pointer_value -> (footprint * mem_value) memM
  val store: Location_ocaml.t -> Ctype.ctype -> (* is_locking *)bool -> pointer_value -> mem_value -> footprint memM

  (* Pointer value constructors *)
  val null_ptrval: Ctype.ctype -> pointer_value
  val fun_ptrval: Symbol.sym -> pointer_value

  (*TODO: revise that, just a hack for codegen*)
  val concrete_ptrval: Nat_big_num.num -> Nat_big_num.num -> pointer_value
  val case_ptrval: pointer_value ->
   (* null pointer *) (unit -> 'a) ->
   (* function pointer *) (Symbol.sym option -> 'a) ->
   (* concrete pointer *) (unit -> 'a) ->
   (* unspecified value *) (unit -> 'a) -> 'a
  val case_funsym_opt: mem_state -> pointer_value -> Symbol.sym option

  (* Operations on pointer values *)
  val eq_ptrval: pointer_value -> pointer_value -> bool memM
  val ne_ptrval: pointer_value -> pointer_value -> bool memM
  val lt_ptrval: pointer_value -> pointer_value -> bool memM
  val gt_ptrval: pointer_value -> pointer_value -> bool memM
  val le_ptrval: pointer_value -> pointer_value -> bool memM
  val ge_ptrval: pointer_value -> pointer_value -> bool memM
  val diff_ptrval: Ctype.ctype -> pointer_value -> pointer_value -> integer_value memM

  val update_prefix: (Symbol.prefix * mem_value) -> unit memM
  val prefix_of_pointer: pointer_value -> string option memM

  val validForDeref_ptrval: Ctype.ctype -> pointer_value -> bool memM
  val isWellAligned_ptrval: Ctype.ctype -> pointer_value -> bool memM

  (* Casting operations *)
  (* the first ctype is the original integer type, the second is the target referenced type *)
  val ptrfromint: Location_ocaml.t -> Ctype.integerType -> Ctype.ctype -> integer_value -> pointer_value memM
  (* the first ctype is the original referenced type, the integerType is the target integer type *)
  val intfromptr: Location_ocaml.t -> Ctype.ctype -> Ctype.integerType -> pointer_value -> integer_value memM

  (* New operations for CHERI *)
  val derive_cap : bool(* is_signed *) -> Mem_common.derivecap_op -> integer_value -> integer_value -> integer_value
  val cap_assign_value: Location_ocaml.t -> integer_value -> integer_value -> integer_value
  val ptr_t_int_value: integer_value -> integer_value
  val null_cap : bool(* is_signed *) -> integer_value

  (* Pointer shifting constructors *)
  val array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value
  val member_shift_ptrval: pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value

  val eff_array_shift_ptrval: Location_ocaml.t -> pointer_value -> Ctype.ctype -> integer_value -> pointer_value memM
  val eff_member_shift_ptrval: Location_ocaml.t -> pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value memM

  val memcpy: pointer_value -> pointer_value -> integer_value -> pointer_value memM
  val memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM
  val realloc: Mem_common.thread_id -> integer_value -> pointer_value -> integer_value -> pointer_value memM

  val va_start: (Ctype.ctype * pointer_value) list -> integer_value memM
  val va_copy: integer_value -> integer_value memM
  val va_arg: integer_value -> Ctype.ctype -> pointer_value memM
  val va_end: integer_value -> unit memM
  val va_list: Nat_big_num.num -> ((Ctype.ctype * pointer_value) list) memM

  val copy_alloc_id: integer_value -> pointer_value -> pointer_value memM

  (* Integer value constructors *)
  val concurRead_ival: Ctype.integerType -> Symbol.sym -> integer_value
  val integer_ival: Nat_big_num.num -> integer_value
  val max_ival: Ctype.integerType -> integer_value
  val min_ival: Ctype.integerType -> integer_value
  val op_ival: Mem_common.integer_operator -> integer_value -> integer_value -> integer_value
  val offsetof_ival: (Symbol.sym, Ctype.tag_definition) Pmap.map -> Symbol.sym -> Symbol.identifier -> integer_value

  val sizeof_ival: Ctype.ctype -> integer_value
  val alignof_ival: Ctype.ctype -> integer_value

  val bitwise_complement_ival: Ctype.integerType -> integer_value -> integer_value
  val bitwise_and_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_or_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_xor_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value

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
  val one_fval: floating_value
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
  val ivfromfloat: Ctype.integerType -> floating_value -> integer_value



  (* Memory value constructors *)
  (*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
  val unspecified_mval: Ctype.ctype -> mem_value
  val integer_value_mval: Ctype.integerType -> integer_value -> mem_value
  val floating_value_mval: Ctype.floatingType -> floating_value -> mem_value
  val pointer_mval: Ctype.ctype -> pointer_value -> mem_value
  val array_mval: mem_value list -> mem_value
  val struct_mval: Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> mem_value
  val union_mval: Symbol.sym -> Symbol.identifier -> mem_value -> mem_value

  (* Memory value destructor *)
  val case_mem_value:
    mem_value ->
    (Ctype.ctype -> 'a) -> (* unspecified case *)
    (Ctype.integerType -> Symbol.sym -> 'a) -> (* concurrency read case *)
    (Ctype.integerType -> integer_value -> 'a) ->
    (Ctype.floatingType -> floating_value -> 'a) ->
    (Ctype.ctype -> pointer_value -> 'a) ->
    (mem_value list -> 'a) ->
    (Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> 'a) ->
    (Symbol.sym -> Symbol.identifier -> mem_value -> 'a) ->
    'a


  (* For race detection *)
  val sequencePoint: unit memM

  (* Memory intrinsics (currently used in CHERI) *)

  val call_intrinsic: Location_ocaml.t -> string -> (mem_value list) -> (mem_value option) memM
  val get_intrinsic_type_spec: string -> Mem_common.intrinsics_signature option


  (* pretty printing *)
  val pp_pointer_value: ?is_verbose:bool -> pointer_value -> PPrint.document
  val pp_integer_value: integer_value -> PPrint.document
  val pp_integer_value_for_core: integer_value -> PPrint.document
  val pp_mem_value: mem_value -> PPrint.document
  val pp_pretty_pointer_value: pointer_value -> PPrint.document
  val pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document
  val pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document

(*
  val string_of_pointer_value: pointer_value -> string
  val string_of_integer_value: integer_value -> string
  val string_of_mem_value: mem_value -> stri(g
*)

  (* JSON serialisation *)
  val serialise_mem_state: Digest.t -> mem_state -> Json.json

                *)

end

open Morello

include CHERIMorello
