open Memory_model

module ND = Nondeterminism
module MC = Mem_common

let name : string = "RefinedC's Caesium memory model"

type pointer_value = Caesium.loc
type integer_value = Caesium.int_repr
type floating_value = float

type mem_value = Caesium.value

type mem_iv_constraint = integer_value MC.mem_constraint
let cs_module : (module Constraints with type t = mem_iv_constraint) =
  assert false (* TODO *)

type footprint = unit
let do_overlap: footprint -> footprint -> bool =
  fun _ _ -> failwith "TODO: do_overlap"

type mem_state = Caesium.heap_state
let initial_mem_state: mem_state =
  Caesium.initial_heap_state

type 'a memM =
  ('a, string, MC.mem_error, integer_value MC.mem_constraint, mem_state) ND.ndM
let return: 'a -> 'a memM =
  ND.nd_return
let bind: 'a memM -> ('a -> 'b memM) -> 'b memM =
  ND.nd_bind

(* Memory actions *)
let allocate_object:
     MC.thread_id      (* the allocating thread *)
  -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
  -> integer_value  (* alignment constraint *)
  -> Ctype.ctype    (* type of the allocation *)
  -> mem_value option   (* optional initialisation value (if provided the allocation is made read-only) *)
  -> pointer_value memM =
  assert false (* TODO *)

let allocate_region:
     MC.thread_id      (* the allocating thread *)
  -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
  -> integer_value  (* alignment constraint *)
  -> integer_value  (* size *)
  -> pointer_value memM =
  assert false (* TODO *)

let kill: Location_ocaml.t -> bool -> pointer_value -> unit memM =
  assert false (* TODO *)

let load: Location_ocaml.t -> Ctype.ctype -> pointer_value -> (footprint * mem_value) memM =
  assert false (* TODO *)
let store: Location_ocaml.t -> Ctype.ctype -> (* is_locking *)bool -> pointer_value -> mem_value -> footprint memM =
  assert false (* TODO *)

(* Pointer value constructors *)
let null_ptrval: Ctype.ctype -> pointer_value =
  assert false (* TODO *)
let fun_ptrval: Symbol.sym -> pointer_value =
  assert false (* TODO *)

(*TODO: revise that, just a hack for codegen*)
let concrete_ptrval: Nat_big_num.num -> Nat_big_num.num -> pointer_value =
  assert false (* TODO *)
let case_ptrval: pointer_value ->
 (* null pointer *) (Ctype.ctype -> 'a) ->
 (* function pointer *) (Symbol.sym -> 'a) ->
 (* concrete pointer *) (Nat_big_num.num option -> Nat_big_num.num -> 'a) ->
 (* unspecified value *) (unit -> 'a) -> 'a =
  assert false (* TODO *)
let case_funsym_opt: mem_state -> pointer_value -> Symbol.sym option =
  assert false (* TODO *)

(* Operations on pointer values *)
let eq_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let ne_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let lt_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let gt_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let le_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let ge_ptrval: pointer_value -> pointer_value -> bool memM =
  assert false (* TODO *)
let diff_ptrval: Ctype.ctype -> pointer_value -> pointer_value -> integer_value memM =
  assert false (* TODO *)

let update_prefix: (Symbol.prefix * mem_value) -> unit memM =
  assert false (* TODO *)
let prefix_of_pointer: pointer_value -> string option memM =
  assert false (* TODO *)

let validForDeref_ptrval: Ctype.ctype -> pointer_value -> bool memM =
  assert false (* TODO *)
let isWellAligned_ptrval: Ctype.ctype -> pointer_value -> bool memM =
  assert false (* TODO *)

(* Casting operations *)
(* the first ctype is the original integer type, the second is the target referenced type *)
let ptrcast_ival: Ctype.ctype -> Ctype.ctype -> integer_value -> pointer_value memM =
  assert false (* TODO *)
(* the first ctype is the original referenced type, the integerType is the target integer type *)
let intcast_ptrval: Ctype.ctype -> Ctype.integerType -> pointer_value -> integer_value memM =
  assert false (* TODO *)

(* Pointer shifting constructors *)
let array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value =
  assert false (* TODO *)
let member_shift_ptrval: pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value =
  assert false (* TODO *)

let eff_array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value memM =
  assert false (* TODO *)

let memcpy: pointer_value -> pointer_value -> integer_value -> pointer_value memM =
  assert false (* TODO *)
let memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM =
  assert false (* TODO *)
let realloc: MC.thread_id -> integer_value -> pointer_value -> integer_value -> pointer_value memM =
  assert false (* TODO *)

let va_start: (Ctype.ctype * pointer_value) list -> integer_value memM =
  assert false (* TODO *)
let va_copy: integer_value -> integer_value memM =
  assert false (* TODO *)
let va_arg: integer_value -> Ctype.ctype -> pointer_value memM =
  assert false (* TODO *)
let va_end: integer_value -> unit memM =
  assert false (* TODO *)
let va_list: Nat_big_num.num -> ((Ctype.ctype * pointer_value) list) memM =
  assert false (* TODO *)


(* Integer value constructors *)
let concurRead_ival: Ctype.integerType -> Symbol.sym -> integer_value =
  assert false (* TODO *)
let integer_ival: Nat_big_num.num -> integer_value =
  assert false (* TODO *)
let max_ival: Ctype.integerType -> integer_value =
  assert false (* TODO *)
let min_ival: Ctype.integerType -> integer_value =
  assert false (* TODO *)
let op_ival: MC.integer_operator -> integer_value -> integer_value -> integer_value =
  assert false (* TODO *)
let offsetof_ival: (Symbol.sym, Ctype.tag_definition) Pmap.map -> Symbol.sym -> Symbol.identifier -> integer_value =
  assert false (* TODO *)

let sizeof_ival: Ctype.ctype -> integer_value =
  assert false (* TODO *)
let alignof_ival: Ctype.ctype -> integer_value =
  assert false (* TODO *)

let bitwise_complement_ival: Ctype.integerType -> integer_value -> integer_value =
  assert false (* TODO *)
let bitwise_and_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value =
  assert false (* TODO *)
let bitwise_or_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value =
  assert false (* TODO *)
let bitwise_xor_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value =
  assert false (* TODO *)

let case_integer_value: (* TODO: expose more ctors *)
  integer_value ->
  (Nat_big_num.num -> 'a) ->
  (unit -> 'a) ->
  'a =
  assert false (* TODO *)

let is_specified_ival: integer_value -> bool =
  assert false (* TODO *)

(* Predicats on integer values *)
let eq_ival: mem_state option -> integer_value -> integer_value -> bool option =
  assert false (* TODO *)
let lt_ival: mem_state option -> integer_value -> integer_value -> bool option =
  assert false (* TODO *)
let le_ival: mem_state option -> integer_value -> integer_value -> bool option =
  assert false (* TODO *)

let eval_integer_value: integer_value -> Nat_big_num.num option =
  assert false (* TODO *)

(* Floating value constructors *)
let zero_fval: floating_value =
  assert false (* TODO *)
let one_fval: floating_value =
  assert false (* TODO *)
let str_fval: string -> floating_value =
  assert false (* TODO *)

(* Floating value destructors *)
let case_fval: floating_value -> (unit -> 'a) -> (float -> 'a) -> 'a =
  assert false (* TODO *)

(* Predicates on floating values *)
let op_fval: MC.floating_operator -> floating_value -> floating_value -> floating_value =
  assert false (* TODO *)
let eq_fval: floating_value -> floating_value -> bool =
  assert false (* TODO *)
let lt_fval: floating_value -> floating_value -> bool =
  assert false (* TODO *)
let le_fval: floating_value -> floating_value -> bool =
  assert false (* TODO *)

(* Integer <-> Floating casting constructors *)
let fvfromint: integer_value -> floating_value =
  assert false (* TODO *)
let ivfromfloat: Ctype.integerType -> floating_value -> integer_value =
  assert false (* TODO *)



(* Memory value constructors *)
(*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
let unspecified_mval: Ctype.ctype -> mem_value =
  assert false (* TODO *)
let integer_value_mval: Ctype.integerType -> integer_value -> mem_value =
  assert false (* TODO *)
let floating_value_mval: Ctype.floatingType -> floating_value -> mem_value =
  assert false (* TODO *)
let pointer_mval: Ctype.ctype -> pointer_value -> mem_value =
  assert false (* TODO *)
let array_mval: mem_value list -> mem_value =
  assert false (* TODO *)
let struct_mval: Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> mem_value =
  assert false (* TODO *)
let union_mval: Symbol.sym -> Symbol.identifier -> mem_value -> mem_value =
  assert false (* TODO *)

(* Memory value destructor *)
let case_mem_value:
  mem_value ->
  (Ctype.ctype -> 'a) -> (* unspecified case *)
  (Ctype.integerType -> Symbol.sym -> 'a) -> (* concurrency read case *)
  (Ctype.integerType -> integer_value -> 'a) ->
  (Ctype.floatingType -> floating_value -> 'a) ->
  (Ctype.ctype -> pointer_value -> 'a) ->
  (mem_value list -> 'a) ->
  (Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> 'a) ->
  (Symbol.sym -> Symbol.identifier -> mem_value -> 'a) ->
  'a =
  assert false (* TODO *)


(* For race detection *)
let sequencePoint: unit memM =
  return ()

(* pretty printing *)
let pp_pointer_value: pointer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_integer_value: integer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_integer_value_for_core: integer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_mem_value: mem_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_pretty_pointer_value: pointer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document =
  fun _ -> assert false (* TODO *)

let serialise_mem_state: Digest.t -> mem_state -> Json.json =
  fun _ _ -> assert false (* TODO *)


let string_of_integer_value: integer_value -> string =
  fun _ -> assert false (* TODO *)
let string_of_mem_value: mem_value -> string =
  fun _ -> assert false (* TODO *)
