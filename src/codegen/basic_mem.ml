(* This is a basic memory model, it simply map pointer to values *)

open Util
open Core_ctype
open Nat_big_num

exception Error of string

type impl_mem_value =
  | Integer of num option
  | Pointer of num option
  | Array of impl_mem_value list
  | Struct of Symbol.sym * (Cabs.cabs_identifier * impl_mem_value) list
  | Union of Symbol.sym * Cabs.cabs_identifier * impl_mem_value

type impl_pointer_value = num option
type impl_integer_value = num option
type impl_floating_value = unit (* not supported *)
type impl_footprint = unit (* not supported *)

(* footprint -> footprint -> bool *)
let impl_do_overlap = (=)

type impl_mem_state = (num, impl_mem_value) Pmap.map

type 'a impl_memM = MemM of (impl_mem_state -> 'a * impl_mem_state)

(* unit memM *)
let impl_sequencePoint = MemM (fun s -> ((), s))

(* mem_state *)
let impl_initial_mem_state = Pmap.empty compare

(* 'a -> 'a memM *)
let impl_return x = MemM (fun s -> (x, s))

(* 'a memM -> ('a -> 'b memM) -> 'b memM *)
let impl_bind (MemM m) f =
  MemM begin fun s ->
    let (x, s') = m s in
    let MemM mf = f x in
    mf s'
  end

(* value -> string *)
let rec impl_prettyStringFromMem_value = function
  | Pointer p -> Option.case to_string (fun _ -> "Unspecified") p
  | Integer n ->  Option.case to_string (fun _ -> "Unspecified") n
  | Array mvs ->
    let arr_str = List.map impl_prettyStringFromMem_value mvs in
    "[" ^ String.concat ", " arr_str  ^ "]"
  | _ -> raise $ Error "todo pretty string from mem value"

(* 'a memM -> mem_state -> (mem_error, ('a, mem_state) Either.eihter) list *)
let impl_runMem (MemM m) s = [Either.Right (m s)]

(* ctype0 -> pointer_value *)
let impl_null_ptrval c = Some zero

(* sym -> pointer_value *)
let impl_fun_ptrval s =
  raise $ Unsupported "Pointer to function currently not supported for basic memory model."

let lift_binop v op x y =
  match (x, y) with
  | (None, _)
  | (_, None) -> v
  | (Some n, Some m) -> op n m

let lift_bool_binop = lift_binop false

(* pointer -> pointer -> bool memM *)
let impl_eq_ptrval p q = impl_return $ lift_bool_binop (=) p q
let impl_ne_ptrval p q = impl_return $ lift_bool_binop (!=) p q
let impl_lt_ptrval p q = impl_return $ lift_bool_binop less p q
let impl_gt_ptrval p q = impl_return $ lift_bool_binop greater p q
let impl_le_ptrval p q = impl_return $ lift_bool_binop less_equal p q
let impl_ge_ptrval p q = impl_return $ lift_bool_binop greater_equal p q

(* pointer -> pointer -> int *)
let impl_diff_ptrval p q =
  match (p, q) with
  | (None, _)
  | (_, None) -> Some zero
  | (Some n, Some m) -> Some (sub n m)

(* ctype -> integerType -> pointer -> int memM *)
let impl_intcast_ptrval c i p = impl_return p

(* pointer -> bool *)
let impl_validForDeref_ptrval p =
  raise $ Unsupported "Valid for deref operation currently not support for basic mempry model."

(* pointer -> ctype -> int -> pointer *)
let impl_array_shift_ptrval p c i = p

(* pointer -> sym -> cabs_identifier -> pointer *)
let impl_member_shift_ptrval p s i = p

(* int -> sym -> int *)
let impl_concurRead_ival _ _ =
  raise $ Unsupported "Concurrent reads not supported in basic memory model."

(* big_num -> int *)
let impl_integer_ival n = Some n

(* integertype -> int *)
let impl_max_ival it = Some zero
let impl_min_ival it = Some zero

(* integer_operator -> int -> int -> int *)
let impl_op_ival op x y = x

(* sym -> cabs_id -> int *)
let impl_offsetof_ival s c = Some zero

(* ctype -> int *)
let impl_sizeof_ival c = Some zero
let impl_alignof_ival c = Some zero

(* int -> (bignum -> 'a) -> (unit -> 'a) -> 'a *)
let impl_case_integer_value n f g = Option.case f g n

(* int -> bool *)
let impl_is_specified_ival : impl_integer_value -> bool =
  Option.case (fun _ -> true) (fun _ -> false)

(* mem_state option -> int -> int -> bool option *)
let impl_eq_ival _ m n = Some (lift_bool_binop (=) m n)
let impl_lt_ival _ m n = Some (lift_bool_binop less m n)
let impl_le_ival _ m n = Some (lift_bool_binop less_equal m n)
let impl_gt_ival _ m n = Some (lift_bool_binop greater m n)
let impl_ge_ival _ m n = Some (lift_bool_binop greater_equal m n)

(* ctype -> ctype -> int -> pointer memM *)
let impl_ptrcast_ival _ _ n = impl_return n

(* ctype -> mem_value *)
let impl_unspecified_mval c = Integer None

(* integertype -> int -> mem_value *)
let impl_integer_value_mval it n = Integer n

(* floatingtype -> float -> mem_value *)
let impl_floating_value_mval ft f =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* ctype pointer -> mem_value *)
let impl_pointer_mval c p = Pointer p

(* mem_value list -> mem_value *)
let impl_array_mval vs = Array vs

(* sym -> (cabs_id * mem_value) list -> mem_value *)
let impl_struct_mval s mvs =
  raise $ Error "todo struct"

(* sym -> cabs_id -> mem_value -> mem_value *)
let impl_union_mval s c mv =
  raise $ Error "todo union"

(* mem_value -> (ctype -> 'a) ->
   (integertype -> int -> 'a) ->
   (floatingtype -> float -> 'a) ->
   (ctype -> pointer -> 'a) ->
   (mem_value list -> 'a) ->
   (sym -> (cid * mem_value) list -> 'a)
   (sym -> cid -> mem_value -> 'a) -> 'a *)
let impl_case_mem_value m caseUnspec caseInt caseFloat casePointer caseArray
    caseStruct caseUnion =
  match m with
  | Integer None
  | Pointer None -> caseUnspec Void0
  | Integer n -> caseInt (AilTypes.Signed AilTypes.Int_) n
  | Pointer p -> casePointer Void0 p
  | Array mvs -> caseArray mvs
  | Struct (s, mvs) -> caseStruct s mvs
  | Union (s, cid, mv) -> caseUnion s cid mv

(* float -> (unit -> 'a) -> (string -> 'a) -> 'a *)
let impl_case_fval n f g =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* float *)
let impl_zero_fval =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* string -> float *)
let impl_str_fval _ =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* integer -> prefix -> int -> ctype -> (pointer) memM *)
let impl_allocate_static _ _ (Some n) _ =
  MemM (fun s -> (Some n, Pmap.add n (Integer None) s))

(* integer -> prefix -> int -> int -> (pointer) memM *)
let impl_allocate_dynamic _ _ (Some n) _ =
  MemM (fun s -> (Some n, Pmap.add n (Integer None) s))

let throw_error_pointer f = function
  | None -> raise $ Error "Dereferecing an unspecified pointer"
  | Some n ->
    if n = zero then
      raise $ Error "Derefercing a null pointer"
    else f n

(* pointer -> unit memM *)
let impl_kill =
  let kill addr = MemM (fun s -> ((), Pmap.remove addr s)) in
  throw_error_pointer kill

(* ctype -> pointer -> (int*mem_value) memM *)
let impl_load _ =
  let load addr = MemM (fun s -> ((0, Pmap.find addr s), s)) in
  throw_error_pointer load

(* ctype -> pointer -> mem_value -> (int) memM *)
let impl_store _ p mv =
  let store addr = MemM (fun s -> (0, Pmap.add addr mv s)) in
  throw_error_pointer store p

(* int -> bignum option *)
let impl_eval_integer_value = id

type impl_mem_constraint2 = unit
let impl_constraint_eqIV _ _ =
  raise $ Unsupported "Constrains not supported in basic memory model."
let impl_constraint_neIV _ _ =
  raise $ Unsupported "Constrains not supported in basic memory model."
let impl_constraint_ltIV _ _ =
  raise $ Unsupported "Constrains not supported in basic memory model."
let impl_constraint_leIV _ _ =
  raise $ Unsupported "Constrains not supported in basic memory model."

let fake_mem_value_eq = (=)
let fake_pointer_value_eq = (=)
