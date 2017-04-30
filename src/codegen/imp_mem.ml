(* This memory model uses a imperative hash table *)

open Util
open Core_ctype
open AilTypes
open Nat_big_num
open Mem_common

exception Error of string

type impl_mem_value =
  | Integer of (integerType * num option)
  | Pointer of (ctype0 * num option)
  | Array of impl_mem_value list
  | Struct of Symbol.sym * (Cabs.cabs_identifier * impl_mem_value) list
  | Union of Symbol.sym * Cabs.cabs_identifier * impl_mem_value

type impl_integer_value = (integerType * num option)
type impl_pointer_value = (ctype0 * num option)
type impl_floating_value = unit (* not supported *)
type impl_footprint = unit (* not supported *)

(* footprint -> footprint -> bool *)
let impl_do_overlap = (=)

(* this is dirty, but it is just to see the impact when using mutable states *)
let state : (num, impl_mem_value) Hashtbl.t = Hashtbl.create 100
type impl_mem_state = unit

type 'a impl_memM = 'a

(* value -> string *)
let rec impl_prettyStringFromMem_value = function
  | Pointer (_,p) -> Option.case to_string (fun _ -> "Unspecified") p
  | Integer (_,n) ->  Option.case to_string (fun _ -> "Unspecified") n
  | Array mvs ->
    let arr_str = List.map impl_prettyStringFromMem_value mvs in
    "[" ^ String.concat ", " arr_str  ^ "]"
  | _ -> raise $ Error "todo pretty string from mem value"

(* unit memM *)
let impl_sequencePoint = ()

(* mem_state *)
let impl_initial_mem_state = ()

(* 'a -> 'a memM *)
let impl_return x = x

(* 'a memM -> ('a -> 'b memM) -> 'b memM *)
let impl_bind x f = f x

(* 'a memM -> mem_state -> (mem_error, ('a, mem_state) Either.eihter) list *)
let impl_runMem n _ = [Either.Right (n, ())]

(* ctype0 -> pointer_value *)
let impl_null_ptrval c = (c, Some zero)

(* sym -> pointer_value *)
let impl_fun_ptrval s =
  raise $ Unsupported "Pointer to function currently not supported for basic memory model."

let lift_bool_binop op (t1, x) (t2, y) =
  match (x, y) with
  | (None, _)
  | (_, None) -> false
  | (Some n, Some m) -> op n m

(* pointer -> pointer -> bool memM *)
let impl_eq_ptrval p q = lift_bool_binop (=) p q
let impl_ne_ptrval p q = lift_bool_binop (!=) p q
let impl_lt_ptrval p q = lift_bool_binop less p q
let impl_gt_ptrval p q = lift_bool_binop greater p q
let impl_le_ptrval p q = lift_bool_binop less_equal p q
let impl_ge_ptrval p q = lift_bool_binop greater_equal p q

(* pointer -> pointer -> int *)
let impl_diff_ptrval (_, p) (_, q) =
  match (p, q) with
  | (None, _)
  | (_, None) -> (Signed Int_, Some zero)
  | (Some n, Some m) -> (Signed Int_, Some (sub n m))

(* ctype -> integerType -> pointer -> int memM *)
let impl_intcast_ptrval c i (_,n) = (i,n)

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
let impl_integer_ival n = (Signed Int_, Some n)

(* integertype -> int *)
(* TODO: this is implementation defined *)
let impl_max_ival it = impl_integer_ival $ of_int max_int
let impl_min_ival it = impl_integer_ival zero

let lift_binop op x y =
  match (x, y) with
  | (None, _)
  | (_, None) -> None
  | (Some n, Some m) -> Some (op n m)

(* integer_operator -> int -> int -> int *)
let impl_op_ival op (t1, x) (t2, y) =
  let binop = match op with
    | IntAdd -> lift_binop add
    | IntSub -> lift_binop sub
    | IntMul -> lift_binop mul
    | IntDiv -> lift_binop div
    | IntRem_t -> lift_binop integerRem_t
    | IntRem_f -> lift_binop integerRem_f
    | IntExp -> lift_binop (fun x y -> pow_int x (to_int y))
  in (t1, binop x y)

(* sym -> cabs_id -> int *)
let impl_offsetof_ival s c = (Signed Int_, Some zero)

(* ctype -> int *)
let impl_sizeof_ival c = (Signed Int_, Some zero)
let impl_alignof_ival c = (Signed Int_, Some zero)

(* int -> (bignum -> 'a) -> (unit -> 'a) -> 'a *)
let impl_case_integer_value (_,n) f g = Option.case f g n

(* int -> bool *)
let impl_is_specified_ival (_, x) =
  Option.case (fun _ -> true) (fun _ -> false) x

(* mem_state option -> int -> int -> bool option *)
let impl_eq_ival _ m n = Some (lift_bool_binop (=) m n)
let impl_lt_ival _ m n = Some (lift_bool_binop less m n)
let impl_le_ival _ m n = Some (lift_bool_binop less_equal m n)
let impl_gt_ival _ m n = Some (lift_bool_binop greater m n)
let impl_ge_ival _ m n = Some (lift_bool_binop greater_equal m n)

(* ctype -> ctype -> int -> pointer memM *)
let impl_ptrcast_ival c _ (_,n) = impl_return (c, n)

(* ctype -> mem_value *)
let impl_unspecified_mval c = Pointer (impl_null_ptrval c)

(* integertype -> int -> mem_value *)
let impl_integer_value_mval it (_, n) = Integer (it, n)

(* floatingtype -> float -> mem_value *)
let impl_floating_value_mval ft f =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* ctype -> pointer -> mem_value *)
let impl_pointer_mval c (_, p) = Pointer (c, p)

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
  | Integer (_, None)
  | Pointer (_, None) -> caseUnspec Void0
  | Integer (it,n) -> caseInt it (it,n)
  | Pointer (c,p) -> casePointer c (c,p)
  | Array mvs -> caseArray mvs
  | Struct (s, mvs) -> caseStruct s mvs
  | Union (s, cid, mv) -> caseUnion s cid mv

(* float -> (unit -> 'a) -> (string -> 'a) -> 'a *)
let impl_case_fval n f g =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* float *)
let impl_zero_fval = ()

(* string -> float *)
let impl_str_fval _ =
  raise $ Unsupported "Floats are not supported in basic memory model."

(* integer -> prefix -> int -> ctype -> (pointer) memM *)
let impl_allocate_static _ pre al c =
  let n = of_int $ Hashtbl.hash pre in
  Hashtbl.add state n (Integer al);
  (c, Some n)

(* integer -> prefix -> int -> int -> (pointer) memM *)
let impl_allocate_dynamic _ pre al _ =
  let n = of_int $ Hashtbl.hash pre in
  Hashtbl.add state n (Integer al);
  (Void0, Some n)

let throw_error_pointer f (_, p) =
  match p with
  | None -> raise $ Error "Dereferencing an unspecified pointer"
  | Some n -> f n

(* pointer -> unit memM *)
let impl_kill (_, p) =
  match p with
  | None -> raise $ Error "Dereferencing an unspecified pointer"
  | Some n -> Hashtbl.remove state n

(* ctype -> pointer -> (int*mem_value) memM *)
let impl_load _ (_, p) =
  match p with
  | None -> raise $ Error "Dereferencing an unspecified pointer"
  | Some n -> (0, Hashtbl.find state n)

(* ctype -> pointer -> mem_value -> (int) memM *)
let impl_store _ (_, p) mv =
  match p with
  | None -> raise $ Error "Dereferencing an unspecified pointer"
  | Some n -> Hashtbl.replace state n mv; 0

(* int -> bignum option *)
let impl_eval_integer_value (_, n) = n

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
let fake_pointer_value_eq (_,x) (_,y) = (x = y)

