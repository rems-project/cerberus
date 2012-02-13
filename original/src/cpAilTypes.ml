open CpPervasives

module A = CpAil
module M = BatMap

let empty = BatSet.empty

(* TODO We need to deal with type qualifiers! *)

let lift_int f_int otherwise = function
  | A.BASE (_, A.INTEGER i) -> f_int i
  | _ -> otherwise

let is_unsigned_int = function
  | A.BOOL -> true
  | A.UNSIGNED _ -> true
  | A.SIGNED _ -> false

let is_signed_int = function
  | A.SIGNED _ -> true
  | A.UNSIGNED _ -> false
  | A.BOOL -> false

let is_unsigned_integer = lift_int is_unsigned_int false
let is_signed_integer = lift_int is_signed_int false

let is_char = function
  | A.BASE (_, A.CHAR) -> true
  | _ -> false

let is_void = function
  | A.BASE (_, A.VOID) -> true
  | _ -> false

let is_character = function
  | A.BASE (_, A.INTEGER (A.UNSIGNED A.ICHAR)) -> true
  | A.BASE (_, A.INTEGER (A.SIGNED   A.ICHAR)) -> true
  | A.BASE (_, A.CHAR) -> true
  | _ -> false

(* TODO No support for floating point, enumerated, structure, union or atomic
   types. *)
let is_real_floating t = false
let is_complex t = false
let is_floating t = is_real_floating t || is_complex t
let is_enumerated t = false

let is_basic t =
  is_char t
  || is_unsigned_integer t
  || is_signed_integer t
  || is_floating t

let is_integer t =
  is_char t
  || is_signed_integer t
  || is_unsigned_integer t
  || is_enumerated t

let is_real t = is_integer t || is_real_floating t
let is_arithmetic t = is_integer t || is_floating t

let is_structure t = false
let is_union t = false
let is_enum t = false
let is_atomic t = false

let is_pointer = function
  | A.POINTER _ -> true
  | _ -> false

let is_function = function
  | A.FUNCTION _ -> true
  | _ -> false

let is_array = function
  | A.ARRAY _ -> true
  | _ -> false

let is_derived t =
  is_array t
  || is_structure t
  || is_union t
  || is_function t
  || is_pointer t
  || is_atomic t

let is_scalar t = is_arithmetic t || is_pointer t

let is_aggregate t = is_array t || is_structure t

let is_unqualified = function
  | A.BASE (q, _) -> BatSet.is_empty q
  | A.POINTER (q, _) -> BatSet.is_empty q
  | _ -> true

let is_object = function
  | A.FUNCTION _ -> false
  | _ -> true

let is_complete_object t =
  match t with
  | A.BASE (_, A.VOID) -> false
  | _ -> is_object t

let is_pointer_to_object = function
  | A.POINTER (_, t) -> is_object t
  | _ -> false

let is_pointer_to_void = function
  | A.POINTER (_, t) -> is_void t
  | _ -> false

let is_pointer_to_function = function
  | A.POINTER (_, t) -> is_function t
  | _ -> false

let is_pointer_to_complete_object = function
  | A.POINTER (_, t) -> is_complete_object t
  | _ -> false 

let compatible_basic s1 s2 = (s1 = s2)

let rec compatible type1 type2 =
  match type1, type2 with
  | A.BASE (q1, s1), A.BASE (q2, s2) ->
      BatSet.equal q1 q2 && compatible_basic s1 s2
  | A.POINTER (q1, t1), A.POINTER (q2, t2) ->
      BatSet.equal q1 q2 && compatible t1 t2
  | A.ARRAY (t1, size1), A.ARRAY (t2, size2) ->
      size1 = size2 && compatible t1 t2
  | A.FUNCTION (t1, args1), A.FUNCTION (t2, args2) ->
      compatible t1 t2
      && List.length args1 = List.length args2
      && BatList.for_all2 compatible args1 args2
  | _ -> false

let qualifiers = function
  | A.POINTER (q, _) -> q
  | A.BASE (q, _) -> q
  | A.FUNCTION _ | A.ARRAY _ -> BatSet.empty

let merge_qualifiers t1 t2 = BatSet.union (qualifiers t1) (qualifiers t2)

let include_qualifiers t q =
  match t with
  | A.BASE (q', b') -> A.BASE (BatSet.union q q', b')
  | A.POINTER (q', t') -> A.POINTER (BatSet.union q q', t')
  | A.FUNCTION _ | A.ARRAY _ -> t

let rec unqualify t =
  let f = unqualify in
  match t with
  | A.BASE (_, b) -> A.BASE (empty, b)
  | A.POINTER (_, t') -> A.POINTER (empty, f t')
  | _ -> CpAilRewrite.map_type f t

let rec eq t1 t2 =
  match t1, t2 with
  | A.BASE    (_, b1), A.BASE    (_, b2) -> b1 = b2
  | A.POINTER (_, t1), A.POINTER (_, t2) -> eq t1 t2
  | A.FUNCTION (t1, ts1), A.FUNCTION (t2, ts2) ->
      eq t1 t2 && BatList.for_all2 eq ts1 ts2
  | A.ARRAY (t1, size1), A.ARRAY (t2, size2) ->
      eq t1 t2 && size1 = size2
  | _ -> false

let eq_rank i1 i2 =
  i1 = i2 || match i1, i2 with
  | A.SIGNED   b1, A.UNSIGNED b2 -> b1 = b2
  | A.UNSIGNED b1, A.SIGNED   b2 -> b1 = b2
  | _ -> false

let rec leq_rank i1 i2 = eq_rank i1 i2 || lt_rank i1 i2

(* We exploit the "linear" transitivity to avoid listing all pairs/building the
   transitive closure. *)
and lt_rank i1 i2 =
  let leq = leq_rank i1 in
  match i2 with
  | A.BOOL               -> false
  | A.SIGNED A.ICHAR     -> leq A.BOOL
  | A.SIGNED A.SHORT     -> leq (A.SIGNED A.ICHAR)
  | A.SIGNED A.INT       -> leq (A.SIGNED A.SHORT)
  | A.SIGNED A.LONG      -> leq (A.SIGNED A.INT)
  | A.SIGNED A.LONG_LONG -> leq (A.SIGNED A.LONG)
  (* Corresponding signed and unsigned integers have the same rank. *)
  | A.UNSIGNED b         -> lt_rank i1 (A.SIGNED b)

let leq_prec ?(omega = CpAilConstraint.empty) i1 i2 =
  let module AC = CpAilConstraint in
  match i1, i2 with
  | A.BOOL, _ -> true
  | _, A.BOOL -> false
  | A.SIGNED _,    A.SIGNED _
  | A.UNSIGNED _,  A.UNSIGNED _
  | A.SIGNED _,    A.UNSIGNED _
    when leq_rank i1 i2 -> true
  | A.SIGNED _,   A.SIGNED _ 
  | A.SIGNED _,   A.UNSIGNED _
  | A.UNSIGNED _, A.SIGNED _
  | A.UNSIGNED _, A.UNSIGNED _ ->
      raise_error "Implementation defined!\n"

(* TODO Test exhaustively for termination. *)
let rec common_int i1 i2 =
  if i1 = i2 then i1 else
    match i1, i2 with
    | A.SIGNED _, A.SIGNED _
    | (A.BOOL | A.UNSIGNED _), (A.BOOL | A.UNSIGNED _)
      when lt_rank i1 i2 -> i2
    | A.SIGNED _, (A.BOOL | A.UNSIGNED _)
      when leq_rank i1 i2 -> i2
    | A.SIGNED _, (A.BOOL | A.UNSIGNED _)
      when leq_prec i2 i1 -> i1
    | A.SIGNED b1, (A.BOOL | A.UNSIGNED _) -> A.UNSIGNED b1
    | _ -> common_int i2 i1

let rec common t1 t2 =
  assert(is_arithmetic t1 && is_arithmetic t2);
  match t1, t2 with
  | A.BASE (_, A.INTEGER i1), A.BASE (_, A.INTEGER i2) ->
      A.BASE (empty, A.INTEGER (common_int i1 i2))
  | _ ->
      let msg = "Non-integer type.\n" in
      invalid_arg msg

let promote_int i =
  let s_int = A.SIGNED A.INT in
  let u_int = A.UNSIGNED A.INT in
  match i with
  (* "Other than int or signed int." *)
  | A.SIGNED A.INT | A.UNSIGNED A.INT -> i
  | A.BOOL | A.SIGNED _ | A.UNSIGNED _ when leq_rank i s_int ->
      if leq_prec i s_int then s_int else u_int
  | A.BOOL | A.SIGNED _ | A.UNSIGNED _ -> i

let promote t =
  match t with
  | A.BASE (q, A.INTEGER i) ->
      A.BASE (q, A.INTEGER (promote_int i))
  | _ -> t

let usual_arithmetic t1 t2 = common (promote t1) (promote t2)

let is_complete t =
  match t with
  | A.BASE _
  | A.POINTER _ -> is_complete_object t
  | A.ARRAY _ -> true
  (* TODO Just a guess. C standard doesn't seem to say about completeness of
     function types. *)
  | A.FUNCTION _ -> false

let is_incomplete t = not (is_complete t)

let is_const = function
  | A.BASE (q, _)
  | A.POINTER (q, _) -> BatSet.mem Cabs.CONST q
  | A.ARRAY _ | A.FUNCTION _ -> false

let is_modifiable t =
  not (is_array t)
  && not (is_incomplete t)
  && not (is_const t)

let is_bool = function
  | A.BASE (_, A.INTEGER A.BOOL) -> true
  | _ -> false

let base_of_pointer = function
  | A.POINTER (_, t) -> t
  | _ -> invalid_arg "Not a pointer type."

let base_of_array = function
  | A.ARRAY (t, _) -> t
  | _ -> invalid_arg "Not a pointer type."

let size_of_array = function
  | A.ARRAY (_, s) -> s
  | _ -> invalid_arg "Not a pointer type."

let function_return = function
  | A.FUNCTION (t, _) -> t
  | _ -> invalid_arg "Not a function type."

let function_parameters = function
  | A.FUNCTION (_, ts) -> ts
  | _ -> invalid_arg "Not a function type."

let well_formed t = true

let composite t1 t2 =
  if compatible t1 t2 then
    t1
  else invalid_arg "A composite type can only be constructed from two \
                    compatible types."

let pointer_convert t =
  match t with
  | A.FUNCTION _    -> A.POINTER (empty, t)
  | A.ARRAY (t', _) -> A.POINTER (empty, t')
  | _ -> t

let lvalue_convert t =
  if is_incomplete t && not (is_array t) then
    invalid_arg "Incomplete non-array type."
  else unqualify t

let is_lvalue = function
  | A.Lvalue _ -> true
  | A.Exp    _ -> false

let is_unsigned_of t1 t2 =
  match t1, t2 with
  | A.BASE (_, A.INTEGER (A.SIGNED i1)), A.BASE (_, A.INTEGER (A.UNSIGNED i2))
    when i1 = i2 -> true
  | _ -> false

let is_signed_of t1 t2 =
  match t1, t2 with
  | A.BASE (_, A.INTEGER (A.UNSIGNED i1)), A.BASE (_, A.INTEGER (A.SIGNED i2))
    when i1 = i2 -> true
  | _ -> false
