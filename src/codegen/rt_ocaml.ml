(* Created by Victor Gomes 2017-03-10 *)

open Util
module M = Mem
module T = AilTypes
module C = Core_ctype

(* Undefined Behaviour *)
exception Undefined of string
exception Error of string

let (>>=) = M.bind0
let return = M.return0

(* Keep track of the last memory operation, for error display *)
type memop = Store | Load | Create | Alloc | None
let last_memop = ref None

let show_memop = function
  | Store -> "store"
  | Load -> "load"
  | Create -> "create"
  | Alloc -> "alloc"
  | None -> raise (Error "unknown last memop")

(* Runtime flags *)
let batch =
  try ignore (Sys.getenv "CERB_BATCH"); true
  with _ -> false

(* stdout if in batch mode *)
let stdout = ref ""

let null_ptr = M.null_ptrval C.Void0

let position fname lnum bol cnum = {
  Lexing.pos_fname = fname;
  Lexing.pos_lnum = lnum;
  Lexing.pos_bol = bol;
  Lexing.pos_cnum = cnum;
}

(* Non deterministic choice *)

let nd n xs =
  Random.self_init ();
  Random.int n |> List.nth xs

(* IV min/max wraps *)

let ivctor memf errmsg = function
  | C.Basic0 (T.Integer it) -> memf it
  | _ -> raise (Error errmsg)

let ivmin = ivctor M.min_ival "ivmin"

let ivmax = ivctor M.max_ival "ivmax"

(* Ail types *)

let ail_qualifier (c, r, v, a) =
  { AilTypes.const = c;
    AilTypes.restrict = r;
    AilTypes.volatile = v;
    AilTypes.atomic = a;
  }

let is_scalar ty =
  AilTypesAux.is_scalar (Core_aux.unproj_ctype ty)

let is_integer ty =
  AilTypesAux.is_integer (Core_aux.unproj_ctype ty)

let is_signed ty =
  AilTypesAux.is_signed_integer_type (Core_aux.unproj_ctype ty)

let is_unsigned ty =
  AilTypesAux.is_unsigned_integer_type (Core_aux.unproj_ctype ty)

(* Loaded - Specified and unspecified values *)

type 'a loaded =
  | Specified of 'a
  | Unspecified of C.ctype0

let specified x = Specified x
let unspecified x = Unspecified x

let case_loaded f g = function
  | Specified x -> f x
  | Unspecified cty -> g cty

exception Label of string * (M.integer_value) loaded

(* Cast from memory values *)

let get_integer m =
  let terr _ _ = raise (Error "Type mismatch, expecting integer values.") in
  M.case_mem_value m unspecified terr (fun _ -> specified)
    terr terr (terr()) terr terr

let get_pointer m =
  let terr _ _ = raise (Error "Type mismatch, expecting pointer values.") in
  M.case_mem_value m unspecified terr terr terr (fun _ p -> specified p)
    (terr()) terr terr

let get_array m =
  let terr _ _ = raise (Error "Type mismatch, expecting array.") in
  M.case_mem_value m unspecified terr terr terr terr
    specified terr terr

let get_struct m =
  let terr _ _ = raise (Error "Type mismatch, expecting struct.") in
  M.case_mem_value m unspecified terr terr terr terr (terr())
    (fun _ -> specified) terr

let get_union m =
  let terr _ _ = raise (Error "Type mismatch, expecting union.") in
  M.case_mem_value m unspecified terr terr terr terr (terr())
    terr (fun _ cid m -> Specified (cid, m))

(* Cast to memory values *)

let mk_int s = M.integer_ival (Nat_big_num.of_string s)

(* Binary operations wrap *)

let add = M.op_ival M.IntAdd
let sub = M.op_ival M.IntSub
let mul = M.op_ival M.IntMul
let div = M.op_ival M.IntDiv
let remt = M.op_ival M.IntRem_t
let remf = M.op_ival M.IntRem_f
let exp = M.op_ival M.IntExp

let eq n m = Option.get (M.eq_ival (Some M.initial_mem_state) n m)
let lt n m = Option.get (M.lt_ival (Some M.initial_mem_state) n m)
let gt n m = Option.get (M.lt_ival (Some M.initial_mem_state) m n)
let le n m = Option.get (M.le_ival (Some M.initial_mem_state) n m)
let ge n m = Option.get (M.le_ival (Some M.initial_mem_state) m n)

let eq_ptrval p q = M.eq_ptrval p q
let ne_ptrval p q = M.ne_ptrval p q
let ge_ptrval p q = M.ge_ptrval p q
let lt_ptrval p q = M.lt_ptrval p q
let gt_ptrval p q = M.gt_ptrval p q
let le_ptrval p q = M.le_ptrval p q
let diff_ptrval p q = M.diff_ptrval p q
let valid_for_deref_ptrval p = return $ M.validForDeref_ptrval p

(* Memory actions wrap *)

let case_loaded_mval f = case_loaded f M.unspecified_mval

let create pre al ty =
  last_memop := Create;
  M.allocate_static 0 pre al ty

let alloc pre al n =
  last_memop := Alloc;
  M.allocate_dynamic 0 pre al n

let load cty ret e =
  last_memop := Load;
  M.load cty e >>= return % ret % snd

let load_integer ity =
  load (C.Basic0 (T.Integer ity)) get_integer

let load_pointer q cty =
  load (C.Pointer0 (q, cty)) get_pointer

let load_array q cty size =
  load (C.Array0 (q, cty, size)) get_array

let load_struct s =
  load (C.Struct0 s) get_struct

let load_union s =
  load (C.Union0 s) get_union

let store f ty e1 e2 =
  last_memop := Store;
  M.store ty e1 $ case_loaded_mval f e2

let store_integer ity =
  store (M.integer_value_mval ity) (C.Basic0 (T.Integer ity))

let store_pointer q cty =
  store (M.pointer_mval cty) (C.Pointer0 (q, cty))

let store_struct s =
  store (M.struct_mval s) (C.Struct0 s)

let store_union s cid =
  store (M.union_mval s cid) (C.Union0 s)

let store_array_of conv cty size q =
  let array_mval e = M.array_mval (List.map (case_loaded_mval conv) e)
  in store array_mval (C.Array0 (q, cty, size))

let store_array_of_int ity =
  store_array_of (M.integer_value_mval ity) (C.Basic0 (T.Integer ity))

let store_array_of_ptr q cty =
  store_array_of (M.pointer_mval cty) (C.Pointer0 (q, cty))

(* Printf wrap *)

let printf (conv : C.ctype0 -> M.integer_value -> M.integer_value)
    (xs:M.integer_value list)
    (args:(C.ctype0 * M.pointer_value) list) =
  let encode ival = match Mem_aux.integerFromIntegerValue ival with
    | Some n -> Decode_ocaml.encode_character_constant n
    | None -> Debug_ocaml.error
                "Printf: one of the element of the format array was invalid"
  in
  let eval_conv cty x =
    let terr _ _ = raise (Error "Rt_ocaml.printf: expecting an integer") in
    let n = M.case_mem_value x (terr()) terr (fun _ -> conv cty)
        terr terr (terr()) terr terr
    in Either.Right (Undefined.Defined0
                       (Core.Vloaded (Core.LVspecified (Core.OVinteger n))))
  in
  Output.printf eval_conv (List.rev (List.map encode xs)) args
  >>= begin function
    | Either.Right (Undefined.Defined0 xs) ->
      let n = List.length xs in
      let output = String.init n (List.nth xs) in
      if batch then stdout := !stdout ^ String.escaped output
      else print_string output;
      return (M.integer_ival (Nat_big_num.of_int n))
    | Either.Right (Undefined.Undef (_, xs) ) ->
      raise (Error (String.concat "," 
                      (List.map Undefined.stringFromUndefined_behaviour xs)))
    | Either.Right (Undefined.Error (_, m) ) -> raise (Error m)
    | Either.Left z -> raise (Error (Pp_errors.to_string z))
  end

(* Exit *)

exception Exit of (M.integer_value loaded)

let constraints = "CONSTRS ==> []\nLog[0]\n\nEnd[0]\n"

let print_batch res =
  Printf.printf
    "Defined {value: \"%s\", stdout: \"%s\", blocked: \"false\"}\n%s"
    res !stdout constraints

let print_err_batch e =
  let err = match e with
    | Mem_common.MerrUnitialised str -> "MerrUnitialised \"" ^  (str ^ "\"")
    | Mem_common.MerrInternal str -> "MerrInternal \"" ^  (str ^ "\"")
    | Mem_common.MerrOther str -> "MerrOther \"" ^  (str ^ "\"")
    | Mem_common.MerrReadFromDead -> "MerrReadFromDead"
    | Mem_common.MerrWIP str -> "Memory WIP: " ^ str
  in Printf.printf
    "Killed {msg: memory layout error (%s seq) ==> %s}\n%s"
    (show_memop !last_memop) err constraints

let string_of_specified n =
  Printf.sprintf "Specified(%s)" (Nat_big_num.to_string n)

let string_of_unspec cty =
  Printf.sprintf "Unspecified(\"%s\")" (String_core_ctype.string_of_ctype cty)

let quit f =
  try
    match M.runMem (f (fun x -> raise (Exit x)) ()) M.initial_mem_state with
    | [] -> raise (Error "continuation not raised: no result from runMem")
    | [Either.Left e] -> if batch then print_err_batch e
    | [Either.Right _] ->
      raise (Error "continuation not raised: one result from runMem")
    | _ -> raise (Error "continuation not raised: multiple results from runMem")
  with
  | Exit x ->
    (match x with
     | Specified x ->
       let n = M.eval_integer_value x |> Option.get in
       if batch then print_batch (string_of_specified n);
       exit (Nat_big_num.to_int n)
     | Unspecified cty ->
       if batch then print_batch (string_of_unspec cty);
       exit(-1)
    )

(* Start *)

let set_global (f, x) =
  f return () >>= fun y -> x := y; return ()

let init_globals glbs =
  List.fold_left
    (fun acc (f, x) -> acc >>= fun _ -> set_global (f, x))
    (return ()) glbs

let create_tag_defs_map defs =
  List.fold_left
    (fun m (s, xs) -> Pmap.add s xs m)
    (Pmap.empty Core_fvs.sym_compare) defs

let run tags gls main =
  begin fun cont args ->
    Tags.set_tagDefs (create_tag_defs_map tags);
    init_globals gls
    >>= fun _ -> main cont args
  end |> quit
