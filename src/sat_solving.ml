open Defacto_memory_types2
open Mem_common


module StringSet = Set.Make (String)

type assertions =
  Assertions of int * StringSet.t * string Dlist.dlist


let initial_assertions () =
  Assertions (0, StringSet.empty, Dlist.nil)

(*

(* TODO: yuck, no to state !! *)
let declared_consts : (string StringMap.t) ref =
  ref StringMap.empty

let declare_const str_name str_sort =
  declared_consts := StringMap.add str_name str_sort !declared_consts
*)

(*
let declare_const str_name str_ty =
  vars := Printf.sprintf "(define %s::%s)" str_name str_ty :: !vars
*)

let string_of_address (Address0 (pref, n)) =
  "addr_" ^ string_of_int n

let declare_address (Address0 (pref, _) as addr) (Assertions (n, addrs, xs) as asserts) =
  let addr_str = string_of_address addr in
  if StringSet.mem addr_str addrs then
    asserts
  else
    Assertions (n, addrs, Dlist.cons (Printf.sprintf "(declare-fun %s () Address); %s" addr_str
                                        (Pp_utils.to_plain_string (Pp_symbol.pp_prefix pref))) xs)


open AilTypes
let smt2_from_integerBaseType = function
  | Ichar ->
      "ichar_ibty"
  | Short ->
      "short_ibty"
  | Int_ ->
     "int_ibty"
  | Long ->
     "long_ibty"
  | LongLong ->
     "long_long_ibty"
  | Intmax_t ->
      "intmax_t_ibty"
  | Intptr_t ->
      "intptr_t_ibty"
  | IntN_t n ->
      "int" ^ string_of_int n ^ "_t_ibty"
  | Int_leastN_t n ->
      "int_least" ^ string_of_int n ^ "_t_ibty"
  | Int_fastN_t n ->
      "int_fast" ^ string_of_int n ^ "_t_ibty"

let smt2_from_integerType = function
  | Char ->
      "char_ity"
  | Bool ->
      "bool_ity"
  | Signed ibty ->
      "(Signed_ity " ^ smt2_from_integerBaseType ibty ^ ")"
  | Unsigned ibty ->
      "(Unsigned_ity " ^ smt2_from_integerBaseType ibty ^ ")"
  | Size_t ->
      "size_t_ity"
  | Ptrdiff_t ->
      "ptrdiff_t_ity"
  | IBuiltin _ ->
      failwith "Sat_folving.smt2_from_integerType: TODO IBuiltin"
  | Enum _ ->
      failwith "Sat_folving.smt2_from_integerType: TODO Enum"


let smt2_from_basicType = function
  | Integer ity ->
      "(Integer_bty " ^ smt2_from_integerType ity ^ ")"
  | Floating _ ->
      failwith "Sat_folving.smt2_from_basicType: TODO Floating"

open Core_ctype
let rec smt2_from_ctype = function
  | Void0 ->
      "void_ty"
  | Basic0 bty ->
      "(Basic_ty " ^ smt2_from_basicType bty ^ ")"
  | Array0 (_, elem_ty, None) ->
      failwith "Sat_folving.smt2_from_ctype: TODO Array, None"
  | Array0 (_, elem_ty, Some n) ->
      "(Array_ty " ^ smt2_from_ctype elem_ty ^ " " ^ Nat_big_num.to_string n ^ ")"
  | Function0 _ ->
      failwith "Sat_folving.smt2_from_ctype: TODO Function"
  | Pointer0 (_, ref_ty) ->
      "(Pointer_ty " ^ smt2_from_ctype ref_ty ^ ")"
  | Struct0 _ 
  | Union0 _ ->
      failwith "Sat_folving.smt2_from_ctype: TODO Struct/Union"
  | Atomic0 _ ->
      failwith "Sat_folving.smt2_from_ctype: TODO Atomic"
  | Builtin0 _ ->
      failwith "Sat_folving.smt2_from_ctype: TODO Builtin"


let rec expression_from_integer_value_base = function
  | IVunspecified ->
      "ivunspecified"
  | IVconcurRead (ity, sym) ->
      failwith "Sat_folving.smt2_from_integer_value_base: TODO IVconcurRead"
  | IVconcrete bign ->
      (Nat_big_num.to_string bign)
  | IVaddress alloc_id ->
      string_of_int alloc_id
  | IVfromptr (ty, ity, ptr_val_) ->
      "(ivfromptr " ^ smt2_from_ctype ty ^ " " ^ smt2_from_integerType ity ^ ")"
  | IVop (iop, [ival1_; ival2_]) ->
      let iop_str = match iop with
      | IntAdd -> "+"
      | IntSub -> "-"
      | IntMul -> "*"
      | IntDiv -> "/" (* TODO: div by zero? *)
      | IntRem_t -> failwith "IntRem_t"
      | IntRem_f -> "mod"
      | IntExp -> "^" in
      Printf.sprintf "(%s %s %s)" iop_str
        (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)
  | IVop (_, _) ->
      failwith "Sat_solving.expression_from_integer_value_base, IVop arity error"
  | IVmin ity ->
      "(TODO IVmin)"
  | IVmax ity ->
      "(TODO IVmax)"
  | IVsizeof ty ->
      (match ty with
         | Core_ctype.Array0 (qs, ty, Some n) ->
             Printf.sprintf "(* (sizeof int_ty) %s)" (Nat_big_num.to_string n)(* TODO *)
         | _ ->
            "(sizeof int_ty)") (* TODO *)
  | IValignof ty ->
      "(TODO IValignof)"
  | IVoffsetof (_, _) ->
      "(TODO IVoffsetof)"
  | IVptrdiff (ptr_val1_, ptr_val2_) ->
      "(TODO IVptrdiff)"
  | IVbyteof (ival_, mval) ->
      "(TODO IVbyteof)"
  | IVcomposite ival_s ->
      "(TODO IVcomposite)"
  | IVbitwise (ity, BW_complement ival_) ->
      "(TODO BW_complement)"
  | IVbitwise (ity, BW_AND (ival_1, ival_2)) ->
      "(TODO BW_AND)"
  | IVbitwise (ity, BW_OR (ival_1, ival_2)) ->
      "(TODO BW_OR)"
  | IVbitwise (ity, BW_XOR (ival_1, ival_2)) ->
      "(TODO BW_XOR)"


let assertion_of_memory_constraint = function
  | MC_eqIV (debug_str, ival1_, ival2_) ->
      [Printf.sprintf "(= %s %s)" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_neIV (ival1_, ival2_) ->
      [Printf.sprintf "(not (= %s %s))" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_leIV (ival1_, ival2_) ->
      [Printf.sprintf "(<= %s %s)" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_addr_distinct (addr_a, addr_bs) ->
      List.map (fun addr_b ->
        Printf.sprintf "(not (= %s %s))" (string_of_address addr_a) (string_of_address addr_b)
      ) (Pset.elements addr_bs)



let is_unsat (Assertions (_, _, strs)) =
  let str_problem =
    String.concat "\n" (
      [
        "(declare-sort Address 0)";
        "(declare-sort Ctype 0)";
        "(declare-fun int_ty () Ctype)";
        "(declare-fun sizeof (Ctype) Int)";
        "(assert (forall ((ty Ctype)) (>= (sizeof ty) 1)))"
      ] @
      (*
      StringMap.fold (fun str_name str_sort acc ->
        Printf.sprintf "(declare-fun %s () %s)" str_name str_sort :: acc
      ) !declared_consts *) (List.filter (fun z -> z <> "") (Dlist.toList strs))
    ) in
  Debug_ocaml.print_debug 3 [] (fun () -> "IS UNSAT?\n" ^ str_problem ^ "\n=================================\n");
  let ic, oc = Unix.open_process "z3 -nw -t:100 -smt2 -in" in
  Pervasives.output_string oc (str_problem ^ "\n(check-sat)\n(exit)\n");
  Pervasives.flush oc;
  let buf = Buffer.create 16 in
  (try
    while true do
      Buffer.add_channel buf ic 1
    done
  with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  match Buffer.contents buf with
  | "unsat\n" ->
      true
  | output ->
      Debug_ocaml.print_debug 3 [] (fun () -> "DEBUG Z3 ==> " ^ output);
      false

let add_mem_constraint constr (Assertions (n, addrs, asserts)) =
  Assertions (n+1, addrs, Dlist.append (Dlist.dlist_fromList (List.map (fun z -> Printf.sprintf "(assert %s)" z) (assertion_of_memory_constraint constr))) asserts)


let check constr (Assertions (n, addrs, strs)) =
  Debug_ocaml.print_debug 3 [] (fun () -> "CHECKING [" ^ string_of_int n ^ "]" ^ (Pp_utils.to_plain_string (Pp_defacto_memory.pp_mem_constraint constr)) ^ "\n");
  let assert_strs = assertion_of_memory_constraint constr in
  if is_unsat (Assertions (n, addrs, Dlist.append (Dlist.dlist_fromList (List.map (fun z -> Printf.sprintf "(assert %s)" z) assert_strs)) strs)) then
    (Debug_ocaml.print_debug 3 [] (fun () -> "check returned FALSE");
    Some false)
  else if is_unsat (Assertions (n, addrs, Dlist.append (Dlist.dlist_fromList (List.map (fun z -> Printf.sprintf "(assert (not %s))" z) assert_strs)) strs)) then
    (Debug_ocaml.print_debug 3 [] (fun () -> "check returned TRUE");
    Some true)
  else
    (Debug_ocaml.print_debug 3 [] (fun () -> "check returned NONE");
    None)
