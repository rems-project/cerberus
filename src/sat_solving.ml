open Defacto_memory_types
open Mem_common


type assertions =
  Assertions of string Dlist.dlist


let initial_assertions () =
  Assertions (Dlist.nil)


module StringMap = Map.Make (String)

(* TODO: yuck, no to state !! *)
let declared_consts : (string StringMap.t) ref =
  ref StringMap.empty

let declare_const str_name str_sort =
  declared_consts := StringMap.add str_name str_sort !declared_consts

(*
let declare_const str_name str_ty =
  vars := Printf.sprintf "(define %s::%s)" str_name str_ty :: !vars
*)


let smt2_from_integerBaseType = function
  | AilTypes.Ichar ->
      "ichar_ity"
  | AilTypes.Short ->
      "short_ity"
  | AilTypes.Int_ ->
     "int_ity"
  | AilTypes.Long ->
     "long_ity"
  | AilTypes.LongLong ->
     "long_long_ity"
  | AilTypes.IBBuiltin _ ->
      failwith "Sat_folving.smt2_from_integerBaseType: TODO IBBuiltin"


let smt2_from_integerType = function
  | AilTypes.Char ->
      "char_ty"
  | AilTypes.Bool ->
      "bool_ty"
  | AilTypes.Signed ibty ->
      "(signed " ^ smt2_from_integerBaseType ibty ^ ")"
  | AilTypes.Unsigned ibty ->
      "(unsigned " ^ smt2_from_integerBaseType ibty ^ ")"
  | AilTypes.IBuiltin _ ->
      failwith "Sat_folving.smt2_from_integerType: TODO IBuiltin"
  | AilTypes.Enum _ ->
      failwith "Sat_folving.smt2_from_integerType: TODO Enum"


let smt2_from_basicType = function
  | AilTypes.Integer ity ->
      smt2_from_integerType ity
  | AilTypes.Floating _ ->
      failwith "Sat_folving.smt2_from_basicType: TODO Floating"



let rec expression_from_integer_value_base = function
  | IVconcrete bign ->
      (Nat_big_num.to_string bign)
  | IVaddress addr_n ->
      let str_name = "addr_" ^ string_of_int addr_n in
      declare_const str_name "Address";
      str_name
  | IVfromptr (_, ptr_val_) ->
      assert false
  | IVop (iop, [ival1_; ival2_]) ->
      let iop_str = match iop with
      | IntAdd -> "+"
      | IntSub -> "-"
      | IntMul -> "*"
      | IntDiv -> "/" (* TODO: div by zero? *)
      | IntMod -> failwith "IntMod"
      | IntExp -> failwith "IntExp" in
      Printf.sprintf "(%s %s %s)" iop_str
        (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)
  | IVmin ity ->
      "(TODO IVmin)"
  | IVmax ity ->
      "(TODO IVmax)"
  | IVsizeof ty ->
      (match ty with
         | Core_ctype.Array0 (ty, Some n) ->
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


let assertion_of_memory_constraint = function
  | MC_eqIV (debug_str, ival1_, ival2_) ->
      [Printf.sprintf "(= %s %s)" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_neIV (ival1_, ival2_) ->
      [Printf.sprintf "(not (= %s %s))" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_leIV (ival1_, ival2_) ->
      [Printf.sprintf "(<= %s %s)" (expression_from_integer_value_base ival1_) (expression_from_integer_value_base ival2_)]
  | MC_addr_distinct (addr_a, addr_bs) ->
      let addr_a_str = "addr_" ^ string_of_int addr_a in
      declare_const addr_a_str "Address";
      List.map (fun addr_b ->
        let addr_b_str = ("addr_" ^ string_of_int addr_b) in
        declare_const addr_b_str "Address";
        Printf.sprintf "(not (= %s %s))" addr_a_str addr_b_str
      ) (Pset.elements addr_bs)



let is_unsat (Assertions strs) =
  let str_problem =
    String.concat "\n" (
      [
        "(declare-sort Address 0)";
        "(declare-sort Ctype 0)";
        "(declare-fun int_ty () Ctype)";
        "(declare-fun sizeof (Ctype) Int)";
        "(assert (forall ((ty Ctype)) (>= (sizeof ty) 1)))"
      ] @

      StringMap.fold (fun str_name str_sort acc ->
        Printf.sprintf "(declare-fun %s () %s)" str_name str_sort :: acc
      ) !declared_consts (List.filter (fun z -> z <> "") (Dlist.toList strs))
    ) in
  Debug.print_debug 3 ("IS UNSAT?\n" ^ str_problem ^ "\n=================================\n");
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
      Debug.print_debug 3 ("DEBUG Z3 ==> " ^ output);
      false

let add_mem_constraint constr (Assertions asserts) =
  Assertions (Dlist.append (Dlist.fromList0 (List.map (fun z -> Printf.sprintf "(assert %s)" z) (assertion_of_memory_constraint constr))) asserts)


let check constr (Assertions strs) =
  Debug.print_debug 3 ("CHECKING " ^ (Pp_utils.to_plain_string (Pp_defacto_memory.pp_mem_constraint constr)) ^ "\n");
  let assert_strs = assertion_of_memory_constraint constr in
  if is_unsat (Assertions (Dlist.append (Dlist.fromList0 (List.map (fun z -> Printf.sprintf "(assert %s)" z) assert_strs)) strs)) then
    (Debug.print_debug 3 "check returned FALSE";
    Some false)
  else if is_unsat (Assertions (Dlist.append (Dlist.fromList0 (List.map (fun z -> Printf.sprintf "(assert (not %s))" z) assert_strs)) strs)) then
    (Debug.print_debug 3 "check returned TRUE";
    Some true)
  else
    (Debug.print_debug 3 "check returned NONE";
    None)
