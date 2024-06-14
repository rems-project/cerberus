module B = Builtins
open Cerb_frontend

let get_builtin_name (fsym : Sym.sym) : string option =
  Option.map
    (fun (fname, _) -> fname)
    (List.find_opt
      (fun (_, fsym') -> Sym.equal fsym fsym')
      B.cn_builtin_fun_names)

let get_builtin_sym (fname : string) : Sym.sym option =
  Option.map
    (fun (_, fsym) -> fsym)
    (List.find_opt
      (fun (name, _) -> String.equal fname name)
      B.cn_builtin_fun_names)

type cn_expr = (Symbol.sym, Ctype.ctype) Cn.cn_expr
type cn_expr_ = (Symbol.sym, Ctype.ctype) Cn.cn_expr_
type cn_resource = (Symbol.sym, Ctype.ctype) Cn.cn_resource
type cn_assertion = (Symbol.sym, Ctype.ctype) Cn.cn_assertion
type cn_clause = (Symbol.sym, Ctype.ctype) Cn.cn_clause
type cn_clauses = (Symbol.sym, Ctype.ctype) Cn.cn_clauses
type cn_condition = (Symbol.sym, Ctype.ctype) Cn.cn_condition
type cn_predicate = (Symbol.sym, Ctype.ctype) Cn.cn_predicate

let string_of_list f l =
  "[" ^ (List.map f l |> String.concat "; ") ^ "]"
;;

let no_quals : Ctype.qualifiers = {const=false;restrict=false;volatile=false};;

let string_of_ctype (ty : Ctype.ctype) : string =
  Cerb_colour.do_colour := false;
  let tmp = String_ail.string_of_ctype ~is_human:true no_quals ty ^ " " in
  Cerb_colour.do_colour := true;
  tmp
;;

let string_of_ctype_ (ty : Ctype.ctype_) : string =
  string_of_ctype (Ctype ([], ty))
;;

let rec string_of_expr_ (e : cn_expr_) : string =
  match e with
  | CNExpr_const c ->
    (match c with
    | CNConst_NULL -> "NULL"
    | CNConst_integer n -> Z.to_string n
    | CNConst_bits ((sign, bits), n) ->
      let s =
        match sign with
        | CN_signed -> "i"
        | CN_unsigned -> "u"
      in
      let b = string_of_int bits in
      Z.to_string n ^ s ^ b
    | CNConst_bool b -> string_of_bool b |> String.uppercase_ascii
    | CNConst_unit -> "()")
  | CNExpr_var x
  | CNExpr_value_of_c_atom (x, _) -> Pp_symbol.to_string_pretty x
  | CNExpr_list _ -> failwith "unsupported expression 'CNExpr_List' (Generator.string_of_expr_)"
  | CNExpr_memberof (e', Symbol.Identifier (_, x)) -> string_of_expr e' ^ "." ^ x
  | CNExpr_record _ -> failwith "unsupported expression 'CNExpr_record' (Generator.string_of_expr_)"
  | CNExpr_memberupdates _ -> failwith "unsupported expression 'CNExpr_memberupdates' (Generator.string_of_expr_)"
  | CNExpr_arrayindexupdates _ -> failwith "unsupported expression 'CNExpr_arrayindexupdates' (Generator.string_of_expr_)"
  | CNExpr_binop (CN_add, e1, e2) -> "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_sub, e1, e2) -> "(" ^ string_of_expr e1 ^ " - " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_mul, e1, e2) -> "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_div, e1, e2) -> "(" ^ string_of_expr e1 ^ " / " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_equal, e1, e2) -> "(" ^ string_of_expr e1 ^ " == " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_inequal, e1, e2) -> "(" ^ string_of_expr e1 ^ " != " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_lt, e1, e2) -> "(" ^ string_of_expr e1 ^ " < " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_le, e1, e2) -> "(" ^ string_of_expr e1 ^ " <= " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_gt, e1, e2) -> "(" ^ string_of_expr e1 ^ " > " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_ge, e1, e2) -> "(" ^ string_of_expr e1 ^ " >= " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_or, e1, e2) -> "(" ^ string_of_expr e1 ^ " || " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_and, e1, e2) -> "(" ^ string_of_expr e1 ^ " && " ^ string_of_expr e2 ^ ")"
  | CNExpr_binop (CN_map_get, _, _) -> failwith "unsupported binop 'CN_map_get' (Generator.string_of_expr_)"
  | CNExpr_sizeof _ -> failwith "unsupported expression 'CNExpr_sizeof' (Generator.string_of_expr_)"
  | CNExpr_offsetof _ -> failwith "unsupported expression 'CNExpr_offsetof' (Generator.string_of_expr_)"
  | CNExpr_membershift _ -> failwith "unsupported expression 'CNExpr_membershift' (Generator.string_of_expr_)"
  | CNExpr_addr _ -> failwith "unsupported expression 'CNExpr_addr' (Generator.string_of_expr_)"
  | CNExpr_cast _ -> failwith "unsupported expression 'CNExpr_cast' (Generator.string_of_expr_)"
  | CNExpr_array_shift _ -> failwith "unsupported expression 'CNExpr_array_shift' (Generator.string_of_expr_)"
  | CNExpr_call (f, args) -> Pp_symbol.to_string_pretty f ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"
  | CNExpr_cons (constr, es) -> Pp_symbol.to_string_pretty constr ^ "{" ^ String.concat ", " (List.map (fun (Symbol.Identifier (_, x), e) -> x ^ ": " ^ string_of_expr e) es) ^ "}"
  | CNExpr_each _ -> failwith "unsupported expression 'CNExpr_each' (Generator.string_of_expr_)"
  | CNExpr_let (x, e1, e2) -> "let " ^ Pp_symbol.to_string_pretty x ^ " = " ^ string_of_expr e1 ^ " in " ^ string_of_expr e2
  | CNExpr_match _ -> failwith "unsupported expression 'CNExpr_match' (Generator.string_of_expr_)"
  | CNExpr_ite _ -> failwith "unsupported expression 'CNExpr_ite' (Generator.string_of_expr_)"
  | CNExpr_good _ -> failwith "unsupported expression 'CNExpr_good' (Generator.string_of_expr_)"
  | CNExpr_deref _ -> failwith "unsupported expression 'CNExpr_deref' (Generator.string_of_expr_)"
  | CNExpr_unchanged _ -> failwith "unsupported expression 'CNExpr_unchanged' (Generator.string_of_expr_)"
  | CNExpr_at_env _ -> failwith "unsupported expression 'CNExpr_at_env' (Generator.string_of_expr_)"
  | CNExpr_not e' -> "!" ^ string_of_expr e'
  | CNExpr_default _ -> failwith "unsupported expression 'CNExpr_default' (Generator.string_of_expr_)"

and string_of_expr (Cn.CNExpr (_, e) : cn_expr) : string =
  string_of_expr_ e
;;

let rec sub_sym_expr_' (x : Symbol.sym) (v : cn_expr_) (e : cn_expr_) : cn_expr_ =
  match e with
  | CNExpr_var x'
  | CNExpr_value_of_c_atom (x', _) ->
    if Symbol.equal_sym x x'
    then v
    else e
  | CNExpr_list es -> CNExpr_list (List.map (sub_sym_expr' x v) es)
  | CNExpr_memberof (e', x') -> CNExpr_memberof (sub_sym_expr' x v e', x')
  | CNExpr_record fs -> CNExpr_record (List.map (fun (x', e') -> (x', sub_sym_expr' x v e')) fs)
  | CNExpr_memberupdates (e', xes) -> CNExpr_memberupdates (sub_sym_expr' x v e', List.map (fun (x', e') -> (x', sub_sym_expr' x v e')) xes)
  | CNExpr_arrayindexupdates (e', ees) -> CNExpr_arrayindexupdates (sub_sym_expr' x v e', List.map (fun (e1, e2) -> (sub_sym_expr' x v e1, sub_sym_expr' x v e2)) ees)
  | CNExpr_binop (op, e1, e2) -> CNExpr_binop (op, sub_sym_expr' x v e1, sub_sym_expr' x v e2)
  | CNExpr_membershift (e', tag, id) -> CNExpr_membershift (sub_sym_expr' x v e', tag, id)
  | CNExpr_cast (ty, e') -> CNExpr_cast (ty, sub_sym_expr' x v e')
  | CNExpr_array_shift (e1, ty, e2) -> CNExpr_array_shift (sub_sym_expr' x v e1, ty, sub_sym_expr' x v e2)
  | CNExpr_call (f, args) -> CNExpr_call (f, List.map (sub_sym_expr' x v) args)
  | CNExpr_cons (constr, exprs) -> CNExpr_cons (constr, List.map (fun (x', e') -> (x', sub_sym_expr' x v e')) exprs)
  | CNExpr_each (x', ty, rng, e') ->
    CNExpr_each (
      x', ty, rng,
      if Symbol.equal_sym x x'
      then e'
      else sub_sym_expr' x v e'
    )
  | CNExpr_let (x', e1, e2) ->
    CNExpr_let (
      x',
      sub_sym_expr' x v e1,
      if Symbol.equal_sym x x'
      then e2
      else sub_sym_expr' x v e2
    )
  | CNExpr_match (e', ms) -> failwith "TODO: Support match in test generation (Generator.sub_sym_expr_')"
  | CNExpr_ite (e1, e2, e3) -> CNExpr_ite (sub_sym_expr' x v e1, sub_sym_expr' x v e2, sub_sym_expr' x v e3)
  | CNExpr_good (ty, e') -> CNExpr_good (ty, sub_sym_expr' x v e')
  | CNExpr_deref e' -> CNExpr_deref (sub_sym_expr' x v e')
  | CNExpr_unchanged e' -> CNExpr_unchanged (sub_sym_expr' x v e')
  | CNExpr_at_env (e', x') -> CNExpr_at_env (sub_sym_expr' x v e', x')
  | CNExpr_not e' -> CNExpr_not (sub_sym_expr' x v e')

  | CNExpr_const _
  | CNExpr_sizeof _
  | CNExpr_offsetof _
  | CNExpr_addr _
  | CNExpr_default _ -> e

and sub_sym_expr' (x : Symbol.sym) (v : cn_expr_) (e : cn_expr) : cn_expr =
  let CNExpr (l, e') = e in
  CNExpr (l, sub_sym_expr_' x v e')
;;

let sub_sym_expr_ (x : Symbol.sym) (v : cn_expr_) (e : cn_expr_) : cn_expr_ =
  sub_sym_expr_' x v e

let sub_sym_expr (x : Symbol.sym) (v : cn_expr_) (e : cn_expr) : cn_expr =
  sub_sym_expr' x v e

let sub_sym_resource (x : Symbol.sym) (v : cn_expr_) (r : cn_resource) : cn_resource =
  match r with
  | CN_pred (l, p, es) ->
    CN_pred (l, p, List.map (sub_sym_expr x v) es)
  | CN_each (x', ty, e, l, p, es) when not (Symbol.equal_sym x x') ->
    CN_each (x', ty, sub_sym_expr x v e, l, p, List.map (sub_sym_expr x v) es)
  | _ -> failwith "unsupported resource (Generator.sub_sym_resource)"

let sub_sym_assertion (x : Symbol.sym) (v : cn_expr_) (a : cn_assertion) : cn_assertion =
  match a with
  | CN_assert_exp e -> CN_assert_exp (sub_sym_expr x v e)
  | CN_assert_qexp (x', ty, e1, e2) when not (Symbol.equal_sym x x') ->
    CN_assert_qexp (x', ty, sub_sym_expr x v e1, sub_sym_expr x v e2)
  | CN_assert_qexp _ -> a

let rec sub_sym_clause (x : Symbol.sym) (v : cn_expr_) (c : cn_clause) : cn_clause =
  match c with
  | CN_letResource (l, x', r, c') ->
    CN_letResource (
      l, x',
      sub_sym_resource x v r,
      if Symbol.equal_sym x x'
      then c'
      else sub_sym_clause x v c'
    )
  | CN_letExpr (l, x', e, c') ->
    CN_letExpr (
      l, x',
      sub_sym_expr x v e,
      if Symbol.equal_sym x x'
      then c'
      else sub_sym_clause x v c'
    )
  | CN_assert (l, a, c') ->
    CN_assert (l, sub_sym_assertion x v a, sub_sym_clause x v c')
  | CN_return (l, e) ->
    CN_return (l, sub_sym_expr x v e)

let rec sub_sym_clauses (x : Symbol.sym) (v : cn_expr_) (s : cn_clauses) : cn_clauses =
  match s with
  | CN_clause (l, c') -> CN_clause (l, sub_sym_clause x v c')
  | CN_if (l, e_if, c_then, s_else) ->
    CN_if (l,
    sub_sym_expr x v e_if,
    sub_sym_clause x v c_then,
    sub_sym_clauses x v s_else
  )

let rec sub_sym_conditions (x : Symbol.sym) (v : cn_expr_) (cs : cn_condition list) : cn_condition list =
  match cs with
  | (CN_cletResource (l, x', r))::cs' ->
    let cs' = if not (Symbol.equal_sym x x')
      then sub_sym_conditions x v cs'
      else cs'
    in
    (CN_cletResource (l, x', sub_sym_resource x v r))::cs'
  | (CN_cletExpr (l, x', e))::cs' ->
    let cs' = if not (Symbol.equal_sym x x')
      then sub_sym_conditions x v cs'
      else cs'
    in
    (CN_cletExpr (l, x', sub_sym_expr x v e))::cs'
  | (CN_cconstr (l, a))::cs' ->
    (CN_cconstr (l, sub_sym_assertion x v a))::(sub_sym_conditions x v cs')
  | [] -> []

let rec sub_sym_predicate' (xvs : (Symbol.sym * cn_expr_) list) (s : cn_clauses) : cn_clauses =
  match xvs with
  | (x, v)::xvs' ->
    sub_sym_clauses x v (sub_sym_predicate' xvs' s)
  | [] -> s

let sub_sym_predicate (pred : cn_predicate) (es : cn_expr_ list) : cn_clauses =
  sub_sym_predicate' (List.combine (List.map fst pred.cn_pred_iargs) es) (Option.get pred.cn_pred_clauses)

type cn_value =
  | CNVal_null
  | CNVal_integer of Z.t
  | CNVal_bits of (Cn.sign * int) * Z.t
  | CNVal_bool of bool
  | CNVal_unit

  | CNVal_struct of (string * (Ctype.ctype * cn_value)) list
  | CNVal_constr of Symbol.identifier * (string * cn_value) list

let rec string_of_value (v : cn_value) : string =
  match v with
  | CNVal_null -> "NULL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n) ^ "U"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 32 -> Int64.to_string (Z.to_int64 n) ^ "L"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 32 -> string_of_int (Z.to_int n) ^ "UL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "LL"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "ULL"

  | CNVal_struct ms -> "{ " ^ String.concat ", " (List.map (fun (x, (ty, v)) -> "." ^ x ^ ": " ^ string_of_ctype ty ^ " = " ^ string_of_value v) ms) ^ "}"

  | CNVal_bool b -> string_of_bool b
  | CNVal_integer n -> Int64.to_string (Z.to_int64 n)

  | CNVal_constr (_, ms) -> "{ " ^ String.concat ", " (List.map (fun (x, v) -> x ^ " = " ^ string_of_value v) ms) ^ "}"
  | CNVal_unit -> "()"
  | CNVal_bits _ -> failwith "unreachable (Generator.string_of_value)"


type context = (Symbol.sym * (Ctype.ctype * cn_value)) list
type heap = (int * (Ctype.ctype * cn_value)) list

let rec eval_expr_ (ctx : context) (e : cn_expr_) : cn_value =
  match e with
  | CNExpr_const c ->
    (match c with
    | CNConst_NULL -> CNVal_null
    | CNConst_integer n -> CNVal_integer n
    | CNConst_bits ((sign, bits), n) -> CNVal_bits ((sign, bits), n)
    | CNConst_bool b -> CNVal_bool b
    | CNConst_unit -> CNVal_unit)
  | CNExpr_var x
  | CNExpr_value_of_c_atom (x, _) -> List.assoc Symbol.equal_sym x ctx |> snd
  | CNExpr_memberof (e', x) ->
    (match eval_expr ctx e', x with
    | CNVal_struct fs, Symbol.Identifier (_, x) -> List.assoc String.equal x fs |> snd
    | CNVal_constr (_, fs), Symbol.Identifier (_, x) -> List.assoc String.equal x fs
    | _ -> failwith "unsupported 'memberof' (Generator.eval_expr_)")
  | CNExpr_binop (op, e1, e2) ->
    let v1 = eval_expr ctx e1 in
    let v2 = eval_expr ctx e2 in
    (match op, v1, v2 with
    | CN_add, CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.add n1 n2)
    | CN_add, CNVal_bits ((sgn1, bits1), n1), CNVal_bits ((sgn2, bits2), n2)
      when Stdlib.(=) sgn1 sgn2 && bits1 = bits2 ->
      CNVal_bits ((sgn1, bits1), Z.add n1 n2)

    | CN_sub, CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.sub n1 n2)
    | CN_sub, CNVal_bits ((sgn1, bits1), n1), CNVal_bits ((sgn2, bits2), n2)
      when Stdlib.(=) sgn1 sgn2 && bits1 = bits2 ->
      CNVal_bits ((sgn1, bits1), Z.sub n1 n2)

    | CN_mul, CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.mul n1 n2)
    | CN_mul, CNVal_bits ((sgn1, bits1), n1), CNVal_bits ((sgn2, bits2), n2)
      when Stdlib.(=) sgn1 sgn2 && bits1 = bits2 ->
      CNVal_bits ((sgn1, bits1), Z.mul n1 n2)

    | CN_div, CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.div n1 n2)
    | CN_div, CNVal_bits ((sgn1, bits1), n1), CNVal_bits ((sgn2, bits2), n2)
      when Stdlib.(=) sgn1 sgn2 && bits1 = bits2 ->
      CNVal_bits ((sgn1, bits1), Z.div n1 n2)

    | CN_equal, _, _ ->
      CNVal_bool (Stdlib.(=) v1 v2)
    | CN_inequal, _, _ ->
      CNVal_bool (Stdlib.(<>) v1 v2)

    | CN_lt, CNVal_integer n1, CNVal_integer n2
    | CN_lt, CNVal_bits (_, n1), CNVal_bits (_, n2) ->
      CNVal_bool (Z.lt n1 n2)
    | CN_le, CNVal_integer n1, CNVal_integer n2
    | CN_le, CNVal_bits (_, n1), CNVal_bits (_, n2) ->
      CNVal_bool (Z.leq n1 n2)
    | CN_gt, CNVal_integer n1, CNVal_integer n2
    | CN_gt, CNVal_bits (_, n1), CNVal_bits (_, n2) ->
      CNVal_bool (Z.gt n1 n2)
    | CN_ge, CNVal_integer n1, CNVal_integer n2
    | CN_ge, CNVal_bits (_, n1), CNVal_bits (_, n2) ->
      CNVal_bool (Z.geq n1 n2)

    | CN_or, CNVal_bool b1, CNVal_bool b2 ->
      CNVal_bool (b1 || b2)
    | CN_and, CNVal_bool b1, CNVal_bool b2 ->
      CNVal_bool (b1 && b2)
    | _ -> failwith ("unsupported binop (Generator.eval_expr_) '" ^ string_of_expr_ e ^ "'"))
  | CNExpr_not e' ->
    let v = eval_expr ctx e' in
    (match v with
    | CNVal_bool b -> CNVal_bool (not b)
    | _ -> failwith "cannot 'not' a non-bool value (Generator.eval_expr_)")
  
  | CNExpr_call (fsym, [e']) when Stdlib.(=) (get_builtin_name fsym) (Some "is_null") ->
    let v = eval_expr ctx e' in
    (match v with
    | CNVal_bits (_, n)
    | CNVal_integer n -> CNVal_bool (Z.equal n Z.zero)
    | CNVal_null -> CNVal_bool true
    | _ -> CNVal_bool false)

  | CNExpr_call (fsym, [e1; e2]) when Stdlib.(=) (get_builtin_name fsym) (Some "mod") ->
    let v1 = eval_expr ctx e1 in
    let v2 = eval_expr ctx e2 in
    (match v1, v2 with
    | CNVal_bits ((sgn1, bits1), n1), CNVal_bits ((sgn2, bits2), n2)
      when Stdlib.(=) sgn1 sgn2 && bits1 = bits2 ->
      CNVal_bits ((sgn1, bits1), Z.(mod) n1 n2)
    | CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.(mod) n1 n2)
    | _ -> failwith ("Invalid values for `mod` '" ^ string_of_value v1 ^ "', '" ^ string_of_value v2 ^ "'"))

  | _ -> failwith ("unsupported expression `" ^ string_of_expr_ e ^ "` (Generator.eval_expr_)")

and eval_expr (ctx : context) (e : cn_expr) : cn_value =
  let CNExpr (_, e) = e in eval_expr_ ctx e

type variables = (Symbol.sym * (Ctype.ctype * cn_expr_)) list

let string_of_variables (vars : variables) : string =
  "{ " ^ (String.concat "; " (
      List.map (
        fun (x, (ty, e)) ->
          Pp_symbol.to_string_pretty x ^ " -> (" ^ string_of_ctype ty ^ ", " ^ string_of_expr_ e ^ ")"
      ) vars
    )
  ) ^ " }"
;;

type locations = (cn_expr_ * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ " ^ (String.concat "; " (
      List.map (
        fun (e, x) ->
           "(*" ^ string_of_expr_ e ^ ") -> " ^ Pp_symbol.to_string_pretty x
      ) locs
    )
  ) ^ " }"
;;

type members = (Symbol.sym * (string * (Ctype.ctype * Symbol.sym)) list) list

let string_of_members (ms : members) : string =
  "{ " ^ (
    String.concat "; " (
      List.map (
        fun (x, ms) ->
          Pp_symbol.to_string_pretty x ^
          " -> {" ^ String.concat ", " (
            List.map (
              fun (y, (ty, z)) ->
                "." ^ y ^ ": " ^
                string_of_ctype ty ^
                " = " ^ Pp_symbol.to_string_pretty z
            ) ms)
      ) ms
    )
  ) ^ " }"
;;

type constraints = cn_expr_ list

let string_of_constraints (cs : constraints) : string =
  "{ " ^ String.concat "; " (List.map string_of_expr_ cs) ^ " }"
;;

type goal = variables * members * locations * constraints

let string_of_goal ((vars, ms, locs, cs) : goal) : string =
  "Vars: " ^ string_of_variables vars ^ "\n" ^
  "Ms: " ^ string_of_members ms ^ "\n" ^
  "Locs: " ^ string_of_locations locs ^ "\n" ^
  "Cs: " ^ string_of_constraints cs ^ "\n"

let apply_builtins e =
  let Cn.CNExpr (_, e) = e in
  let res =
    match e with
    | CNExpr_call (fsym, [e]) when Stdlib.(=) (get_builtin_name fsym) (Some "is_null") ->
      Cn.CNExpr_binop (CN_equal, e, CNExpr (Cerb_location.unknown, CNExpr_const CNConst_NULL))
    | _ -> e
  in
  Cn.CNExpr (Cerb_location.unknown, res)

let is_pointer_ctype (ty : Ctype.ctype) : bool =
  match ty with
  | Ctype (_, Pointer _) -> true
  | _ -> false
;;

let add_to_vars_ms (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (sym : Symbol.sym) (ty : Ctype.ctype) (vars : variables) (ms : members) : variables * members =
  match ty with
  | Ctype (_, Struct n) ->
    (match List.assoc (Symbol.equal_sym) n ail_prog.tag_definitions with
    | (_, _, StructDef (membs, _)) ->
      let f (Symbol.Identifier (_, id), (_, _, _, ty)) =
        let sym' = Symbol.fresh () in
        ((sym', (ty, Cn.CNExpr_var sym')), (id, (ty, sym')))
      in
      let vars', member_data = List.split (List.map f membs) in
      ((sym, (ty, Cn.CNExpr_var sym))::vars @ vars', (sym, member_data)::ms)
    | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
  | _ -> ((sym, (ty, Cn.CNExpr_var sym))::vars, ms)

let (>>=) (x : 'a list QCheck.Gen.t) (f : 'a -> 'b list QCheck.Gen.t) : 'b list QCheck.Gen.t =
  QCheck.Gen.(map List.flatten ((x >>= fun l -> (List.map f l |> flatten_l))))

let return (x : 'a) : 'a list QCheck.Gen.t =
  QCheck.Gen.return [x]

let map (f : 'a -> 'b) (x : 'a list QCheck.Gen.t) : 'b list QCheck.Gen.t =
  QCheck.Gen.(map (List.map f) x)

let lift_gen (x : 'a QCheck.Gen.t) : 'a list QCheck.Gen.t =
  QCheck.Gen.(x >>= fun v -> return [v])

let lift_list (x : 'a list) : 'a list QCheck.Gen.t =
  QCheck.Gen.return x

let unlift_gen (x : 'a list QCheck.Gen.t) : 'a QCheck.Gen.t =
  QCheck.Gen.(>>=) x QCheck.Gen.oneofl

let sample (x : 'a QCheck.Gen.t) : 'a =
  QCheck.Gen.generate1 x

let unlift_list (x : 'a list QCheck.Gen.t) : 'a list = sample x

let rec collect_resource (depth : int) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (ms : members) (r : cn_resource) : (cn_expr_ * variables * members * locations * constraints) list QCheck.Gen.t =
  match r with
  | CN_pred (_, CN_owned (Some ty), [Cn.CNExpr (_, e)])
  | CN_pred (_, CN_block ty, [Cn.CNExpr (_, e)]) ->
    let sym = Symbol.fresh () in
    let vars, ms = add_to_vars_ms ail_prog sym ty vars ms in
    return (Cn.CNExpr_var sym, vars, ms, [(e, sym)], [])
  | CN_pred (_, CN_named x, es) ->
    let pred = List.assoc Symbol.equal_sym x psi in
    let es' = List.map (fun (Cn.CNExpr (_, e')) -> e') es in
    collect_clauses depth ail_prog psi vars ms (sub_sym_predicate pred es')

  | CN_pred (_, CN_owned (Some _), _) -> failwith "incorrect number of args for Owned"
  | CN_pred (_, CN_block _, _) -> failwith "incorrect number of args for Block"
  | CN_pred (_, CN_owned None, _) -> failwith "requires type for Owned"
  | CN_each _ -> failwith "each not supported"

and collect_clause (depth : int) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (ms : members) (c : cn_clause) : (cn_expr_ * variables * members * locations * constraints) list QCheck.Gen.t =
    match c with
    | CN_letResource (_, x, r, c') ->
      collect_resource depth ail_prog psi vars ms r >>= fun (e, vars, ms, locs, cs) ->
      collect_clause depth ail_prog psi vars ms (sub_sym_clause x e c') >>= fun (e', vars, ms, locs', cs') ->
      return (e', vars, ms, locs @ locs', cs @ cs')
    | CN_letExpr (_, x, CNExpr (_, e), c') ->
      collect_clause depth ail_prog psi vars ms (sub_sym_clause x e c')
    | CN_assert (_, CN_assert_exp (Cn.CNExpr (_, e)), c') ->
      collect_clause depth ail_prog psi vars ms c' >>= fun (e', vars, ms, locs, cs) ->
      return (e', vars, ms, locs, e::cs)
    | CN_return (_, Cn.CNExpr (_, e)) ->
      return (e, vars, ms, [], [])
    | CN_assert (_, CN_assert_qexp _, _) -> failwith "quantified assert not supported"

and collect_clauses (depth : int) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (ms : members) (s : cn_clauses) : (cn_expr_ * variables * members * locations * constraints) list QCheck.Gen.t =
  match s with
  | CN_clause (_, c) -> collect_clause depth ail_prog psi vars ms c
  | CN_if (_, e_if, c_then, s_else) ->
    if depth <= 0 then lift_list [] else
    let e_if = apply_builtins e_if in
    let t =
      collect_clause (depth - 1) ail_prog psi vars ms c_then >>= fun (e, vars, ms, locs, cs) ->
      let Cn.CNExpr (_, e_if) = e_if in
      return (e, vars, ms, locs, e_if::cs)
    in
    let f =
      collect_clauses (depth - 1) ail_prog psi vars ms s_else >>= fun (e, vars, ms, locs, cs) ->
      return (e, vars, ms, locs, (Cn.CNExpr_not e_if)::cs)
    in
    QCheck.Gen.map
      (List.flatten)
      (QCheck.Gen.flatten_l [t; f])

let rec collect_conditions (depth : int) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (ms : members) (c : cn_condition list) : goal list QCheck.Gen.t =
  match c with
  | (CN_cletResource (_, x, r))::c' ->
    collect_resource depth ail_prog psi vars ms r >>= fun (e, vars, ms, locs, cs) ->
    collect_conditions depth ail_prog psi vars ms (sub_sym_conditions x e c') >>= fun (vars, ms, locs', cs') ->
    return (vars, ms, locs @ locs', cs @ cs')
  | (CN_cletExpr (_, x, CNExpr (_, e)))::c' ->
    collect_conditions depth ail_prog psi vars ms (sub_sym_conditions x e c')
  | (CN_cconstr (_, CN_assert_exp Cn.CNExpr (_, e)))::c' ->
    collect_conditions depth ail_prog psi vars ms c' >>= fun (vars, ms, locs, cs) ->
    return (vars, ms, locs, e::cs)
  | (CN_cconstr (_, CN_assert_qexp _))::_ -> failwith "quantified assert not supported"
  | [] -> return (vars, ms, [], [])

let sub_sym_variables (x : Symbol.sym) (v : cn_expr_) (vars : variables) : variables =
  List.map (fun (x', (ty, e)) -> (x', (ty, sub_sym_expr_ x v e))) vars

let sub_sym_locations (x : Symbol.sym) (v : cn_expr_) (locs : locations) : locations =
  List.map (fun (e, y) -> (sub_sym_expr_ x v e, y)) locs

let sub_sym_constraints (x : Symbol.sym) (v : cn_expr_) (cs : constraints) : constraints =
  List.map (fun e -> sub_sym_expr_ x v e) cs

let sub_sym_goal (x : Symbol.sym) (v : cn_expr_) ((vars, ms, locs, cs) : goal) : goal =
  (sub_sym_variables x v vars, ms, sub_sym_locations x v locs, sub_sym_constraints x v cs)

let rec inline_constants' (g : goal) (iter : constraints) : goal =
  match iter with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_const c), CNExpr (_, CNExpr_var x)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_const c)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_const c), CNExpr (_, CNExpr_value_of_c_atom (x, _))))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_const c)))::iter' ->
    let g = sub_sym_goal x (CNExpr_const c) g in
    inline_constants' g iter'
  | _::iter' -> inline_constants' g iter'
  | [] -> g
;;

let inline_constants (g : goal) : goal =
  let (_, _, _, cs) = g in
  inline_constants' g cs

let rec remove_tautologies ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_var y)))::cs when Symbol.equal_sym x y ->
    remove_tautologies (vars, ms, locs, cs)
  | c::cs ->
    (try
      let v = eval_expr_ [] c in
      if Stdlib.(=) v (CNVal_bool true)
      then remove_tautologies (vars, ms, locs, cs)
      else failwith "Inconsistent constraints"
    with Not_found ->
      let (vars, ms, locs, cs) = remove_tautologies (vars, ms, locs, cs) in
      (vars, ms, locs, c::cs))
  | [] -> (vars, ms, locs, cs)

let rec cnf_ (e : cn_expr_) : cn_expr_ =
  Cn.(
    match e with
    (* Double negation elimination *)
    | CNExpr_not (CNExpr (_, CNExpr_not (CNExpr (_, e)))) ->
      e

    (* Flip equalities *)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_equal, e1, e2))) ->
      CNExpr_binop (CN_inequal, cnf e1, cnf e2)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_inequal, e1, e2))) ->
      CNExpr_binop (CN_equal, cnf e1, cnf e2)

    (* Flip inequalities *)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_lt, e1, e2))) ->
      CNExpr_binop (CN_ge, cnf e1, cnf e2)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_le, e1, e2))) ->
      CNExpr_binop (CN_gt, cnf e1, cnf e2)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_gt, e1, e2))) ->
      CNExpr_binop (CN_le, cnf e1, cnf e2)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_ge, e1, e2))) ->
      CNExpr_binop (CN_lt, cnf e1, cnf e2)

    (* De Morgan's Law *)
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_and, e1, e2))) ->
      CNExpr_binop (CN_or,
        CNExpr (l, CNExpr_not (cnf e1)),
        CNExpr (l, CNExpr_not (cnf e2)))
    | CNExpr_not (CNExpr (l, CNExpr_binop (CN_or, e1, e2))) ->
      CNExpr_binop (CN_and,
        CNExpr (l, CNExpr_not (cnf e1)),
        CNExpr (l, CNExpr_not (cnf e2)))

    (* Distribute disjunction *)
    | CNExpr_binop (CN_or, e1, CNExpr (l, CNExpr_binop (CN_and, e2, e3)))
    | CNExpr_binop (CN_or, CNExpr (l, CNExpr_binop (CN_and, e2, e3)), e1) ->
      CNExpr_binop (CN_and,
        CNExpr (l, CNExpr_binop (CN_or, e1, e2)),
        CNExpr (l, CNExpr_binop (CN_or, e1, e3)))

    | _ -> e
  )

and cnf (e : cn_expr) : cn_expr =
  let CNExpr (l, e) = e in
  CNExpr (l, cnf_ e)
;;

let rec inline_aliasing' (g : goal) (iter : constraints) : goal =
  match iter with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_var y)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_value_of_c_atom (y, _))))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_var y)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_value_of_c_atom (y, _))))::iter' ->
    let (vars, ms, locs, cs) = g in
    (match List.assoc Symbol.equal_sym x vars, List.assoc Symbol.equal_sym y vars with
    | (_, CNExpr_var x'), (_, e) when Symbol.equal_sym x x' -> sub_sym_goal x (CNExpr_var y) g
    | _ -> sub_sym_goal y (CNExpr_var x) g)
  | _::iter' -> inline_aliasing' g iter'
  | [] -> g
;;

let inline_aliasing (g : goal) : goal =
  let (_, _, _, cs) = g in
  inline_aliasing' g cs

let rec remove_nonnull_for_locs ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | (CNExpr_binop (CN_inequal, CNExpr (_, e), CNExpr (_, CNExpr_const CNConst_NULL)))::cs
    when List.assoc_opt Stdlib.(=) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | c::cs ->
    let (vars, ms, locs, cs) = remove_nonnull_for_locs (vars, ms, locs, cs) in
    (vars, ms, locs, c::cs)
  | [] -> (vars, ms, locs, [])

let rec indirect_members_expr_ (ms : members) (e : cn_expr_) : cn_expr_ =
  match e with
  | CNExpr_memberof (CNExpr (_, CNExpr_var x), Symbol.Identifier (_, y)) ->
    let new_sym =
      List.assoc Symbol.equal_sym x ms
      |> List.assoc String.equal y
      |> snd
    in
    CNExpr_var new_sym
  | CNExpr_list es -> CNExpr_list (List.map (indirect_members_expr ms) es)
  | CNExpr_memberof (e', x') -> CNExpr_memberof (indirect_members_expr ms e', x')
  | CNExpr_record fs -> CNExpr_record (List.map (fun (x', e') -> (x', indirect_members_expr ms e')) fs)
  | CNExpr_memberupdates (e', xes) -> CNExpr_memberupdates (indirect_members_expr ms e', List.map (fun (x', e') -> (x', indirect_members_expr ms e')) xes)
  | CNExpr_arrayindexupdates (e', ees) -> CNExpr_arrayindexupdates (indirect_members_expr ms e', List.map (fun (e1, e2) -> (indirect_members_expr ms e1, indirect_members_expr ms e2)) ees)
  | CNExpr_binop (op, e1, e2) -> CNExpr_binop (op, indirect_members_expr ms e1, indirect_members_expr ms e2)
  | CNExpr_membershift (e', tag, id) -> CNExpr_membershift (indirect_members_expr ms e', tag, id)
  | CNExpr_cast (ty, e') -> CNExpr_cast (ty, indirect_members_expr ms e')
  | CNExpr_array_shift (e1, ty, e2) -> CNExpr_array_shift (indirect_members_expr ms e1, ty, indirect_members_expr ms e2)
  | CNExpr_call (f, args) -> CNExpr_call (f, List.map (indirect_members_expr ms) args)
  | CNExpr_cons (constr, exprs) -> CNExpr_cons (constr, List.map (fun (x, e') -> (x, indirect_members_expr ms e')) exprs)
  | CNExpr_each (x, ty, r, e') -> CNExpr_each (x, ty, r, indirect_members_expr ms e')
  | CNExpr_let (x, e1, e2) ->
    CNExpr_let (
      x,
      indirect_members_expr ms e1,
      indirect_members_expr ms e2
    )
  | CNExpr_match (e', ps) -> CNExpr_match (indirect_members_expr ms e', List.map (fun (p, e') -> (p, indirect_members_expr ms e')) ps)
  | CNExpr_ite (e1, e2, e3) -> CNExpr_ite (indirect_members_expr ms e1, indirect_members_expr ms e2, indirect_members_expr ms e3)
  | CNExpr_good (ty, e') -> CNExpr_good (ty, indirect_members_expr ms e')
  | CNExpr_deref e' -> CNExpr_deref (indirect_members_expr ms e')
  | CNExpr_unchanged e' -> CNExpr_unchanged (indirect_members_expr ms e')
  | CNExpr_at_env (e', x') -> CNExpr_at_env (indirect_members_expr ms e', x')
  | CNExpr_not e' -> CNExpr_not (indirect_members_expr ms e')

  | CNExpr_var _
  | CNExpr_value_of_c_atom _
  | CNExpr_const _
  | CNExpr_sizeof _
  | CNExpr_offsetof _
  | CNExpr_addr _
  | CNExpr_default _ -> e

and indirect_members_expr (ms : members) (e : cn_expr) : cn_expr =
  let CNExpr (l, e) = e in
  CNExpr (l, indirect_members_expr_ ms e)

let indirect_members ((vars, ms, locs, cs) : goal) : goal =
  (
    List.map (fun (x, (ty, e)) -> (x, (ty, indirect_members_expr_ ms e))) vars,
    ms,
    List.map (fun (e, x) -> (indirect_members_expr_ ms e, x)) locs,
    List.map (fun e -> indirect_members_expr_ ms e) cs
  )

let rec listify_constraints' (c : cn_expr_) : constraints =
  match c with
  | CNExpr_binop (CN_and, CNExpr (_, e1), CNExpr (_, e2)) ->
    listify_constraints' e1 @ listify_constraints' e2
  | _ -> [c]

let listify_constraints (cs : constraints) : constraints =
  List.map listify_constraints' cs |> List.flatten

let rec simplify' (g : goal) : goal =
  let og = g in
  let g = inline_constants g in
  let g = inline_aliasing g in
  let (vars, ms, locs, cs) = remove_tautologies g in
  let cs = listify_constraints cs in
  let g = (vars, ms, locs, cs) in
  if Stdlib.(<>) og g
  then
    simplify' g
  else
    g

let simplify (g : goal) : goal =
  let g = indirect_members g in
  let (vars, ms, locs, cs) = g in
  let g = (vars, ms, locs, List.map cnf_ cs) in
  let g = remove_nonnull_for_locs g in
  simplify' g

let rec pow a p =
  match p with
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let rec type_gen (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (ty : Ctype.ctype) : cn_value QCheck.Gen.t =
  QCheck.Gen.(
    let Ctype (_, cty) = ty in
    match cty with
    | Basic (Integer ity) ->
      int_range
        (Memory.min_integer_type ity |> Z.to_int)
        (Memory.max_integer_type ity |> Z.to_int)
      >>= fun n ->
      let sgn =
        if Memory.is_signed_integer_type ity
        then Cn.CN_signed
        else Cn.CN_unsigned
      in
      return (CNVal_bits ((sgn, Memory.size_of_integer_type ity |> Int.mul 8), Z.of_int n))
    | Struct n ->
      (match List.assoc (Symbol.equal_sym) n ail_prog.tag_definitions with
      | (_, _, StructDef (members, _)) ->
        let f (Symbol.Identifier (_, id), (_, _, _, ty')) =
          if is_pointer_ctype ty'
          then
            return (id, failwith "unreachable (Generator.type_gen)")
          else
            type_gen ail_prog ty' >>= fun v ->
            return (id, (ty', v))
        in
        flatten_l (List.map f members) >>= fun ms ->
        return (CNVal_struct ms)
      | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
    | Pointer _ -> type_gen ail_prog (Ctype ([], Basic (Integer Ptraddr_t)))
      (* failwith (
        "Tried using type-based generator on pointer type '" ^
        string_of_ctype_ cty ^
        "' (Generator.type_gen)"
      ) *)
    | _ ->
      failwith (
        "Unsupported type '" ^
        string_of_ctype_ cty ^
        "' (Generator.type_gen)"
      )
  )
;;

let rec check_constraints (ctx : context) (cs : constraints) : constraints option =
  match cs with
  | c::cs' ->
    (try
      let v = eval_expr_ ctx c in
      if Stdlib.(=) v (CNVal_bool true)
      then check_constraints ctx cs'
      else None
    with Not_found ->
      Option.map (fun cs -> c::cs) (check_constraints ctx cs'))
  | [] -> Some []
;;

let string_of_context (ctx : context) : string =
  "{ " ^ (
    String.concat "; " (
      List.map (
        fun (x, (ty, v)) ->
          Pp_symbol.to_string_pretty x ^ " -> (" ^ string_of_ctype ty ^ ", " ^ string_of_value v ^ ")"
      ) ctx
    )
  ) ^ " }"
;;

let is_integer_ctype (ty : Ctype.ctype) : bool =
  match ty with
  | Ctype (_, Basic (Integer _)) -> true
  | _ -> false

let rec concretize_context_generate ail_prog ((vars, ms, locs, cs) : goal) (ctx : context) : (goal * context) QCheck.Gen.t =
  QCheck.Gen.(
    match vars with
    | (x, (ty, CNExpr_var x'))::vars'
    | (x, (ty, CNExpr_value_of_c_atom (x', _)))::vars'
      when Symbol.equal_sym x x' && is_integer_ctype ty ->
        type_gen ail_prog ty >>= fun v ->
        (match check_constraints ((x, (ty, v))::ctx) cs with
        | Some cs -> concretize_context_generate ail_prog (vars', ms, locs, cs) ((x, (ty, v))::ctx)
        | None ->
          concretize_context_generate ail_prog (vars', ms, locs, cs) ctx >>= fun ((vars, ms, locs, cs), ctx) ->
          return (((x, (ty, Cn.CNExpr_var x))::vars, ms, locs, cs), ctx))
    | v::vars' ->
      concretize_context_generate ail_prog (vars', ms, locs, cs) ctx >>= fun ((vars, ms, locs, cs), ctx) ->
      return ((v::vars, ms, locs, cs), ctx)
    | [] -> return ((vars, ms, locs, cs), ctx)
  )
;;

let rec concretize_context_evaluate ((vars, ms, locs, cs) : goal) (ctx : context) : goal * context =
  match vars with
  | (x, (ty, e))::vars' ->
    (try
      let v = eval_expr_ ctx e in
      concretize_context_evaluate (vars', ms, locs, cs) ((x, (ty, v))::ctx)
    with Not_found ->
      let ((vars, ms, locs, cs), ctx) = concretize_context_evaluate (vars', ms, locs, cs) ctx in
      (((x, (ty, e))::vars, ms, locs, cs), ctx))
  | [] -> ((vars, ms, locs, cs), ctx)
;;

let rec concretize_context' ail_prog (g : goal) (ctx : context) (tolerance : int) : context QCheck.Gen.t =
  QCheck.Gen.(
    let (vars, _, _, _) = g in
    let old_num_left = List.length (List.filter (fun (_, (ty, _)) -> is_integer_ctype ty) vars) in
    concretize_context_generate ail_prog g ctx >>= fun (g, ctx) ->
    let ((vars, ms, locs, cs), ctx) = concretize_context_evaluate g ctx in
    let num_left = List.length (List.filter (fun (_, (ty, _)) -> is_integer_ctype ty) vars) in
    if num_left = 0
    then
      return ctx
    else if num_left <> old_num_left
    then
      concretize_context' ail_prog (vars, ms, locs, cs) ctx tolerance
    else if tolerance > 0
    then
      concretize_context' ail_prog (vars, ms, locs, cs) ctx (tolerance - 1)
    else
      failwith "Failed to concretize"
  )

let concretize_context ail_prog (g : goal) : context QCheck.Gen.t =
  concretize_context' ail_prog g [] 10

let generate_location (max_size : int) (ps : int list) : int QCheck.Gen.t =
  QCheck.Gen.(
    int_range 1 (max_size - List.length ps) >>= fun n ->
    return (
      ps
      |> List.sort compare
      |> List.fold_left (fun acc i -> if acc >= i then acc + 1 else acc) n
    )
  )

let concretize_pointers ((vars, ms, locs, cs) : goal) : goal QCheck.Gen.t =
  QCheck.Gen.(
    let max_size = List.length locs in
    let csps = List.fold_left
      (fun csps (e, x) ->
        csps >>= fun (cs, ps) ->
        generate_location max_size ps >>= fun p ->
        let e1 = Cn.CNExpr (Cerb_location.unknown, e) in
        let e2 = Cn.CNExpr (Cerb_location.unknown, CNExpr_const (CNConst_bits ((CN_unsigned, 64), Z.of_int p))) in
        return ((Cn.CNExpr_binop (CN_equal, e1, e2))::cs, p::ps)
      ) (return (cs, [])) locs
    in
    csps >>= fun (cs, _) ->
    return (simplify' (vars, ms, locs, cs))
  )

let construct_structs (vars : variables) (ms : members) (ctx : context) : context =
  List.fold_left (
    fun ctx (x, (ty, _)) ->
      (match ty with
      | Ctype.Ctype (_, Struct _) ->
        let fs =
          List.assoc Symbol.equal_sym x ms
          |> List.map (fun (x, (_, y)) ->
            (x,
              match List.assoc_opt Symbol.equal_sym y ctx with
              | Some (ty, v) -> (ty, v)
              | None -> failwith (Sym.pp_string y)
            ))
        in
        (x, (ty, CNVal_struct fs))::ctx
      | _ -> ctx)
  ) ctx vars

let rec concretize_heap' (max_size : int) (ctx : context) (vars : variables) (locs : locations) (h : heap) : (context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    match locs with
    | (e, x)::locs' ->
      let (ty, v) = List.assoc Symbol.equal_sym x ctx in
      (match eval_expr_ ctx e with
      | CNVal_integer n
      | CNVal_bits ((_, _), n) -> concretize_heap' max_size ctx vars locs' ((Z.to_int n, (ty, v))::h)
      | _ -> failwith "Invalid pointer (Generator.concretize_heap)")
    | [] -> return (ctx, h)
  )

let concretize_heap (ctx : context) (g : goal) : (context * heap) QCheck.Gen.t =
  let (vars, _, locs, _) = g in
  let max_size =
    locs
    |> List.map snd
    |> List.map (fun x -> List.assoc Symbol.equal_sym x ctx)
    |> List.map fst
    |> List.map Sctypes.of_ctype
    |> List.map Option.get
    |> List.map Memory.size_of_ctype
    |> List.fold_left (+) 0 in
  concretize_heap' max_size ctx vars locs []

let concretize ail_prog (g : goal) : (context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    concretize_pointers g >>= fun g ->
    concretize_context ail_prog g >>= fun ctx ->
    let (vars, ms, _, _) = g in
    let ctx = construct_structs vars ms ctx in
    concretize_heap ctx g
  )

(***************)
(* Compilation *)
(***************)

let rec get_free_vars_ (e : cn_expr_) : Symbol.sym list =
  match e with
  | CNExpr_var x
  | CNExpr_value_of_c_atom (x, _) -> [x]

  | CNExpr_memberof (e', _)
  | CNExpr_membershift (e', _, _)
  | CNExpr_cast (_, e')
  | CNExpr_good (_, e')
  | CNExpr_deref e'
  | CNExpr_unchanged e'
  | CNExpr_at_env (e', _)
  | CNExpr_not e' -> get_free_vars e'

  | CNExpr_list es -> List.fold_left (fun acc e -> acc @ get_free_vars e) [] es
  | CNExpr_record fs -> List.fold_left (fun acc (_, e') -> acc @ get_free_vars e') [] fs
  | CNExpr_memberupdates (e', xes) -> List.fold_left (fun acc (_, e') -> acc @ get_free_vars e') (get_free_vars e') xes
  | CNExpr_arrayindexupdates (e', ees) -> List.fold_left (fun acc (e1, e2) -> acc @ get_free_vars e1 @ get_free_vars e2) (get_free_vars e') ees
  | CNExpr_binop (_, e1, e2)
  | CNExpr_array_shift (e1, _, e2) -> get_free_vars e1 @ get_free_vars e2
  | CNExpr_call (_, args) -> List.fold_left (fun acc arg -> acc @ get_free_vars arg) [] args
  | CNExpr_cons (_, es) -> List.fold_left (fun acc (_, e') -> acc @ get_free_vars e') [] es
  | CNExpr_each (x, _, _, e') -> List.filter (fun x' -> not (Symbol.equal_sym x x')) (get_free_vars e')
  | CNExpr_let (x', e1, e2) ->
    let xs1 = get_free_vars e1 in
    let xs2 = List.filter (fun x -> not (Symbol.equal_sym x x')) (get_free_vars e2) in
    xs1 @ xs2
  | CNExpr_match _ -> failwith "TODO: Support match in test generation (Generator.get_free_vars_)"
  | CNExpr_ite (e1, e2, e3) -> get_free_vars e1 @ get_free_vars e2 @ get_free_vars e3

  | CNExpr_const _
  | CNExpr_sizeof _
  | CNExpr_offsetof _
  | CNExpr_addr _
  | CNExpr_default _ -> []

and get_free_vars (e : cn_expr) : Symbol.sym list =
  let CNExpr (_, e) = e in get_free_vars_ e
;;

type gen =
  | Arbitrary of Ctype.ctype
  | Return of Ctype.ctype * cn_expr
  | Filter of Sym.sym * Ctype.ctype * cn_expr * gen
  | Map of Sym.sym * Ctype.ctype * cn_expr * gen
  | Alloc of Ctype.ctype * gen
  | Struct of Ctype.ctype * (string * Sym.sym) list

let rec string_of_gen (g : gen) : string =
  match g with
  | Arbitrary ty -> "arbitrary<" ^ string_of_ctype ty ^ ">"
  | Return (ty, e) -> "return<" ^ string_of_ctype ty ^ ">(" ^ string_of_expr e ^ ")"
  | Filter (x, ty, e, g') -> "filter(" ^ "|" ^ Pp_symbol.to_string_pretty x ^ ": " ^ string_of_ctype ty ^ "| " ^ string_of_expr e ^ ", " ^ string_of_gen g' ^ ")"
  | Map (x, ty, e, g') -> "map(" ^ "|" ^ Pp_symbol.to_string_pretty x ^ ": " ^ string_of_ctype ty ^ "| " ^ string_of_expr e ^ ", " ^ string_of_gen g' ^ ")"
  | Alloc (ty, g') -> "alloc<" ^ string_of_ctype ty ^ ">(" ^ string_of_gen g' ^ ")"
  | Struct (ty, ms) -> "struct<" ^ string_of_ctype ty ^ ">(" ^ String.concat ", " (List.map (fun (x, g') -> "." ^ x ^ ": " ^ Pp_symbol.to_string_pretty g') ms) ^ ")"
;;

type gen_context = (Symbol.sym * gen) list

let string_of_gen_context (gtx : gen_context) : string =
  "{ " ^ (
    String.concat "; " (
      List.map (
        fun (x, g) ->
          "\"" ^ Pp_symbol.to_string_pretty x ^ "\" <- \"" ^ string_of_gen g ^ "\""
      ) gtx
    )
  ) ^ " }"
;;

let filter_gen (x : Symbol.sym) (ty : Ctype.ctype) (cs : constraints) : gen =
  match cs with
  | c::cs' ->
    Filter (
      x, ty,
      List.fold_left (
        fun acc c' ->
          Cn.CNExpr (
            Cerb_location.unknown,
            CNExpr_binop (
              CN_and, acc,
              CNExpr (Cerb_location.unknown, c'))))
        (Cn.CNExpr (Cerb_location.unknown, c)) cs',
      Arbitrary ty)
  | [] -> Arbitrary ty
;;

let range_gen (x : Symbol.sym) (ty : Ctype.ctype) (min : cn_expr) (max : cn_expr) (cs : constraints) : gen =
  let l = Cerb_location.unknown in
  let y = Symbol.fresh () in
  (* max - min *)
  let e = Cn.CNExpr (l, CNExpr_binop (CN_sub, max, min)) in
  (* mod(y, (max - min)) *)
  let e = Cn.CNExpr (l, CNExpr_call (get_builtin_sym "mod" |> Option.get, [CNExpr (l, CNExpr_var y); e])) in
  (* mod(y, (max - min)) + min *)
  let e = Cn.CNExpr (l, CNExpr_binop (CN_add, e, min)) in
  (* map y (mod(y, (max - min)) + min) arbitrary *)
  let gen = Map (y, ty, e, Arbitrary ty) in
  (* filter (map y (mod(y, (max - min)) + min) arbitrary) cs *)
  match cs with
  | c::cs' ->
    Filter (
      x, ty,
      List.fold_left (
        fun acc c' ->
          Cn.CNExpr (
            l,
            CNExpr_binop (
              CN_and, acc,
              CNExpr (l, c'))))
        (Cn.CNExpr (l, c)) cs',
      gen)
  | [] -> gen
;;

let mult_range_gen (x : Symbol.sym) (ty : Ctype.ctype) (mult : cn_expr) (min : cn_expr) (max : cn_expr) (cs : constraints) : gen =
  let l = Cerb_location.unknown in
  let y = Symbol.fresh () in
  let e_y = Cn.CNExpr (l, CNExpr_var y) in
  (* mult * y *)
  let e_map = Cn.CNExpr (l, CNExpr_binop (CN_mul, mult, e_y)) in
  (* min / mult *)
  let e_min = Cn.CNExpr (l, CNExpr_binop (CN_div, min, mult)) in
  (* max / mult *)
  let e_max = Cn.CNExpr (l, CNExpr_binop (CN_div, max, mult)) in
  (* range (min / mult) (max / mult) *)
  let gen = range_gen y ty e_min e_max [] in
  (* map y (mult * y) (range (min / mult) (max / mult)) *)
  let gen = Map (y, ty, e_map, gen) in
  (* filter (map y (mult * y) (range (min / mult) (max / mult))) cs *)
  match cs with
  | c::cs' ->
    Filter (
      x, ty,
      List.fold_left (
        fun acc c' ->
          Cn.CNExpr (
            l,
            CNExpr_binop (
              CN_and, acc,
              CNExpr (l, c'))))
        (Cn.CNExpr (l, c)) cs',
      gen)
  | [] -> gen
;;

let get_const_expr (ty : Ctype.ctype) (n : Z.t) : cn_expr =
  let l = Cerb_location.unknown in
  let Ctype (_, cty) = ty in
  match cty with
  | Basic (Integer ity) ->
    let sgn =
      if Memory.is_signed_integer_type ity
      then Cn.CN_signed
      else Cn.CN_unsigned
    in
    CNExpr (l, CNExpr_const (CNConst_bits ((sgn, Memory.size_of_integer_type ity |> Int.mul 8), n)))
  | _ -> failwith ("Tried to generate multiple of invalid type '" ^ string_of_ctype_ cty ^ "'")

let get_min_max_expr (ty : Ctype.ctype) : cn_expr * cn_expr =
  let Ctype (_, cty) = ty in
  match cty with
  | Basic (Integer ity) ->
    (get_const_expr ty (Memory.min_integer_type ity), get_const_expr ty (Memory.max_integer_type ity))
  | _ -> failwith ("Tried to generate multiple of invalid type '" ^ string_of_ctype_ cty ^ "'")
;;

(* let mult_gen (x : Symbol.sym) (ty : Ctype.ctype) (mult : cn_expr) (cs : constraints) : gen =
  let Ctype (_, cty) = ty in
  match cty with
  | Basic (Integer ity) ->
    let sgn =
      if Memory.is_signed_integer_type ity
      then Cn.CN_signed
      else Cn.CN_unsigned
    in
    let l = Cerb_location.unknown in
    let get_val n = Cn.CNExpr (l, CNExpr_const (CNConst_bits ((sgn, Memory.size_of_integer_type ity |> Int.mul 8), n))) in
    let min = get_val (Memory.min_integer_type ity) in
    let max = get_val (Memory.max_integer_type ity) in
    mult_range_gen x ty mult min max cs
  | cty -> failwith ("Tried to generate multiple of invalid type '" ^ string_of_ctype_ cty ^ "'") *)

let compile_gen (x : Symbol.sym) (ty : Ctype.ctype) (e : cn_expr) (cs : constraints) : gen =
  match e with
  | CNExpr (_, CNExpr_var x') when Sym.equal_sym x x' ->
    let l = Cerb_location.unknown in
    let mult = List.find_map (
      fun (c : cn_expr_) ->
        match c with
        | CNExpr_binop (
            CN_equal,
            CNExpr (_, CNExpr_call (fsym, [CNExpr (_, CNExpr_var x'); e2])),
            CNExpr (_, CNExpr_const (CNConst_bits (_, n))))
        | CNExpr_binop (
          CN_equal,
          CNExpr (_, CNExpr_call (fsym, [CNExpr (_, CNExpr_var x'); e2])),
          CNExpr (_, CNExpr_const (CNConst_integer n)))
        | CNExpr_binop (
            CN_equal,
            CNExpr (_, CNExpr_const (CNConst_bits (_, n))),
            CNExpr (_, CNExpr_call (fsym, [CNExpr (_, CNExpr_var x'); e2])))
        | CNExpr_binop (
          CN_equal,
          CNExpr (_, CNExpr_const (CNConst_integer n)),
          CNExpr (_, CNExpr_call (fsym, [CNExpr (_, CNExpr_var x'); e2])))
          when
            Stdlib.(=) (get_builtin_name fsym) (Some "mod") &&
            Sym.equal_sym x x' &&
            Z.equal n (Z.of_int 0)->
          Some e2
        | _ -> None
        ) cs
    in
    let min = List.find_map (
      fun (c : cn_expr_) ->
        match c with
        | CNExpr_binop (CN_gt, CNExpr (_, CNExpr_var x'), e')
        | CNExpr_binop (CN_lt, e', CNExpr (_, CNExpr_var x'))
          when Sym.equal_sym x x' ->
          let e_one = get_const_expr ty (Z.of_int 1) in
          Some (Cn.CNExpr (l, CNExpr_binop (CN_add, e', e_one)))
        | CNExpr_binop (CN_ge, CNExpr (_, CNExpr_var x'), e')
        | CNExpr_binop (CN_le, e', CNExpr (_, CNExpr_var x'))
          when Sym.equal_sym x x' ->
          Some e'
        | _ -> None
        ) cs
    in
    let max = List.find_map (
      fun (c : cn_expr_) ->
        match c with
        | CNExpr_binop (CN_gt, e', CNExpr (_, CNExpr_var x'))
        | CNExpr_binop (CN_lt, CNExpr (_, CNExpr_var x'), e')
          when Sym.equal_sym x x' ->
          let e_one = get_const_expr ty (Z.of_int 1) in
          Some (Cn.CNExpr (l, CNExpr_binop (CN_sub, e', e_one)))
        | CNExpr_binop (CN_ge, e', CNExpr (_, CNExpr_var x'))
        | CNExpr_binop (CN_le, CNExpr (_, CNExpr_var x'), e')
          when Sym.equal_sym x x' ->
          Some e'
        | _ -> None
        ) cs
    in
    (match mult with
    | Some mult ->
      let (def_min, def_max) = get_min_max_expr ty in
      mult_range_gen x ty mult
        (Option.value min ~default:def_min)
        (Option.value max ~default:def_max) cs
    | None ->
      if Option.is_some min || Option.is_some max
      then
        let (def_min, def_max) = get_min_max_expr ty in
        range_gen x ty
          (Option.value min ~default:def_min)
          (Option.value max ~default:def_max) cs
      else
        Arbitrary ty)

  | _ -> Return (ty, e)
;;

let rec compile_singles' (gtx : gen_context) (locs : locations) (cs : constraints) (iter : variables) : gen_context * variables =
  let get_loc x =
    List.find_map (
      fun (e, y) ->
        if Sym.equal x y
        then
          match e with
          | Cn.CNExpr_var z
          | Cn.CNExpr_value_of_c_atom (z, _) ->
            Some z
          | _ -> None
        else
          None
    ) locs
  in
  match iter with
  | (x, (ty, e))::iter' ->
    let var_in_gtx y = List.find_opt (fun (z, _) -> Symbol.equal_sym y z) gtx |> Option.is_some in
    let relevant_cs = List.filter (fun c -> List.exists (Sym.equal_sym x) (get_free_vars_ c)) cs in
    let no_free_vars = List.for_all (
      fun c -> List.for_all
        (fun y -> Sym.equal_sym x y || var_in_gtx y)
        (get_free_vars_ c)) relevant_cs in
    if no_free_vars
    then
      let l = Cerb_location.unknown in
      let gen = compile_gen x ty (CNExpr (l, e)) cs in
      let gen_loc = Alloc (Ctype.Ctype ([], Pointer (no_quals, ty)), gen) in
      match get_loc x with
      | Some x_loc -> compile_singles' ((x_loc, gen_loc)::(x, gen)::gtx) locs cs iter'
      | None -> compile_singles' ((x, gen)::gtx) locs cs iter'
    else
      let (gtx, iter') = compile_singles' gtx locs cs iter' in
      (gtx, (x, (ty, e))::iter')
  | [] -> (gtx, iter)

let rec compile_singles (gtx : gen_context) (vars : variables) (locs : locations) (cs : constraints) : gen_context =
  let (gtx, vars) = compile_singles' gtx locs cs vars in
  if List.non_empty vars
  then compile_singles gtx vars locs cs
  else gtx

let rec compile_structs' (gtx : gen_context) (vars : variables) (ms : members) (locs : locations) : gen_context * members =
  let get_loc x =
    List.find_map (
      fun (e, y) ->
        if Sym.equal x y
        then
          match e with
          | Cn.CNExpr_var z
          | Cn.CNExpr_value_of_c_atom (z, _) ->
            Some z
          | _ -> None
        else
          None
    ) locs
  in
  match ms with
  | (x, syms)::ms' ->
    let (gtx, ms') = compile_structs' gtx vars ms' locs in
    let free_vars =
      not (List.for_all (
        fun (_, (ty, sym)) ->
          (List.assoc_opt Sym.equal_sym sym gtx
          |> Option.is_some)) syms)
    in
    if free_vars then (gtx, (x, syms)::ms') else
    let (_, (ty, _)) = List.find (fun (y, _) -> Sym.equal_sym x y) vars in
    let mems = List.map (fun (id, (ty, sym)) -> (id, sym)) syms in
    (match get_loc x with
    | Some loc ->
      let gen = Struct (ty, mems) in
      let gen_loc = Alloc (Ctype.Ctype ([], Pointer (no_quals, ty)), gen) in
      ((loc, gen_loc)::(x, gen)::gtx, ms')
    | None -> ((x, Struct (ty, mems))::gtx, ms'))
  | [] -> (gtx, [])

let rec compile_structs (gtx : gen_context) (vars : variables) (ms : members) (locs : locations) : gen_context =
  let (gtx, ms) = compile_structs' gtx vars ms locs in
  if List.non_empty ms
  then compile_structs gtx vars ms locs
  else gtx

let compile ((vars, ms, locs, cs) : goal) : gen_context =
  (* Not a location *)
  let vars' = List.filter (
    fun (x, _) -> List.for_all (
      fun (e, _) ->
        match e with
        | Cn.CNExpr_var y
        | Cn.CNExpr_value_of_c_atom (y, _) ->
          not (Sym.equal_sym x y)
        | e -> true) locs) vars
  in
  (* Not a struct *)
  let vars' = List.filter (
    fun (x, _) -> List.for_all (
      fun (y, _) -> not (Sym.equal_sym x y)) ms) vars'
  in
  let gtx = compile_singles [] vars' locs cs in
  compile_structs gtx vars ms locs |> List.rev

let rec interpret_gen (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (x : Symbol.sym) (g : gen) (max_size : int) (ctx : context) (h : heap) : (context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    match g with
    | Arbitrary ty ->
      type_gen ail_prog ty >>= fun v ->
      return ((x, (ty, v))::ctx, h)
    | Return (ty, e) -> return ((x, (ty, eval_expr ctx e))::ctx, h)
    | Filter (y, ty, e, g') ->
      if not (Sym.equal_sym x y) then failwith "Mismatch" else
      interpret_gen ail_prog x g' max_size ctx h >>= fun (ctx', h') ->
      (match eval_expr ctx' e with
      | CNVal_bool b ->
        if b
        then
          return (ctx', h')
        else
          interpret_gen ail_prog x g max_size ctx h
      | _ -> failwith "Type error")
    | Map (y, ty, e, g) ->
      interpret_gen ail_prog y g max_size ctx h >>= fun (ctx, h) ->
      return ((x, (ty, eval_expr ctx e))::ctx, h)
    | Alloc (ty, g') ->
      let y = Sym.fresh () in
      interpret_gen ail_prog y g' max_size ctx h >>= fun (ctx, h) ->
      generate_location max_size (List.map fst h) >>= fun l ->
      return ((x, (ty, CNVal_bits ((CN_unsigned, 64), Z.of_int l)))::ctx, (l, List.assoc Sym.equal_sym y ctx)::h)
    | Struct (ty, ms) ->
      QCheck.Gen.(
        let vs =
          List.map (fun (x, sym) -> (x, List.assoc Sym.equal_sym sym ctx)) ms
        in
        return ((x, (ty, CNVal_struct vs))::ctx, h)
      )
  )

let rec interpret' (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (gtx : gen_context) (max_size : int) (ctx : context) (h : heap) : (context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    match gtx with
    | (x, g)::gtx' ->
      interpret_gen ail_prog x g max_size ctx h >>= fun (ctx, h) ->
      interpret' ail_prog gtx' max_size ctx h
    | [] -> return (ctx, h)
  )

let interpret (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (gtx : gen_context) (max_size : int) : (context * heap) QCheck.Gen.t =
  interpret' ail_prog gtx max_size [] []

(************************)
(* Unit Test Generation *)
(************************)

let generate (depth : int) ail_prog (psi : (Symbol.sym * cn_predicate) list) (args : (Symbol.sym * Ctype.ctype) list) (c : cn_condition list) : (context * heap) list QCheck.Gen.t =
  let vars, ms =
    (List.fold_left
      (fun (vars, ms) (x, ty) ->
        add_to_vars_ms ail_prog x ty vars ms
      ) ([], []) args)
  in

  let gs = collect_conditions depth ail_prog psi vars ms c in
  gs >>= fun g ->
  let g = simplify g in
  let gtx = compile g in
  lift_gen QCheck.Gen.(
    let (_, _, locs, _) = g in
    interpret ail_prog gtx (List.length locs) >>= fun (ctx, h) ->
    let ctx = List.filter (
      fun (x, _) ->
        List.assoc_opt Sym.equal_sym x args
        |> Option.is_some) ctx
    in
    return (ctx, h)
  )

let rec codify_value' (root : string) (v : cn_value) : string =
  match v with
  | CNVal_null -> "NULL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n) ^ "U"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 32 -> Int64.to_string (Z.to_int64 n) ^ "L"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 32 -> string_of_int (Z.to_int n) ^ "UL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "LL"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "ULL"

  | CNVal_struct ms ->
    "{ " ^
    String.concat ", " (
      List.map (
        fun (x, (ty, v)) ->
          "." ^ x ^ " = " ^ codify_value root ty v) ms) ^
    "}"

  | CNVal_bool _ -> failwith "Booleans aren't yet supported in unit test generation"
  | CNVal_integer _ -> failwith "Can't generate mathematical integers"

  | CNVal_constr _ 
  | CNVal_unit
  | CNVal_bits _ -> failwith ("unreachable (Generator.codify_value')")

and codify_value root ty v =
  if is_pointer_ctype ty
  then
    match v with
    | CNVal_integer n
    | CNVal_bits (_, n) ->
      ("(" ^ string_of_ctype ty ^ ")((uintptr_t)" ^ root ^ " + " ^ Z.to_string n ^ ")")
    | CNVal_null -> "NULL"
    | _ -> failwith ("Invalid pointer value " ^ string_of_value v)
  else
    codify_value' root v

let rec remap_pointer_value (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (old_p : int) (new_p : int) (ty : Ctype.ctype) (v : cn_value) : cn_value =
  let Ctype (_, cty) = ty in
  match cty, v with
  | Pointer _, CNVal_integer n
  | Pointer _, CNVal_bits (_, n) ->
    if Z.to_int n = old_p
    then CNVal_bits ((CN_unsigned, 64), Z.of_int new_p)
    else v
  | Pointer _, v when Stdlib.(<>) v CNVal_null -> failwith ("Invalid pointer value " ^ string_of_value v)
  | Struct n, CNVal_struct fs ->
    (match List.assoc (Symbol.equal_sym) n ail_prog.tag_definitions with
      | (_, _, StructDef (members, _)) ->
        let f (Symbol.Identifier (_, id), (_, _, _, ty')) =
          let v = List.assoc String.equal id fs |> snd in
          let v =  remap_pointer_value ail_prog old_p new_p ty' v in
          (id, (ty', v))
        in
        CNVal_struct (List.map f members)
      | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
  | _, _ -> v

let rec remap_pointer_context (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (old_p : int) (new_p : int) (ctx : context) : context =
  match ctx with
  | (x, (ty, v))::ctx' ->
    let v = remap_pointer_value ail_prog old_p new_p ty v in
    (x, (ty, v))::(remap_pointer_context ail_prog old_p new_p ctx')
  | [] -> []

let rec remap_pointer_heap (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (old_p : int) (new_p : int) (h : heap) : heap =
  match h with
  | (p, (ty, v))::h' ->
    let p = if p = old_p then new_p else p in
    let v = remap_pointer_value ail_prog old_p new_p ty v in
    (p, (ty, v))::(remap_pointer_heap ail_prog old_p new_p h')
  | [] -> []

let remap_pointer (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (old_p : int) (new_p : int) (ctx : context) (h : heap) : context * heap =
  (remap_pointer_context ail_prog old_p new_p ctx, remap_pointer_heap ail_prog old_p new_p h)

let rec expand_heap' (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (ctx : context) (h : heap) (root : int) (iter : heap) : context * heap =
  match iter with
  | (p, (ty, _))::iter' ->
    let (ctx, h) = remap_pointer ail_prog p (root + p) ctx h in
    let sz = Sctypes.of_ctype ty |> Option.get |> Memory.size_of_ctype in
    expand_heap' ail_prog ctx h (root + sz - 1) iter'
  | [] -> (ctx, h)

let expand_heap (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (ctx : context) (h : heap) : (context * heap) =
  let h = List.sort (fun (i, _) (j, _) -> compare i j) h in
  expand_heap' ail_prog ctx h (-1) h
;;

let codify_heap (root : string) (max_size : int) (h : heap) (oc : out_channel) : unit =
  output_string oc ("void *" ^ root ^ " = malloc(");
  output_string oc (string_of_int max_size);
  output_string oc ");\n";
  List.iter
    (fun (p, (ty, v)) ->
      let ty_str = string_of_ctype ty in
      let rhs = "*(" ^ ty_str ^ "*)((uintptr_t)" ^ root ^ " + " ^ string_of_int p ^ ") = " in
      output_string oc rhs;
      output_string oc (codify_value root ty v);
      output_string oc ";\n")
    h

let codify_context (root : string) (ctx : context) (args : (Symbol.sym * Ctype.ctype) list) (oc : out_channel) : unit =
  List.iter
    (fun (x, ty) ->
      let name = Pp_symbol.to_string_pretty x in
      Cerb_colour.do_colour := false;
      let ty_str = string_of_ctype ty in
      let value =
        match List.assoc_opt Symbol.equal_sym x ctx with
        | Some (ty', v) ->
          if Ctype.ctypeEqual ty ty'
          then
            codify_value root ty v
          else failwith (
            "Type mismatch '" ^
            string_of_ctype ty ^
            "' versus '" ^
            string_of_ctype ty' ^
            "' (Generator.codify_context)")
        | None -> failwith ("Could not find '" ^ name ^ "' in generated context")
      in
      Cerb_colour.do_colour := false;
      output_string oc (ty_str ^ " ");
      Cerb_colour.do_colour := true;
      output_string oc name;
      output_string oc " = ";
      output_string oc value;
      output_string oc ";\n";
    )
    args

type test_framework =
  | GTest
  | Catch2

let codify_unit_header (tf : test_framework) (suite : string) (test : string) (oc : out_channel) : unit =
  match tf with
  | GTest -> output_string oc ("\nTEST(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ "){\n")
  | Catch2 -> output_string oc ("\nTEST_CASE(\"" ^ test ^ "\", \"[" ^ String.lowercase_ascii suite ^ "]\"){\n");
;;

let codify_unit (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (args : (Symbol.sym * Ctype.ctype) list) (ctx : context) (h : heap) (index : int) (oc : out_channel) : unit =
  codify_unit_header tf (Pp_symbol.to_string_pretty instrumentation.fn) ("Test" ^ string_of_int index) oc;

  let (ctx, h) = expand_heap ail_prog ctx h in
  let root = Symbol.fresh () |> Sym.pp_string in
  let max_size =
    h
    |> List.map snd
    |> List.map fst
    |> List.map Sctypes.of_ctype
    |> List.map Option.get
    |> List.map Memory.size_of_ctype
    |> List.fold_left (+) 0 in
  (if max_size > 0 then codify_heap root max_size h oc);
  codify_context root ctx args oc;
  output_string oc (Pp_symbol.to_string_pretty instrumentation.fn);
  output_string oc "(";
  output_string oc (args |> List.map fst |> List.map Pp_symbol.to_string_pretty |> String.concat ", ");
  output_string oc ");\n";

  output_string oc "}\n";
;;

let range i j =
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux (j-1) []
;;

let generate_unit_tests' (depth : int) (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (oc : out_channel) (tolerance : int) : unit =
  let psi = List.map (fun (pred : cn_predicate) -> (pred.cn_pred_name, pred)) ail_prog.cn_predicates in
  let lookup_fn = fun (x, _) -> Symbol.equal_sym x instrumentation.fn in
  let fn_decl = List.filter lookup_fn ail_prog.declarations in
  let fn_def = List.filter lookup_fn ail_prog.function_definitions in
  let (arg_types, arg_syms) =
    match (fn_decl, fn_def) with 
      | ((_, (_, _, (Decl_function (_, _, arg_types, _, _, _)))) :: _), ((_, (_, _, _, arg_syms, _)) :: _) -> 
        let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
        (arg_types, arg_syms)
      | _ -> ([], [])
  in
  let args = List.combine arg_syms arg_types in
  let gs = QCheck.Gen.map (List.mapi (fun i g -> (i, g))) (generate depth ail_prog psi args (instrumentation.surface.requires)) in
  let runners : unit list QCheck.Gen.t = map (fun (i, (ctx, h)) -> codify_unit tf instrumentation ail_prog args ctx h (i + 1) oc) gs in
  sample (unlift_gen runners)
;;

let generate_unit_tests (depth : int) (tf : test_framework) (instrumentation_list : Core_to_mucore.instrumentation list) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (oc : out_channel) : unit =
  List.iter
    (fun inst ->
      try
        generate_unit_tests' depth tf inst ail_prog oc 10
      with Failure m ->
        print_string ("Failed to generate all tests for `" ^ Sym.pp_string inst.fn ^ "` due to the following:\n" ^ m ^ "\n")
    ) instrumentation_list

(******************)
(* PBT Generation *)
(******************)

let rec codify_gen' (g : gen) : string =
  match g with
  | Arbitrary ty -> "rc::gen::arbitrary<" ^ string_of_ctype ty ^ ">()"
  | Return (ty, e) -> "rc::gen::just<" ^ string_of_ctype ty ^ ">(" ^ string_of_expr e ^ ")"
  | Filter (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::suchThat(" ^ gen ^ ", [=](" ^ string_of_ctype ty ^ " " ^ Pp_symbol.to_string_pretty x' ^ "){ return " ^ string_of_expr e ^ "; })"
  | Map (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::map(" ^ gen ^ ", [=](" ^ string_of_ctype ty ^ " " ^ Pp_symbol.to_string_pretty x' ^ "){ return " ^ string_of_expr e ^ "; })"
  | Alloc (ty, g') ->
    (match ty with
    | Ctype (_, Pointer (_, ty')) ->
      "rc::gen::exec([=](){ return new (" ^ string_of_ctype ty' ^ ") {*" ^ codify_gen' g' ^ "}; })"
    | _ -> failwith "Tried allocation without pointer type (Generator.codify_gen')")
  | Struct (ty, ms) ->
    "rc::gen::just((" ^ string_of_ctype ty ^ "){ " ^
    String.concat ", " (
      List.map (
        fun (x, y) ->
          "." ^ x ^ " = " ^ Pp_symbol.to_string_pretty y) ms) ^
    "})"

let get_gen_ty (g : gen) : Ctype.ctype =
  match g with
  | Arbitrary ty
  | Return (ty, _) 
  | Filter (_, ty, _, _)
  | Map (_, ty, _, _)
  | Alloc (ty, _)
  | Struct (ty, _) -> ty

let codify_gen (x : Sym.sym) (g : gen) : string =
  string_of_ctype (get_gen_ty g) ^ " " ^ Pp_symbol.to_string_pretty x ^ " = *" ^ codify_gen' g ^ ";\n"

let rec codify_gen_context (gtx : gen_context) : string =
  match gtx with
  | (x, g)::gtx' -> codify_gen x g ^ codify_gen_context gtx'
  | [] -> ""

let codify_pbt_header (tf : test_framework) (suite : string) (test : string) (oc : out_channel) : unit =
  match tf with
  | GTest -> output_string oc ("\nRC_GTEST_PROP(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ ", ()){\n")
  | Catch2 -> output_string oc ("\nTEST_CASE(\"" ^ test ^ "\"){\n\trc::prop(\"[" ^ String.lowercase_ascii suite ^ "]\"), [](){\n")
;;

let codify_pbt (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (args : (Symbol.sym * Ctype.ctype) list) (gtx : gen_context) (index : int) (oc : out_channel) : unit =
  codify_pbt_header tf (Pp_symbol.to_string_pretty instrumentation.fn) ("Test" ^ string_of_int index) oc;

  output_string oc (codify_gen_context gtx);

  output_string oc (Pp_symbol.to_string_pretty instrumentation.fn);
  output_string oc "(";
  output_string oc (args |> List.map fst |> List.map Pp_symbol.to_string_pretty |> String.concat ", ");
  output_string oc ");\n";

  match tf with
  | GTest -> output_string oc "}\n";
  | Catch2 -> output_string oc "})}\n"
;;

let full_compile (depth : int) ail_prog (psi : (Symbol.sym * cn_predicate) list) (args : (Symbol.sym * Ctype.ctype) list) (c : cn_condition list) : gen_context list QCheck.Gen.t =
  let vars, ms =
    (List.fold_left
      (fun (vars, ms) (x, ty) ->
        add_to_vars_ms ail_prog x ty vars ms
      ) ([], []) args)
  in

  let gs = collect_conditions depth ail_prog psi vars ms c in
  gs >>= fun g ->
  return (g |> simplify |> compile)

let generate_pbt' (depth : int) (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (oc : out_channel) : unit =
  let psi = List.map (fun (pred : cn_predicate) -> (pred.cn_pred_name, pred)) ail_prog.cn_predicates in
  let lookup_fn = fun (x, _) -> Symbol.equal_sym x instrumentation.fn in
  let fn_decl = List.filter lookup_fn ail_prog.declarations in
  let fn_def = List.filter lookup_fn ail_prog.function_definitions in
  let (arg_types, arg_syms) =
    match (fn_decl, fn_def) with 
      | ((_, (_, _, (Decl_function (_, _, arg_types, _, _, _)))) :: _), ((_, (_, _, _, arg_syms, _)) :: _) -> 
        let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
        (arg_types, arg_syms)
      | _ -> ([], [])
  in
  let args = List.combine arg_syms arg_types in
  let gtxs = QCheck.Gen.map (List.mapi (fun i g -> (i, g))) (full_compile depth ail_prog psi args (instrumentation.surface.requires)) in
  let runners : unit list QCheck.Gen.t = map (fun (i, gtx) -> codify_pbt tf instrumentation ail_prog args gtx (i + 1) oc) gtxs in
  sample (unlift_gen runners)
;;

let generate_pbt (depth : int) (tf : test_framework) (instrumentation_list : Core_to_mucore.instrumentation list) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (oc : out_channel) : unit =
  List.iter
    (fun inst ->
      try
        generate_pbt' depth tf inst ail_prog oc
      with Failure m ->
        print_string ("Failed to generate PBT tests for `" ^ Sym.pp_string inst.fn ^ "` due to the following:\n" ^ m ^ "\n")
    ) instrumentation_list
