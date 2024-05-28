module B = Builtins
open Cerb_frontend

type cn_expr = (Symbol.sym, Ctype.ctype) Cn.cn_expr
type cn_expr_ = (Symbol.sym, Ctype.ctype) Cn.cn_expr_
type cn_resource = (Symbol.sym, Ctype.ctype) Cn.cn_resource
type cn_assertion = (Symbol.sym, Ctype.ctype) Cn.cn_assertion
type cn_clause = (Symbol.sym, Ctype.ctype) Cn.cn_clause
type cn_clauses = (Symbol.sym, Ctype.ctype) Cn.cn_clauses
type cn_condition = (Symbol.sym, Ctype.ctype) Cn.cn_condition
type cn_predicate = (Symbol.sym, Ctype.ctype) Cn.cn_predicate

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
  | CNExpr_each (x', ty, r, e') when not (Symbol.equal_sym x x') -> CNExpr_each (x', ty, r, sub_sym_expr' x v e')
  | CNExpr_let (x', e1, e2) ->
    CNExpr_let (
      x',
      sub_sym_expr' x v e1,
      if Symbol.equal_sym x x'
      then e2
      else sub_sym_expr' x v e2
    )
  | CNExpr_match (e', ms) -> CNExpr_match (sub_sym_expr' x v e', List.map (fun (p, e') -> (p, sub_sym_expr' x v e')) ms)
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
  | CNExpr_each _ 
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

  | CNVal_struct of Ctype.ctype * (string * cn_value) list
  | CNVal_constr of Symbol.identifier * (string * cn_value) list

type context = (Symbol.sym * (Ctype.ctype * cn_value)) list
type heap = (int * (Ctype.ctype * cn_value)) list

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
  | CNExpr_var x -> Pp_symbol.to_string_pretty x
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
  | CNExpr_value_of_c_atom (x, _) -> Pp_symbol.to_string_pretty x
  | CNExpr_unchanged _ -> failwith "unsupported expression 'CNExpr_unchanged' (Generator.string_of_expr_)"
  | CNExpr_at_env _ -> failwith "unsupported expression 'CNExpr_at_env' (Generator.string_of_expr_)"
  | CNExpr_not e' -> "!" ^ string_of_expr e'
  | CNExpr_default _ -> failwith "unsupported expression 'CNExpr_default' (Generator.string_of_expr_)"

and string_of_expr (Cn.CNExpr (_, e) : cn_expr) : string =
  string_of_expr_ e
;;

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
    | CNVal_struct (_, fs), Symbol.Identifier (_, x)
    | CNVal_constr (_, fs), Symbol.Identifier (_, x) -> List.assoc String.equal x fs
    | _ -> failwith "unsupported 'memberof' (Generator.eval_expr_)")
  | CNExpr_binop (op, e1, e2) ->
    let v1 = eval_expr ctx e1 in
    let v2 = eval_expr ctx e2 in
    (match op, v1, v2 with
    | CN_add, CNVal_integer n1, CNVal_integer n2 ->
      CNVal_integer (Z.(+) n1 n2)
    | CN_add, CNVal_bits ((CN_signed, 32), n1), CNVal_bits ((CN_signed, 32), n2) ->
      CNVal_bits ((CN_signed, 32), Z.of_int32 (Int32.add (Z.to_int32 n1) (Z.to_int32 n2)))
    | CN_add, CNVal_bits ((CN_signed, 64), n1), CNVal_bits ((CN_signed, 64), n2) ->
      CNVal_bits ((CN_signed, 64), Z.of_int64 (Int64.add (Z.to_int64 n1) (Z.to_int64 n2)))

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
    | _ -> failwith "unsupported binop (Generator.eval_expr_)")
  | CNExpr_not e' ->
    let v = eval_expr ctx e' in
    (match v with
    | CNVal_bool b -> CNVal_bool (not b)
    | _ -> failwith "cannot 'not' a non-bool value (Generator.eval_expr_)")
  | _ -> failwith ("unsupported expression `" ^ string_of_expr_ e ^ "` (Generator.eval_expr_)")

and eval_expr (ctx : context) (e : cn_expr) : cn_value =
  let CNExpr (_, e) = e in eval_expr_ ctx e

type variables = (Symbol.sym * (Ctype.ctype * cn_expr_)) list

let string_of_variables (vars : variables) : string =
  "{ " ^ (
    List.fold_left (
      fun a b ->
        if String.equal a ""
        then b
        else a ^ "; " ^ b
    ) "" (
      List.map (
        fun (x, (ty, e)) ->
          Pp_symbol.to_string_pretty x ^ " -> (" ^ string_of_ctype ty ^ ", " ^ string_of_expr_ e ^ ")"
      ) vars
    )
  ) ^ " }"
;;

type locations = (cn_expr_ * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ " ^ (
    List.fold_left (
      fun a b ->
        if String.equal a ""
        then b
        else a ^ "; " ^ b
    ) "" (
      List.map (
        fun (e, x) ->
           "(" ^ string_of_expr_ e ^ ") -> " ^ Pp_symbol.to_string_pretty x
      ) locs
    )
  ) ^ " }"
;;

type constraints = cn_expr_ list

let string_of_constraints (cs : constraints) : string =
  "{ " ^ (
    List.fold_left (
      fun a b ->
        if String.equal a ""
        then b
        else a ^ "; " ^ b
    ) "" (
      List.map string_of_expr_ cs
    )
  ) ^ " }"
;;

type goal = variables * locations * constraints

let string_of_goal ((vars, locs, cs) : goal) : string =
  string_of_variables vars ^ "\n" ^
  string_of_locations locs ^ "\n" ^
  string_of_constraints cs ^ "\n"

let get_builtin_name fsym =
  let (name, _) =
    List.find
      (fun (_, fsym') -> Sym.equal fsym fsym')
      B.cn_builtin_fun_names
  in
  name

let apply_builtins e =
  let Cn.CNExpr (_, e) = e in
  let res =
    match e with
    | CNExpr_call (fsym, [e]) when String.equal (get_builtin_name fsym) "is_null"->
      Cn.CNExpr_binop (CN_equal, e, CNExpr (Cerb_location.unknown, CNExpr_const CNConst_NULL))
    | _ -> e
  in
  Cn.CNExpr (Cerb_location.unknown, res)

let rec collect_resource (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (r : cn_resource) : (cn_expr_ * variables * locations * constraints) QCheck.Gen.t =
  match r with
  | CN_pred (_, CN_owned (Some ty), [Cn.CNExpr (_, e)])
  | CN_pred (_, CN_block ty, [Cn.CNExpr (_, e)]) ->
    let sym = Symbol.fresh () in
    let e' = Cn.CNExpr_var sym in
    QCheck.Gen.return (e', (sym, (ty, e'))::vars, [(e, sym)], [])
  | CN_pred (_, CN_named x, es) ->
    let pred = List.assoc Symbol.equal_sym x psi in
    let es' = List.map (fun (Cn.CNExpr (_, e')) -> e') es in
    collect_clauses psi vars (sub_sym_predicate pred es')

  | CN_pred (_, CN_owned (Some _), _) -> failwith "incorrect number of args for Owned"
  | CN_pred (_, CN_block _, _) -> failwith "incorrect number of args for Block"
  | CN_pred (_, CN_owned None, _) -> failwith "requires type for Owned"
  | CN_each _ -> failwith "each not supported"

and collect_clause (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (c : cn_clause) : (cn_expr_ * variables * locations * constraints) QCheck.Gen.t =
  QCheck.Gen.(
    match c with
    | CN_letResource (_, x, r, c') ->
      collect_resource psi vars r >>= fun (e, vars, locs, cs) ->
      collect_clause psi vars (sub_sym_clause x e c') >>= fun (e', vars, locs', cs') ->
      return (e', vars, locs @ locs', cs @ cs')
    | CN_letExpr (_, x, CNExpr (_, e), c') ->
      collect_clause psi vars (sub_sym_clause x e c')
    | CN_assert (_, CN_assert_exp (Cn.CNExpr (_, e)), c') ->
      collect_clause psi vars c' >>= fun (e', vars, locs, cs) ->
      return (e', vars, locs, e::cs)
    | CN_return (_, Cn.CNExpr (_, e)) ->
      return (e, vars, [], [])
    | CN_assert (_, CN_assert_qexp _, _) -> failwith "quantified assert not supported"
  )

and collect_clauses (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (s : cn_clauses) : (cn_expr_ * variables * locations * constraints) QCheck.Gen.t =
  match s with
  | CN_clause (_, c) -> collect_clause psi vars c
  | CN_if (_, e_if, c_then, s_else) ->
    let e_if = apply_builtins e_if in
    QCheck.Gen.(
      bool >>= fun b ->
        if b
        then
          collect_clause psi vars c_then >>= fun (e, vars, locs, cs) ->
          let Cn.CNExpr (_, e_if) = e_if in
          return (e, vars, locs, e_if::cs)
        else
          collect_clauses psi vars s_else >>= fun (e, vars, locs, cs) ->
          return (e, vars, locs, (Cn.CNExpr_not e_if)::cs)
    )

let rec collect_conditions (psi : (Symbol.sym * cn_predicate) list) (vars : variables) (c : cn_condition list) : goal QCheck.Gen.t =
  QCheck.Gen.(
    match c with
    | (CN_cletResource (_, x, r))::c' ->
      collect_resource psi vars r >>= fun (e, vars, locs, cs) ->
      collect_conditions psi vars (sub_sym_conditions x e c') >>= fun (vars, locs', cs') ->
      return (vars, locs @ locs', cs @ cs')
    | (CN_cletExpr (_, x, CNExpr (_, e)))::c' ->
      collect_conditions psi vars (sub_sym_conditions x e c')
    | (CN_cconstr (_, CN_assert_exp Cn.CNExpr (_, e)))::c' ->
      collect_conditions psi vars c' >>= fun (vars, locs, cs) ->
      return (vars, locs, e::cs)
    | (CN_cconstr (_, CN_assert_qexp _))::_ -> failwith "quantified assert not supported"
    | [] -> return (vars, [], [])
  )

let sub_sym_variables (x : Symbol.sym) (v : cn_expr_) (vars : variables) : variables =
  List.map (fun (x, (ty, e)) -> (x, (ty, sub_sym_expr_ x v e))) vars

let sub_sym_locations (x : Symbol.sym) (v : cn_expr_) (locs : locations) : locations =
  List.map (fun (e, y) -> (sub_sym_expr_ x v e, y)) locs

let sub_sym_constraints (x : Symbol.sym) (v : cn_expr_) (cs : constraints) : constraints =
  List.map (fun e -> sub_sym_expr_ x v e) cs

let sub_sym_goal (x : Symbol.sym) (v : cn_expr_) ((vars, locs, cs) : goal) : goal =
  (sub_sym_variables x v vars, sub_sym_locations x v locs, sub_sym_constraints x v cs)

let rec inline_constants (g : goal) (iter : constraints) : goal =
  match iter with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_const c), CNExpr (_, CNExpr_var x)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_const c)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_const c), CNExpr (_, CNExpr_value_of_c_atom (x, _))))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_const c)))::iter' ->
    let g = sub_sym_goal x (CNExpr_const c) g in
    inline_constants g iter'
  | _::iter' -> inline_constants g iter'
  | [] -> g
;;

let rec remove_tautologies ((vars, locs, cs) : goal) : goal =
  match cs with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_var y)))::cs when Symbol.equal_sym x y ->
    remove_tautologies (vars, locs, cs)
  | c::cs ->
    (try
      let v = eval_expr_ [] c in
      if Stdlib.(=) v (CNVal_bool true)
      then remove_tautologies (vars, locs, cs)
      else failwith "Inconsistent constraints"
    with Not_found ->
      let (vars, locs, cs) = remove_tautologies (vars, locs, cs) in
      (vars, locs, c::cs))
  | [] -> (vars, locs, cs)

let rec distribute_negation_ (e : cn_expr_) : cn_expr_ =
  Cn.(
    match e with
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_equal, e1, e2)))) ->
      CNExpr_binop (CN_inequal, distribute_negation e1, distribute_negation e2)
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_inequal, e1, e2)))) ->
      CNExpr_binop (CN_equal, distribute_negation e1, distribute_negation e2)

    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_lt, e1, e2)))) ->
      CNExpr_binop (CN_ge, distribute_negation e1, distribute_negation e2)
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_le, e1, e2)))) ->
      CNExpr_binop (CN_gt, distribute_negation e1, distribute_negation e2)
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_gt, e1, e2)))) ->
      CNExpr_binop (CN_le, distribute_negation e1, distribute_negation e2)
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_ge, e1, e2)))) ->
      CNExpr_binop (CN_lt, distribute_negation e1, distribute_negation e2)

    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_and, e1, e2)))) ->
      CNExpr_binop (CN_or,
        CNExpr (l, CNExpr_not (distribute_negation e1)),
        CNExpr (l, CNExpr_not (distribute_negation e2)))
    | (CNExpr_not (CNExpr (l, CNExpr_binop (CN_or, e1, e2)))) ->
      CNExpr_binop (CN_and,
        CNExpr (l, CNExpr_not (distribute_negation e1)),
        CNExpr (l, CNExpr_not (distribute_negation e2)))

    | _ -> e
  )

and distribute_negation (e : cn_expr) : cn_expr =
  let CNExpr (l, e) = e in
  CNExpr (l, distribute_negation_ e)
;;

let rec inline_aliasing (g : goal) (iter : constraints) : goal =
  match iter with
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_var y)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_var x), CNExpr (_, CNExpr_value_of_c_atom (y, _))))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_var y)))::iter'
  | (CNExpr_binop (CN_equal, CNExpr (_, CNExpr_value_of_c_atom (x, _)), CNExpr (_, CNExpr_value_of_c_atom (y, _))))::iter' ->
    let (vars, locs, cs) = g in
    (match List.assoc Symbol.equal_sym x vars, List.assoc Symbol.equal_sym y vars with
    | (_, CNExpr_var x'), (_, e) when Symbol.equal_sym x x' -> sub_sym_goal x (CNExpr_var y) g
    | _ -> sub_sym_goal y (CNExpr_var x) g)
  | _::iter' -> inline_aliasing g iter'
  | [] -> g
;;

let rec remove_nonnull_for_locs ((vars, locs, cs) : goal) : goal =
  match cs with
  | (CNExpr_binop (CN_inequal, CNExpr (_, e), CNExpr (_, CNExpr_const CNConst_NULL)))::cs
    when List.assoc_opt Stdlib.(=) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, locs, cs)
  | c::cs ->
    let (vars, locs, cs) = remove_nonnull_for_locs (vars, locs, cs) in
    (vars, locs, c::cs)
  | [] -> (vars, locs, [])

let rec simplify (g : goal) : goal =
  let og = g in
  let (vars, locs, cs) = g in
  let g = inline_constants g cs in
  let g = inline_aliasing g cs in
  let (vars, locs, cs) = remove_tautologies g in
  let g = (vars, locs, List.map distribute_negation_ cs) in
  let g = remove_nonnull_for_locs g in
  if Stdlib.(<>) og g
  then
    simplify g
  else
    g

let rec pow a p =
  match p with
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let is_pointer_ctype (ty : Ctype.ctype) : bool =
  match ty with
  | Ctype (_, Pointer _) -> true
  | _ -> false
;;

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
      return (CNVal_bits ((sgn, Memory.size_of_integer_type ity), Z.of_int n))
    | Struct n ->
      (match List.assoc (Symbol.equal_sym) n ail_prog.tag_definitions with
      | (_, _, StructDef (members, _)) ->
        let f m =
          let (Symbol.Identifier (_, id), (_, _, _, ty')) = m in
          if is_pointer_ctype ty'
          then
            return (id, failwith "TODO")
          else
            type_gen ail_prog ty' >>= fun v ->
            return (id, v)
        in
        flatten_l (List.map f members) >>= fun ms ->
        return (CNVal_struct (ty, ms))
      | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
    | Pointer _ ->
      failwith (
        "Tried using type-based generator on pointer type '" ^
        string_of_ctype_ cty ^
        "' (Generator.type_gen)"
      )
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

(* let rec concretize_context_constants ((vars, locs, cs) : goal) (ctx : context) : goal * context =
  match vars with
  | (x, (ty, CNExpr_const c))::vars' ->
    (try
      let v = eval_expr_ ctx (CNExpr_const c) in
      concretize_context_constants (vars', locs, cs) ((x, v)::ctx)
    with Failure _ ->
      let ((vars, locs, cs), ctx) = concretize_context_constants (vars', locs, cs) ctx in
      (((x, (ty, CNExpr_const c))::vars, locs, cs), ctx))
  | v::vars' ->
    let ((vars, locs, cs), ctx) = concretize_context_constants (vars', locs, cs) ctx in
    ((v::vars, locs, cs), ctx)
  | [] -> ((vars, locs, cs), ctx)
;; *)

let rec string_of_value (v : cn_value) : string =
  match v with
  | CNVal_null -> "NULL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n) ^ "U"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 32 -> Int64.to_string (Z.to_int64 n) ^ "L"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 32 -> string_of_int (Z.to_int n) ^ "UL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "LL"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "ULL"

  | CNVal_struct (_, ms) -> "{ " ^ String.concat ", " (List.map (fun (x, v) -> "." ^ x ^ " = " ^ string_of_value v) ms) ^ "}"

  | CNVal_bool b -> string_of_bool b
  | CNVal_integer n -> Int64.to_string (Z.to_int64 n)

  | CNVal_constr (_, ms) -> "{ " ^ String.concat ", " (List.map (fun (x, v) -> x ^ " = " ^ string_of_value v) ms) ^ "}"
  | CNVal_unit -> "()"
  | CNVal_bits _ -> failwith "unreachable"

let string_of_context (ctx : context) : string =
  "{ " ^ (
    List.fold_left (
      fun a b ->
        if String.equal a ""
        then b
        else a ^ "; " ^ b
    ) "" (
      List.map (
        fun (x, (ty, v)) ->
          Pp_symbol.to_string_pretty x ^ " -> (" ^ string_of_ctype ty ^ ", " ^ string_of_value v ^ ")"
      ) ctx
    )
  ) ^ " }"
;;

let rec concretize_context_generate ail_prog ((vars, locs, cs) : goal) (ctx : context) : (goal * context) QCheck.Gen.t =
  QCheck.Gen.(
    match vars with
    | (x, (ty, CNExpr_var x'))::vars'
    | (x, (ty, CNExpr_value_of_c_atom (x', _)))::vars'
      when Symbol.equal_sym x x' && not (is_pointer_ctype ty) ->
        type_gen ail_prog ty >>= fun v ->
        (match check_constraints ((x, (ty, v))::ctx) cs with
        | Some cs -> concretize_context_generate ail_prog (vars', locs, cs) ((x, (ty, v))::ctx)
        | None ->
          concretize_context_generate ail_prog (vars', locs, cs) ctx >>= fun ((vars, locs, cs), ctx) ->
          return (((x, (ty, Cn.CNExpr_var x))::vars, locs, cs), ctx))
    | v::vars' ->
      concretize_context_generate ail_prog (vars', locs, cs) ctx >>= fun ((vars, locs, cs), ctx) ->
      return ((v::vars, locs, cs), ctx)
    | [] -> return ((vars, locs, cs), ctx)
  )
;;

let rec concretize_context_evaluate ((vars, locs, cs) : goal) (ctx : context) : goal * context =
  match vars with
  | (x, (ty, e))::vars' ->
    (try
      let v = eval_expr_ ctx e in
      concretize_context_evaluate (vars', locs, cs) ((x, (ty, v))::ctx)
    with Not_found ->
      let ((vars, locs, cs), ctx) = concretize_context_evaluate (vars', locs, cs) ctx in
      (((x, (ty, e))::vars, locs, cs), ctx))
  | [] -> ((vars, locs, cs), ctx)
;;

let rec concretize_context' ail_prog (g : goal) (ctx : context) (tolerance : int) : context QCheck.Gen.t =
  QCheck.Gen.(
    let (vars, _, _) = g in
    let old_num_left = List.length (List.filter (fun (_, (ty, _)) -> not (is_pointer_ctype ty)) vars) in
    concretize_context_generate ail_prog g ctx >>= fun (g, ctx) ->
    let ((vars, locs, cs), ctx) = concretize_context_evaluate g ctx in
    let num_left = List.length (List.filter (fun (_, (ty, _)) -> not (is_pointer_ctype ty)) vars) in
    if num_left = 0
    then
      return ctx
    else if num_left <> old_num_left
    then
      concretize_context' ail_prog (vars, locs, cs) ctx tolerance
    else if tolerance > 0
    then
      concretize_context' ail_prog (vars, locs, cs) ctx (tolerance - 1)
    else
      failwith "Failed to concretize"
  )

let concretize_context ail_prog (g : goal) : context QCheck.Gen.t =
  concretize_context' ail_prog g [] 10

let generate_location (max_size : int) (h : heap) : int QCheck.Gen.t =
  QCheck.Gen.(
    int_range 1 (max_size / 8 - List.length h) >>= fun n ->
    return (
      h
      |> List.map fst
      |> List.sort compare
      |> List.fold_left (fun acc i -> if n >= i then n + 1 else n) n
    )
  )

let rec concretize_heap' (max_size : int) (ctx : context) (locs : locations) (h : heap) : (context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    match locs with
    | (e, x)::locs' ->
      generate_location max_size h >>= fun l ->
      let (ty, v) = List.assoc Symbol.equal_sym x ctx in
      let ctx =
        match e with
        | CNExpr_var x'
        | CNExpr_value_of_c_atom (x', _) ->
          let ty = Ctype.Ctype ([], Pointer (no_quals, ty)) in
          (x', (ty, CNVal_bits ((CN_unsigned, 64), Z.of_int l)))::ctx
        | _ -> ctx
      in
      (match eval_expr_ ctx e with
      | CNVal_integer n
      | CNVal_bits ((_, _), n) -> concretize_heap' max_size ctx locs' ((Z.to_int n, (ty, v))::h)
      | _ -> failwith "Invalid pointer (Generator.concretize_heap)")
    | [] -> return (ctx, h)
  )

let concretize_heap (max_size : int) (ctx : context) (g : goal) : (context * heap) QCheck.Gen.t =
  let (_, locs, _) = g in
  concretize_heap' max_size ctx locs []

let concretize ail_prog (max_size : int) (g : goal) : (goal * context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    concretize_context ail_prog g >>= fun ctx ->
    concretize_heap max_size ctx g >>= fun (ctx, h) ->
    return (g, ctx, h)
  )

let generate ail_prog (psi : (Symbol.sym * cn_predicate) list) (args : (Symbol.sym * Ctype.ctype) list) (c : cn_condition list) (max_size : int) : (goal * context * heap) QCheck.Gen.t =
  QCheck.Gen.(
    let vars = List.map (fun (x, ty) -> (x, (ty, Cn.CNExpr_var x))) args in
    collect_conditions psi vars c >>= fun g ->
    let g = simplify g in
    concretize ail_prog max_size g
  )

let string_of_list f l =
  (List.fold_left (fun acc s -> acc ^ (if String.equal acc "[" then "" else "; ") ^ f s) "[" l) ^ "]"
;;

let rec codify_value (v : cn_value) : string =
  match v with
  | CNVal_null -> "NULL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 16 -> Int64.to_string (Z.to_int64 n) ^ "U"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 32 -> Int64.to_string (Z.to_int64 n) ^ "L"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 32 -> string_of_int (Z.to_int n) ^ "UL"
  | CNVal_bits ((CN_signed, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "LL"
  | CNVal_bits ((CN_unsigned, bits), n) when bits <= 64 -> Int64.to_string (Z.to_int64 n) ^ "ULL"

  | CNVal_struct (_, ms) -> "{ " ^ String.concat ", " (List.map (fun (x, v) -> "." ^ x ^ " = " ^ codify_value v) ms) ^ "}"

  | CNVal_bool _ -> failwith "Booleans aren't yet supported in unit test generation"
  | CNVal_integer _ -> failwith "Can't generate mathematical integers"

  | CNVal_constr _ 
  | CNVal_unit
  | CNVal_bits _ -> failwith "unreachable"

let expand_heap (ctx : context) (h : heap) : (context * heap) =
  let root = ref (-1) in
  let ctx = ref ctx in
  let h = List.map
    (fun (p, (ty, v)) ->
      let res = (!root + p) in
      root := !root + (Memory.size_of_ctype (Sctypes.of_ctype_unsafe Cerb_location.unknown ty)) - 1;
      ctx :=
        (List.map
          (fun (i, (ty, v)) ->
            if not (is_pointer_ctype ty)
            then
              (i, (ty, v))
            else
             match v with
              | CNVal_integer n
              | CNVal_bits (_, n) ->
                if Z.to_int n = p
                then (i, (ty, CNVal_bits ((CN_unsigned, 64), Z.of_int res)))
                else (i, (ty, v))
              | CNVal_null -> (i, (ty, v))
              | _ -> failwith ("Invalid pointer value " ^ string_of_value v)
          ) !ctx);
      (res, (ty, v)))
    (List.sort (fun (i, _) (j, _) -> compare i j) h)
  in
  (!ctx, h)
;;

let codify_heap (h : heap) (max_size : int) (oc : out_channel) : unit =
  output_string oc "void *h = malloc(";
  output_string oc (string_of_int max_size);
  output_string oc ");\n";
  List.iter
    (fun (p, (ty, v)) ->
      let ty_str = string_of_ctype ty in
      let rhs = "*(" ^ ty_str ^ "*)((uintptr_t)h + " ^ string_of_int p ^ ") = " in
      output_string oc rhs;
      output_string oc (codify_value v);
      output_string oc ";\n")
    h

let codify_context (ctx : context) (args : (Symbol.sym * Ctype.ctype) list) (oc : out_channel) : unit =
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
            if is_pointer_ctype ty
            then
              match v with
              | CNVal_integer n
              | CNVal_bits (_, n) ->
                ("(" ^ ty_str ^ ")((uintptr_t)h + " ^ Z.to_string n ^ "ULL)")
              | CNVal_null -> "nullptr"
              | _ -> failwith ("Invalid pointer value " ^ string_of_value v)
            else
              codify_value v
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

let codify_header (tf : test_framework) (suite : string) (test : string) (oc : out_channel) : unit =
  match tf with
  | GTest -> output_string oc ("\nTEST(" ^ String.capitalize_ascii suite ^ ", " ^ test ^ "){\n")
  | Catch2 -> output_string oc ("\nTEST_CASE(\"" ^ test ^ "\", \"[" ^ String.lowercase_ascii suite ^ "]\"){\n");
;;

let codify (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (args : (Symbol.sym * Ctype.ctype) list) (ctx : context) (h : heap) (index : int) (max_size : int) (oc : out_channel) : unit =
  codify_header tf (Pp_symbol.to_string_pretty instrumentation.fn) ("Test" ^ string_of_int index) oc;

  let (ctx, h) = expand_heap ctx h in
  codify_heap h max_size oc;
  codify_context ctx args oc;
  output_string oc (Pp_symbol.to_string_pretty instrumentation.fn);
  output_string oc "(";
  output_string oc (args |> List.map fst |> List.map Pp_symbol.to_string_pretty |> String.concat ", ");
  output_string oc ");\n";

  output_string oc "}\n";
;;



let generate_unit_test (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (max_size : int) (oc : out_channel) (generated : goal list) (tolerance : int) : goal list =
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
  List.iter
    (fun (ty : Ctype.ctype) ->
      match ty with
      | Ctype (_, Basic (Integer ity)) -> ()
      | _ -> ())
       (* failwith "Only support unit tests for integers") *)
    arg_types;
  let args = List.combine arg_syms arg_types in
  let (g, ctx, h) = QCheck.Gen.generate1 (generate ail_prog psi args (instrumentation.surface.requires) max_size) in
  if tolerance == 0 || (List.find_opt (fun g' -> Stdlib.(=) g g') generated |> Option.is_none)
  then (
    codify tf instrumentation ail_prog args ctx h (List.length generated + 1) max_size oc;
    g::generated
  ) else generated
;;

let range i j =
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux (j-1) []
;;

let rec generate_unit_tests (tf : test_framework) (instrumentation : Core_to_mucore.instrumentation) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (max_size : int) (oc : out_channel) (generated : goal list) (num_tests : int) (tolerance : int) : unit =
  let n = num_tests - List.length generated in
  let generated = ref generated in
  List.iter
    (fun _ -> generated := generate_unit_test tf instrumentation ail_prog max_size oc !generated tolerance)
    (range 0 n);
  let num_generated = List.length !generated in
  if tolerance >= 0 && num_generated < num_tests
  then
    generate_unit_tests tf instrumentation ail_prog max_size oc !generated num_tests (tolerance - 1)
;;

let generate_tests (tf : test_framework) (instrumentation_list : Core_to_mucore.instrumentation list) (ail_prog : GenTypes.genTypeCategory AilSyntax.sigma) (max_size : int) (oc : out_channel) (num_tests : int) : unit =
  List.iter
    (fun inst ->
      try
        generate_unit_tests tf inst ail_prog max_size oc [] num_tests (10 * num_tests)
      with Failure m ->
        print_string ("Failed to generate all tests for `" ^ Sym.pp_string inst.fn ^ "` due to the following:\n" ^ m ^ "\n")
    ) instrumentation_list
