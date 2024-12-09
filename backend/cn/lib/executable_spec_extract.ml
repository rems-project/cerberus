open Mucore

type statement = Locations.t * Cnprog.t list

let statement_subst subst ((loc, cnprogs) : statement) : statement =
  (loc, List.map (Cnprog.subst subst) cnprogs)


type statements = statement list

let statements_subst subst = List.map (statement_subst subst)

type loop = Locations.t * Locations.t * statements ArgumentTypes.t

let loop_subst subst ((cond_loc, loop_loc, at) : loop) =
  (cond_loc, loop_loc, ArgumentTypes.subst statements_subst subst at)


type loops = loop list

let loops_subst subst = List.map (loop_subst subst)

type fn_body = statements * loops

let fn_body_subst subst ((statements, loops) : fn_body) =
  (statements_subst subst statements, loops_subst subst loops)


type fn_rt_and_body = ReturnTypes.t * fn_body

let fn_rt_and_body_subst subst ((rt, fn_body) : fn_rt_and_body) =
  (ReturnTypes.subst subst rt, fn_body_subst subst fn_body)


type fn_args_and_body = fn_rt_and_body ArgumentTypes.t

let fn_args_and_body_subst subst (at : fn_args_and_body) : fn_args_and_body =
  ArgumentTypes.subst fn_rt_and_body_subst subst at


type fn_largs_and_body = fn_rt_and_body LogicalArgumentTypes.t

let fn_largs_and_body_subst subst (lat : fn_largs_and_body) : fn_largs_and_body =
  LogicalArgumentTypes.subst fn_rt_and_body_subst subst lat


type instrumentation =
  { fn : Sym.t;
    fn_loc : Locations.t;
    internal : fn_args_and_body option
  }

(* replace `s_replace` of basetype `bt` with `s_with` *)
let sym_subst (s_replace, bt, s_with) =
  let module IT = IndexTerms in
  IT.make_subst [ (s_replace, IT.sym_ (s_with, bt, Cerb_location.unknown)) ]


(**  
let concat2 (x : 'a list * 'b list) (y : 'a list * 'b list) : 'a list * 'b list =
  let a1, b1 = x in
  let a2, b2 = y in
  (a1 @ a2, b1 @ b2)


let concat2_map (f : 'a -> 'b list * 'c list) (xs : 'a list) : 'b list * 'c list =
  List.fold_right (fun x acc -> concat2 (f x) acc) xs ([], [])


let rec stmts_in_expr (Mucore.Expr (loc, _, _, e_)) =
  match e_ with
  | Epure _ -> ([], [])
  | Ememop _ -> ([], [])
  | Eaction _ -> ([], [])
  | Eskip -> ([], [])
  | Eccall _ -> ([], [])
  | Elet (_, _, e) -> stmts_in_expr e
  | Eunseq es -> concat2_map stmts_in_expr es
  | Ewseq (_, e1, e2) -> concat2 (stmts_in_expr e1) (stmts_in_expr e2)
  | Esseq (_, e1, e2) -> concat2 (stmts_in_expr e1) (stmts_in_expr e2)
  | Eif (_, e1, e2) -> concat2 (stmts_in_expr e1) (stmts_in_expr e2)
  | Ebound e -> stmts_in_expr e
  | End es -> concat2_map stmts_in_expr es
  | Erun _ -> ([], [])
  | CN_progs (stmts_s, stmts_i) -> ([ (loc, stmts_s) ], [ (loc, stmts_i) ])
*)

let rec stmts_in_expr (Mucore.Expr (loc, _, _, e_)) =
  match e_ with
  | Epure _ -> []
  | Ememop _ -> []
  | Eaction _ -> []
  | Eskip -> []
  | Eccall _ -> []
  | Elet (_, _, e) -> stmts_in_expr e
  | Eunseq es -> List.concat_map stmts_in_expr es
  | Ewseq (_, e1, e2) -> stmts_in_expr e1 @ stmts_in_expr e2
  | Esseq (_, e1, e2) -> stmts_in_expr e1 @ stmts_in_expr e2
  | Eif (_, e1, e2) -> stmts_in_expr e1 @ stmts_in_expr e2
  | Ebound e -> stmts_in_expr e
  | End es -> List.concat_map stmts_in_expr es
  | Erun _ -> []
  | CN_progs (_stmts_s, stmts_i) -> [ (loc, stmts_i) ]


let from_loop ((_label_sym : Sym.t), (label_def : _ label_def)) : loop option =
  match label_def with
  | Return _ -> None
  | Label (_loc, label_args_and_body, _annots, _, `Loop (loop_condition_loc, loop_loc)) ->
    let label_args_and_body = Core_to_mucore.at_of_arguments Fun.id label_args_and_body in
    let label_args_and_statements = ArgumentTypes.map stmts_in_expr label_args_and_body in
    Some (loop_condition_loc, loop_loc, label_args_and_statements)


let from_fn (fn, decl) =
  match decl with
  | ProcDecl (fn_loc, _fn) -> { fn; fn_loc; internal = None }
  | Proc { loc = fn_loc; args_and_body; _ } ->
    let args_and_body = Core_to_mucore.at_of_arguments Fun.id args_and_body in
    let internal =
      ArgumentTypes.map
        (fun (body, labels, rt) ->
          let stmts = stmts_in_expr body in
          let loops = List.filter_map from_loop (Pmap.bindings_list labels) in
          (rt, (stmts, loops)))
        args_and_body
    in
    { fn; fn_loc; internal = Some internal }


let from_file (file : _ Mucore.file) =
  let instrs = List.map from_fn (Pmap.bindings_list file.funs) in
  (instrs, Compile.symtable)


let collect_instrumentation = from_file
