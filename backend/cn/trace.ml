module CF = Cerb_frontend

module Mucore = CF.Mucore
module New = NewMu.New
module SymSet = Set.Make(Sym)

module IntSet = Set.Make(Int)

module IT = IndexTerms

type opt_pat = unit New.mu_sym_or_pattern option
type expr = unit New.mu_expr
type pexpr = unit New.mu_pexpr

type mu_trace_step = {
    expr: expr;
    pat: opt_pat;
    ct_before: Context.t;
    ct_after: Context.t;
  }

type mu_trace = mu_trace_step list

type t = {
  mu_trace: mu_trace
}

let empty = {mu_trace = []}

let add_trace_step pat expr (ct1, ct2) (tr : t) =
  let step = {expr; pat; ct_before = ct1; ct_after = ct2} in
  {mu_trace = step :: tr.mu_trace}

let add_pure_trace_step pat expr cts tr =
  add_trace_step pat (New.embed_pexpr_expr expr) cts tr

let rec take i xs = match i <= 0, xs with
  | true, _ -> []
  | _, [] -> []
  | _, (x :: xs) -> x :: take (i - 1) xs

let list_new xs ys =
  (* difference between xs and ys, assuming ys (pre-) extends xs *)
  let len = List.length ys - List.length xs in
  take len ys

let ctxt_diff ct1 ct2 =
  let open Context in
  let log = list_new ct1.logical ct2.logical in
  let com = list_new ct1.computational ct2.computational
    |> List.map (fun (nm, (t, _)) -> (nm, t)) in
  let con = list_new (snd ct1.constraints) (snd ct2.constraints) in
  let rs1 = IntSet.of_list (List.map snd (fst ct1.resources)) in
  let rs2 = IntSet.of_list (List.map snd (fst ct2.resources)) in
  let rs_del = List.filter (fun (_, i) -> not (IntSet.mem i rs2)) (fst ct1.resources)
    |> List.map fst in
  let rs_add = List.filter (fun (_, i) -> not (IntSet.mem i rs1)) (fst ct2.resources)
    |> List.map fst in
  (log, com, con, (rs_del, rs_add))

let format_mu (p : opt_pat) expr =
  let open Pp in
  let rhs = match expr with
    | NewMu.New.M_Expr (_, _, NewMu.New.M_Epure e) -> NewMu.pp_pexpr e
    | _ -> NewMu.pp_expr expr
  in
  match p with
    | None -> rhs
    (* | Some (M_Symbol sym) -> Sym.pp sym ^^^ string "<-" ^^^ rhs *)
    | Some (M_Pat pat) -> NewMu.PP_MUCORE.pp_pattern pat ^^^ string "<-" ^^^ rhs

let format_var model global (sym, bt) =
  let open Pp in
  match Solver.eval global model (IT.sym_ (sym, bt)) with
  | None -> Sym.pp sym ^^^ !^"=??"
  | Some v -> Sym.pp sym ^^^ equals ^^^ IT.pp v

let format_mu_step model (s : mu_trace_step) =
  let open Pp in
  let (log, com, con, (rs_del, rs_add)) = ctxt_diff s.ct_before s.ct_after in
  let doc_new nm f = function
    | [] -> []
    | syms -> [hang 8 (string nm ^^ colon ^^ break 1 ^^
        (flow (comma ^^ break 1) (List.map f syms)))]
  in
  let global = s.ct_after.global in
  let deleted (rt, _) = ResourceTypes.pp rt ^^^ !^"|-> X" in
  let added (rt, oargs) = ResourceTypes.pp rt ^^^ !^"|->" ^^ break 1 ^^ Resources.pp_oargs oargs in
  let docs = format_mu s.pat s.expr ::
    doc_new "Logical vars" (format_var model global) log @
    doc_new "Computational vars" (format_var model global) com @
    doc_new "Constraints" LogicalConstraints.pp con @
    List.map added rs_add @ List.map deleted rs_del
  in
  hang 4 (flow hardline docs)

let group_to_statements statement_locs trace =
  let step_reg step = Locations.is_region (New.loc_of_expr step.expr) in
  let m step opt_reg = Option.equal Locations.region_inter (step_reg step) opt_reg in
  let regs = statement_locs |> List.filter_map Locations.is_region in
  let rec f cur_reg cur_group groups = function
    | [] -> List.rev ((cur_reg, List.rev cur_group) :: groups)
    | step :: steps -> if m step cur_reg
      then f cur_reg (step :: cur_group) groups
      else
        let opt_reg = List.find_opt (m step) regs in
        f opt_reg [step] ((cur_reg, List.rev cur_group) :: groups)
  in
  match trace with
    | [] -> []
    | step :: steps -> f (List.find_opt (m step) regs) [step] [] steps


let format_trace model (tr : t) = match tr.mu_trace with
  | [] -> Pp.string "empty trace"
  | fin_step :: _ ->
    let fin_ctxt = fst_step.ct_after in
    let locs = fin_ctxt.statement_locs in
    let groups = List.rev tr.mu_trace |> group_to_statements locs in
    Pp.flow_map Pp.hardline (format_mu_step model) (List.rev tr.mu_trace)


