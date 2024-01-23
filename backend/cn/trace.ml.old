module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module StringMap = Map.Make(String)
module IntSet = Set.Make(Int)
module IT = IndexTerms
module BT = BaseTypes
open Mucore

type 'TY opt_pat = 'TY mu_pattern option
type 'TY expr = 'TY mu_expr
type 'TY pexpr = 'TY mu_pexpr

type mu_trace_step = {
    expr_doc : Pp.doc Lazy.t;
    expr_loc : Locations.t;
    pat_opt_doc: Pp.doc Lazy.t option;
    ct_before: Context.t;
    ct_after: Context.t;
  }

type mu_trace = mu_trace_step list

type t = {
  mu_trace: mu_trace
}

let empty = {mu_trace = []}

let add_trace_step pat (expr : 'a mu_expr) (ct1, ct2) (tr : t) =
  let expr_doc = lazy (Pp_mucore.pp_expr_w (Some 100) expr) in
  let expr_loc = loc_of_expr expr in
  let pat_opt_doc = Option.map (fun pat -> lazy (Pp_mucore.Basic.pp_pattern pat)) pat in
  let step = {expr_doc; expr_loc; pat_opt_doc; ct_before = ct1; ct_after = ct2} in
  {mu_trace = step :: tr.mu_trace}

let add_pure_trace_step pat (expr : 'a mu_pexpr) (ct1, ct2) (tr : t) =
  let expr_doc = lazy (Pp_mucore.pp_pexpr_w (Some 100) expr) in
  let expr_loc = loc_of_pexpr expr in
  let pat_opt_doc = Option.map (fun pat -> lazy (Pp_mucore.Basic.pp_pattern pat)) pat in
  let step = {expr_doc; expr_loc; pat_opt_doc; ct_before = ct1; ct_after = ct2} in
  {mu_trace = step :: tr.mu_trace}

let rec take i xs = match i <= 0, xs with
  | true, _ -> []
  | _, [] -> []
  | _, (x :: xs) -> x :: take (i - 1) xs

let list_new xs ys =
  (* difference between xs and ys, assuming ys (pre-) extends xs *)
  let len = List.length ys - List.length xs in
  take len ys

let set_new xs ys =
  let open Context in
  (* difference between xs and ys, assuming ys (pre-) extends xs *)
  LCSet.elements (LCSet.diff ys xs)

let map_new xs ys =
  let open Context in
  (* difference between xs and ys, assuming ys (pre-) extends xs *)
  SymMap.bindings
    (SymMap.merge (fun s in_xs in_ys ->
         match in_xs, in_ys with
         | Some _, Some _ -> None
         | None, Some b -> Some b
         | Some x, None ->
             Pp.warn Locations.unknown (Pp.item "trace: map_new: element disappeared" (Sym.pp s));
             None
         | None, None -> None
       ) xs ys
    )

let ctxt_diff ct1 ct2 =
  let open Context in
  let log = map_new ct1.logical ct2.logical in
  let com = map_new ct1.computational ct2.computational
    |> List.map (fun (nm, t) -> (nm, t)) in
  let con = set_new ct1.constraints ct2.constraints in
  let rs1 = IntSet.of_list (List.map snd (fst ct1.resources)) in
  let rs2 = IntSet.of_list (List.map snd (fst ct2.resources)) in
  let rs_del = List.filter (fun (_, i) -> not (IntSet.mem i rs2)) (fst ct1.resources)
    |> List.map fst in
  let rs_add = List.filter (fun (_, i) -> not (IntSet.mem i rs1)) (fst ct2.resources)
    |> List.map fst in
  (log, com, con, (rs_del, rs_add))

let format_mu (p : Pp.doc Lazy.t option) expr_doc =
  let open Pp in
  let rhs = Lazy.force expr_doc in
  match p with
    | None -> rhs
    (* | Some (M_Symbol sym) -> Sym.pp sym ^^^ string "<-" ^^^ rhs *)
    | Some ((* M_Pat *) pat_pp) ->
       !^ "mu_step:" ^^^ Lazy.force pat_pp ^^^ !^ "<-" ^^^ rhs

let format_eval model global it =
  let open Pp in
  match Solver.eval global model it with
  | None -> parens (!^ "cannot eval:" ^^^ IT.pp it)
  | Some v -> IT.pp it ^^^ equals ^^^ IT.pp v

let format_var model global (sym, (binding, _)) =
  match binding with
  | Context.BaseType bt -> format_eval model global (IT.sym_ (sym, bt))
  | Context.Value it -> format_eval model global it

let pp_oargs model global = function
  | Resources.O it -> format_eval model global it

let try_eval model global it =
  match Solver.eval global model it with
  | None -> it
  | Some v -> v

let eval_in_pred model global res =
  let open ResourceTypes in
  match res with
  | P p -> P {p with
    pointer = try_eval model global p.pointer;
    iargs = List.map (try_eval model global) p.iargs
  }
  | _ -> res

let format_delta model ct1 ct2 =
  let open Pp in
  let (log, com, con, (rs_del, rs_add)) = ctxt_diff ct1 ct2 in
  let doc_new nm f = function
    | [] -> []
    | syms -> [hang 8 (string nm ^^ colon ^^ break 1 ^^
        (flow (comma ^^ break 1) (List.map f syms)))]
  in
  let global = ct2.global in
  let pp_res_ty res = ResourceTypes.pp (eval_in_pred model global res) in
  let deleted (rt, _) = pp_res_ty rt ^^^ !^"|-> X" in
  let added (rt, oargs) = pp_res_ty rt ^^^ !^"|->" ^^^ pp_oargs model global oargs in
  List.map added rs_add @ List.map deleted rs_del @
    doc_new "Logical vars" (format_var model global) log @
    doc_new "Computational vars" (format_var model global) com @
    doc_new "Constraints" LogicalConstraints.pp con

let format_mu_step model (s : mu_trace_step) =
  Pp.hang 4 (Pp.flow Pp.hardline
    (format_mu s.pat_opt_doc s.expr_doc :: format_delta model s.ct_before s.ct_after))

let region_subset (x_l, x_r) (y_l, y_r) =
  let open Lexing in
  String.equal x_l.pos_fname y_l.pos_fname
    && x_l.pos_cnum >= y_l.pos_cnum
    && y_r.pos_cnum <= y_r.pos_cnum

let group_to_statements statement_locs trace =
  let step_stmt_loc step = CStatements.LocMap.find_opt step.expr_loc statement_locs in
  let eq_opt_loc = Option.equal CStatements.LocCompare.equal in
  let rec f cur_reg cur_group groups = function
    | [] -> List.rev ((cur_reg, List.rev cur_group) :: groups)
    | step :: steps ->
      let sloc = step_stmt_loc step in
      if eq_opt_loc sloc cur_reg
      then f cur_reg (step :: cur_group) groups steps
      else
        f sloc [step] ((cur_reg, List.rev cur_group) :: groups) steps
  in
  match trace with
    | [] -> []
    | step :: steps -> f (step_stmt_loc step) [step] [] steps

let get_file_lines groups =
  let rec read_all file =
    try
      let l = input_line file in
      l :: read_all file
    with
      End_of_file -> []
  in
  let get fname m =
    if not (StringMap.mem fname m) && Sys.file_exists fname
    then
      let file = open_in fname in
      let ls = read_all file in
      close_in file;
      StringMap.add fname ls m
    else m
  in
  let open Lexing in
  let fs = List.filter_map fst groups
    |> List.filter_map Locations.is_region
    |> List.map (fun (p, _) -> p.pos_fname)
  in
  List.fold_right get fs StringMap.empty

let line_range (x, y) =
  let open Pp in
  let open Lexing in
  if x.pos_lnum == y.pos_lnum
    then Pp.int x.pos_lnum
    else Pp.int x.pos_lnum ^^^ !^ "-" ^^^ Pp.int y.pos_lnum

let reg_snippet opt_loc = match Option.bind opt_loc Locations.is_region with
  | None -> Pp.string "<non-statement scope>"
  | Some (loc_start, loc_end) ->
  let open Pp in
  try
    let open Lexing in
    if Sys.file_exists loc_start.pos_fname
    then
      let file = open_in loc_start.pos_fname in
      seek_in file loc_start.pos_cnum;
      let s = really_input_string file (loc_end.pos_cnum - loc_start.pos_cnum) in
      close_in file;
      line_range (loc_start, loc_end) ^^ colon ^^ break 1 ^^ !^ s
    else
      !^ "<missing file" ^^^ !^ (loc_start.pos_fname) ^^ !^ ">"
  with
    End_of_file -> !^ "<truncated file" ^^^ !^ (loc_start.pos_fname) ^^ !^ ">"

let reg_snippet2 opt_loc file_lines = match Option.bind opt_loc Locations.is_region with
  | None -> Pp.string "<non-statement scope>"
  | Some (loc_start, loc_end) ->
    let open Pp in
    let r = line_range (loc_start, loc_end) in
    let fname = loc_start.pos_fname in
    let snip = match StringMap.find_opt fname file_lines with
      | None -> !^ "<file not found" ^^^ !^ fname ^^ !^ ">"
      | Some lines -> begin match List.nth_opt lines (loc_start.pos_lnum - 1) with
          | None -> !^ "<file truncated" ^^^ !^ fname ^^ !^ ">"
          | Some l ->
              let x = loc_start.pos_cnum - loc_start.pos_bol in
              let y = loc_end.pos_cnum - loc_start.pos_cnum in
              let extra = if loc_end.pos_lnum == loc_start.pos_lnum then "" else " ..." in
              begin try !^ (String.sub l x y) ^^ !^ extra
                with Invalid_argument _ -> !^ "in" ^^^ parens (!^ l ^^ !^ extra)
              end
          end
    in
    r ^^ colon ^^^ snip

let format_group model file_lines (opt_region, steps) =
  let open Pp in
  let l1 = !^ "Executing" ^^^ reg_snippet2 opt_region file_lines in
  let init_ct = (List.hd steps).ct_before in
  let end_ct = (List.hd (List.rev steps)).ct_after in
  let bit1 = !^ "Summary:" :: format_delta model init_ct end_ct in
  let step_docs = List.map (format_mu_step model) steps in
  hang 4 (Pp.flow Pp.hardline (l1 :: bit1 @ (!^ "") :: step_docs)) ^^ hardline

let format_init_step model step =
  let open Pp in
  let l1 = !^ "Initial state:" in
  let ct = step.ct_before in
  hang 4 (Pp.flow Pp.hardline (l1 :: format_delta model Context.empty ct))


let format_trace model (tr : t) = match tr.mu_trace with
  | [] -> Pp.string "empty trace"
  | fin_step :: _ ->
    let fin_ctxt = fin_step.ct_after in
    let locs = fin_ctxt.statement_locs in
    let tr_ord = List.rev tr.mu_trace in
    let init_step = format_init_step model (List.hd tr_ord) in
    let groups = tr_ord |> group_to_statements locs in
    let file_lines = get_file_lines groups in
    Pp.flow Pp.hardline (init_step :: List.map (format_group model file_lines) groups)


let format_eval_sym model global sym bt =
  let typ_pp = Pp.typ (Sym.pp sym) (BT.pp bt) in
  let open Pp in
  match Solver.eval global model (IT.sym_ (sym, bt)) with
  | None -> typ_pp ^^^ parens (format [Red] "cannot eval")
  | Some v -> typ_pp ^^^ equals ^^^ IT.pp v


let log_block ctxt model (sym, (bt, (loc, info))) =
  let (head, pos) = Locations.head_pos_of_location loc in
  let open Pp in
  format_eval_sym model ctxt.Context.global sym bt ^^ hardline ^^
  Lazy.force info ^^ hardline ^^
  string ("at:") ^^^ string head ^^ colon ^^ hardline ^^
  string pos ^^ hardline

let format_ctxt_logical_trace model (ctxt : Context.t) =
  let preamble = [Pp.string "Logical variables created in type-checking:"] in
  let non_unit =
    List.filter_map (fun (s, (binding, linfo)) ->
      match binding with
      | Context.BaseType bt when not (BT.equal bt BT.Unit) ->
        Some (s, (bt, linfo))
      | _ ->
        None
    ) (Context.SymMap.bindings ctxt.Context.logical)
  in
  Pp.flow Pp.hardline (preamble @ List.map (log_block ctxt model) non_unit)



