(* This file is for transforming Core programs which use run/save, into Core
   programs which use a jump/where, a more compositional construct with the
   following semantics (plus context reduction, omitted).

     [Where-Pure]
     pe => val
     ---------------------------------
     pure(pe) where defs end --> pure(val)

     [Jump-Sub]
     defs(l) = x . E
     ----------------------------------------------
     jump l(pe) where defs end --> {val/x} E where defs

     [Jump-Where]
     l not in defs
     ------------------------------------
     jump l(pe) where defs end --> jump l(pe)

     [Jump-Let]
     ---------------------------------------
     lets _ = jump l(pe) in E --> jump l(pe)

   Semantics are reminiscent of checked exceptions: jump
   propagates out through let-strong continuations until caught
   by an enclosing where.

   We do this in 2 stages:
   1. Annotate the AST with dominator context for each label.
    - First, a bottom-up pass which annotates each node with a map from labels
      to number of children which refer to that label.
    - Second, a top-down pass uses that information to find the tightest node
      which encloses all uses of a label.
   2. Start from a label, and capture its context outwards.
      Since labels can share contexts, multiple can be capturing
      at the same time, and this is tracked.
      At each dominator context, remove the dominated labels from
      the tracked set.
      When the set of live labels is empty, that is where we place a
      where-expression.

   We simplifiy the problem by observing (in the absence of GCC statement
   expressions) labels only occur inside some combination of Esseq,
   Eif, Ecase, Esave. *)

open Core

open Cerb_colour
open Cerb_pp_prelude

type pattern = Symbol.sym generic_pattern

type pexpr = (unit, Symbol.sym) generic_pexpr

type expr = (unit, unit, Symbol.sym) generic_expr

type 'a param = {
  name : Symbol.sym;
  bTy : core_base_type;
  optCTy : (Ctype.ctype * pass_by_value_or_pointer) option;
  pexpr : 'a;
}

let param_map f { name; bTy; optCTy; pexpr } =
  { name; bTy; optCTy; pexpr = f pexpr }

type 'info where = {
  info : 'info;
  annot : Annot.annot list;
  node : 'info where_
}

and 'info where_ =
  | Base of (unit, unit, Symbol.sym) generic_expr_
  | If of pexpr * 'info where * 'info where
  | Sseq of pattern * 'info where * 'info where
  | Case of pexpr * (pattern * 'info where) list
  | Run of Symbol.sym * pexpr list
  | Jump of Symbol.sym * pexpr list
  | Where of 'info where * ('info, unit) label_def list
  | Save of ('info, pexpr) label_def

and ('info, 'pexpr) label_def = {
  label : Symbol.sym;
  ret_bTy : core_base_type;
  params : 'pexpr param list;
  body : 'info where
}

let pp_sym s = !^ (Pp_symbol.to_string_pretty s)

let pp_where pp_info w =
  let open Cerb_pp_prelude in
  let pp_keyword w = pp_ansi_format [Bold; Magenta] (fun () -> !^ w) in
  let pp_control w = pp_ansi_format [Bold; Blue] (fun () -> !^ w) in
  let pp_pexpr pe = Pp_core.All.pp_pexpr pe in
  let pp_pat pat = Pp_core.All.pp_pattern pat in
  let pp_bty bTy = Pp_core.Basic.pp_core_base_type bTy in
  let rec pp w =
    let info = pp_info w.info in
    let some x = pp_ansi_format [Green] (fun () -> P.enclose P.space P.space (P.brackets x)) in
    let info = Option.fold ~none:P.space ~some info in
    match w.node with
    | Base _ ->
        !^ "..."
    | If (pe, w1, w2) ->
        pp_control "if" ^^ info ^^ pp_pexpr pe ^^^ pp_control "then" ^^
        P.nest 2 (P.break 1 ^^ pp w1) ^^ P.break 1 ^^
        pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp w2)
    | Sseq (pat, w1, w2) ->
        P.group begin
          (pp_control "let" ^^ info ^^ pp_pat pat ^^^ P.equals) ^//^
            (pp w1 ^^^ pp_control "in")
        end ^^ P.hardline ^^ pp w2
    | Case (pe, cases) ->
        pp_control "case" ^^ info ^^ pp_pexpr pe ^^^ pp_control "of" ^^
        P.nest 2 (
          P.hardline ^^
          P.separate_map P.hardline (fun (pat, wc) ->
            P.bar ^^^ pp_pat pat ^^^ P.equals ^^ P.rangle ^^
            P.nest 4 (P.hardline ^^ pp wc)
          ) cases ^^
          P.hardline ^^ pp_keyword "end")
    | Run (sym, pes) ->
        pp_keyword "run" ^^ info ^^ pp_sym sym ^^ P.parens (comma_list pp_pexpr pes)
    | Jump (sym, pes) ->
        pp_keyword "jump" ^^ info ^^ pp_sym sym ^^ P.parens (comma_list pp_pexpr pes)
    | Save ld ->
        pp_keyword "save" ^^ info ^^ pp_sym ld.label ^^ P.colon ^^^ pp_bty ld.ret_bTy ^^^
        P.parens (comma_list (fun p ->
          pp_sym p.name ^^ P.colon ^^^ pp_bty p.bTy ^^
          P.colon ^^ P.equals ^^^ !^ ".."
        ) ld.params) ^^^
        pp_control "in" ^^^
        P.nest 2 (P.break 1 ^^ pp ld.body)
    | Where (body, defs) ->
        (* "where" keyword binds tightest to exprs *)
        let needs_paren =
          let { info = _; annot = _; node } = body in
          let base = function
            | Eif _ | Esseq _ | Ewseq _ | Esave _ | Elet _ ->
              (* end with an expr *)
              true
            | Epure _ | Ememop _ | Eaction _ | Ecase _ | Eccall _
            | Eproc _ | Eunseq _ | Ebound _ | End _ | Erun _ | Epar _
            | Ewhere _ | Ejump _ | Ewait _ | Eannot _ | Eexcluded _ ->
              (* end with a token *)
              false in
          match node with
          | If _ | Sseq _ | Save _ ->
            true
          | Base expr -> base expr
          | Case (_, _) | Run (_, _) | Jump (_, _) | Where (_, _) ->
            false in
        let pp_def kw ld =
          kw ^^ info ^^ pp_sym ld.label ^^^
          P.parens (comma_list (fun p ->
            pp_sym p.name ^^ P.colon ^^^ pp_bty p.bTy
          ) ld.params) ^^^
          P.colon ^^^ pp_bty ld.ret_bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp ld.body)
        in
        begin match defs with
        | [] -> assert false
        | first :: rest ->
            (if needs_paren then P.parens else Fun.id) (pp body) ^^
            P.nest 2 (
              P.hardline ^^ pp_def (pp_control "where") first ^^
              P.concat (List.map (fun d ->
                P.hardline ^^ pp_def (pp_keyword "and") d
              ) rest)
            ^^ P.hardline ^^ pp_keyword "end")
        end
  in
  pp w

type count_labels = (Symbol.sym, int) Pmap.map

let pp_int x = !^ (string_of_int x)

let pp_count_map map =
  if Pmap.is_empty map then
    None
  else
    let pp_bind (sym, count) = pp_sym sym ^^ P.colon ^^ pp_int count in
    Some (P.separate_map (P.comma ^^ P.space) pp_bind @@ Pmap.bindings_list map)

let add_counts sym int_opt1 int_opt2 =
  match int_opt1, int_opt2 with
  | None, None -> assert false
  | Some _, None
  | None, Some _ -> Some 1
  | Some _, Some _ -> Some 2

let merge_counts count1 count2 = Pmap.merge add_counts count1 count2

let empty_map = Pmap.empty Symbol.compare_sym

let singleton_count sym = Pmap.add sym 1 empty_map

let rec count_labels (Expr (annot, expr_) : expr) : count_labels where =
  match expr_ with
  | Eif (pe, e1, e2) ->
    let w1 = count_labels e1 in
    let w2 = count_labels e2 in
    { info = merge_counts w1.info w2.info; annot; node = If (pe, w1, w2) }
  | Esseq (pat, e1, e2) ->
    let w1 = count_labels e1 in
    let w2 = count_labels e2 in
    { info = merge_counts w1.info w2.info; annot; node = Sseq (pat, w1, w2) }
  | Ecase (pe, cases) ->
    let wcases = List.map (fun (pat, e) -> (pat, count_labels e)) cases in
    let info = List.fold_left
      (fun acc (_, w) -> merge_counts acc w.info)
      empty_map wcases in
    { info; annot; node = Case (pe, wcases) }
  | Erun ((), sym, pes) ->
    { info = singleton_count sym; annot; node = Run (sym, pes) }
  | Esave ((sym, ret_bTy), params_list, body) ->
    let wbody = count_labels body in
    let params = List.map (fun (name, ((bTy, optCTy), pe)) ->
      { name; bTy; optCTy; pexpr = pe }
    ) params_list in
    { info = merge_counts wbody.info (singleton_count sym);
      annot;
      node = Save { label = sym; ret_bTy; params; body = wbody } }
  | Ejump _ -> assert false
  | Ewhere _ -> assert false
  | _ ->
    { info = empty_map; annot; node = Base expr_ }

(* We could skip this and just use plain [Symbol.sym Pset.set],
   but this will allow us to tidy up unused, auto-generated nodes. *)
type usage = Used | Unused
type dominates = (Symbol.sym, usage) Pmap.map

let pp_dom_map map =
  if Pmap.is_empty map then
    None
  else
    let pp_bind (sym, used) =
      (match used with
      | Used -> P.empty
      | Unused -> P.bang)
      ^^ pp_sym sym in
    Some (P.separate_map (P.comma ^^ P.space) pp_bind @@ Pmap.bindings_list map)

let union_dom sym int_opt1 int_opt2 =
  match int_opt1, int_opt2 with
  | None, None -> assert false
  | Some _, Some _ ->
    (* A label is dominated exactly once, so this case is impossible *)
    assert false
  | Some x, None
  | None, Some x ->
    Some x

let union_dom = Pmap.merge union_dom

let singleton_dom sym used = Pmap.add sym used empty_map

let rec dominates dominated ({ info; annot; node } : count_labels where) : dominates where =
  let ones, manys =
    info
    |> Pmap.filter (fun sym _ -> not (Pmap.mem sym dominated))
    |> Pmap.partition (fun _ count -> count = 1) in
  let info = Pmap.map (fun _ -> Used) manys in
  let dominated = union_dom dominated info in
  let wrap node = { info; annot; node } in
  match node with
  | If (pexpr, true_, false_) ->
    let true_ = dominates dominated true_ in
    let false_ = dominates dominated false_ in
    wrap (If (pexpr, true_, false_))
  | Sseq (pat, e1, e2) ->
    let e1 = dominates dominated e1 in
    let e2 = dominates dominated e2 in
    wrap (Sseq (pat, e1, e2))
  | Case (pexpr, branches) ->
    let dom_snd (pat, e) = (pat, dominates dominated e) in
    wrap (Case (pexpr, List.map dom_snd branches))
  | Run (label, pexprs) ->
    assert (Pmap.is_empty info);
    wrap (Run (label, pexprs))
  | Save { label; ret_bTy; params; body } ->
    let info =
      if not (Pmap.mem label dominated) then
        (* At this point we know:
           1. Label was not used outside of the save
              (shadowed [dominated] value).
           2. Label was not used inside the save
              (otherwise it would have been in [manys]).
           Hence, the label is [Unused] (in [ones]). *)
        (assert (Pmap.mem label ones);
        Pmap.add label Unused info)
      else
        info in
    let body = dominates dominated body in
    let node = Save { label; ret_bTy; params; body } in
    { info; annot; node }
  | Base expr ->
    assert (Pmap.is_empty info);
    wrap (Base expr)
  | Jump (_, _) -> assert false
  | Where _ -> assert false

module Helper = struct
  let pat ?sym bTy = Pattern ([], CaseBase (sym, bTy))

  let epure pe = Expr ([], Epure pe)

  let pe_sym sym = Pexpr ([],  (), PEsym sym)

  let pe_val v = Pexpr ([], (), PEval v)

  let wrap_sseq1 bTy expr =
    Expr ([], Esseq (pat bTy, expr, epure (pe_val Vunit)))

  let wrap_sseq2 _bty expr =
    Expr ([], Esseq (pat BTy_unit, epure (pe_val Vunit), expr))

  let wrap_if1 bTy expr =
    Expr ([], Eif (pe_val Vtrue, wrap_sseq1 bTy expr, Expr ([], Epure (Pexpr ([], (), PEval Vunit)))))

  let wrap_if2 bTy expr =
    Expr ([], Eif (pe_val Vfalse, epure (pe_val Vunit), wrap_sseq1 bTy expr))
end

let bTy_of_pat pat =
  let inferred = Core_typing.infer_pattern pat in
  let to_cbt (_, inferred, _) = Core_typing_aux.toCoreBaseType inferred in
  match Exception.except_fmap to_cbt inferred   with
  | Exception.Result (Some bty) -> bty
  | _ -> assert false (* elaboration guarantee *)

(* The function can be thought of first transforming saves as follows:

     save l (x := pe) in E ~> jump l(pe) where l(x) := E end

   and then bubbling this outward, capturing (moving inside a label definiton)
   the continuation (layers of enclosing let strong pat = _ in E) of that
   expression until it reaches the dominating context of l.

   In reality, labels may overlap this happens when we goto _inside_ C blocks,
   so more than one label may be "live" (capturing) at the same time.

   To handle this we need to keep track of not just the labels definitions, but
   also the "live" labels being captured. Loops and gotos which only jump out
   of scopes will only capture the continuation of exactly one label at a time
   (and would not need to track "live" labels).

   The implementation is essentially a rewrite rule of the form:

     E ~> (E', None) or E ~> (E' where defs, live)

   For the latter, case, when we reach a node with non-empty dominators, we
   transform it as so:

     dominators(E) = labels
     (E' where defs, live) ~> (E' where defs, live \ labels).

   If the set of live labels being captured is empty, we stop capturing and place
   a where-expression at that point:

      (E' where defs, {}) ~> (E' where defs, None).

   Note that by convention, the first def in defs is will always be the one
   capturing the continuation. In E where (def :: defs), E can be thought of as
   an "entry block" and def as the "exit" block. There is always exactly one
   because we synthesise join-point labels for any capturing if-expressions.

   NOTE: the analysis doesn't take into account free and bound variables when
   moving expressions around, but this doesn't seem to matter much because the
   "free" variables in saves are re-used for function local variables (across
   different lifetimes). They are introduced upfront, before any runs/saves
   (and so are always part of the dominator frame, I think). *)
let rec to_where bTy ({ info; annot; node } : dominates where) =
  let dominators = Pmap.domain info in
  let empty_set = Pset.empty Symbol.compare_sym in
  let singleton sym = Pset.singleton Symbol.compare_sym sym in
  let labels_info defs =
    List.map (fun def -> (def.label, def.body.info)) defs
    |> List.fold_left (fun (defs, bodies) (label, used) -> (Pset.add label defs, Pset.union bodies used)) (empty_set, empty_set) in
  let new_ info node = { info; annot = []; node } in
  let wrap info node = { info; annot; node} in
  let unwrap_set_defs capturing =
    let default = (Pset.empty Symbol.symbol_compare, []) in
    Option.value ~default capturing in
  let map_e_or_fst_def f e capturing =
    let (live, defs) = unwrap_set_defs capturing in
    match defs with
    | [] -> (f e, live, defs)
    | def :: defs -> (e, live, { def with body = f def.body } :: defs) in
  begin match node with
  | If (pexpr, true_, false_) ->
    let (true_, capturing_t) = to_where bTy true_ in
    let (false_, capturing_f) = to_where bTy false_ in
    begin match capturing_t, capturing_f with
      | None, None ->
        let info = Pset.union true_.info false_.info in
        (wrap info (If (pexpr, true_, false_)), None)
      | _, _ ->
        (* Approximately (not to be taken too literally) here is what's
           happening:

             E1 ~> E1' where t(xt) := Et and defs1 end
             E2 ~> E2' where f(xt) := Ef and defs2 end
             ---------------------------------------
             if pe1 then E1 else E2 ~>
               if pe1 then E1' else E2'
                 where join(x) := pure(x)
                 and   t(xt) := let strong yt = Et in jump join(yt)
                 and   defs1
                 and   f(xf) := lef sfrong yf = Ef in jump join(yf)
                 and   defs2 end

           Note that join is first, so that any continuations captured will
           thus be place inside its body. *)
        let label = Symbol.fresh_pretty "join" in
        let sseq_jump body =
          let sym = Symbol.fresh () in
          let pat = Helper.pat ~sym bTy in
          let jump = new_ (singleton label) (Jump (label, [Helper.pe_sym sym])) in
          new_ (Pset.add label body.info) (Sseq (pat, body, jump)) in
        let (true_j, live_t, defs_t) =
          map_e_or_fst_def sseq_jump true_ capturing_t in
        let (false_j, live_f, defs_f) =
          map_e_or_fst_def sseq_jump false_ capturing_f in
        let def =
          let param = {
            name = Symbol.fresh ();
            bTy;
            optCTy = None;
            pexpr = ();
          } in {
            label;
            ret_bTy = bTy;
            params = [ param ];
            body = new_ empty_set (Base (Epure (Helper.pe_sym param.name)));
          } in
        let live =
          let unioned = Pset.union live_t live_f in
          assert (Pset.subset dominators unioned);
          Pset.diff unioned dominators in
        let defs = defs_t @ defs_f in
        if Pset.is_empty live then
          (* We don't add the join-point def here because we're not capturing
             any more continuations. *)
          let (labels, used) = labels_info defs in
          let if_info = Pset.union true_.info false_.info in
          let where_info = Pset.diff (Pset.union used if_info) labels in
          (new_ where_info (Where (wrap if_info (If (pexpr, true_, false_)), defs)), None)
        else
          let info = Pset.union true_j.info false_j.info in
          (wrap info (If (pexpr, true_j, false_j)), Some (live, def :: defs))
    end
  | Sseq (pat, e1, e2) ->
    let inner_bTy = bTy_of_pat pat in
    let (e2, capturing2) = to_where bTy e2 in
    let (e1, capturing1) = to_where inner_bTy e1 in
    begin match capturing1, capturing2 with
      | None, None ->
        (wrap (Pset.union e1.info e2.info) (Sseq (pat, e1, e2)), None)
      | _, _ ->
        (* Approximately (not to be taken too literally) here is what's
           happening:

             E1 ~> E1' where def1(x) := E and defs1 end
             E2 ~> E2' where defs2 end
             ---------------------------------------
             let strong pat = E1 in E2 ~>
               E1' where defs2
                   and def1(x) := let strong pat = E in E2'
                   and defs1 end

           Note that defs2 is first, so that any continuations captured will
           be place inside the head of its body. *)
        let sseq_e2 body = wrap (Pset.union body.info e2.info) (Sseq (pat, body, e2)) in
        let (e, live1, defs1) = map_e_or_fst_def sseq_e2 e1 capturing1 in
        let (live2, defs2) = unwrap_set_defs capturing2 in
        let live =
          let unioned = Pset.union live1 live2 in
          assert (Pset.subset dominators unioned);
          Pset.diff unioned dominators in
        let defs = defs2 @ defs1 in
        let (labels, used) = labels_info defs in
        if Pset.is_empty live then
          let info = Pset.diff (Pset.union used e.info) labels in
          (wrap info (Where (e, defs)), None)
        else
          (e, Some (live, defs))
    end
  | Case (pexpr, branches) ->
    let do_branch (pat, body) =
      let (body, capturing) = to_where bTy body in
      (* Case expressions can have runs inside them, but not saves,
         so they'll never capture any continuations *)
      assert (Option.is_none capturing);
      (pat, body) in
    let branches = List.map do_branch branches in
    let info = List.fold_left (fun acc (_, body) -> Pset.union acc body.info) empty_set branches in
    (wrap info (Case (pexpr, branches)), None)
  | Run (label, pexprs) ->
    (wrap (singleton label) (Jump (label, pexprs)), None)
  | Save { label; ret_bTy; params; body } ->
    let (body, capturing) = to_where ret_bTy body in
    begin match Pmap.lookup label info with
      | Some Unused ->
        (* This is basically

             ----------------------------------------------
             save unused (x := pe) in E ~> let x = pe in E *)
        let pat, expr =
          let tuple { name; bTy; optCTy; pexpr } = ((name, bTy), pexpr) in
          let syms, pexprs = List.split @@ List.map tuple params in
          let mk_pat (sym, bTy) = Helper.pat ~sym bTy in
          let pat = Pattern ([], CaseCtor (Ctuple, List.map mk_pat syms)) in
          (pat, Epure (Pexpr ([], (), PEctor (Ctuple, pexprs)))) in
        (wrap body.info (Sseq (pat, new_ empty_set (Base expr), body)), capturing)
      | Some Used | None ->
        (* Approximately (not to be taken too literally) here is
           what's happening:

             E ~> E' where defs
             -------------------------------------------------
             save l (x := pe) in E ~>
                 jump l(pe) where defs and l(x) := E' end         *)
        let pexprs = List.map (fun x -> x.pexpr) params in
        let params = List.map (param_map (fun _ -> ())) params in
        let jump = new_ (singleton label) (Jump (label, pexprs)) in
        let def = {
          label;
          ret_bTy = bTy;
          params;
          body;
        } in
        let (live, defs) = unwrap_set_defs capturing in
        let live =
          let added = Pset.add label live in
          assert (Pset.subset dominators added);
          Pset.diff added dominators in
        let defs = defs @ [ def ] in
        let (labels, used) = labels_info defs in
        if Pset.is_empty live then
          let info = Pset.diff (Pset.union used body.info) labels in
          (wrap info (Where (jump, defs)), None)
        else
          (jump, Some (live, defs))
    end
  | Base expr ->
    (wrap empty_set (Base expr), None)
  | Jump (_, _) -> assert false
  | Where _ -> assert false
  end

let to_where bTy dominated =
  let (whered, capturing) = to_where bTy dominated in
  match capturing with
  | None -> whered
  | Some _ -> assert false

let rec to_expr { info; annot; node } =
  let wrap expr = Expr (annot, expr) in
  wrap @@
  begin match node with
  | If (pexpr, true_, false_) ->
    Eif (pexpr, to_expr true_, to_expr false_)
  | Sseq ((Pattern ([], CaseCtor (Ctuple, pats)) as pat),
          { info; annot = [];
            node = Base (Epure (Pexpr ([], (), PEctor (Ctuple, pexprs)) as pexpr)) },
          e2) ->
    (* Tidy up the unused label case *)
    let pat, pexpr =
      match pats, pexprs with
      | [ pat ], [ pexpr ] -> (pat, pexpr)
      | _ -> (pat, pexpr) in
      Elet (pat, pexpr, to_expr e2)
  | Sseq (pat, e1, e2) ->
    Esseq (pat, to_expr e1, to_expr e2)
  | Case (pexpr, branches) ->
    Ecase (pexpr, List.map (fun (pat, e) -> (pat, to_expr e)) branches)
  | Base expr ->
    expr
  | Jump (label, pexprs) ->
    Ejump ((), label, pexprs)
  | Where (e, defs) ->
    let def { label; ret_bTy; params; body } =
      let param { name; bTy; optCTy; pexpr = () } =
      (name, (bTy, optCTy)) in
      ((label, ret_bTy), List.map param params, to_expr body) in
    Ewhere (to_expr e, List.map def defs)
  | Run _
  | Save _ ->
    assert false
  end

let pp_sym_set set =
  if Pset.is_empty set then
    None
  else
    Some (P.separate_map (P.comma ^^ P.space) pp_sym (Pset.elements set))

let transform_expr bTy expr =
  let counted = count_labels expr in
  let () = Cerb_debug.print_debug 1 []
    (fun () -> "\n" ^ Pp_utils.to_plain_pretty_string
      (pp_where pp_count_map counted)) in
  let dominated = dominates empty_map counted in
  let () = Cerb_debug.print_debug 1 []
    (fun () -> "\n" ^ Pp_utils.to_plain_pretty_string
      (pp_where pp_dom_map dominated)) in
  let whered = to_where bTy dominated in
  let () = Cerb_debug.print_debug 1 []
    (fun () -> "\n" ^ Pp_utils.to_plain_pretty_string
      (pp_where pp_sym_set whered)) in
  to_expr whered

let transform_file file =
  let rewrite_fun_map_decl = function
    | Proc (loc, mrk, bTy, args, e) -> Proc (loc, mrk, bTy, args, transform_expr bTy e)
    | decl                           -> decl in
  { file with funs = Pmap.map rewrite_fun_map_decl file.funs }
