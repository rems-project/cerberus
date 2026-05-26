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
  ret_bty : core_base_type;
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
  let pp_bty bty = Pp_core.Basic.pp_core_base_type bty in
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
        pp_keyword "save" ^^ info ^^ pp_sym ld.label ^^ P.colon ^^^ pp_bty ld.ret_bty ^^^
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
          P.colon ^^^ pp_bty ld.ret_bty ^^^
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
            ) ^^
            P.hardline ^^ pp_keyword "end"
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

let empty_counts = Pmap.empty Symbol.compare_sym

let singleton_count sym = Pmap.add sym 1 empty_counts

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
      empty_counts wcases in
    { info; annot; node = Case (pe, wcases) }
  | Erun ((), sym, pes) ->
    { info = singleton_count sym; annot; node = Run (sym, pes) }
  | Esave ((sym, ret_bty), params_list, body) ->
    let wbody = count_labels body in
    let params = List.map (fun (name, ((bTy, optCTy), pe)) ->
      { name; bTy; optCTy; pexpr = pe }
    ) params_list in
    { info = merge_counts wbody.info (singleton_count sym);
      annot;
      node = Save { label = sym; ret_bty; params; body = wbody } }
  | Ejump _ -> assert false
  | Ewhere _ -> assert false
  | _ ->
    { info = empty_counts; annot; node = Base expr_ }

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

let empty_dom = Pmap.empty Symbol.compare_sym

let singleton_dom sym used = Pmap.add sym used empty_dom

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
  | Save { label; ret_bty; params; body } ->
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
    let node = Save { label; ret_bty; params; body } in
    { info; annot; node }
  | Base expr ->
    assert (Pmap.is_empty info);
    wrap (Base expr)
  | Jump (_, _) -> assert false
  | Where _ -> assert false


module Debug = struct
  let pat bty = Pattern ([], CaseBase (None, bty))

  let epure pe = Expr ([], Epure pe)

  let pe v = Pexpr ([], (), PEval v)

  let wrap_sseq1 bty expr =
    Expr ([], Esseq (pat bty, expr, epure (pe Vunit)))

  let wrap_sseq2 _bty expr =
    Expr ([], Esseq (pat BTy_unit, epure (pe Vunit), expr))

  let wrap_if1 bty expr =
    Expr ([], Eif (pe Vtrue, wrap_sseq1 bty expr, Expr ([], Epure (Pexpr ([], (), PEval Vunit)))))

  let wrap_if2 bty expr =
    Expr ([], Eif (pe Vfalse, epure (pe Vunit), wrap_sseq1 bty expr))
end

let transform_expr bty expr =
  (* let expr = Debug.wrap_sseq1 bty expr in *)
  let counted = count_labels expr in
  let () = Cerb_debug.print_debug 1 []
    (fun () -> "\n" ^ Pp_utils.to_plain_pretty_string
      (pp_where pp_count_map counted)) in
  let dominated = dominates empty_dom counted in
  let () = Cerb_debug.print_debug 1 []
    (fun () -> "\n" ^ Pp_utils.to_plain_pretty_string
      (pp_where pp_dom_map dominated)) in
  expr

let transform_file file =
  let rewrite_fun_map_decl = function
    | Proc (loc, mrk, bty, args, e) -> Proc (loc, mrk, bty, args, transform_expr bty e)
    | decl                           -> decl in
  { file with funs = Pmap.map rewrite_fun_map_decl file.funs }
