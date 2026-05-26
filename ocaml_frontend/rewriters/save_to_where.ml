(* This file is for transforming Core programs which use run/save, into Core
   programs which use a jump/where, a more compositional construct with the
   following semantics (plus context reduction, omitted).

     [Where-Pure]
     ------------------------------
     pure(v) where defs --> pure(v)

     [Jump-Sub]
     ( defs(l) = x . E )
     ----------------------------------------------
     jump l(pe) where defs --> {val/x} E where defs

     [Jump-Where]
     (l not in defs)
     ------------------------------------
     jump l(pe) where defs --> jump l(pe)

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

type count_labels = (Symbol.sym, int) Pmap.map

let add_counts sym int_opt1 int_opt2 =
  match int_opt1, int_opt2 with
  | None, None -> assert false
  | Some _, None
  | None, Some _ -> Some 1
  | Some _, Some _ -> Some 2

let merge_counts count1 count2 = Pmap.merge add_counts count1 count2

let empty_counts : count_labels = Pmap.empty Symbol.compare_sym

let singleton_count sym : count_labels = Pmap.add sym 1 empty_counts

let rec count_labels (Expr (annot, expr_) : expr) : count_labels where =
  let base () = { info = empty_counts; annot; node = Base expr_ } in
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
    base ()

let transform_expr _bty expr =
  let _ = count_labels expr in
  expr

let transform_file file =
  let rewrite_fun_map_decl = function
    | Proc (loc, mrk, bty, args, e) -> Proc (loc, mrk, bty, args, transform_expr bty e)
    | decl                           -> decl in
  { file with funs = Pmap.map rewrite_fun_map_decl file.funs }
