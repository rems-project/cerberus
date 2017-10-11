(* Created by Victor Gomes 2017-03-10 *)
open Core

let core_expr_map f = function
 | Ecase (pe, cs) -> Ecase (pe, List.map (fun (p, e) -> (p, f e)) cs)
 | Elet (p, pe, e) -> Elet (p, pe, f e) 
 | Eif (pe1, e2, e3) -> Eif (pe1, f e2, f e3)
 | Eunseq es -> Eunseq (List.map f es)
 | Ewseq (p, e1, e2) -> Ewseq (p, f e1, f e2)
 | Esseq (p, e1, e2) -> Esseq (p, f e1, f e2)
 | Eindet (n, e) -> Eindet (n, f e)
 | Ebound (n, e) -> Ebound (n, f e)
 | End es -> End (List.map f es)
 | Esave (x, y, e) -> Esave (x, y, f e)
 | Epar es -> Epar (List.map f es)
 | Eloc (l, e) -> Eloc (l, f e)
 | Estd (s, e) -> Estd (s, f e)
 | e -> e

(* Eliminates weak sequential operation, since strong and weak have
   the same semantics when translated to Ocaml. *)
let rec elim_wseq = function
  | Ewseq (pat, e1, e2) -> Esseq (pat, elim_wseq e1, elim_wseq e2)
  | e -> core_expr_map elim_wseq e

(* Associate every sequential operation to the right. *)
let rec assoc_seq = function
  | Esseq (pat2, Esseq (pat1, e1, e2), e3) ->
    assoc_seq (Esseq (pat1, e1, assoc_seq (Esseq (pat2, e2, e3))))
  | e -> core_expr_map assoc_seq e

(* Eliminates skip expressions, it does not eliminate "lonely" skips. *)
(* TODO: unsafe_core_aux.subst_pattern Vunit *)
let rec elim_skip = function
  | Esseq (_, Eskip, e) -> elim_skip e
  | Esseq (_, e, Eskip) -> elim_skip e
  | e -> core_expr_map elim_skip e

(* Eliminates loc expressions. *)
let rec elim_loc = function
  | Eloc (_, e) -> elim_loc e
  | e -> core_expr_map elim_loc e

(* Eliminates let expressions. *)
let rec elim_let = function
  | Elet (p, pe, e) -> Esseq (p, Epure pe, e)
  | e -> core_expr_map elim_let e

(* Eliminates std expressions. *)
let rec elim_let = function
  | Estd (s, e) -> elim_loc e
  | e -> core_expr_map elim_let e

let runf opt = function
  | Proc (bty, param, e) -> Proc (bty, param, opt e)
  | f -> f

let run opt core =
  {
    main = core.main;
    tagDefs = core.tagDefs;
    stdlib = Pmap.map (runf opt) core.stdlib;
    impl = core.impl;
    globs = List.map (fun (s, bty, e) -> (s, bty, opt e)) core.globs;
    funs = Pmap.map (runf opt) core.funs;
  }

(* Eliminate procedures declarations *)
let elim_proc_decls core =
  let elim_decls funs =
    Pmap.fold begin fun s f m ->
      match f with
      | ProcDecl _ -> m
      | _ -> Pmap.add s f m
    end funs (Pmap.empty Core_fvs.sym_compare)
  in {
    main = core.main;
    tagDefs = core.tagDefs;
    stdlib = core.stdlib;
    impl = core.impl;
    globs = core.globs;
    funs = elim_decls core.funs;
  }

