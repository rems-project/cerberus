(* Created by Victor Gomes 2017-03-10 *)
open Core

let core_expr_map f (Expr (annot, expr_)) =
  Expr (annot, match expr_ with
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
   | _ -> expr_)

(* Eliminates weak sequential operation, since strong and weak have
   the same semantics when translated to Ocaml. *)
let rec elim_wseq (Expr (annot, expr_) as expr) =
  match expr_ with
    | Ewseq (pat, e1, e2) -> Expr (annot, Esseq (pat, elim_wseq e1, elim_wseq e2))
    | _ -> core_expr_map elim_wseq expr

(* Associate every sequential operation to the right. *)
let rec assoc_seq = function
  | Expr (annot, Esseq (pat2, Expr (annot', Esseq (pat1, e1, e2)), e3)) ->
      assoc_seq (Expr (annot', Esseq (pat1, e1, assoc_seq (Expr (annot, Esseq (pat2, e2, e3))))))
  | e -> core_expr_map assoc_seq e

(* Eliminates skip expressions, it does not eliminate "lonely" skips. *)
(* TODO: unsafe_core_aux.subst_pattern Vunit *)
let rec elim_skip = function
  | Expr (_, Esseq (_, Expr (_, Eskip), e)) -> elim_skip e
  | Expr (_, Esseq (_, e, Expr (_, Eskip))) -> elim_skip e
  | e -> core_expr_map elim_skip e

(* Eliminates let expressions. *)
let rec elim_let = function
  | Expr (annot, Elet (p, pe, e)) -> Expr (annot, Esseq (p, Expr ([], Epure pe), e))
  | e -> core_expr_map elim_let e

let runf opt = function
  | Proc (loc, bty, param, e) -> Proc (loc, bty, param, opt e)
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

