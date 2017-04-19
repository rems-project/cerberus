(* Created by Victor Gomes 2017-03-10 *)
(* Few passes to *)

open Core
exception PassError of string

(* Eliminates weak sequential operation, since strong and weak have
   the same semantics when translated to Ocaml. *)
let rec elim_wseq = function
  | Ewseq (pat, e1, e2) -> Esseq (pat, elim_wseq e1, elim_wseq e2)
  | Esseq (pat, e1, e2) -> Esseq (pat, elim_wseq e1, elim_wseq e2)
  | Esave (x, y, e) -> Esave (x, y, elim_wseq e)
  | Eif (pe1, e2, e3) -> Eif (pe1, elim_wseq e2, elim_wseq e3)
  | Ecase (pe, cases) ->
    Ecase (pe, List.map (fun (p, e) -> (p, elim_wseq e)) cases)
  | End es -> End (List.map elim_wseq es)
  | e -> e

(* Associate every sequential operation to the right.
   Dependency: elim_wseq *)
let rec assoc_seq = function
  | Esseq (pat2, Esseq (pat1, e1, e2), e3) ->
    assoc_seq (Esseq (pat1, e1, assoc_seq (Esseq (pat2, e2, e3))))
  | Esseq (pat, e1, e2) -> Esseq (pat, assoc_seq e1, assoc_seq e2)
  | Esave (s, ps, e) -> Esave (s, ps, assoc_seq e)
  | Eif (pe1, e2, e3) -> Eif (pe1, assoc_seq e2, assoc_seq e3)
  | Ecase (pe, cases) ->
    Ecase (pe, List.map (fun (p, e) -> (p, assoc_seq e)) cases)
  | End es -> End (List.map assoc_seq es)
  | Ewseq _ -> raise (PassError "assoc_seq: Ewseq found.")
  | e -> e

(* Eliminates skip expressions, it does not eliminate "lonely" skips.
   Dependencies: elim_wseq, assoc_seq *)
let rec elim_skip e =
  match e with
  | Esseq (_, Eskip, e) -> elim_skip e
  | Esseq (_, e, Eskip) -> elim_skip e
  | Esseq (pat, e1, e2) -> Esseq (pat, elim_skip e1, elim_skip e2)
  | Esave (x, y, e) -> Esave (x, y, elim_skip e)
  | Eif (pe1, e2, e3) -> Eif (pe1, elim_skip e2, elim_skip e3)
  | Ecase (pe, cases) -> Ecase (pe, List.map (fun (p, e) -> (p, elim_skip e)) cases)
  | End es -> End (List.map elim_skip es)
  | Ewseq _ -> raise (PassError "elim_skip: Ewseq found.")
  | e -> e

let runf opt = function
  | Fun (bty, param, pe) -> Fun (bty, param, pe)
  | Proc (bty, param, e) -> Proc (bty, param, opt e)

let run opt core =
  {
    main = core.main;
    stdlib = Pmap.map (runf opt) core.stdlib;
    impl = core.impl;
    globs = List.map (fun (s, bty, e) -> (s, bty, opt e)) core.globs;
    funs = Pmap.map (runf opt) core.funs;
  }
