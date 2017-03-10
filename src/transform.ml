open Util
open Pp_prelude

exception Unsupported of string
exception FatalError of string
let ( ^//^ ) x y = x ^^ P.break 1 ^^ P.break 1 ^^ y
let ( !> ) x = P.nest 2 (P.break 1 ^^ x)

(* Tail call transformation of Core expressions *)

type basic_expr =
  | Pure of Core.typed_pexpr
  | Memop of Mem_common.memop * Core.typed_pexpr list
  | Action of unit Core.typed_paction
  | Ccall of Core.typed_pexpr * Core.typed_pexpr list
  | Proc of Core.name * Core.typed_pexpr list

type control_expr =
  | Goto of (Symbol.sym * Core.typed_pexpr list)
  | If of Core.typed_pexpr * (Symbol.sym * Core.typed_pexpr list) * (Symbol.sym * Core.typed_pexpr list)
  | Case of Core.typed_pexpr * (Core.typed_pattern * (Symbol.sym * Core.typed_pexpr list)) list

(* this is ugly but whatever *)
let label_id = ref 0
let fresh_label () =
  label_id := !label_id + 1;
  Symbol.Symbol (0, Some ("l" ^ string_of_int !label_id))

let rec fv_pat fvs = function
  | Core.CaseBase (None, _) -> fvs
  | Core.CaseBase (Some l, _) -> l::fvs
  | Core.CaseCtor (_, pats) -> List.fold_left fv_pat fvs pats

let rec fv_pe fvs (Core.Pexpr (_, e)) =
  match e with
  | Core.PEsym l -> l::fvs
  | Core.PEimpl _ -> fvs
  | Core.PEval _ -> fvs
  | Core.PEconstrained cs -> List.fold_left (fun acc (_, pe) -> fv_pe acc pe) fvs cs
  | Core.PEundef _ -> fvs
  | Core.PEerror (_, pe) -> fv_pe fvs pe
  | Core.PEctor (_, pes) -> List.fold_left fv_pe fvs pes
  | Core.PEcase (pe, cases) -> List.fold_left (fun acc (pat, pe) -> fv_pe (fv_pat acc pat) pe) (fv_pe fvs pe) cases
  | Core.PEarray_shift (pe1, _, pe2) -> fv_pe (fv_pe fvs pe1) pe2
  | Core.PEmember_shift (pe1, l, _) -> l::(fv_pe fvs pe1)
  | Core.PEnot pe -> fv_pe fvs pe
  | Core.PEop (_, pe1, pe2) -> fv_pe (fv_pe fvs pe1) pe2
  | Core.PEstruct (l,cs) -> l::(List.fold_left (fun acc (_, pe) -> fv_pe acc pe) fvs cs)
  | Core.PEunion (l,_,pe) -> l::(fv_pe fvs pe)
  | Core.PEcall (l, pes) -> List.fold_left fv_pe fvs pes
  | Core.PElet (pat, pe1, pe2) -> fv_pe (fv_pe (fv_pat fvs pat) pe1) pe2
  | Core.PEif (pe1, pe2, pe3) -> fv_pe (fv_pe (fv_pe fvs pe1) pe2) pe3
  | Core.PEis_scalar pe -> fv_pe fvs pe
  | Core.PEis_integer pe -> fv_pe fvs pe
  | Core.PEis_signed pe -> fv_pe fvs pe
  | Core.PEis_unsigned pe -> fv_pe fvs pe

let fv_act fvs (Core.Paction(_, Core.Action (_, _, act))) =
  match act with
  | Core.Create (pe1, pe2, _) -> fv_pe (fv_pe fvs pe1) pe2
  | Core.Alloc0 (pe1, pe2, _) -> fv_pe (fv_pe fvs pe1) pe2
  | Core.Kill pe -> fv_pe fvs pe
  | Core.Store0 (pe1, pe2, pe3, _) -> fv_pe (fv_pe (fv_pe fvs pe1) pe2) pe3
  | Core.Load0 (pe1, pe2, _) -> fv_pe (fv_pe fvs pe1) pe2
  | Core.RMW0 (pe1, pe2, pe3, pe4, _, _) -> fv_pe (fv_pe (fv_pe (fv_pe fvs pe1) pe2) pe3) pe4
  | Core.Fence0 _ -> fvs

let rec remove x = function
  | [] -> []
  | (y::ys) -> if x=y then ys else y::(remove x ys)

let rec rm_many xs ys =
  match xs with
  | [] -> ys
  | (x::xs) -> rm_many xs (remove x ys)

let rec fv_e fvs = function
  | Core.Epure pe            -> fv_pe fvs pe
  | Core.Ememop (memop, pes) -> List.fold_left fv_pe fvs pes
  | Core.Eaction act         -> fv_act fvs act
  | Core.Eccall (_, nm, pes) -> List.fold_left fv_pe fvs (nm::pes)
  | Core.Eproc  (_, nm, pes) -> List.fold_left fv_pe fvs pes
  | Core.Eskip               -> fvs
  | Core.Esave (_, ps, e) ->
    let bvs = List.map fst ps in
    let pes = List.map (snd % snd) ps in
    rm_many bvs (fv_e (List.fold_left fv_pe fvs pes) e)
  | Core.Eif (pe1, e2, e3) -> fv_e (fv_e (fv_pe fvs pe1) e2) e3
  | Core.Ecase (pe, cases) ->
    let fvs' = fv_pe fvs pe in
    List.fold_left (fun acc (pat, e) -> rm_many (fv_pat [] pat) (fv_e acc e)) fvs' cases
  | Core.Ewseq (pat, e1, e2) ->
    let fvs2 = rm_many (fv_pat [] pat) (fv_e [] e2) in
    fv_e fvs2 e1
  | Core.Esseq (pat, e1, e2) ->
    let fvs2 = rm_many (fv_pat [] pat) (fv_e [] e2) in
    fv_e fvs2 e1
  | Core.Erun (_, _, pes) -> List.fold_left fv_pe fvs pes
  | Core.Eunseq _ -> raise (Unsupported "unseq")
  | Core.Easeq  _ -> raise (Unsupported "aseq")
  | Core.Eindet _ -> raise (Unsupported "indet")
  | Core.Ebound _ -> raise (Unsupported "bound")
  | Core.End    _ -> raise (Unsupported "end")
  | Core.Elet   _ -> raise (Unsupported "let")
  | Core.Epar   _ -> raise (Unsupported "par")
  | Core.Ewait  _ -> raise (Unsupported "wait")
  | Core.Eloc   _ -> raise (Unsupported "loc")

let fv fvs = function
  | Pure pe -> fv_pe fvs pe
  | Memop (memop, pes) -> List.fold_left fv_pe fvs pes
  | Action act -> fv_act fvs act
  | Ccall (pe, pes) ->  List.fold_left fv_pe fvs (pe::pes)
  | Proc (_, pes) ->  List.fold_left fv_pe fvs pes

let fv_bind (pato, e) fvs =
  let fvs_in_e = fv fvs e in
  match pato with
  | None -> fvs_in_e
  | Some pat -> rm_many (fv_pat [] pat) fvs_in_e

let fv_cb fvs (pato, jmp) =
  let fvs_in_cb =
  match jmp with
  | Goto (pato, pes) -> List.fold_left fv_pe fvs pes
  | If (pe1, (_, pes2), (_, pes3)) -> List.fold_left fv_pe (List.fold_left fv_pe (fv_pe fvs pe1) pes2) pes3
  | Case (pe1, cases) ->
    List.fold_left (fun fvs (pat, (_, pes)) -> rm_many (fv_pat [] pat) (List.fold_left fv_pe fvs pes)) (fv_pe fvs pe1) cases
  in
  match pato with
  | None -> fvs_in_cb
  | Some pat -> rm_many (fv_pat [] pat) fvs_in_cb

let fresh_basic_pat () =
  let l = fresh_label() in
  Core.CaseBase (Some l, Core.BTy_unit)

let debug_basic_pat p =
  match p with
  | Some (Core.CaseBase (Some (Symbol.Symbol (_, Some l)), _)) -> print_string l
  | Some _ -> print_string "CPLX"
  | None -> print_string "NONE"

(* return value passed to next continuation *)
let ret_sym = Symbol.Symbol (0, Some "ret")
let ret_pat = Core.CaseBase (Some ret_sym, Core.BTy_unit)
let ret_pe  = Core.Pexpr (Core.BTy_unit, Core.PEsym ret_sym)

(*
let rec transform_left bbs es pato (jpato, jmp) e =
  let to_basic e = (bbs, ((pato, e)::es, jpato, jmp)) in
  match e with
  | Core.Epure pe            -> to_basic (Pure pe)
  | Core.Ememop (memop, pes) -> to_basic (Memop (memop, pes))
  | Core.Eaction act         -> to_basic (Action act)
  | Core.Eccall (_, nm, pes) -> to_basic (Ccall (nm, pes))
  | Core.Eproc  (_, nm, pes) -> to_basic (Proc (nm, pes))
  | Core.Eskip -> (bbs, (es, pato, jmp))
  | Core.Esave ((sym, _), xs, e') ->
    let ps = List.map fst xs in
    let pes = List.map (snd % snd) xs in
    let (bbs', bb') = transform bbs [] None (jpato, jmp) e' in
    (((sym, ps), bb')::bbs', (es, pato, Goto (sym, pes)))
  | Core.Eif (pe1, e2, e3) ->
    let l2 = fresh_label() in
    let l3 = fresh_label() in
    let (bbs2, (es2, pato2, jmp2)) = transform bbs [] None (jpato, jmp) e2 in
    let fvs2 = List.fold_left fv_bind [] es2 in
    let bb2 = ((l2, fvs2), (es2, pato2, jmp2)) in
    let (bbs3, (es3, pato3, jmp3)) = transform bbs [] None (jpato, jmp) e3 in
    let fvs3 = List.fold_left fv_bind [] es3 in
    let bb3 = ((l3, fvs3), (es3, pato3, jmp3)) in
    (bb3::bb2::bbs3@bbs2, (es, pato, If (pe1, (l2, []), (l3, []))))
  | Core.Ecase (pe, cases) ->
    let xs = List.map (fun (p, e) ->
        let (bbs', bb') = transform bbs [] None (jpato, jmp) e in
        let l = fresh_label() in
        (bbs', (((l, []), bb'), (p, (l, []))))
      ) cases in
    let bbs1 = List.concat (List.map fst xs) in
    let bbs2 = List.map (fst % snd) xs in
    let cases = List.map (snd % snd) xs in
    (bbs@bbs1@bbs2, (es, pato, Case (pe, cases)))
  | Core.Ewseq (pat, e1, e2) -> raise (FatalError "not assoc")
  | Core.Esseq (pat, e1, e2) -> raise (FatalError "not assoc")
  | Core.Erun (u, sym, pes) ->
    (bbs, (es, pato, Goto (sym, pes)))
  | Core.End [] -> raise (Unsupported "empty end")
  | Core.End (e::_) -> transform_left bbs es pato (jpato, jmp) e
  | Core.Eunseq _ -> raise (Unsupported "unseq")
  | Core.Easeq  _ -> raise (Unsupported "aseq")
  | Core.Eindet _ -> raise (Unsupported "indet")
  | Core.Ebound _ -> raise (Unsupported "bound")
  | Core.Elet   _ -> raise (Unsupported "let")
  | Core.Epar   _ -> raise (Unsupported "par")
  | Core.Ewait  _ -> raise (Unsupported "wait")
  | Core.Eloc   _ -> raise (Unsupported "loc")
*)

let sym_to_pe ss =
  List.map (fun s -> Core.Pexpr (Core.BTy_unit, Core.PEsym s)) ss

let sym_compare s1 s2 =
  match s1, s2 with
  | Symbol.Symbol (n, None), Symbol.Symbol (m, None) -> n - m
  | Symbol.Symbol (n, Some l), Symbol.Symbol (_, None) -> n
  | Symbol.Symbol (_, None), Symbol.Symbol (m, Some l) -> m
  | Symbol.Symbol (_, Some l1), Symbol.Symbol (_, Some l2) -> String.compare l1 l2


type body_bb = (Core.typed_pattern option * basic_expr) list * (Core.typed_pattern option * control_expr)

type basic_block = (Symbol.sym * Core.typed_pexpr list)

let uniq_fv es cont = List.sort_uniq sym_compare (List.fold_right fv_bind es (fv_cb [] cont))

let build_bb es (pato, jmp) =
  let l = fresh_label() in
  let fvs =
    match es with
    | [] -> uniq_fv es (pato, jmp) @ (match pato with None -> [] | Some pat -> fv_pat [] pat)
    | _  -> uniq_fv es (pato, jmp)
  in
  ((l, fvs), (es, (pato, jmp)))

let decl_bb ((l, fvs), _) =
  (l, sym_to_pe fvs)

let pato_bb ((l, fvs), (pato, jmp)) = pato

let pato_cont (pato, _) = pato

let rec transform_left bbs es pato cont e =
  match e with
  | Core.Esseq _ -> raise (FatalError "no assoc")
  | e -> transform bbs es pato cont e
and transform bbs es pato cont e =
  let to_basic e = (bbs, ((pato, e)::es, cont)) in
  match e with
  | Core.Epure pe            -> to_basic (Pure pe)
  | Core.Ememop (memop, pes) -> to_basic (Memop (memop, pes))
  | Core.Eaction act         -> to_basic (Action act)
  | Core.Eccall (_, nm, pes) -> to_basic (Ccall (nm, pes))
  | Core.Eproc  (_, nm, pes) -> to_basic (Proc (nm, pes))
  | Core.Esave ((sym, _), xs, e) ->
    let bb = build_bb es cont in
    let cont_save = (pato_cont cont, Goto (decl_bb bb)) in
    let (ps, pes) = List.fold_left (fun (ls, pes) (l, (_, pe)) -> (l::ls, pe::pes)) ([], []) xs in
    let (bbs', bb') = transform bbs [] None cont_save e in
    (((sym, ps), bb')::bb::bbs', ([], (pato, Goto (sym, pes))))
  | Core.Eif (pe1, e2, e3) ->
    let (bbs2, (es2, cont2)) = transform bbs [] None cont e2 in
    let (bbs3, (es3, cont3)) = transform bbs [] None cont e3 in
    let bb2 = build_bb es2 cont2 in
    let bb3 = build_bb es3 cont3 in
    let cont = (pato, If (pe1, decl_bb bb2, decl_bb bb3)) in
    (bb3::bb2::bbs3@bbs2, (es, cont))
  | Core.Ecase (pe, cases) ->
    let bb = build_bb es cont in
    let (bbs, cases) = List.fold_left (fun (acc, cases) (p, e) ->
        let (bbs, (es, cont)) = transform bbs [] None cont e in
        let bb = build_bb es cont in
        (bb::bbs@acc, (p, decl_bb bb)::cases)
      ) (bbs, []) cases
    in
    (bb::bbs, ([], (pato, Case (pe, cases))))
  | Core.Esseq (pat, e1, e2) ->
    let (bbs2, (es2, cont2)) = transform bbs es (Some pat) cont e2 in
    transform_left bbs2 es2 pato cont2 e1
  | Core.Erun (u, sym, pes) ->
    (bbs, ([], (pato, Goto (sym, pes))))
  | Core.End (e::_) -> transform bbs es pato cont e
  | Core.Eskip ->
    if es != [] then
      raise (FatalError "no skip elim")
    else
      (* eliminate pattern *)
      (bbs, ([], (match cont with (_, jmp) -> (None, jmp))))
  | Core.Ewseq _ -> raise (FatalError "no only_sseq")
  | Core.End [] -> raise (Unsupported "empty end")
  | Core.Eunseq _ -> raise (Unsupported "unseq")
  | Core.Easeq  _ -> raise (Unsupported "aseq")
  | Core.Eindet _ -> raise (Unsupported "indet")
  | Core.Ebound _ -> raise (Unsupported "bound")
  | Core.Elet   _ -> raise (Unsupported "let")
  | Core.Epar   _ -> raise (Unsupported "par")
  | Core.Ewait  _ -> raise (Unsupported "wait")
  | Core.Eloc   _ -> raise (Unsupported "loc")


let rec only_sseq = function
  | Core.Ewseq (pat, e1, e2) -> Core.Esseq (pat, only_sseq e1, only_sseq e2)
  | Core.Esseq (pat, e1, e2) -> Core.Esseq (pat, only_sseq e1, only_sseq e2)
  | Core.Esave (x, y, e) -> Core.Esave (x, y, only_sseq e)
  | Core.Eif (pe1, e2, e3) -> Core.Eif (pe1, only_sseq e2, only_sseq e3)
  | Core.Ecase (pe, cases) -> Core.Ecase (pe, List.map (fun (p, e) -> (p, only_sseq e)) cases)
  | Core.End es -> Core.End (List.map only_sseq es)
  | e -> e

let rec seq_assoc = function
  | Core.Esseq (pat2, Core.Esseq (pat1, e1, e2), e3) ->
    seq_assoc (Core.Esseq (pat1, e1, seq_assoc (Core.Esseq (pat2, e2, e3))))
  | Core.Esseq (pat, e1, e2) -> Core.Esseq (pat, seq_assoc e1, seq_assoc e2)
  | Core.Esave (s, ps, e) -> Core.Esave (s, ps, seq_assoc e)
  | Core.Eif (pe1, e2, e3) -> Core.Eif (pe1, seq_assoc e2, seq_assoc e3)
  | Core.Ecase (pe, cases) -> Core.Ecase (pe, List.map (fun (p, e) -> (p, seq_assoc e)) cases)
  | Core.End es -> Core.End (List.map seq_assoc es)
  | Core.Ewseq _ -> raise (FatalError "no only_sseq")
  | e -> e

(* it does not elimate "lonely" skips *)
let rec skip_elim e = 
  match e with
  | Core.Esseq (_, Core.Eskip, e) -> skip_elim e
  | Core.Esseq (_, e, Core.Eskip) -> skip_elim e
  | Core.Esseq (pat, e1, Core.Esseq (_, Core.Eskip, e2)) -> skip_elim (Core.Esseq (pat, skip_elim e1, skip_elim e2))
  | Core.Esseq (pat, e1, e2) -> Core.Esseq (pat, skip_elim e1, skip_elim e2)
  | Core.Esave (x, y, e) -> Core.Esave (x, y, skip_elim e)
  | Core.Eif (pe1, e2, e3) -> Core.Eif (pe1, skip_elim e2, skip_elim e3)
  | Core.Ecase (pe, cases) -> Core.Ecase (pe, List.map (fun (p, e) -> (p, skip_elim e)) cases)
  | Core.End es -> Core.End (List.map only_sseq es)
  | Core.Ewseq _ -> raise (FatalError "no only_sseq")
  | e -> e

let rec print_basic_expr = function
  | Pure pe            -> !^"A.value" ^^^ P.parens (Codegen_ocaml2.print_pure_expr pe)
  | Memop (memop, pes) -> Codegen_ocaml2.print_memop memop pes
  | Action (Core.Paction (p, (Core.Action (_, bs, act)))) -> Codegen_ocaml2.print_action act
  | Ccall (nm, es) ->
    Codegen_ocaml2.print_pure_expr nm ^^^ (
      if List.length es = 0
      then P.parens P.space
      else (P.separate_map P.space (fun x -> P.parens (Codegen_ocaml2.print_pure_expr x)) es)
    )
  | Proc (nm, pes) ->
      Codegen_ocaml2.print_name nm ^^^ !^"cont" ^^^ (P.separate_map P.space (fun z -> P.parens (Codegen_ocaml2.print_pure_expr z))) pes

let print_call (sym, pes) =
  Codegen_ocaml2.print_symbol sym ^^^
  P.parens (P.separate_map (P.comma ^^ P.space) Codegen_ocaml2.print_pure_expr pes)

let print_control = function
  | Goto goto -> print_call goto
  | If (pe1, goto2, goto3) -> Codegen_ocaml2.print_if (Codegen_ocaml2.print_pure_expr pe1) (print_call goto2) (print_call goto3)
  | Case (pe, cases) -> Codegen_ocaml2.print_match (Codegen_ocaml2.print_pure_expr pe) print_call cases

let print_pato p =
  !^">>= fun" ^^^
  (match p with
   | None -> !^"_"
   | Some pat -> Codegen_ocaml2.print_pattern pat
  ) ^^ !^" ->"

let print_bb (es, (pato, ct)) =
  match es with
  | [] -> print_control ct
  | ((_, e)::es) -> print_basic_expr e ^^
                         (List.fold_left (fun acc (p, e) ->
                           acc ^/^ print_pato p ^/^ print_basic_expr e
                            ) P.space es) ^^^ !> (print_pato pato) ^/^ print_control ct

let print_decl ((sym, ps), bb) =
  Codegen_ocaml2.print_symbol sym ^^^
  P.parens (P.separate_map (P.comma ^^ P.space) Codegen_ocaml2.print_symbol ps) ^^^
  !^"=" ^^ !> (print_bb bb)


(* TODO: Wrong type *)


let default = Symbol.Symbol (0, Some "cont")

let print_transformed e bty =
  let e = only_sseq e in
  let e = seq_assoc e in
  let e = skip_elim e in
  let (bbs, bb) = transform [] [] None (Some ret_pat, Goto (default, [ret_pe])) e in
  let bbs = List.sort_uniq (fun ((l1, _), _) ((l2, _), _) -> sym_compare l1 l2) bbs in
  if List.length bbs = 0 then
    print_bb bb
  else
    !^"let rec" ^^^ print_decl (List.hd bbs) ^^^
    List.fold_left (fun acc decl -> acc ^/^ !^"and" ^^^ print_decl decl) P.space (List.tl bbs)
    ^/^ !^"in" ^/^ print_bb bb
