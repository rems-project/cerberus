open Typed_ast

let rec list_to_mac = function
  | [] -> (fun e -> None)
  | m1::ms ->
      let ms_f = list_to_mac ms in
        (fun e ->
           match m1 e with
             | None -> ms_f e
             | Some(e) -> Some(e))

let rec list_to_bool_mac = function
  | [] -> (fun b e -> None)
  | m1::ms ->
      let ms_f = list_to_bool_mac ms in
        (fun b e ->
           match m1 b e with
             | None -> ms_f b e
             | Some(e) -> Some(e))


module Expander(C : Exp_context) = struct

(* Using the checks here adds significant overhead *)
module C = Exps_in_context(C)

let rec expand_pat top_level p r : pat = 
  let trans p = expand_pat top_level p r in 
  let old_t = Some(p.typ) in
  let old_l = p.locn in
    match r top_level p with
      | Some(p') -> trans p'
      | None ->
          match p.term with
            | P_as(p,s,nl) -> 
                C.mk_pas old_l (trans p) s nl old_t
            | P_typ(s1,p,s2,t,s3) -> 
                C.mk_ptyp old_l s1 (trans p) s2 t s3 old_t
            | P_constr(c,ps) -> 
                C.mk_pconstr old_l 
                  c 
                  (List.map (fun p -> (trans p)) ps)
                  old_t
            | P_record(s1,fieldpats,s2) ->
                C.mk_precord old_l
                  s1 
                  (Seplist.map 
                     (fun (fid,s1,p) -> (fid,s1,trans p))
                     fieldpats)
                  s2
                  old_t
            | P_tup(s1,ps,s2) -> 
                C.mk_ptup old_l s1 (Seplist.map trans ps) s2 old_t
            | P_list(s1,ps,s2) -> 
                C.mk_plist old_l s1 (Seplist.map trans ps) s2 p.typ
            | P_paren(s1,p,s2) -> 
                C.mk_pparen old_l s1 (trans p) s2 old_t
            | P_cons(p1,s,p2) -> 
                C.mk_pcons old_l (trans p1) s (trans p2) old_t
            | P_var _ | P_var_annot _ ->
                p
            | (P_lit _ | P_wild _) ->
                p


let rec expand_exp (r,pat_r) (e : exp) : exp = 
  let trans = expand_exp (r,pat_r) in 
  let transp p = expand_pat false p pat_r in
  let old_t = Some(exp_to_typ e) in
  let old_l = exp_to_locn e in
    match r e with
      | Some(e') -> 
          begin
            C.type_eq old_l (exp_to_typ e) (exp_to_typ e');
            trans e'
          end
      | None ->
          begin
            match (C.exp_to_term e) with
              | Tup_constructor(c,s1,es,s2) ->
                  C.mk_tup_ctor old_l 
                    c 
                    s1 (Seplist.map trans es) s2 old_t
              | Fun(s1,ps,s2,e) ->
                  C.mk_fun old_l 
                    s1 (List.map (fun p -> transp p) ps) 
                    s2 (trans e)
                    old_t
              | Function(s1,pes,s2) ->
                  C.mk_function old_l
                    s1 (Seplist.map 
                          (fun (p,s1,e,l) -> (transp p,s1,trans e,l))
                          pes)
                    s2
                    old_t
              | App(e1,e2) ->
                  C.mk_app old_l
                    (skip_apps (r,pat_r) e1)
                    (trans e2)
                    old_t
              | Infix(e1,e2,e3) ->
                  C.mk_infix old_l (trans e1) (trans e2) (trans e3) old_t
              | Record(s1,fieldexps,s2) ->
                  C.mk_record old_l
                    s1
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s2
                    old_t
              | Record_coq(n,s1,fieldexps,s2) ->
                  C.mk_record_coq old_l
                    s1
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s2
                    old_t
              | Recup(s1,e,s2,fieldexps,s3) ->
                  C.mk_recup old_l
                    s1 (trans e) s2
                    (Seplist.map 
                       (fun (fid,s1,e,l) -> (fid,s1,trans e,l))
                       fieldexps)
                    s3
                    old_t
              | Field(e,s,fid) ->
                  C.mk_field old_l 
                    (trans e) s fid
                    old_t
              | Case(s1,e,s2,patexps,s3) ->
                  C.mk_case old_l
                    s1 (trans e) s2
                    (Seplist.map
                       (fun (p,s1,e,l) -> (transp p,s1,trans e,l))
                       patexps)
                    s3
                    old_t
              | Typed(s1,e,s2,t,s3) ->
                  C.mk_typed old_l 
                    s1 (trans e) s2 t s3
                    old_t
              | Let(s1,letbind,s2,e) ->
                  C.mk_let old_l
                    s1 (expand_letbind false (r,pat_r) letbind) s2 (trans e)
                    old_t
              | Tup(s1,es,s2) ->
                  C.mk_tup old_l
                    s1 (Seplist.map trans es) s2
                    old_t
              | List(s1,es,s2) ->
                  C.mk_list old_l
                    s1 (Seplist.map trans es) s2
                    (exp_to_typ e)
              | Paren(s1,e,s2) ->
                  C.mk_paren old_l
                    s1 (trans e) s2
                    old_t
              | Begin(s1,e,s2) ->
                  C.mk_begin old_l
                    s1 (trans e) s2
                    old_t
              | If(s1,e1,s2,e2,s3,e3) ->
                  C.mk_if old_l
                    s1 (trans e1) s2 (trans e2) s3 (trans e3)
                    old_t
              | Set(s1,es,s2) ->
                  C.mk_set old_l
                    s1 (Seplist.map trans es) s2
                    (exp_to_typ e)
              | Setcomp(s1,e1,s2,e2,s3,b) ->
                  C.mk_setcomp old_l
                    s1 (trans e1) s2 (trans e2) s3 b
                    old_t
              | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) ->
                  C.mk_comp_binding old_l
                    is_lst s1 (trans e1) s2 s3 qbs s4 (trans e2) s5
                    old_t
              | Quant(q,qbs,s,e) ->
                  C.mk_quant old_l
                    q
                    (List.map
                       (function
                          | Qb_var(n) -> Qb_var(n)
                          | Qb_restr(is_lst,s1,n,s2,e,s3) ->
                              Qb_restr(is_lst,s1,n,s2,trans e,s3))
                       qbs)
                    s
                    (trans e)
                    old_t
              | Constructor(c) ->
                  C.mk_constr old_l c old_t
              | Constant(c) ->
                  C.mk_const old_l c old_t
              | Var(n) ->
                  C.mk_var old_l n (exp_to_typ e) 
              | Lit _  ->
                  e
          end

and skip_apps r e = match (C.exp_to_term e) with
  | App(e1,e2) ->
      C.mk_app (exp_to_locn e)
        (skip_apps r e1)
        (expand_exp r e2)
        (Some(exp_to_typ e))
  | _ -> expand_exp r e

and expand_letbind top_level (r,pat_r) (lb,l) = match lb with
  | Let_val(p,topt,s,e) ->
      C.mk_let_val l
        (expand_pat top_level p pat_r) topt s (expand_exp (r,pat_r) e)
  | Let_fun(n,ps,t,s1,e) -> 
      C.mk_let_fun l
        n (List.map (fun p -> expand_pat top_level p pat_r) ps) t s1 
        (expand_exp (r,pat_r) e)

let rec expand_defs defs r =
  let expand_val_def = function
    | Let_def(s1,targets,lb) ->
        Let_def(s1, targets,expand_letbind true r lb)
    | Rec_def(s1,s2,targets,clauses) ->
        Rec_def(s1,
                s2,
                targets,
                Seplist.map
                  (fun (nl,ps,topt,s3,e) -> 
                     (nl, List.map (fun p -> expand_pat true p (snd r)) ps,
                      topt,s3,expand_exp r e))
                  clauses)
  in
  let rec expand_def = function
    | Val_def(d,tvs) -> Val_def(expand_val_def d,tvs)
    | Indreln(s1,targets,c) ->
        Indreln(s1,
                targets,
                Seplist.map
                  (fun (s1,ns,s2,e,s3,n,es) ->
                     (s1,ns,s2,expand_exp r e, s3, n, 
                      List.map (expand_exp r) es))
                  c)
    | Module(sk1, nl, sk2, sk3, ds, sk4) ->
        Module(sk1, nl, sk2, sk3, List.map (fun ((d,s),l) -> ((expand_def d,s),l)) ds, sk4)
    | Instance(sk1,is,vdefs,sk2,e_v,n) ->
        Instance(sk1, is, List.map expand_val_def vdefs, sk2, e_v, n)
    | def -> def
  in
    match defs with
      | [] -> []
      | ((def,s),l)::defs ->
          ((expand_def def,s),l)::expand_defs defs r
end
