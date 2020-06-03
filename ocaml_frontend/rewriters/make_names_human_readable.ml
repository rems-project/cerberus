open Core_rewriter
open Core

module type Type = sig
  type t
end

(* TODO: unclear what to do with annotations if they mention Core variables *)

module Binding_aware_rewriter = struct
  type annots = Annot.annot list
  type action = Traverse
  module Make (Bty : Type) (Sym : Type) (F : Type) (M : Monad) = struct
    let (let*) x f = M.bind x f

    type a_generic_pattern = Sym.t generic_pattern
    type a_generic_pexpr = (Bty.t, Sym.t) generic_pexpr
    type a_generic_action = (F.t, Bty.t, Sym.t) generic_action
    type a_generic_paction = (F.t, Bty.t, Sym.t) generic_paction
    type a_generic_expr = (F.t, Bty.t, Sym.t) generic_expr

    type ('pre, 'mid) pe_binding_action = {
      barw_pb_pre : annots -> Bty.t -> a_generic_pattern -> 'pre M.t;
      barw_pb_mid : 'mid M.t;
      barw_pb_post : (annots * Bty.t * a_generic_pattern) * 'pre * 'mid ->
        a_generic_pexpr -> a_generic_pexpr -> a_generic_pexpr M.t;
    }
    let pe_binding_traverse = {
      barw_pb_pre = (fun annots bTy pat -> M.return (annots, bTy, pat));
      barw_pb_mid = M.return ();
      barw_pb_post =
        (fun ((annots, bTy, pat), _, _) e1 e2 -> M.return (Pexpr (annots, bTy, (PElet (pat, e1, e2)))));
    }

    type ('pre, 'mid, 'case, 'post) pecase_action = {
      (* this leaves the case as is; TODO: allow for changing the case *)
      barw_pecase_cased : annots -> Bty.t -> a_generic_pexpr -> 'pre M.t;
      barw_pecase_each_pre : a_generic_pattern -> 'mid M.t;
      barw_pecase_each_mid : a_generic_pexpr -> 'case M.t;
      barw_pecase_post : 'pre -> ('mid * 'case) list -> a_generic_pexpr M.t;
    }
    let pecase_traverse = {
      barw_pecase_cased = (fun annots bty pe -> M.return (annots, bty, pe));
      barw_pecase_each_pre = (fun pat -> M.return pat);
      barw_pecase_each_mid = (fun e -> M.return e);
      barw_pecase_post = (fun (annots, bty, pe) cases -> M.return (Pexpr (annots, bty, PEcase (pe, cases))));
    }

    type ('pre, 'mid, 'pre2, 'mid2, 'case2, 'post2) pe_rewrites = {
      barw_pesym : annots -> Bty.t -> Sym.t ->  a_generic_pexpr M.t;
      barw_pelet : ('pre, 'mid) pe_binding_action;
      barw_pecase : ('pre2, 'mid2, 'case2, 'post2) pecase_action;
      (* TODO: allow rewriters for non-binding constructors *)
    }
    let pe_rewrite_traverse = {
      barw_pesym = (fun annots bty x -> M.return (Pexpr (annots, bty, PEsym x)));
      barw_pelet = pe_binding_traverse;
      barw_pecase = pecase_traverse;
    }

    let rec rewrite_pexpr rws = function (Pexpr (annots, bty, pe_)) ->
      match pe_ with
      | PEsym x ->
        rws.barw_pesym annots bty x
      | PEimpl c ->
        (* TODO *)
        M.return (Pexpr (annots, bty, PEimpl c))
      | PEval v ->
        (* TODO *)
        M.return (Pexpr (annots, bty, PEval v))
      | PEconstrained cs ->
        (* TODO *)
        let* cs' =
          M.foldlM
            (fun (c, pe) cs' ->
              let* pe' = rewrite_pexpr rws pe in
              M.return ((c, pe') :: cs'))
            cs
            [] in
        M.return (Pexpr (annots, bty, PEconstrained (List.rev cs')))
      | PEundef (loc, u) ->
        M.return (Pexpr (annots, bty, PEundef (loc, u)))
      | PEerror (s, pe) ->
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEerror (s, pe')))
      | PEctor (c, pes) ->
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws pe in
              M.return (pe' :: pes'))
            pes
            [] in
        M.return (Pexpr (annots, bty, PEctor (c, List.rev pes')))
      | PEcase (pe, cases) ->
        let* pe' = rws.barw_pecase.barw_pecase_cased annots bty pe in
        let* cases' =
          M.foldlM
            (fun (pat, e) acc ->
              let* pat' = rws.barw_pecase.barw_pecase_each_pre pat in
              let* e' = rws.barw_pecase.barw_pecase_each_mid e in
              M.return ((pat', e') :: acc))
            cases
            [] in
        rws.barw_pecase.barw_pecase_post pe' (List.rev cases')
      | PEarray_shift (pe1, cty, pe2) ->
        (* TODO *)
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Pexpr (annots, bty, PEarray_shift (pe1', cty, pe2')))
      | PEmember_shift (pe, f, i) ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEmember_shift (pe', f, i)))
      | PEnot pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEnot pe'))
      | PEop (o, pe1, pe2) ->
        (* TODO *)
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Pexpr (annots, bty, PEop (o, pe1', pe2')))
      | PEstruct (s, flds) ->
        let* flds' =
          M.foldlM
            (fun (n, pe) flds' ->
              let* pe' = rewrite_pexpr rws pe in
              M.return ((n, pe') :: flds'))
            flds
            [] in
        M.return (Pexpr (annots, bty, PEstruct (s, List.rev flds')))
      | PEunion (s, f, pe) ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEunion (s, f, pe')))
      | PEcfunction pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEcfunction pe'))
      | PEmemberof (s, f, pe) ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEmemberof (s, f, pe')))
      | PEcall (gn, pes) ->
        (* TODO *)
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws pe in
              M.return (pe' :: pes'))
            pes
            [] in
        M.return (Pexpr (annots, bty, PEcall (gn, List.rev pes')))
      | PElet (pat, e1, e2) ->
        let* x = rws.barw_pelet.barw_pb_pre annots bty pat in
        let* e1' = rewrite_pexpr rws e1 in
        let* y = rws.barw_pelet.barw_pb_mid in
        let* e2' = rewrite_pexpr rws e2 in
        rws.barw_pelet.barw_pb_post ((annots, bty, pat), x, y) e1' e2'
      | PEif (pe1, pe2, pe3) ->
        (* TODO *)
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        M.return (Pexpr (annots, bty, PEif (pe1', pe2', pe3')))
      | PEis_scalar pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEis_scalar pe'))
      | PEis_integer pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEis_integer pe'))
      | PEis_signed pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEis_signed pe'))
      | PEis_unsigned pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEis_unsigned pe'))
      | PEbmc_assume pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws pe in
        M.return (Pexpr (annots, bty, PEbmc_assume pe'))
      | PEare_compatible (pe1, pe2) ->
        (* TODO *)
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Pexpr (annots, bty, PEare_compatible (pe1', pe2')))


    type ('pre, 'mid, 'case, 'post) ecase_action = {
      (* this leaves the case as is; TODO: allow for changing the case *)
      barw_ecase_cased : annots -> a_generic_pexpr -> 'pre M.t;
      barw_ecase_each_pre : a_generic_pattern -> 'mid M.t;
      barw_ecase_each_mid : a_generic_expr -> 'case M.t;
      barw_ecase_post : 'pre -> ('mid * 'case) list -> a_generic_expr M.t;
    }
    let ecase_traverse = {
      barw_ecase_cased = (fun annots pe -> M.return (annots, pe));
      barw_ecase_each_pre = (fun pat -> M.return pat);
      barw_ecase_each_mid = (fun e -> M.return e);
      barw_ecase_post = (fun (annots, pe) cases -> M.return (Expr (annots, Ecase (pe, cases))));
    }

    type ('pre, 'mid1, 'mid2, 'mid3) esave_action = {
      barw_esave_pre : annots -> (Sym.t * core_base_type) -> 'pre M.t;
      barw_esave_each_pre : Sym.t -> core_base_type -> 'mid1 M.t;
      barw_esave_each_mid : 'mid1 -> a_generic_pexpr -> 'mid2 M.t;
      barw_esave_mid : 'mid3 M.t;
      barw_esave_post :
        'pre ->
        'mid2 list ->
        a_generic_expr -> a_generic_expr M.t;
    }
    let esave_traverse = {
      barw_esave_pre = (fun annots fbty -> M.return (annots, fbty));
      barw_esave_each_pre = (fun x bty -> M.return (x, bty));
      barw_esave_each_mid = (fun (x, bty) pe -> M.return (x, (bty, pe)));
      barw_esave_mid = M.return ();
      barw_esave_post =
        (fun (annots, fbty) args e ->
          M.return (Expr (annots, Esave (fbty, args, e))))
    }

    type 'acc eunseq_action = {
      barw_eunseq_pre : annots -> 'acc M.t;
      barw_eunseq_each : 'acc -> a_generic_expr -> 'acc M.t;
      barw_eunseq_post : 'acc -> a_generic_expr list -> a_generic_expr M.t;
    }
    let eunseq_traverse = {
      barw_eunseq_pre = (fun annots -> M.return annots);
      barw_eunseq_each = (fun annots _ -> M.return annots);
      barw_eunseq_post = (fun annots cases ->
        M.return (Expr (annots, Eunseq cases)));
    }

    type ('pre, 'mid) pebinding_action = {
      barw_pebinding_pre : Annot.annot list -> Sym.t generic_pattern -> 'pre M.t;
      barw_pebinding_mid : 'mid M.t;
      barw_pebinding_post : 'pre -> 'mid ->
      (Bty.t, Sym.t) generic_pexpr -> (F.t, Bty.t, Sym.t) generic_expr ->
      (F.t, Bty.t, Sym.t) generic_expr M.t;
    }
    let elet_traverse = {
      barw_pebinding_pre = (fun annots pat -> M.return (annots, pat));
      barw_pebinding_mid = M.return ();
      barw_pebinding_post = (fun (annots, pat) () e1 e2 -> M.return (Expr (annots, Elet (pat, e1, e2))));
    }

    type ('pre, 'mid) e_binding_action = {
      barw_binding_pre : Annot.annot list -> Sym.t generic_pattern -> 'pre M.t;
      barw_binding_mid : 'mid M.t;
      barw_binding_post :
        'pre ->
        'mid ->
        a_generic_expr ->
        a_generic_expr ->
        a_generic_expr M.t;
    }
    let ewseq_traverse = {
      barw_binding_pre = (fun annots pat -> M.return (annots, pat));
      barw_binding_mid = M.return ();
      barw_binding_post = (fun (annots, pat) () e1' e2' -> M.return (Expr (annots, Ewseq (pat, e1', e2'))));
    }
    let esseq_traverse = {
      barw_binding_pre = (fun annots pat -> M.return (annots, pat));
      barw_binding_mid = M.return ();
      barw_binding_post = (fun (annots, pat) () e1' e2' -> M.return (Expr (annots, Esseq (pat, e1', e2'))));
    }

    type ('pre, 'mid) easeq_action = {
      barw_easeq_pre : Annot.annot list -> Sym.t -> core_base_type -> 'pre M.t;
      barw_easeq_mid : 'mid M.t;
      barw_easeq_post :
        'pre ->
        'mid ->
        a_generic_action ->
        a_generic_paction ->
        a_generic_expr M.t;
    }
    let easeq_traverse = {
      barw_easeq_pre = (fun annots x bty  -> M.return (annots, x, bty));
      barw_easeq_mid = M.return ();
      barw_easeq_post = (fun (annots, x, bty) () e1' e2' -> M.return (Expr (annots, Easeq ((x, bty), e1', e2'))));
    }

    type ('pre1, 'mid1, 'a1, 'b1, 'c1, 'd1, 'pre2, 'mid2, 'case2, 'post2, 'pre3, 'mid3, 'pre4, 'mid4, 'pre5, 'mid5, 'a6, 'pre7, 'mid7, 'pre8, 'acc8, 'mid8, 'post8) e_rewrites
    (* TODO: rename type args for clarity *)
    = {
      barw_epure : ('pre1, 'mid1, 'a1, 'b1, 'c1, 'd1) pe_rewrites;
      barw_ecase : ('pre2, 'mid2, 'case2, 'post2) ecase_action;
      barw_elet : ('pre3, 'mid3) pebinding_action;
      barw_eunseq : 'a6 eunseq_action;
      barw_ewseq : ('pre4, 'mid4) e_binding_action;
      barw_esseq : ('pre5, 'mid5) e_binding_action;
      barw_easeq : ('pre7, 'mid7) easeq_action;
      barw_esave : ('pre8, 'acc8, 'mid8, 'post8) esave_action;
    }
    let e_traverse = {
      barw_epure = pe_rewrite_traverse;
      barw_ecase = ecase_traverse;
      barw_elet = elet_traverse;
      barw_eunseq = eunseq_traverse;
      barw_ewseq = ewseq_traverse;
      barw_esseq = esseq_traverse;
      barw_easeq = easeq_traverse;
      barw_esave = esave_traverse;
    }

    let rec rewrite_action rws = function (Action (loc, x, a_)) ->
      match a_ with
      | Create (pe1, pe2, pfx) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Action (loc, x, Create (pe1', pe2', pfx)))
      | CreateReadOnly (pe1, pe2, pe3, pfx) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        M.return (Action (loc, x, CreateReadOnly (pe1', pe2', pe3', pfx)))
      | Alloc0 (pe1, pe2, pfx) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Action (loc, x, Alloc0 (pe1', pe2', pfx)))
      | Kill (b, pe) ->
        let* pe' = rewrite_pexpr rws pe in
        M.return (Action (loc, x, Kill (b, pe')))
      | Store0 (b, pe1, pe2, pe3, mo) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        M.return (Action (loc, x, Store0 (b, pe1', pe2', pe3', mo)))
      | Load0 (pe1, pe2, mo) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Action (loc, x, Load0 (pe1', pe2', mo)))
      | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        let* pe4' = rewrite_pexpr rws pe4 in
        M.return (Action (loc, x, RMW0 (pe1', pe2', pe3', pe4', mo1, mo2)))
      | Fence0 mo ->
        M.return (Action (loc, x, Fence0 mo))
      | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        let* pe4' = rewrite_pexpr rws pe4 in
        M.return (Action (loc, x, CompareExchangeStrong (pe1', pe2', pe3', pe4', mo1, mo2)))
      | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        let* pe4' = rewrite_pexpr rws pe4 in
        M.return (Action (loc, x, CompareExchangeWeak (pe1', pe2', pe3', pe4', mo1, mo2)))
      | LinuxFence mo -> failwith "<case>"
      | LinuxLoad (pe1, pe2, mo) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        M.return (Action (loc, x, LinuxLoad (pe1', pe2', mo)))
      | LinuxStore (pe1, pe2, pe3, mo) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        M.return (Action (loc, x, LinuxStore (pe1', pe2', pe3', mo)))
      | LinuxRMW (pe1, pe2, pe3, mo) ->
        let* pe1' = rewrite_pexpr rws pe1 in
        let* pe2' = rewrite_pexpr rws pe2 in
        let* pe3' = rewrite_pexpr rws pe3 in
        M.return (Action (loc, x, LinuxRMW (pe1', pe2', pe3', mo)))

    let rec rewrite_paction rws = function (Paction (pol, a)) ->
      let* a' = rewrite_action rws a in
      M.return (Paction (pol, a'))

    let rec rewrite_expr rws = function (Expr (annots, e_)) ->
      match e_ with
      | Epure pe ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws.barw_epure pe in
        M.return (Expr (annots, Epure pe'))
      | Ememop (mo, pes) ->
        (* TODO *)
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws.barw_epure pe in
              M.return (pe' :: pes'))
            pes
            [] in
        M.return (Expr (annots, Ememop (mo, List.rev pes')))
      | Eaction pa ->
        (* TODO *)
        let* pa' = rewrite_paction rws.barw_epure pa in
        M.return (Expr (annots, Eaction pa'))
      | Ecase (pe, cases) ->
        let* pe' = rws.barw_ecase.barw_ecase_cased annots pe in
        let* cases' =
          M.foldlM
            (fun (pat, e) acc ->
              let* pat' = rws.barw_ecase.barw_ecase_each_pre pat in
              let* e' = rws.barw_ecase.barw_ecase_each_mid e in
              M.return ((pat', e') :: acc))
            cases
            [] in
        rws.barw_ecase.barw_ecase_post pe' (List.rev cases')
      | Elet (pat, e1, e2) ->
        let* x = rws.barw_elet.barw_pebinding_pre annots pat in
        let* e1' = rewrite_pexpr rws.barw_epure e1 in
        let* y = rws.barw_elet.barw_pebinding_mid in
        let* e2' = rewrite_expr rws e2 in
        rws.barw_elet.barw_pebinding_post x y e1' e2'
      | Eif (pe, e1, e2) ->
        (* TODO *)
        let* pe' = rewrite_pexpr rws.barw_epure pe in
        let* e1' = rewrite_expr rws e1 in
        let* e2' = rewrite_expr rws e2 in
        M.return (Expr (annots, Eif (pe', e1', e2')))
      | Eskip ->
        (* TODO *)
        M.return (Expr (annots, Eskip))
      | Eccall (f, pe1, pe2, pes) ->
        (* TODO *)
        let* pe1' = rewrite_pexpr rws.barw_epure pe1 in
        let* pe2' = rewrite_pexpr rws.barw_epure pe2 in
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws.barw_epure pe in
              M.return (pe' :: pes'))
            pes
            [] in
        M.return (Expr (annots, Eccall (f, pe1', pe2', List.rev pes')))
      | Eproc (f, nm, pes) ->
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws.barw_epure pe in
              M.return (pe :: pes'))
            pes
            [] in
        (* TODO *)
        M.return (Expr (annots, Eproc (f, nm, List.rev pes')))
      | Eunseq es ->
        (* TODO *)
        let* acc = rws.barw_eunseq.barw_eunseq_pre annots in
        let* (acc', es') =
          M.foldlM
            (fun e (acc, es') ->
              let* e' = rewrite_expr rws e in
              let* acc' = rws.barw_eunseq.barw_eunseq_each acc e' in
              M.return (acc', e' :: es'))
            es
            (acc, []) in
        rws.barw_eunseq.barw_eunseq_post acc' (List.rev es')
      | Ewseq (pat, e1, e2) ->
        let* x = rws.barw_ewseq.barw_binding_pre annots pat in
        let* e1' = rewrite_expr rws e1 in
        let* y = rws.barw_ewseq.barw_binding_mid in
        let* e2' = rewrite_expr rws e2 in
        rws.barw_ewseq.barw_binding_post x y e1' e2'
      | Esseq (pat, e1, e2) ->
        let* x = rws.barw_esseq.barw_binding_pre annots pat in
        let* e1' = rewrite_expr rws e1 in
        let* y = rws.barw_esseq.barw_binding_mid in
        let* e2' = rewrite_expr rws e2 in
        rws.barw_esseq.barw_binding_post x y e1' e2'
      | Easeq ((x, bty), a, pa) ->
        let* xx = rws.barw_easeq.barw_easeq_pre annots x bty in
        let* a' = rewrite_action rws.barw_epure a in
        let* yy = rws.barw_easeq.barw_easeq_mid in
        let* pa' = rewrite_paction rws.barw_epure pa in
        rws.barw_easeq.barw_easeq_post xx yy a' pa'
      | Eindet (n, e) ->
        (* TODO: allow rewriting *)
        let* e' = rewrite_expr rws e in
        M.return (Expr (annots, Eindet (n, e')))
      | Ebound (n, e) ->
        (* TODO: allow rewriting *)
        let* e' = rewrite_expr rws e in
        M.return (Expr (annots, Ebound (n, e')))
      | End es ->
        (* TODO *)
        let* es' =
          M.foldlM
            (fun e es' ->
              let* e' = rewrite_expr rws e in
              M.return (e' :: es'))
              es
              [] in
        M.return (Expr (annots, End (List.rev es')))
      | Esave (lab_bty, args, e) ->
        (* TODO *)
        let* x = rws.barw_esave.barw_esave_pre annots lab_bty in
        let* args' =
          M.foldlM
            (fun (lab, (bty, pe)) pes' ->
              let* x = rws.barw_esave.barw_esave_each_pre lab bty  in
              let* pe' = rewrite_pexpr rws.barw_epure pe in
              let* y = rws.barw_esave.barw_esave_each_mid x pe' in
              M.return (y :: pes'))
              args
              [] in
        let* () = rws.barw_esave.barw_esave_mid in
        let* e' = rewrite_expr rws e in
        rws.barw_esave.barw_esave_post x (List.rev args') e'
      | Erun (f, lab, pes) ->
        let* pes' =
          M.foldlM
            (fun pe pes' ->
              let* pe' = rewrite_pexpr rws.barw_epure pe in
              M.return (pe' :: pes'))
            pes
            [] in
        (* TODO *)
        M.return (Expr (annots, Erun (f, lab, List.rev pes')))
      | Epar es ->
        let* es' =
          M.foldlM
            (fun e es' ->
              let* e' = rewrite_expr rws e in
              M.return (e' :: es'))
              es
              [] in
        (* TODO *)
        M.return (Expr (annots, Epar (List.rev es')))
      | Ewait tid ->
        (* TODO *)
        M.return (Expr (annots, Ewait tid))
  end
end

module Gensym = struct
    type state = int
    
    type 'a t = ('a, state) State.stateM
    
    let return : 'a -> 'a t = State.return
    let bind : 'a t -> ('a -> 'b t) -> 'b t = State.bind
    let (>>=) = bind
    let mapM = State.mapM
    let mapM_ = State.mapM_
    let rec foldlM (f: ('a -> 'b -> 'b t)) xs init =
      match xs with
      | [] ->
        return init
      | x::xs' ->
        f x init >>= fun init' ->
        foldlM f xs' init'
    
    let gen : state t =
      bind (State.get)
        (fun x -> bind (State.update (fun y -> y + 1)) (fun () -> return x))

    let runStateM : 'a t -> state -> ('a * state) = State.runStateM
end

module Int_map = Map.Make(Int)

module Scoped_remapping = struct
    type state = {
      sr_counter : int;
      sr_stk_aside : int Int_map.t list;
      sr_stk_in_scope : int Int_map.t list;
    }
    
    type 'a t = ('a, state) State.stateM
    
    let return : 'a -> 'a t = State.return
    let bind : 'a t -> ('a -> 'b t) -> 'b t = State.bind
    let (>>=) = bind
    let mapM = State.mapM
    let mapM_ = State.mapM_
    let rec foldlM (f: ('a -> 'b -> 'b t)) xs init =
      match xs with
       | [] ->
           return init
       | x::xs' ->
           f x init >>= fun init' ->
           foldlM f xs' init'
    
    let (let+) x f = State.bind x f

    let add_to_head k v = function
    | [] -> assert false
    | m :: stk -> Int_map.add k v m :: stk

    (** generate and register a remapping for `k` *)
    let gen : int -> int t = fun k ->
      let+ st = State.get in
      let+ () =
        State.update
          (fun st2 ->
            { st2 with
              sr_counter = st2.sr_counter + 1;
              sr_stk_in_scope = add_to_head k st.sr_counter st2.sr_stk_in_scope }) in
      State.return st.sr_counter

    let rec lookup_in_stack x = function
    | [] -> None
    | m :: stk ->
      begin match Int_map.find_opt x m with
      | None -> lookup_in_stack x stk
      | Some y -> Some y
      end

    let lookup : int -> (int option) t = fun x ->
      let+ st = State.get in
      State.return (lookup_in_stack x st.sr_stk_in_scope)

    let new_scope : unit t =
      State.update (fun st -> { st with sr_stk_in_scope = Int_map.empty :: st.sr_stk_in_scope })

    let enter_aside_scope : unit t =
      State.update
        (fun st ->
          match st.sr_stk_aside with
          | [] -> assert false
          | m :: rest_aside ->
            { st with
              sr_stk_in_scope = m :: st.sr_stk_in_scope;
              sr_stk_aside = rest_aside })

    let set_scope_aside : unit t =
      State.update
        (fun st ->
          match st.sr_stk_in_scope with
          | [] -> assert false
          | m :: rest_in_scope ->
            { st with
              sr_stk_in_scope = rest_in_scope;
              sr_stk_aside = m :: st.sr_stk_aside })

    let leave_scope : unit t =
      State.update
        (fun st ->
          match st.sr_stk_in_scope with
          | [] -> assert false
          | _ :: rest_in_scope ->
            { st with
              sr_stk_in_scope = rest_in_scope })

    let runStateM : 'a t -> state -> ('a * state) = State.runStateM

    let init_scope = {
      sr_counter = 1;
      sr_stk_aside = [];
      sr_stk_in_scope = [];
    }


    let debug_only_dump : state t =
      State.get
end

module State = struct
    module Make (X : Type) = struct
    type state = X.t
    
    type 'a t = ('a, state) State.stateM
    
    let return : 'a -> 'a t = State.return
    let bind : 'a t -> ('a -> 'b t) -> 'b t = State.bind
    let (>>=) = bind
    let mapM = State.mapM
    let mapM_ = State.mapM_
    let rec foldlM (f: ('a -> 'b -> 'b t)) xs init =
      match xs with
       | [] ->
           return init
       | x::xs' ->
           f x init >>= fun init' ->
           foldlM f xs' init'
    
    let get : 'a t = State.get

    let update : (state -> state) -> 'a t = State.update

    let runStateM : 'a t -> state -> ('a * state) = State.runStateM

    end
end

module Symbol_helper = struct
  type t = Symbol.sym
end

module RW = Binding_aware_rewriter.Make(Unit)(Symbol_helper)(Unit)(Scoped_remapping)

(*
  let rewrite_impl_decl = function
    | Def (bTy, pe) ->
        Def (bTy, rewrite_pexpr pe)
    | IFun (bTy, args, pe) ->
        IFun (bTy, args, rewrite_pexpr pe) in*)
  
let rewrite_fun_map_decl rws = function
  | Fun (bTy, args, pe) ->
    let (pe', _) = Scoped_remapping.runStateM (RW.rewrite_pexpr rws.RW.barw_epure pe) Scoped_remapping.init_scope in
    Fun (bTy, args, pe')
  | Proc (loc, bTy, args, e) ->
    let (e', _) = Scoped_remapping.runStateM (RW.rewrite_expr rws e) Scoped_remapping.init_scope in
    Proc (loc, bTy, args, e')
  | decl -> decl

let rewrite_file rws file =
  { main = file.main
  ; tagDefs = file.tagDefs
  ; stdlib = file.stdlib
  ; impl = file.impl
  ; globs = file.globs
  ; funs = Pmap.map (rewrite_fun_map_decl rws) file.funs
  ; extern = file.extern
  ; funinfo = file.funinfo }

let mk_name x = "a" ^ Int.to_string x

let rec rewrite_pat = let open RW in function
| Pattern (annots, pat_) ->
  let* pat_' = rewrite_pat_ pat_ in
  Scoped_remapping.return (Pattern (annots, pat_'))
and rewrite_pat_ = let open RW in function
| CaseBase (None, ty) ->
  Scoped_remapping.return (CaseBase (None, ty))
| CaseBase (Some (Symbol.Symbol (d, n, Some x)), ty) ->
  Scoped_remapping.return (CaseBase (Some (Symbol.Symbol (d, n, Some x)), ty))
| CaseBase (Some (Symbol.Symbol (d, n, None)), ty) ->
  let* x = Scoped_remapping.gen n in
  Scoped_remapping.return (CaseBase (Some (Symbol.Symbol (d, n, Some (mk_name x))), ty))
| CaseCtor (ctor, pats) ->
  let* pats' =
    Scoped_remapping.foldlM
      (fun pat pats ->
        let* pat' = rewrite_pat pat in
        Scoped_remapping.return (pat' :: pats)) pats [] in
  Scoped_remapping.return (CaseCtor (ctor, List.rev pats'))

let create_scope_from_pat_and_set_aside annots pat = let open RW in
  let* () = Scoped_remapping.new_scope in
  let* pat' = rewrite_pat pat in
  let* () = Scoped_remapping.set_scope_aside in
  Scoped_remapping.return (annots, pat')

let string_of_scope (sr : Scoped_remapping.state) =
  let string_of_partial_scope m =
    "{" ^ String.concat ", " (List.map (fun (n, n') -> string_of_int n ^ ":" ^ string_of_int n') (Int_map.bindings m)) ^ "}" in
  let string_of_half_scope l = String.concat "; " (List.map string_of_partial_scope l) in
  string_of_half_scope sr.sr_stk_aside ^ " | " ^ string_of_half_scope sr.sr_stk_in_scope

let rewrite_make_name_human_readable = let open RW in { RW.e_traverse with
  RW.barw_epure = { RW.pe_rewrite_traverse with
    barw_pesym =
      (fun annots bty s ->
        match s with
        | Symbol.Symbol (_, _, Some _) -> Scoped_remapping.return (Pexpr (annots, bty, PEsym s))
        | Symbol.Symbol (d, n, None) ->
          let* x = Scoped_remapping.lookup n in
          begin match x with
          | None ->
            (* TODO: how could these appear?
            let* scp = Scoped_remapping.debug_only_dump in
            prerr_string ("a_" ^ string_of_int n ^ " not in scope " ^ string_of_scope scp ^ "\n");
            *)
            Scoped_remapping.return (Pexpr (annots, bty, PEsym (Symbol.Symbol (d, n, None))))
          | Some x ->
            let x = mk_name x in
            Scoped_remapping.return (Pexpr (annots, bty, PEsym (Symbol.Symbol (d, n, Some x))))
          end);
    (* TODO: let and case? *)
  };
  barw_elet = {
    barw_pebinding_pre = create_scope_from_pat_and_set_aside;
    barw_pebinding_mid = Scoped_remapping.enter_aside_scope;
    barw_pebinding_post =
      (fun (annots, pat') () e1' e2' ->
        let* () = Scoped_remapping.leave_scope in
        Scoped_remapping.return (Expr (annots, Elet (pat', e1', e2'))));
  };
  barw_ewseq = {
    barw_binding_pre = create_scope_from_pat_and_set_aside;
    barw_binding_mid = Scoped_remapping.enter_aside_scope;
    barw_binding_post =
      (fun (annots, pat') () e1' e2' ->
        let* () = Scoped_remapping.leave_scope in
        Scoped_remapping.return (Expr (annots, Ewseq (pat', e1', e2'))));
  };
  barw_esseq = {
    barw_binding_pre = create_scope_from_pat_and_set_aside;
    barw_binding_mid = Scoped_remapping.enter_aside_scope;
    barw_binding_post =
      (fun (annots, pat') () e1' e2' ->
        let* () = Scoped_remapping.leave_scope in
        Scoped_remapping.return (Expr (annots, Esseq (pat', e1', e2'))));
  };
  (* TODO: other constructs! including case! *)
  barw_esave = {
    barw_esave_pre =
      (fun annots lab_bty ->
        let* () = Scoped_remapping.new_scope in
        let* () = Scoped_remapping.set_scope_aside in
        Scoped_remapping.return (annots, lab_bty));
    barw_esave_each_pre =
      (fun s bty ->
        match s with
        | Symbol.Symbol (_, _, Some _) ->
          Scoped_remapping.return (s, bty)
        | Symbol.Symbol (d, n, None) ->
          let* () = Scoped_remapping.enter_aside_scope in
          let* s' = Scoped_remapping.gen n in
          let* () = Scoped_remapping.set_scope_aside in
          Scoped_remapping.return (Symbol.Symbol (d, n, Some (mk_name s')), bty));
    barw_esave_each_mid = (fun (lab, bty) pe -> Scoped_remapping.return (lab, (bty, pe)));
    barw_esave_mid =
      Scoped_remapping.enter_aside_scope;
    barw_esave_post =
      (fun (annots, labbty) args e ->
        let* () = Scoped_remapping.leave_scope in
        Scoped_remapping.return (Expr (annots, Esave (labbty, args, e))));
  }
}

let rewrite_file file =
  rewrite_file rewrite_make_name_human_readable file
