module C = Core
open C


module type Monad = sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val foldlM: ('a -> 'b -> 'b t) -> 'a list -> 'b -> 'b t
end


module Rewriter = functor (Eff: Monad) -> struct
  include Eff
  
  let has_changed =
    ref false
  
  let rec repeat n m z =
    if n = 0 then
      return z
    else begin
      has_changed := false;
      m z >>= fun z' ->
      if !has_changed then
        repeat (n-1) m z'
      else
        return z'
    end
  
  type 'a action =
    | Unchanged
    | Update of 'a Eff.t
    | Traverse
    | PostTraverseAction of (unit -> unit Eff.t)
    | DoChildrenPost of ('a -> 'a Eff.t)
    | ChangeDoChildrenPost of ('a Eff.t) * ('a -> 'a Eff.t) (* NOTE: the name comes from CIL *)
  
  type 'a rw =
    | RW of ('a -> 'a action)
  
  type 'bty rewriter = {
      rw_pexpr : (('bty, Symbol.sym) C.generic_pexpr) rw;
      rw_action: ((unit, 'bty, Symbol.sym) generic_action) rw;
      rw_expr  : ((unit, 'bty, Symbol.sym) generic_expr) rw;
  }
 
  type (_, 'bty) selector =
    | PEXPR  : (('bty, Symbol.sym) C.generic_pexpr, 'bty) selector
    | ACTION : ((unit, 'bty, Symbol.sym) C.generic_action, 'bty) selector
    | EXPR   : ((unit, 'bty, Symbol.sym) C.generic_expr, 'bty) selector
  
  
  let doRewrite (type a bty) (z: (a, bty) selector) (rw: bty rewriter) (children: bty rewriter -> a -> a Eff.t) (node: a) : a Eff.t =
    let _start : a rw = match z with
      | PEXPR  -> rw.rw_pexpr
      | ACTION -> rw.rw_action
      | EXPR   -> rw.rw_expr in
    let RW start = _start in (* TODO, not sure why I need this intermediate step to typecheck *)
    match start node with
      | Unchanged ->
          return node
      | Update node' ->
          has_changed := true;
          node'
      | Traverse ->
          children rw node
      | PostTraverseAction a ->
          children rw node >>= fun ch ->
          a () >>= fun () ->
          return ch
      | DoChildrenPost post ->
          children rw node >>= fun ch ->
          post ch
      | ChangeDoChildrenPost (m_node', post) ->
          has_changed := true;
          m_node' >>= fun node' ->
          children rw node' >>= fun ch ->
          post ch
  
  
  let rec rewritePexpr (rw: 'bty rewriter) (pe: ('bty, Symbol.sym) C.generic_pexpr) : (('bty, Symbol.sym) C.generic_pexpr) Eff.t =
    doRewrite PEXPR rw childrenPexpr pe
  
  and childrenPexpr (rw: 'bty rewriter) (Pexpr (annots, bty, pexpr_) as pexpr) =
    let aux = rewritePexpr rw in
    let return_wrap z = return (Pexpr (annots, bty, z)) in
    match pexpr_ with
      | PEsym _
      | PEimpl _
      | PEval _ ->
          return pexpr
      | PEconstrained xs ->
          mapM (fun (x, pe) ->
            aux pe >>= fun pe' ->
            return (x, pe')
          ) xs >>= fun xs' ->
          return_wrap (PEconstrained xs')
      | PEundef _ ->
          return pexpr
      | PEerror (str, pe) ->
          aux pe >>= fun pe' ->
          return_wrap (PEerror (str, pe'))
      | PEctor (ctor, pes) ->
          mapM aux pes >>= fun pes' ->
          return_wrap (PEctor (ctor, pes'))
      | PEcase (pe, pat_pes) ->
          aux pe >>= fun pe' ->
          mapM (fun (pat, pe) ->
            aux pe >>= fun pe' ->
            return (pat, pe')
          ) pat_pes >>= fun pat_pes' ->
          return_wrap (PEcase (pe', pat_pes'))
      | PEarray_shift (pe1, ty, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEarray_shift (pe1', ty, pe2'))
      | PEmember_shift (pe, sym, ident) ->
          aux pe >>= fun pe' ->
          return_wrap (PEmember_shift (pe', sym, ident))
      | PEnot pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEnot pe')
      | PEop (bop, pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEop (bop, pe1', pe2'))
      | PEstruct (sym, xs) ->
          mapM (fun (ident, pe) ->
            aux pe >>= fun pe' ->
            return (ident, pe')
          ) xs >>= fun xs' ->
          return_wrap (PEstruct (sym, xs'))
      | PEunion (sym, ident, pe) ->
          aux pe >>= fun pe' ->
          return_wrap (PEunion (sym, ident, pe'))
      | PEcfunction pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEcfunction pe')
      | PEmemberof (sym, ident, pe) ->
          aux pe >>= fun pe' ->
          return_wrap (PEmemberof (sym, ident, pe'))
      | PEcall (nm, pes) ->
          mapM aux pes >>= fun pes' ->
          return_wrap (PEcall (nm, pes'))
      | PElet (pat, pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PElet (pat, pe1', pe2'))
      | PEif (pe1, pe2, pe3) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          aux pe3 >>= fun pe3' ->
          return_wrap (PEif (pe1', pe2', pe3'))
      | PEis_scalar pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEis_scalar pe')
      | PEis_integer pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEis_integer pe')
      | PEis_signed pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEis_signed pe')
      | PEis_unsigned pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEis_unsigned pe')
      | PEbmc_assume pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEbmc_assume pe')
      | PEare_compatible (pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEare_compatible (pe1', pe2'))
  
  
  let rec rewriteAction (rw: 'bty rewriter) (act: (unit, 'bty, Symbol.sym) C.generic_action) : ((unit, 'bty, Symbol.sym) C.generic_action) Eff.t =
    doRewrite ACTION rw childrenAction act
  
  and childrenAction (rw: 'bty rewriter) (Action (loc, (), act_)) =
    let aux_pexpr = rewritePexpr rw in
    let return_wrap z = return (Action (loc, (), z)) in
    match act_ with
      | Create (pe1, pe2, pref) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          return_wrap (Create (pe1', pe2', pref))
      | CreateReadOnly (pe1, pe2, pe3, pref) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (CreateReadOnly (pe1', pe2', pe3', pref))
      | Alloc0 (pe1, pe2, pref) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          return_wrap (Alloc0 (pe1', pe2', pref))
      | Kill (b, pe) ->
          aux_pexpr pe >>= fun pe' ->
          return_wrap (Kill (b, pe'))
      | Store0 (b, pe1, pe2, pe3, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (Store0 (b, pe1', pe2', pe3', mo))
      | Load0 (pe1, pe2, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          return_wrap (Load0 (pe1', pe2', mo))
      | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          aux_pexpr pe4 >>= fun pe4' ->
          return_wrap (RMW0 (pe1', pe2', pe3', pe4', mo1, mo2))
      | Fence0 mo ->
          return_wrap (Fence0 mo)
      | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          aux_pexpr pe4 >>= fun pe4' ->
          return_wrap (CompareExchangeStrong (pe1', pe2', pe3', pe4', mo1, mo2))
      | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          aux_pexpr pe4 >>= fun pe4' ->
          return_wrap (CompareExchangeWeak (pe1', pe2', pe3', pe4', mo1, mo2))
      | LinuxFence mo ->
          return_wrap (LinuxFence mo)
      | LinuxLoad (pe1, pe2, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          return_wrap (LinuxLoad (pe1', pe2', mo))
      | LinuxStore (pe1, pe2, pe3, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (LinuxStore (pe1', pe2', pe3', mo))
      | LinuxRMW (pe1, pe2, pe3, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (LinuxRMW (pe1', pe2', pe3', mo))
  
  
  let rec rewriteExpr (rw: 'bty rewriter) (expr: (unit, 'bty, Symbol.sym) C.generic_expr) : ((unit, 'bty, Symbol.sym) C.generic_expr) Eff.t =
    doRewrite EXPR rw childrenExpr expr
  
  and childrenExpr (rw: 'bty rewriter) (Expr (annots, expr_)) =
    let aux = rewriteExpr rw in
    let aux_pexpr = rewritePexpr rw in
    let aux_action = rewriteAction rw in
    let return_wrap z = return (Expr (annots, z)) in
    match expr_ with
      | Epure pe ->
          aux_pexpr pe >>= fun pe' ->
          return_wrap (Epure pe')
      | Ememop (mop, pes) ->
          mapM aux_pexpr pes >>= fun pes' ->
          return_wrap (Ememop (mop, pes'))
      | Eaction (Paction (p, act)) ->
          aux_action act >>= fun act' ->
          return_wrap (Eaction (Paction (p, act')))
      | Ecase (pe, pat_es) ->
          aux_pexpr pe >>= fun pe' ->
          mapM (fun (pat, e) ->
            aux e >>= fun e' ->
            return (pat, e')
          ) pat_es >>= fun pat_es' ->
          return_wrap (Ecase (pe', pat_es'))
      | Elet (pat, pe, e) ->
          aux_pexpr pe >>= fun pe' ->
          aux e >>= fun e' ->
          return_wrap (Elet (pat, pe', e'))
      | Eif (pe, e1, e2) ->
          aux_pexpr pe >>= fun pe' ->
          aux e1 >>= fun e1' ->
          aux e2 >>= fun e2' ->
          return_wrap (Eif (pe', e1', e2'))
      | Eskip ->
          return_wrap Eskip
      | Eccall ((), pe1, pe2, pes) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          mapM aux_pexpr pes >>= fun pes' ->
          return_wrap (Eccall ((), pe1', pe2', pes'))
      | Eproc ((), nm ,pes) ->
          mapM aux_pexpr pes >>= fun pes' ->
          return_wrap (Eproc ((), nm, pes'))
      | Eunseq es ->
          mapM aux es >>= fun es' ->
          return_wrap (Eunseq es')
      | Ewseq (pat, e1, e2) ->
          aux e1 >>= fun e1' ->
          aux e2 >>= fun e2' ->
          return_wrap (Ewseq (pat, e1', e2'))
      | Esseq (pat, e1, e2) ->
          aux e1 >>= fun e1' ->
          aux e2 >>= fun e2' ->
          return_wrap (Esseq (pat, e1', e2'))
      | Easeq (sym_bTy, act1, Paction (p, act2)) ->
          aux_action act1 >>= fun act1' ->
          aux_action act2 >>= fun act2' ->
          return_wrap (Easeq (sym_bTy, act1', Paction (p, act2')))
      | Eindet (n, e) ->
          aux e >>= fun e' ->
          return_wrap (Eindet (n, e'))
      | Ebound (n, e) ->
          aux e >>= fun e' ->
          return_wrap (Ebound (n, e'))
      | End es ->
          mapM aux es >>= fun es' ->
          return_wrap (End es')
      | Esave (sym_bTy, xs, e) ->
          mapM (fun (sym, (bTy, pe)) ->
            aux_pexpr pe >>= fun pe' ->
            return (sym, (bTy, pe'))
          ) xs >>= fun xs' ->
          aux e >>= fun e' ->
          return_wrap (Esave (sym_bTy, xs', e'))
      | Erun ((), sym, pes) ->
          mapM aux_pexpr pes >>= fun pes' ->
          return_wrap (Erun ((), sym, pes'))
      | Epar es ->
          mapM aux es >>= fun es' ->
          return_wrap (Epar es')
      | Ewait tid ->
          return_wrap (Ewait tid)
end
