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
  type state = {
    rw_loc: Cerb_location.t;
    rw_has_changed: bool;
  }

  type 'a t =
    state -> (state * 'a Eff.t)
  
  let return (z: 'a) : 'a t =
    fun st -> (st, Eff.return z)
  
  let bind (ma : 'a t) (f : 'a -> 'b t) : 'b t =
    fun st ->
      let (st', a) = ma st in
      (st', Eff.bind a (fun z -> snd (f z st')))
  
  let (>>=) ma f = bind ma f

  let sequence ms =
    List.fold_right
      (fun m m' ->
        m  >>= fun x  ->
        m' >>= fun xs ->
        return (x::xs)
      ) ms (return [])
  
  let listM t xs = sequence (t xs)
  
  let mapM f = listM (List.map f)

  let rec foldlM f a = function
    | [] ->
        return a
    | x::xs ->
        bind (f a x) (fun z -> foldlM f z xs)
  
  let liftM (ma: 'a Eff.t) : 'a t =
    fun st -> (st, ma)
  
  let runM (ma: 'a t) : 'a Eff.t =
    snd (ma { rw_loc= Cerb_location.unknown; rw_has_changed= false })
  
  let update_loc loc : unit t =
    fun st ->
      ({ st with rw_loc= loc }, Eff.return ())
  
  let get_loc : Cerb_location.t t =
    fun st ->
      (st, Eff.return st.rw_loc)
  
  let has_changed =
    ref false
  
  let rec repeat n m z =
    let open Eff in
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
    | RW of (Cerb_location.t -> 'a -> 'a action)
  
  type 'bty rewriter = {
      rw_pexpr : (('bty, Symbol.sym) C.generic_pexpr) rw;
      rw_action: ((unit, 'bty, Symbol.sym) generic_action) rw;
      rw_expr  : ((unit, 'bty, Symbol.sym) generic_expr) rw;
  }
 
  type (_, 'bty) selector =
    | PEXPR  : (('bty, Symbol.sym) C.generic_pexpr, 'bty) selector
    | ACTION : ((unit, 'bty, Symbol.sym) C.generic_action, 'bty) selector
    | EXPR   : ((unit, 'bty, Symbol.sym) C.generic_expr, 'bty) selector
  
  let doRewrite (type a bty) (z: (a, bty) selector) (rw: bty rewriter) (children: bty rewriter -> a -> a t) (node: a) : a t =
    let _start : a rw = match z with
      | PEXPR  -> rw.rw_pexpr
      | ACTION -> rw.rw_action
      | EXPR   -> rw.rw_expr in
    let RW start = _start in (* TODO, not sure why I need this intermediate step to typecheck *)
    get_loc >>= fun loc ->
    match start loc node with
      | Unchanged ->
          return node
      | Update node' ->
          has_changed := true;
          liftM node'
      | Traverse ->
          children rw node
      | PostTraverseAction a ->
          children rw node >>= fun ch ->
          liftM (a ()) >>= fun () ->
          return ch
      | DoChildrenPost post ->
          children rw node >>= fun ch ->
          liftM (post ch)
      | ChangeDoChildrenPost (m_node', post) ->
          has_changed := true;
          liftM m_node' >>= fun node' ->
          children rw node' >>= fun ch ->
          liftM (post ch)
  
  
  let rec rewritePexpr_ (rw: 'bty rewriter) (pe: ('bty, Symbol.sym) C.generic_pexpr) : (('bty, Symbol.sym) C.generic_pexpr) t =
    doRewrite PEXPR rw childrenPexpr pe
  
  and childrenPexpr (rw: 'bty rewriter) (Pexpr (annots, bty, pexpr_) as pexpr) =
    let aux = rewritePexpr_ rw in
    let return_wrap z = return (Pexpr (annots, bty, z)) in
    begin match Annot.get_loc annots with
      | Some loc ->
          update_loc loc
      | None ->
          return ()
    end >>= fun () ->
    match pexpr_ with
      | PEsym _
      | PEimpl _
      | PEval _ ->
          return pexpr
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
      | PEmemop (mop, pes) ->
          mapM aux pes >>= fun pes' ->
          return_wrap (PEmemop (mop, pes'))
      | PEnot pe ->
          aux pe >>= fun pe' ->
          return_wrap (PEnot pe')
      | PEop (bop, pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEop (bop, pe1', pe2'))
      | PEconv_int (ity, pe) ->
          aux pe >>= fun pe' ->
          return_wrap (PEconv_int (ity, pe'))
      | PEwrapI (ity, iop, pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEwrapI (ity, iop, pe1', pe2'))
      | PEcatch_exceptional_condition (ity, iop, pe1, pe2) ->
          aux pe1 >>= fun pe1' ->
          aux pe2 >>= fun pe2' ->
          return_wrap (PEcatch_exceptional_condition (ity, iop, pe1', pe2'))
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
  
  
  let rec rewriteAction_ (rw: 'bty rewriter) (act: (unit, 'bty, Symbol.sym) C.generic_action) : ((unit, 'bty, Symbol.sym) C.generic_action) t =
    doRewrite ACTION rw childrenAction act
  
  and childrenAction (rw: 'bty rewriter) (Action (loc, (), act_)) =
    let aux_pexpr = rewritePexpr_ rw in
    let return_wrap z = return (Action (loc, (), z)) in
    update_loc loc >>= fun () ->
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
      | Kill (kind, pe) ->
          aux_pexpr pe >>= fun pe' ->
          return_wrap (Kill (kind, pe'))
      | Store0 (b, pe1, pe2, pe3, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (Store0 (b, pe1', pe2', pe3', mo))
      | Load0 (pe1, pe2, mo) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          return_wrap (Load0 (pe1', pe2', mo))
      | SeqRMW (b, pe1, pe2, sym, pe3) ->
          aux_pexpr pe1 >>= fun pe1' ->
          aux_pexpr pe2 >>= fun pe2' ->
          aux_pexpr pe3 >>= fun pe3' ->
          return_wrap (SeqRMW (b, pe1', pe2', sym, pe3'))
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
  
  
  let rec rewriteExpr_ (rw: 'bty rewriter) (expr: (unit, 'bty, Symbol.sym) C.generic_expr) : ((unit, 'bty, Symbol.sym) C.generic_expr) t =
    doRewrite EXPR rw childrenExpr expr
  
  and childrenExpr (rw: 'bty rewriter) (Expr (annots, expr_)) =
    let aux = rewriteExpr_ rw in
    let aux_pexpr = rewritePexpr_ rw in
    let aux_action = rewriteAction_ rw in
    let return_wrap z = return (Expr (annots, z)) in
    begin match Annot.get_loc annots with
      | Some loc ->
          update_loc loc
      | None ->
          return ()
    end >>= fun () ->
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
      | Ebound e ->
          aux e >>= fun e' ->
          return_wrap (Ebound e')
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
      | Eannot (fps, e) ->
          aux e >>= fun e' ->
          return_wrap (Eannot (fps, e'))
      | Eexcluded (n, act) ->
          aux_action act >>= fun act' ->
          return_wrap (Eexcluded (n, act'))

  let rewritePexpr (rw: 'bty rewriter) (pe: ('bty, Symbol.sym) C.generic_pexpr) : (('bty, Symbol.sym) C.generic_pexpr) Eff.t =
    runM (rewritePexpr_ rw pe)
  
  let rewriteAction (rw: 'bty rewriter) (act: (unit, 'bty, Symbol.sym) C.generic_action) : ((unit, 'bty, Symbol.sym) C.generic_action) Eff.t =
    runM (rewriteAction_ rw act)
  
  let rewriteExpr (rw: 'bty rewriter) (expr: (unit, 'bty, Symbol.sym) C.generic_expr) : ((unit, 'bty, Symbol.sym) C.generic_expr) Eff.t =
    runM (rewriteExpr_ rw expr)
end
