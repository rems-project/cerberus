open Bool
open CoqEqDec
open Datatypes
open List0
open MetatheoryAtom
open Alist
open Genericvalues
open Infrastructure
open Syntax

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module SBSE = 
 struct 
  type coq_Result =
    | Rok
    | Rabort
  
  (** val coq_Result_rect : 'a1 -> 'a1 -> coq_Result -> 'a1 **)
  
  let coq_Result_rect f f0 = function
    | Rok -> f
    | Rabort -> f0
  
  (** val coq_Result_rec : 'a1 -> 'a1 -> coq_Result -> 'a1 **)
  
  let coq_Result_rec f f0 = function
    | Rok -> f
    | Rabort -> f0
  
  (** val callLib :
      LLVMgv.mem -> LLVMsyntax.id -> LLVMgv.coq_GenericValue list ->
      ((LLVMgv.coq_GenericValue option*LLVMgv.mem)*coq_Result) option **)
  
  let callLib = Symexe_aux.callLib
  
  (** val isCallLib : LLVMsyntax.id -> bool **)
  
  let isCallLib = Symexe_aux.isCallLib
  
  (** val isCall : LLVMsyntax.cmd -> bool **)
  
  let isCall = function
    | LLVMsyntax.Coq_insn_call (i0, n, c, t, v, p) ->
        (match v with
           | LLVMsyntax.Coq_value_id i1 -> true
           | LLVMsyntax.Coq_value_const c0 ->
               (match c0 with
                  | LLVMsyntax.Coq_const_gid (t0, fid) ->
                      negb (isCallLib fid)
                  | _ -> true))
    | _ -> false
  
  type nbranch =
    LLVMsyntax.cmd
    (* singleton inductive, whose constructor was mkNB *)
  
  (** val nbranch_rect : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rect f n =
    f n __
  
  (** val nbranch_rec : (LLVMsyntax.cmd -> __ -> 'a1) -> nbranch -> 'a1 **)
  
  let nbranch_rec f n =
    f n __
  
  (** val nbranching_cmd : nbranch -> LLVMsyntax.cmd **)
  
  let nbranching_cmd n =
    n
  
  type subblock = { coq_NBs : nbranch list; call_cmd : LLVMsyntax.cmd }
  
  (** val subblock_rect :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rect f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val subblock_rec :
      (nbranch list -> LLVMsyntax.cmd -> __ -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rec f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0 __
  
  (** val coq_NBs : subblock -> nbranch list **)
  
  let coq_NBs x = x.coq_NBs
  
  (** val call_cmd : subblock -> LLVMsyntax.cmd **)
  
  let call_cmd x = x.call_cmd
  
  (** val isCall_dec : LLVMsyntax.cmd -> bool **)
  
  let isCall_dec = function
    | LLVMsyntax.Coq_insn_call (i0, n, c0, t, v, p) ->
        (match v with
           | LLVMsyntax.Coq_value_id i1 -> false
           | LLVMsyntax.Coq_value_const c1 ->
               (match c1 with
                  | LLVMsyntax.Coq_const_gid (t0, i1) ->
                      let b = isCallLib i1 in if b then true else false
                  | _ -> false))
    | _ -> true
  
  (** val cmds2sbs : LLVMsyntax.cmds -> subblock list*nbranch list **)
  
  let rec cmds2sbs = function
    | [] -> [],[]
    | c::cs' ->
        if isCall_dec c
        then let l0,nbs0 = cmds2sbs cs' in
             (match l0 with
                | [] -> [],(c::nbs0)
                | s::sbs' ->
                    let { coq_NBs = nbs; call_cmd = call0 } = s in
                    ({ coq_NBs = (c::nbs); call_cmd = call0 }::sbs'),nbs0)
        else let sbs,nbs0 = cmds2sbs cs' in
             ({ coq_NBs = []; call_cmd = c }::sbs),nbs0
  
  (** val nbranchs2cmds : nbranch list -> LLVMsyntax.cmd list **)
  
  let rec nbranchs2cmds = function
    | [] -> []
    | n::nbs' -> n::(nbranchs2cmds nbs')
  
  (** val cmd2nbranch : LLVMsyntax.cmd -> nbranch option **)
  
  let cmd2nbranch c =
    if isCall_dec c then Some c else None
  
  (** val cmds2nbranchs : LLVMsyntax.cmd list -> nbranch list option **)
  
  let rec cmds2nbranchs = function
    | [] -> Some []
    | c::cs' ->
        let o = cmd2nbranch c in
        let o0 = cmds2nbranchs cs' in
        (match o with
           | Some nb ->
               (match o0 with
                  | Some nbs' -> Some (nb::nbs')
                  | None -> None)
           | None -> None)
  
  type sterm =
    | Coq_sterm_val of LLVMsyntax.value
    | Coq_sterm_bop of LLVMsyntax.bop * LLVMsyntax.sz * sterm * sterm
    | Coq_sterm_fbop of LLVMsyntax.fbop * LLVMsyntax.floating_point * 
       sterm * sterm
    | Coq_sterm_extractvalue of LLVMsyntax.typ * sterm
       * LLVMsyntax.list_const
    | Coq_sterm_insertvalue of LLVMsyntax.typ * sterm * 
       LLVMsyntax.typ * sterm * LLVMsyntax.list_const
    | Coq_sterm_malloc of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_alloca of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_sterm_gep of LLVMsyntax.inbounds * LLVMsyntax.typ * 
       sterm * list_sz_sterm
    | Coq_sterm_trunc of LLVMsyntax.truncop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_ext of LLVMsyntax.extop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_cast of LLVMsyntax.castop * LLVMsyntax.typ * 
       sterm * LLVMsyntax.typ
    | Coq_sterm_icmp of LLVMsyntax.cond * LLVMsyntax.typ * sterm * sterm
    | Coq_sterm_fcmp of LLVMsyntax.fcond * LLVMsyntax.floating_point * 
       sterm * sterm
    | Coq_sterm_phi of LLVMsyntax.typ * list_sterm_l
    | Coq_sterm_select of sterm * LLVMsyntax.typ * sterm * sterm
    | Coq_sterm_lib of smem * LLVMsyntax.id * list_sterm
  and list_sz_sterm =
    | Nil_list_sz_sterm
    | Cons_list_sz_sterm of LLVMsyntax.sz * sterm * list_sz_sterm
  and list_sterm =
    | Nil_list_sterm
    | Cons_list_sterm of sterm * list_sterm
  and list_sterm_l =
    | Nil_list_sterm_l
    | Cons_list_sterm_l of sterm * LLVMsyntax.l * list_sterm_l
  and smem =
    | Coq_smem_init
    | Coq_smem_malloc of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_free of smem * LLVMsyntax.typ * sterm
    | Coq_smem_alloca of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_load of smem * LLVMsyntax.typ * sterm * LLVMsyntax.align
    | Coq_smem_store of smem * LLVMsyntax.typ * sterm * 
       sterm * LLVMsyntax.align
    | Coq_smem_lib of smem * LLVMsyntax.id * list_sterm
  and sframe =
    | Coq_sframe_init
    | Coq_sframe_alloca of smem * sframe * LLVMsyntax.typ * 
       sterm * LLVMsyntax.align
  
  (** val sterm_rect :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm -> 'a1) ->
      (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (smem ->
      LLVMsyntax.id -> list_sterm -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s2)
    | Coq_sterm_fbop (f16, f17, s0, s1) ->
        f1 f16 f17 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f2 t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f3 t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0 s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) l0
    | Coq_sterm_malloc (s0, t, s1, a) ->
        f4 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_alloca (s0, t, s1, a) ->
        f5 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_load (s0, t, s1, a) ->
        f6 s0 t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_gep (i, t, s0, l0) ->
        f7 i t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) l0
    | Coq_sterm_trunc (t, t0, s0, t1) ->
        f8 t t0 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t1
    | Coq_sterm_ext (e, t, s0, t0) ->
        f9 e t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f10 c t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f11 c t s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_fcmp (f16, f17, s0, s1) ->
        f12 f16 f17 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_phi (t, l0) -> f13 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f14 s0
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t s1
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) s2
          (sterm_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s2)
    | Coq_sterm_lib (s0, i, l0) -> f15 s0 i l0
  
  (** val sterm_rec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> LLVMsyntax.typ -> sterm ->
      'a1 -> LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds ->
      LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm -> 'a1) ->
      (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ
      -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop -> LLVMsyntax.typ -> sterm
      -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.cond -> LLVMsyntax.typ
      -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fcond ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> list_sterm_l -> 'a1) -> (sterm -> 'a1 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) -> (smem ->
      LLVMsyntax.id -> list_sterm -> 'a1) -> sterm -> 'a1 **)
  
  let rec sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | Coq_sterm_val v -> f v
    | Coq_sterm_bop (b, s0, s1, s2) ->
        f0 b s0 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s2)
    | Coq_sterm_fbop (f16, f17, s0, s1) ->
        f1 f16 f17 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_extractvalue (t, s0, l0) ->
        f2 t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) l0
    | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
        f3 t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0 s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) l0
    | Coq_sterm_malloc (s0, t, s1, a) ->
        f4 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_alloca (s0, t, s1, a) ->
        f5 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_load (s0, t, s1, a) ->
        f6 s0 t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) a
    | Coq_sterm_gep (i, t, s0, l0) ->
        f7 i t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) l0
    | Coq_sterm_trunc (t, t0, s0, t1) ->
        f8 t t0 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t1
    | Coq_sterm_ext (e, t, s0, t0) ->
        f9 e t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0
    | Coq_sterm_cast (c, t, s0, t0) ->
        f10 c t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t0
    | Coq_sterm_icmp (c, t, s0, s1) ->
        f11 c t s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_fcmp (f16, f17, s0, s1) ->
        f12 f16 f17 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1)
    | Coq_sterm_phi (t, l0) -> f13 t l0
    | Coq_sterm_select (s0, t, s1, s2) ->
        f14 s0
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s0) t s1
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s1) s2
          (sterm_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            s2)
    | Coq_sterm_lib (s0, i, l0) -> f15 s0 i l0
  
  (** val list_sz_sterm_rect :
      'a1 -> (LLVMsyntax.sz -> sterm -> list_sz_sterm -> 'a1 -> 'a1) ->
      list_sz_sterm -> 'a1 **)
  
  let rec list_sz_sterm_rect f f0 = function
    | Nil_list_sz_sterm -> f
    | Cons_list_sz_sterm (s, s0, l1) ->
        f0 s s0 l1 (list_sz_sterm_rect f f0 l1)
  
  (** val list_sz_sterm_rec :
      'a1 -> (LLVMsyntax.sz -> sterm -> list_sz_sterm -> 'a1 -> 'a1) ->
      list_sz_sterm -> 'a1 **)
  
  let rec list_sz_sterm_rec f f0 = function
    | Nil_list_sz_sterm -> f
    | Cons_list_sz_sterm (s, s0, l1) ->
        f0 s s0 l1 (list_sz_sterm_rec f f0 l1)
  
  (** val list_sterm_rect :
      'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1 **)
  
  let rec list_sterm_rect f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, l1) -> f0 s l1 (list_sterm_rect f f0 l1)
  
  (** val list_sterm_rec :
      'a1 -> (sterm -> list_sterm -> 'a1 -> 'a1) -> list_sterm -> 'a1 **)
  
  let rec list_sterm_rec f f0 = function
    | Nil_list_sterm -> f
    | Cons_list_sterm (s, l1) -> f0 s l1 (list_sterm_rec f f0 l1)
  
  (** val list_sterm_l_rect :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rect f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rect f f0 l2)
  
  (** val list_sterm_l_rec :
      'a1 -> (sterm -> LLVMsyntax.l -> list_sterm_l -> 'a1 -> 'a1) ->
      list_sterm_l -> 'a1 **)
  
  let rec list_sterm_l_rec f f0 = function
    | Nil_list_sterm_l -> f
    | Cons_list_sterm_l (s, l1, l2) -> f0 s l1 l2 (list_sterm_l_rec f f0 l2)
  
  (** val smem_rect :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) ->
      (smem -> 'a1 -> LLVMsyntax.id -> list_sterm -> 'a1) -> smem -> 'a1 **)
  
  let rec smem_rect f f0 f1 f2 f3 f4 f5 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_free (s0, t, s1) ->
        f1 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_load (s0, t, s1, a) ->
        f3 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_store (s0, t, s1, s2, a) ->
        f4 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) t s1 s2 a
    | Coq_smem_lib (s0, i, l0) ->
        f5 s0 (smem_rect f f0 f1 f2 f3 f4 f5 s0) i l0
  
  (** val smem_rec :
      'a1 -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align ->
      'a1) -> (smem -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> LLVMsyntax.align -> 'a1) -> (smem -> 'a1
      -> LLVMsyntax.typ -> sterm -> sterm -> LLVMsyntax.align -> 'a1) ->
      (smem -> 'a1 -> LLVMsyntax.id -> list_sterm -> 'a1) -> smem -> 'a1 **)
  
  let rec smem_rec f f0 f1 f2 f3 f4 f5 = function
    | Coq_smem_init -> f
    | Coq_smem_malloc (s0, t, s1, a) ->
        f0 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_free (s0, t, s1) ->
        f1 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) t s1
    | Coq_smem_alloca (s0, t, s1, a) ->
        f2 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_load (s0, t, s1, a) ->
        f3 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) t s1 a
    | Coq_smem_store (s0, t, s1, s2, a) ->
        f4 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) t s1 s2 a
    | Coq_smem_lib (s0, i, l0) ->
        f5 s0 (smem_rec f f0 f1 f2 f3 f4 f5 s0) i l0
  
  (** val sframe_rect :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rect f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rect f f0 s1) t s2 a
  
  (** val sframe_rec :
      'a1 -> (smem -> sframe -> 'a1 -> LLVMsyntax.typ -> sterm ->
      LLVMsyntax.align -> 'a1) -> sframe -> 'a1 **)
  
  let rec sframe_rec f f0 = function
    | Coq_sframe_init -> f
    | Coq_sframe_alloca (s0, s1, t, s2, a) ->
        f0 s0 s1 (sframe_rec f f0 s1) t s2 a
  
  (** val sframe_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) -> sframe ->
      'a6 **)
  
  let sframe_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f36
  
  (** val smem_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) -> smem ->
      'a5 **)
  
  let smem_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f35
  
  (** val list_sterm_l_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) ->
      list_sterm_l -> 'a4 **)
  
  let list_sterm_l_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f34
  
  (** val list_sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) ->
      list_sterm -> 'a3 **)
  
  let list_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f33
  
  (** val list_sz_sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) ->
      list_sz_sterm -> 'a2 **)
  
  let list_sz_sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f32
  
  (** val sterm_rec2 :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) -> sterm ->
      'a1 **)
  
  let sterm_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
    let rec f31 = function
      | Coq_sterm_val v -> f v
      | Coq_sterm_bop (b, s0, s1, s2) -> f0 b s0 s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_fbop (f37, f38, s0, s1) ->
          f1 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_extractvalue (t, s0, l0) -> f2 t s0 (f31 s0) l0
      | Coq_sterm_insertvalue (t, s0, t0, s1, l0) ->
          f3 t s0 (f31 s0) t0 s1 (f31 s1) l0
      | Coq_sterm_malloc (s0, t, s1, a) -> f4 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_alloca (s0, t, s1, a) -> f5 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_load (s0, t, s1, a) -> f6 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_sterm_gep (i, t, s0, l0) -> f7 i t s0 (f31 s0) l0 (f32 l0)
      | Coq_sterm_trunc (t, t0, s0, t1) -> f8 t t0 s0 (f31 s0) t1
      | Coq_sterm_ext (e, t, s0, t0) -> f9 e t s0 (f31 s0) t0
      | Coq_sterm_cast (c, t, s0, t0) -> f10 c t s0 (f31 s0) t0
      | Coq_sterm_icmp (c, t, s0, s1) -> f11 c t s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_fcmp (f37, f38, s0, s1) ->
          f12 f37 f38 s0 (f31 s0) s1 (f31 s1)
      | Coq_sterm_phi (t, l0) -> f13 t l0 (f34 l0)
      | Coq_sterm_select (s0, t, s1, s2) ->
          f14 s0 (f31 s0) t s1 (f31 s1) s2 (f31 s2)
      | Coq_sterm_lib (s0, i, l0) -> f15 s0 (f35 s0) i l0 (f33 l0)
    and f32 = function
      | Nil_list_sz_sterm -> f16
      | Cons_list_sz_sterm (s, s0, l1) -> f17 s s0 (f31 s0) l1 (f32 l1)
    and f33 = function
      | Nil_list_sterm -> f18
      | Cons_list_sterm (s, l1) -> f19 s (f31 s) l1 (f33 l1)
    and f34 = function
      | Nil_list_sterm_l -> f20
      | Cons_list_sterm_l (s, l1, l2) -> f21 s (f31 s) l1 l2 (f34 l2)
    and f35 = function
      | Coq_smem_init -> f22
      | Coq_smem_malloc (s0, t, s1, a) -> f23 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_free (s0, t, s1) -> f24 s0 (f35 s0) t s1 (f31 s1)
      | Coq_smem_alloca (s0, t, s1, a) -> f25 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_load (s0, t, s1, a) -> f26 s0 (f35 s0) t s1 (f31 s1) a
      | Coq_smem_store (s0, t, s1, s2, a) ->
          f27 s0 (f35 s0) t s1 (f31 s1) s2 (f31 s2) a
      | Coq_smem_lib (s0, i, l0) -> f28 s0 (f35 s0) i l0 (f33 l0)
    and f36 = function
      | Coq_sframe_init -> f29
      | Coq_sframe_alloca (s0, s1, t, s2, a) ->
          f30 s0 (f35 s0) s1 (f36 s1) t s2 (f31 s2) a
    in f31
  
  (** val se_mutrec :
      (LLVMsyntax.value -> 'a1) -> (LLVMsyntax.bop -> LLVMsyntax.sz -> sterm
      -> 'a1 -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.fbop ->
      LLVMsyntax.floating_point -> sterm -> 'a1 -> sterm -> 'a1 -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.list_const -> 'a1) ->
      (LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 ->
      LLVMsyntax.list_const -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem -> 'a5 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) -> (smem ->
      'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a1) ->
      (LLVMsyntax.inbounds -> LLVMsyntax.typ -> sterm -> 'a1 -> list_sz_sterm
      -> 'a2 -> 'a1) -> (LLVMsyntax.truncop -> LLVMsyntax.typ -> sterm -> 'a1
      -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
      sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.typ -> 'a1) ->
      (LLVMsyntax.cond -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1 ->
      'a1) -> (LLVMsyntax.fcond -> LLVMsyntax.floating_point -> sterm -> 'a1
      -> sterm -> 'a1 -> 'a1) -> (LLVMsyntax.typ -> list_sterm_l -> 'a4 ->
      'a1) -> (sterm -> 'a1 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> 'a1) -> (smem -> 'a5 -> LLVMsyntax.id -> list_sterm -> 'a3 -> 'a1)
      -> 'a2 -> (LLVMsyntax.sz -> sterm -> 'a1 -> list_sz_sterm -> 'a2 ->
      'a2) -> 'a3 -> (sterm -> 'a1 -> list_sterm -> 'a3 -> 'a3) -> 'a4 ->
      (sterm -> 'a1 -> LLVMsyntax.l -> list_sterm_l -> 'a4 -> 'a4) -> 'a5 ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> 'a5) -> (smem
      -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a5) ->
      (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align ->
      'a5) -> (smem -> 'a5 -> LLVMsyntax.typ -> sterm -> 'a1 -> sterm -> 'a1
      -> LLVMsyntax.align -> 'a5) -> (smem -> 'a5 -> LLVMsyntax.id ->
      list_sterm -> 'a3 -> 'a5) -> 'a6 -> (smem -> 'a5 -> sframe -> 'a6 ->
      LLVMsyntax.typ -> sterm -> 'a1 -> LLVMsyntax.align -> 'a6) ->
      (((((sterm -> 'a1)*(list_sz_sterm -> 'a2))*(list_sterm ->
      'a3))*(list_sterm_l -> 'a4))*(smem -> 'a5))*(sframe -> 'a6) **)
  
  let se_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 =
    (((((sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
          h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32),
      (list_sz_sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)),
      (list_sterm_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)),
      (list_sterm_l_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)),
      (smem_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)),
      (sframe_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
        h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32)
  
  (** val map_list_sterm : (sterm -> 'a1) -> list_sterm -> 'a1 list **)
  
  let rec map_list_sterm f = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> (f h)::(map_list_sterm f tl_)
  
  (** val make_list_sterm : sterm list -> list_sterm **)
  
  let rec make_list_sterm = function
    | [] -> Nil_list_sterm
    | h::tl_ -> Cons_list_sterm (h, (make_list_sterm tl_))
  
  (** val unmake_list_sterm : list_sterm -> sterm list **)
  
  let rec unmake_list_sterm = function
    | Nil_list_sterm -> []
    | Cons_list_sterm (h, tl_) -> h::(unmake_list_sterm tl_)
  
  (** val nth_list_sterm : nat -> list_sterm -> sterm option **)
  
  let rec nth_list_sterm n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_sterm -> None
             | Cons_list_sterm (h, tl_) -> nth_list_sterm m tl_)
  
  (** val app_list_sterm : list_sterm -> list_sterm -> list_sterm **)
  
  let rec app_list_sterm l0 m =
    match l0 with
      | Nil_list_sterm -> m
      | Cons_list_sterm (h, tl_) -> Cons_list_sterm (h,
          (app_list_sterm tl_ m))
  
  (** val map_list_sterm_l :
      (sterm -> LLVMsyntax.l -> 'a1) -> list_sterm_l -> 'a1 list **)
  
  let rec map_list_sterm_l f = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (f h0 h1)::(map_list_sterm_l f tl_)
  
  (** val make_list_sterm_l : (sterm*LLVMsyntax.l) list -> list_sterm_l **)
  
  let rec make_list_sterm_l = function
    | [] -> Nil_list_sterm_l
    | p::tl_ ->
        let h0,h1 = p in Cons_list_sterm_l (h0, h1, (make_list_sterm_l tl_))
  
  (** val unmake_list_sterm_l : list_sterm_l -> (sterm*LLVMsyntax.l) list **)
  
  let rec unmake_list_sterm_l = function
    | Nil_list_sterm_l -> []
    | Cons_list_sterm_l (h0, h1, tl_) -> (h0,h1)::(unmake_list_sterm_l tl_)
  
  (** val nth_list_sterm_l :
      nat -> list_sterm_l -> (sterm*LLVMsyntax.l) option **)
  
  let rec nth_list_sterm_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> Some (h0,h1))
      | S m ->
          (match l0 with
             | Nil_list_sterm_l -> None
             | Cons_list_sterm_l (h0, h1, tl_) -> nth_list_sterm_l m tl_)
  
  (** val app_list_sterm_l : list_sterm_l -> list_sterm_l -> list_sterm_l **)
  
  let rec app_list_sterm_l l0 m =
    match l0 with
      | Nil_list_sterm_l -> m
      | Cons_list_sterm_l (h0, h1, tl_) -> Cons_list_sterm_l (h0, h1,
          (app_list_sterm_l tl_ m))
  
  (** val map_list_sz_sterm :
      (LLVMsyntax.sz -> sterm -> 'a1) -> list_sz_sterm -> 'a1 list **)
  
  let rec map_list_sz_sterm f = function
    | Nil_list_sz_sterm -> []
    | Cons_list_sz_sterm (s, h, tl_) -> (f s h)::(map_list_sz_sterm f tl_)
  
  (** val make_list_sz_sterm :
      (LLVMsyntax.sz*sterm) list -> list_sz_sterm **)
  
  let rec make_list_sz_sterm = function
    | [] -> Nil_list_sz_sterm
    | p::tl_ ->
        let s,h = p in Cons_list_sz_sterm (s, h, (make_list_sz_sterm tl_))
  
  (** val unmake_list_sz_sterm :
      list_sz_sterm -> (LLVMsyntax.sz*sterm) list **)
  
  let rec unmake_list_sz_sterm = function
    | Nil_list_sz_sterm -> []
    | Cons_list_sz_sterm (s, h, tl_) -> (s,h)::(unmake_list_sz_sterm tl_)
  
  (** val nth_list_sz_sterm :
      nat -> list_sz_sterm -> (LLVMsyntax.sz*sterm) option **)
  
  let rec nth_list_sz_sterm n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sz_sterm -> None
             | Cons_list_sz_sterm (s, h, tl_) -> Some (s,h))
      | S m ->
          (match l0 with
             | Nil_list_sz_sterm -> None
             | Cons_list_sz_sterm (s, s0, tl_) -> nth_list_sz_sterm m tl_)
  
  (** val app_list_sz_sterm :
      list_sz_sterm -> list_sz_sterm -> list_sz_sterm **)
  
  let rec app_list_sz_sterm l0 m =
    match l0 with
      | Nil_list_sz_sterm -> m
      | Cons_list_sz_sterm (s, h, tl_) -> Cons_list_sz_sterm (s, h,
          (app_list_sz_sterm tl_ m))
  
  type sterminator =
    | Coq_stmn_return of LLVMsyntax.id * LLVMsyntax.typ * sterm
    | Coq_stmn_return_void of LLVMsyntax.id
    | Coq_stmn_br of LLVMsyntax.id * sterm * LLVMsyntax.l * LLVMsyntax.l
    | Coq_stmn_br_uncond of LLVMsyntax.id * LLVMsyntax.l
    | Coq_stmn_unreachable of LLVMsyntax.id
  
  (** val sterminator_rect :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rect f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  (** val sterminator_rec :
      (LLVMsyntax.id -> LLVMsyntax.typ -> sterm -> 'a1) -> (LLVMsyntax.id ->
      'a1) -> (LLVMsyntax.id -> sterm -> LLVMsyntax.l -> LLVMsyntax.l -> 'a1)
      -> (LLVMsyntax.id -> LLVMsyntax.l -> 'a1) -> (LLVMsyntax.id -> 'a1) ->
      sterminator -> 'a1 **)
  
  let sterminator_rec f f0 f1 f2 f3 = function
    | Coq_stmn_return (x, x0, x1) -> f x x0 x1
    | Coq_stmn_return_void x -> f0 x
    | Coq_stmn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_stmn_br_uncond (x, x0) -> f2 x x0
    | Coq_stmn_unreachable x -> f3 x
  
  type scall =
    | Coq_stmn_call of LLVMsyntax.id * LLVMsyntax.noret * 
       LLVMsyntax.clattrs * LLVMsyntax.typ * LLVMsyntax.value
       * ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list
  
  (** val scall_rect :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list -> 'a1) -> scall ->
      'a1 **)
  
  let scall_rect f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  (** val scall_rec :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list -> 'a1) -> scall ->
      'a1 **)
  
  let scall_rec f = function
    | Coq_stmn_call (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
  
  type smap = (AtomImpl.atom*sterm) list
  
  type sstate = { coq_STerms : smap; coq_SMem : smem; coq_SFrame : 
                  sframe; coq_SEffects : sterm list }
  
  (** val sstate_rect :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rect f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val sstate_rec :
      (smap -> smem -> sframe -> sterm list -> 'a1) -> sstate -> 'a1 **)
  
  let sstate_rec f s =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = s
    in
    f x x0 x1 x2
  
  (** val coq_STerms : sstate -> smap **)
  
  let coq_STerms x = x.coq_STerms
  
  (** val coq_SMem : sstate -> smem **)
  
  let coq_SMem x = x.coq_SMem
  
  (** val coq_SFrame : sstate -> sframe **)
  
  let coq_SFrame x = x.coq_SFrame
  
  (** val coq_SEffects : sstate -> sterm list **)
  
  let coq_SEffects x = x.coq_SEffects
  
  (** val sstate_init : sstate **)
  
  let sstate_init =
    { coq_STerms = []; coq_SMem = Coq_smem_init; coq_SFrame =
      Coq_sframe_init; coq_SEffects = [] }
  
  (** val lookupSmap : smap -> LLVMsyntax.id -> sterm **)
  
  let rec lookupSmap sm i0 =
    match sm with
      | [] -> Coq_sterm_val (LLVMsyntax.Coq_value_id i0)
      | p::sm' ->
          let id0,s0 = p in
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i0 id0
          then s0
          else lookupSmap sm' i0
  
  (** val value2Sterm : smap -> LLVMsyntax.value -> sterm **)
  
  let value2Sterm sm v = match v with
    | LLVMsyntax.Coq_value_id i0 -> lookupSmap sm i0
    | LLVMsyntax.Coq_value_const c -> Coq_sterm_val v
  
  (** val list_param__list_typ_subst_sterm :
      LLVMsyntax.params -> smap ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list **)
  
  let rec list_param__list_typ_subst_sterm list_param1 sm =
    match list_param1 with
      | [] -> []
      | p::list_param1' ->
          let p0,v = p in
          (p0,(value2Sterm sm v))::(list_param__list_typ_subst_sterm
                                     list_param1' sm)
  
  type list_value =
    | Nil_list_value
    | Cons_list_value of LLVMsyntax.value * list_value
  
  (** val list_value_rect :
      'a1 -> (LLVMsyntax.value -> list_value -> 'a1 -> 'a1) -> list_value ->
      'a1 **)
  
  let rec list_value_rect f f0 = function
    | Nil_list_value -> f
    | Cons_list_value (v, l1) -> f0 v l1 (list_value_rect f f0 l1)
  
  (** val list_value_rec :
      'a1 -> (LLVMsyntax.value -> list_value -> 'a1 -> 'a1) -> list_value ->
      'a1 **)
  
  let rec list_value_rec f f0 = function
    | Nil_list_value -> f
    | Cons_list_value (v, l1) -> f0 v l1 (list_value_rec f f0 l1)
  
  (** val map_list_value :
      (LLVMsyntax.value -> 'a1) -> list_value -> 'a1 list **)
  
  let rec map_list_value f = function
    | Nil_list_value -> []
    | Cons_list_value (h, tl_) -> (f h)::(map_list_value f tl_)
  
  (** val make_list_value : LLVMsyntax.value list -> list_value **)
  
  let rec make_list_value = function
    | [] -> Nil_list_value
    | h::tl_ -> Cons_list_value (h, (make_list_value tl_))
  
  (** val unmake_list_value : list_value -> LLVMsyntax.value list **)
  
  let rec unmake_list_value = function
    | Nil_list_value -> []
    | Cons_list_value (h, tl_) -> h::(unmake_list_value tl_)
  
  (** val nth_list_value : nat -> list_value -> LLVMsyntax.value option **)
  
  let rec nth_list_value n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_value -> None
             | Cons_list_value (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_value -> None
             | Cons_list_value (h, tl_) -> nth_list_value m tl_)
  
  (** val app_list_value : list_value -> list_value -> list_value **)
  
  let rec app_list_value l0 m =
    match l0 with
      | Nil_list_value -> m
      | Cons_list_value (h, tl_) -> Cons_list_value (h,
          (app_list_value tl_ m))
  
  (** val se_lib :
      LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.noret ->
      LLVMsyntax.clattrs -> LLVMsyntax.typ -> LLVMsyntax.value ->
      LLVMsyntax.params -> sstate -> sstate **)
  
  let se_lib i0 id0 noret0 tailc0 ft fv lp st =
    match fv with
      | LLVMsyntax.Coq_value_id i1 -> assert false (* absurd case *)
      | LLVMsyntax.Coq_value_const c ->
          (match c with
             | LLVMsyntax.Coq_const_gid (t, i1) -> { coq_STerms =
                 (updateAddAL st.coq_STerms id0 (Coq_sterm_lib (st.coq_SMem,
                   i1,
                   (make_list_sterm
                     (map_list_value (value2Sterm st.coq_STerms)
                       (make_list_value (snd (split lp)))))))); coq_SMem =
                 (Coq_smem_lib (st.coq_SMem, i1,
                 (make_list_sterm
                   (map_list_value (value2Sterm st.coq_STerms)
                     (make_list_value (snd (split lp))))))); coq_SFrame =
                 st.coq_SFrame; coq_SEffects = st.coq_SEffects }
             | _ -> assert false (* absurd case *))
  
  (** val se_cmd : sstate -> nbranch -> sstate **)
  
  let se_cmd st c = match c with
    | LLVMsyntax.Coq_insn_bop (id0, op0, sz0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_bop (op0, sz0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_fbop (id0, op0, fp0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_fbop (op0, fp0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_extractvalue (id0, t1, v1, cs3) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_extractvalue (t1,
          (value2Sterm st.coq_STerms v1), cs3))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_insertvalue (id0, t1, v1, t2, v2, cs3) ->
        { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_insertvalue (t1,
          (value2Sterm st.coq_STerms v1), t2, (value2Sterm st.coq_STerms v2),
          cs3))); coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_malloc (id0, t1, v1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_malloc (st.coq_SMem, t1,
          (value2Sterm st.coq_STerms v1), al1))); coq_SMem = (Coq_smem_malloc
        (st.coq_SMem, t1, (value2Sterm st.coq_STerms v1), al1)); coq_SFrame =
        st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_free (id0, t0, v0) -> { coq_STerms = st.coq_STerms;
        coq_SMem = (Coq_smem_free (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v0))); coq_SFrame = st.coq_SFrame;
        coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_alloca (id0, t1, v1, al1) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_alloca (st.coq_SMem, t1,
          (value2Sterm st.coq_STerms v1), al1))); coq_SMem = (Coq_smem_alloca
        (st.coq_SMem, t1, (value2Sterm st.coq_STerms v1), al1)); coq_SFrame =
        (Coq_sframe_alloca (st.coq_SMem, st.coq_SFrame, t1,
        (value2Sterm st.coq_STerms v1), al1)); coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_load (id0, t2, v2, align0) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_load (st.coq_SMem, t2,
          (value2Sterm st.coq_STerms v2), align0))); coq_SMem =
        (Coq_smem_load (st.coq_SMem, t2, (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_store (id0, t0, v1, v2, align0) -> { coq_STerms =
        st.coq_STerms; coq_SMem = (Coq_smem_store (st.coq_SMem, t0,
        (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2),
        align0)); coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_gep (id0, inbounds0, t1, v1, lv2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_gep (inbounds0, t1,
          (value2Sterm st.coq_STerms v1),
          (make_list_sz_sterm
            (LLVMsyntax.map_list_sz_value (fun sz' v' ->
              sz',(value2Sterm st.coq_STerms v')) lv2))))); coq_SMem =
        st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_trunc (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_trunc (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_ext (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_ext (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_cast (id0, op0, t1, v1, t2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_cast (op0, t1,
          (value2Sterm st.coq_STerms v1), t2))); coq_SMem = st.coq_SMem;
        coq_SFrame = st.coq_SFrame; coq_SEffects = st.coq_SEffects }
    | LLVMsyntax.Coq_insn_icmp (id0, c0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_icmp (c0, t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_fcmp (id0, c0, fp0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_fcmp (c0, fp0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_select (id0, v0, t0, v1, v2) -> { coq_STerms =
        (updateAddAL st.coq_STerms id0 (Coq_sterm_select
          ((value2Sterm st.coq_STerms v0), t0,
          (value2Sterm st.coq_STerms v1), (value2Sterm st.coq_STerms v2))));
        coq_SMem = st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
        st.coq_SEffects }
    | LLVMsyntax.Coq_insn_call (id0, noret0, tailc0, ft, fv, lp) ->
        se_lib c id0 noret0 tailc0 ft fv lp st
  
  (** val _se_phinodes :
      sstate -> sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec _se_phinodes st st0 = function
    | [] -> st
    | p::ps' ->
        let LLVMsyntax.Coq_insn_phi (id0, t0, idls0) = p in
        _se_phinodes { coq_STerms =
          (updateAL st.coq_STerms id0 (Coq_sterm_phi (t0,
            (make_list_sterm_l
              (LLVMsyntax.map_list_value_l (fun v5 l5 ->
                (value2Sterm st.coq_STerms v5),l5) idls0))))); coq_SMem =
          st.coq_SMem; coq_SFrame = st.coq_SFrame; coq_SEffects =
          st.coq_SEffects } st0 ps'
  
  (** val se_phinodes : sstate -> LLVMsyntax.phinode list -> sstate **)
  
  let rec se_phinodes st ps =
    _se_phinodes st st ps
  
  (** val se_cmds : sstate -> nbranch list -> sstate **)
  
  let rec se_cmds st = function
    | [] -> st
    | c::cs' -> se_cmds (se_cmd st c) cs'
  
  (** val se_terminator : sstate -> LLVMsyntax.terminator -> sterminator **)
  
  let se_terminator st = function
    | LLVMsyntax.Coq_insn_return (id0, t0, v0) -> Coq_stmn_return (id0, t0,
        (value2Sterm st.coq_STerms v0))
    | LLVMsyntax.Coq_insn_return_void id0 -> Coq_stmn_return_void id0
    | LLVMsyntax.Coq_insn_br (id0, v0, l1, l2) -> Coq_stmn_br (id0,
        (value2Sterm st.coq_STerms v0), l1, l2)
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> Coq_stmn_br_uncond (id0, l0)
    | LLVMsyntax.Coq_insn_unreachable id0 -> Coq_stmn_unreachable id0
  
  (** val se_call : sstate -> LLVMsyntax.cmd -> scall **)
  
  let se_call st = function
    | LLVMsyntax.Coq_insn_call (i1, n, c, t, v, p) -> Coq_stmn_call (i1, n,
        c, t, v, (list_param__list_typ_subst_sterm p st.coq_STerms))
    | _ -> assert false (* absurd case *)
  
  (** val subst_tt : LLVMsyntax.id -> sterm -> sterm -> sterm **)
  
  let rec subst_tt id0 s0 s = match s with
    | Coq_sterm_val v ->
        (match v with
           | LLVMsyntax.Coq_value_id id1 ->
               if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
               then s0
               else s
           | LLVMsyntax.Coq_value_const c -> Coq_sterm_val
               (LLVMsyntax.Coq_value_const c))
    | Coq_sterm_bop (op, sz0, s1, s2) -> Coq_sterm_bop (op, sz0,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_fbop (op, fp, s1, s2) -> Coq_sterm_fbop (op, fp,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_extractvalue (t1, s1, cs) -> Coq_sterm_extractvalue (t1,
        (subst_tt id0 s0 s1), cs)
    | Coq_sterm_insertvalue (t1, s1, t2, s2, cs) -> Coq_sterm_insertvalue
        (t1, (subst_tt id0 s0 s1), t2, (subst_tt id0 s0 s2), cs)
    | Coq_sterm_malloc (m1, t1, s1, align0) -> Coq_sterm_malloc
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_alloca (m1, t1, s1, align0) -> Coq_sterm_alloca
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_load (m1, t1, s1, align0) -> Coq_sterm_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_sterm_gep (inbounds0, t1, s1, ls2) -> Coq_sterm_gep (inbounds0, t1,
        (subst_tt id0 s0 s1), (subst_tlzt id0 s0 ls2))
    | Coq_sterm_trunc (truncop0, t1, s1, t2) -> Coq_sterm_trunc (truncop0,
        t1, (subst_tt id0 s0 s1), t2)
    | Coq_sterm_ext (extop0, t1, s1, t2) -> Coq_sterm_ext (extop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_cast (castop0, t1, s1, t2) -> Coq_sterm_cast (castop0, t1,
        (subst_tt id0 s0 s1), t2)
    | Coq_sterm_icmp (cond0, t1, s1, s2) -> Coq_sterm_icmp (cond0, t1,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_fcmp (cond0, fp1, s1, s2) -> Coq_sterm_fcmp (cond0, fp1,
        (subst_tt id0 s0 s1), (subst_tt id0 s0 s2))
    | Coq_sterm_phi (t1, lsl1) -> Coq_sterm_phi (t1,
        (subst_tltl id0 s0 lsl1))
    | Coq_sterm_select (s1, t1, s2, s3) -> Coq_sterm_select
        ((subst_tt id0 s0 s1), t1, (subst_tt id0 s0 s2),
        (subst_tt id0 s0 s3))
    | Coq_sterm_lib (m, id1, ls) -> Coq_sterm_lib (
        (subst_tm id0 s0 m), id1, (subst_tlt id0 s0 ls))
  
  (** val subst_tlzt :
      LLVMsyntax.id -> sterm -> list_sz_sterm -> list_sz_sterm **)
  
  and subst_tlzt id0 s0 = function
    | Nil_list_sz_sterm -> Nil_list_sz_sterm
    | Cons_list_sz_sterm (sz0, s, ls') -> Cons_list_sz_sterm (sz0,
        (subst_tt id0 s0 s), (subst_tlzt id0 s0 ls'))
  
  (** val subst_tlt : LLVMsyntax.id -> sterm -> list_sterm -> list_sterm **)
  
  and subst_tlt id0 s0 = function
    | Nil_list_sterm -> Nil_list_sterm
    | Cons_list_sterm (s, ls') -> Cons_list_sterm (
        (subst_tt id0 s0 s), (subst_tlt id0 s0 ls'))
  
  (** val subst_tltl :
      LLVMsyntax.id -> sterm -> list_sterm_l -> list_sterm_l **)
  
  and subst_tltl id0 s0 = function
    | Nil_list_sterm_l -> Nil_list_sterm_l
    | Cons_list_sterm_l (s, l0, ls') -> Cons_list_sterm_l
        ((subst_tt id0 s0 s), l0, (subst_tltl id0 s0 ls'))
  
  (** val subst_tm : LLVMsyntax.id -> sterm -> smem -> smem **)
  
  and subst_tm id0 s0 = function
    | Coq_smem_init -> Coq_smem_init
    | Coq_smem_malloc (m1, t1, sz0, align0) -> Coq_smem_malloc
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_free (m1, t1, s1) -> Coq_smem_free (
        (subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1))
    | Coq_smem_alloca (m1, t1, sz0, align0) -> Coq_smem_alloca
        ((subst_tm id0 s0 m1), t1, sz0, align0)
    | Coq_smem_load (m1, t1, s1, align0) -> Coq_smem_load
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1), align0)
    | Coq_smem_store (m1, t1, s1, s2, align0) -> Coq_smem_store
        ((subst_tm id0 s0 m1), t1, (subst_tt id0 s0 s1),
        (subst_tt id0 s0 s2), align0)
    | Coq_smem_lib (m0, id1, ls) -> Coq_smem_lib ((subst_tm id0 s0 m0), id1,
        (subst_tlt id0 s0 ls))
  
  (** val subst_mt : smap -> sterm -> sterm **)
  
  let rec subst_mt sm s =
    match sm with
      | [] -> s
      | p::sm' -> let id0,s0 = p in subst_mt sm' (subst_tt id0 s0 s)
  
  (** val subst_mm : smap -> smem -> smem **)
  
  let rec subst_mm sm m =
    match sm with
      | [] -> m
      | p::sm' -> let id0,s0 = p in subst_mm sm' (subst_tm id0 s0 m)
  
  type sterm_dec_prop = sterm -> bool
  
  type list_sz_sterm_dec_prop = list_sz_sterm -> bool
  
  type list_sterm_dec_prop = list_sterm -> bool
  
  type list_sterm_l_dec_prop = list_sterm_l -> bool
  
  type smem_dec_prop = smem -> bool
  
  type sframe_dec_prop = sframe -> bool
  
  (** val se_dec :
      (((((sterm -> sterm_dec_prop)*(list_sz_sterm ->
      list_sz_sterm_dec_prop))*(list_sterm ->
      list_sterm_dec_prop))*(list_sterm_l -> list_sterm_l_dec_prop))*(smem ->
      smem_dec_prop))*(sframe -> sframe_dec_prop) **)
  
  let se_dec =
    se_mutrec (fun v st2 ->
      match st2 with
        | Coq_sterm_val v0 -> LLVMinfra.value_dec v v0
        | _ -> false) (fun b s s0 h s1 h0 st2 ->
      match st2 with
        | Coq_sterm_bop (b0, s2, st2_1, st2_2) ->
            let s3 = LLVMinfra.bop_dec b b0 in
            if s3
            then let s4 = LLVMsyntax.Size.dec s s2 in
                 if s4
                 then let s5 = h st2_1 in if s5 then h0 st2_2 else false
                 else false
            else false
        | _ -> false) (fun f f0 s h s0 h0 st2 ->
      match st2 with
        | Coq_sterm_fbop (f1, f2, st2_1, st2_2) ->
            let s1 = LLVMinfra.fbop_dec f f1 in
            if s1
            then let s2 = LLVMinfra.floating_point_dec f0 f2 in
                 if s2
                 then let s3 = h st2_1 in if s3 then h0 st2_2 else false
                 else false
            else false
        | _ -> false) (fun t s h l0 st2 ->
      match st2 with
        | Coq_sterm_extractvalue (t0, st3, l1) ->
            let s0 = LLVMinfra.typ_dec t t0 in
            if s0
            then let s1 = h st3 in
                 if s1 then LLVMinfra.list_const_dec l0 l1 else false
            else false
        | _ -> false) (fun t s h t0 s0 h0 l0 st2 ->
      match st2 with
        | Coq_sterm_insertvalue (t1, st2_1, t2, st2_2, l1) ->
            let s1 = LLVMinfra.typ_dec t t1 in
            if s1
            then let s2 = h st2_1 in
                 if s2
                 then let s3 = LLVMinfra.typ_dec t0 t2 in
                      if s3
                      then let s4 = h0 st2_2 in
                           if s4
                           then LLVMinfra.list_const_dec l0 l1
                           else false
                      else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 a st2 ->
      match st2 with
        | Coq_sterm_malloc (s1, t0, st3, a0) ->
            let s2 = h s1 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = h0 st3 in
                      if s4 then LLVMsyntax.Align.dec a a0 else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 a st2 ->
      match st2 with
        | Coq_sterm_alloca (s1, t0, st3, a0) ->
            let s2 = h s1 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = h0 st3 in
                      if s4 then LLVMsyntax.Align.dec a a0 else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 a st2 ->
      match st2 with
        | Coq_sterm_load (s1, t0, st3, a0) ->
            let s2 = h s1 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = LLVMsyntax.Align.dec a a0 in
                      if s4 then h0 st3 else false
                 else false
            else false
        | _ -> false) (fun i0 t s h l0 h0 st2 ->
      match st2 with
        | Coq_sterm_gep (i1, t0, st3, l1) ->
            let s0 = bool_dec i0 i1 in
            if s0
            then let s1 = LLVMinfra.typ_dec t t0 in
                 if s1
                 then let s2 = h st3 in if s2 then h0 l1 else false
                 else false
            else false
        | _ -> false) (fun t t0 s h t1 st2 ->
      match st2 with
        | Coq_sterm_trunc (t2, t3, st3, t4) ->
            let s0 = LLVMinfra.truncop_dec t t2 in
            if s0
            then let s1 = LLVMinfra.typ_dec t0 t3 in
                 if s1
                 then let s2 = h st3 in
                      if s2 then LLVMinfra.typ_dec t1 t4 else false
                 else false
            else false
        | _ -> false) (fun e t s h t0 st2 ->
      match st2 with
        | Coq_sterm_ext (e0, t1, st3, t2) ->
            let s0 = LLVMinfra.extop_dec e e0 in
            if s0
            then let s1 = LLVMinfra.typ_dec t t1 in
                 if s1
                 then let s2 = h st3 in
                      if s2 then LLVMinfra.typ_dec t0 t2 else false
                 else false
            else false
        | _ -> false) (fun c t s h t0 st2 ->
      match st2 with
        | Coq_sterm_cast (c0, t1, st3, t2) ->
            let s0 = LLVMinfra.castop_dec c c0 in
            if s0
            then let s1 = LLVMinfra.typ_dec t t1 in
                 if s1
                 then let s2 = h st3 in
                      if s2 then LLVMinfra.typ_dec t0 t2 else false
                 else false
            else false
        | _ -> false) (fun c t s h s0 h0 st2 ->
      match st2 with
        | Coq_sterm_icmp (c0, t0, st2_1, st2_2) ->
            let s1 = LLVMinfra.cond_dec c c0 in
            if s1
            then let s2 = LLVMinfra.typ_dec t t0 in
                 if s2
                 then let s3 = h st2_1 in if s3 then h0 st2_2 else false
                 else false
            else false
        | _ -> false) (fun f f0 s h s0 h0 st2 ->
      match st2 with
        | Coq_sterm_fcmp (f1, f2, st2_1, st2_2) ->
            let s1 = LLVMinfra.fcond_dec f f1 in
            if s1
            then let s2 = LLVMinfra.floating_point_dec f0 f2 in
                 if s2
                 then let s3 = h st2_1 in if s3 then h0 st2_2 else false
                 else false
            else false
        | _ -> false) (fun t l0 h st2 ->
      match st2 with
        | Coq_sterm_phi (t0, l1) ->
            let s = LLVMinfra.typ_dec t t0 in if s then h l1 else false
        | _ -> false) (fun s h t s0 h0 s1 h1 st2 ->
      match st2 with
        | Coq_sterm_select (st2_1, t0, st2_2, st2_3) ->
            let s2 = LLVMinfra.typ_dec t t0 in
            if s2
            then let s3 = h st2_1 in
                 if s3
                 then let s4 = h0 st2_2 in if s4 then h1 st2_3 else false
                 else false
            else false
        | _ -> false) (fun s h i0 l0 h0 st2 ->
      match st2 with
        | Coq_sterm_lib (s0, i1, l1) ->
            let s1 = LLVMinfra.id_dec i0 i1 in
            if s1
            then let s2 = h s0 in if s2 then h0 l1 else false
            else false
        | _ -> false) (fun stls2 ->
      match stls2 with
        | Nil_list_sz_sterm -> true
        | Cons_list_sz_sterm (s, s0, stls3) -> false)
      (fun s s0 h l0 h0 stls2 ->
      match stls2 with
        | Nil_list_sz_sterm -> false
        | Cons_list_sz_sterm (s1, s2, stls3) ->
            let s3 = LLVMsyntax.Size.dec s s1 in
            if s3
            then let s4 = h s2 in if s4 then h0 stls3 else false
            else false) (fun sts2 ->
      match sts2 with
        | Nil_list_sterm -> true
        | Cons_list_sterm (s, sts3) -> false) (fun s h l0 h0 sts2 ->
      match sts2 with
        | Nil_list_sterm -> false
        | Cons_list_sterm (s0, sts3) ->
            let s1 = h s0 in if s1 then h0 sts3 else false) (fun stls2 ->
      match stls2 with
        | Nil_list_sterm_l -> true
        | Cons_list_sterm_l (s, l0, stls3) -> false)
      (fun s h l0 l1 h0 stls2 ->
      match stls2 with
        | Nil_list_sterm_l -> false
        | Cons_list_sterm_l (s0, l2, stls3) ->
            let s1 = h s0 in
            if s1
            then let s2 = LLVMinfra.l_dec l0 l2 in
                 if s2 then h0 stls3 else false
            else false) (fun sm2 ->
      match sm2 with
        | Coq_smem_init -> true
        | _ -> false) (fun s h t s0 h0 a sm2 ->
      match sm2 with
        | Coq_smem_malloc (sm3, t0, s1, a0) ->
            let s2 = h sm3 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = h0 s1 in
                      if s4 then LLVMsyntax.Align.dec a a0 else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 sm2 ->
      match sm2 with
        | Coq_smem_free (sm3, t0, s1) ->
            let s2 = h sm3 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3 then h0 s1 else false
            else false
        | _ -> false) (fun s h t s0 h0 a sm2 ->
      match sm2 with
        | Coq_smem_alloca (sm3, t0, s1, a0) ->
            let s2 = h sm3 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = h0 s1 in
                      if s4 then LLVMsyntax.Align.dec a a0 else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 a sm2 ->
      match sm2 with
        | Coq_smem_load (sm3, t0, s1, a0) ->
            let s2 = h sm3 in
            if s2
            then let s3 = LLVMinfra.typ_dec t t0 in
                 if s3
                 then let s4 = LLVMsyntax.Align.dec a a0 in
                      if s4 then h0 s1 else false
                 else false
            else false
        | _ -> false) (fun s h t s0 h0 s1 h1 a sm2 ->
      match sm2 with
        | Coq_smem_store (sm3, t0, s2, s3, a0) ->
            let s4 = h sm3 in
            if s4
            then let s5 = LLVMinfra.typ_dec t t0 in
                 if s5
                 then let s6 = LLVMsyntax.Align.dec a a0 in
                      if s6
                      then let s7 = h0 s2 in if s7 then h1 s3 else false
                      else false
                 else false
            else false
        | _ -> false) (fun s h i0 l0 h0 sm2 ->
      match sm2 with
        | Coq_smem_lib (sm3, i1, l1) ->
            let s0 = LLVMinfra.id_dec i0 i1 in
            if s0
            then let s1 = h sm3 in if s1 then h0 l1 else false
            else false
        | _ -> false) (fun sf2 ->
      match sf2 with
        | Coq_sframe_init -> true
        | Coq_sframe_alloca (s, sf3, t, s0, a) -> false)
      (fun s h s0 h0 t s1 h1 a sf2 ->
      match sf2 with
        | Coq_sframe_init -> false
        | Coq_sframe_alloca (s2, sf3, t0, s3, a0) ->
            let s4 = h s2 in
            if s4
            then let s5 = h0 sf3 in
                 if s5
                 then let s6 = LLVMinfra.typ_dec t t0 in
                      if s6
                      then let s7 = h1 s3 in
                           if s7 then LLVMsyntax.Align.dec a a0 else false
                      else false
                 else false
            else false)
  
  (** val sterm_dec : sterm -> sterm -> bool **)
  
  let sterm_dec =
    let p,x = se_dec in
    let p0,x0 = p in let p1,x1 = p0 in let p2,x2 = p1 in let h,l0 = p2 in h
  
  (** val list_sz_sterm_dec : list_sz_sterm -> list_sz_sterm -> bool **)
  
  let list_sz_sterm_dec =
    let p,x = se_dec in
    let p0,x0 = p in let p1,x1 = p0 in let p2,x2 = p1 in let s,h = p2 in h
  
  (** val list_sterm_dec : list_sterm -> list_sterm -> bool **)
  
  let list_sterm_dec =
    let p,x = se_dec in let p0,x0 = p in let p1,x1 = p0 in let p2,h = p1 in h
  
  (** val list_sterm_l_dec : list_sterm_l -> list_sterm_l -> bool **)
  
  let list_sterm_l_dec =
    let p,x = se_dec in let p0,x0 = p in let p1,h = p0 in h
  
  (** val smem_dec : smem -> smem -> bool **)
  
  let smem_dec =
    let p,x = se_dec in let p0,h = p in h
  
  (** val sframe_dec : sframe -> sframe -> bool **)
  
  let sframe_dec =
    let p,h = se_dec in h
  
  (** val sterminator_dec : sterminator -> sterminator -> bool **)
  
  let sterminator_dec st1 st2 =
    match st1 with
      | Coq_stmn_return (x, x0, x1) ->
          (match st2 with
             | Coq_stmn_return (i1, t0, s0) ->
                 if AtomImpl.eq_atom_dec x i1
                 then if LLVMinfra.typ_dec x0 t0
                      then sterm_dec x1 s0
                      else false
                 else false
             | _ -> false)
      | Coq_stmn_return_void x ->
          (match st2 with
             | Coq_stmn_return_void i1 -> AtomImpl.eq_atom_dec x i1
             | _ -> false)
      | Coq_stmn_br (x, x0, x1, x2) ->
          (match st2 with
             | Coq_stmn_br (i1, s0, l2, l3) ->
                 if AtomImpl.eq_atom_dec x i1
                 then if sterm_dec x0 s0
                      then if AtomImpl.eq_atom_dec x1 l2
                           then AtomImpl.eq_atom_dec x2 l3
                           else false
                      else false
                 else false
             | _ -> false)
      | Coq_stmn_br_uncond (x, x0) ->
          (match st2 with
             | Coq_stmn_br_uncond (i1, l1) ->
                 if AtomImpl.eq_atom_dec x i1
                 then AtomImpl.eq_atom_dec x0 l1
                 else false
             | _ -> false)
      | Coq_stmn_unreachable x ->
          (match st2 with
             | Coq_stmn_unreachable i1 -> AtomImpl.eq_atom_dec x i1
             | _ -> false)
  
  (** val list_typ_attributes_sterm_dec :
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*sterm) list -> bool **)
  
  let rec list_typ_attributes_sterm_dec l0 l1 =
    match l0 with
      | [] -> (match l1 with
                 | [] -> true
                 | p::l2 -> false)
      | y::l2 ->
          (match l1 with
             | [] -> false
             | p::l3 ->
                 if let p0,x = y in
                    let t,a = p0 in
                    let p1,x0 = p in
                    let t0,a0 = p1 in
                    let s1 = LLVMinfra.typ_dec t t0 in
                    if s1
                    then let s2 = LLVMinfra.attributes_dec a a0 in
                         if s2 then sterm_dec x x0 else false
                    else false
                 then list_typ_attributes_sterm_dec l2 l3
                 else false)
  
  (** val scall_dec : scall -> scall -> bool **)
  
  let scall_dec sc1 sc2 =
    let Coq_stmn_call (x, x0, x1, x2, x3, x4) = sc1 in
    let Coq_stmn_call (i1, n0, c0, t0, v0, l1) = sc2 in
    if AtomImpl.eq_atom_dec x i1
    then if bool_dec x0 n0
         then if let LLVMsyntax.Coq_clattrs_intro (t1, c, a, a0) = x1 in
                 let LLVMsyntax.Coq_clattrs_intro (t2, c1, a1, a2) = c0 in
                 let s = bool_dec t1 t2 in
                 if s
                 then let s0 = LLVMinfra.callconv_dec c c1 in
                      if s0
                      then let s1 = LLVMinfra.attributes_dec a a1 in
                           if s1
                           then LLVMinfra.attributes_dec a0 a2
                           else false
                      else false
                 else false
              then if LLVMinfra.typ_dec x2 t0
                   then if LLVMinfra.value_dec x3 v0
                        then list_typ_attributes_sterm_dec x4 l1
                        else false
                   else false
              else false
         else false
    else false
  
  (** val smap_dec : smap -> smap -> bool **)
  
  let rec smap_dec l0 sm0 =
    match l0 with
      | [] -> (match sm0 with
                 | [] -> true
                 | p::l1 -> false)
      | y::l1 ->
          (match sm0 with
             | [] -> false
             | p::l2 ->
                 if let a,s = y in
                    let a0,s0 = p in
                    let s1 = LLVMinfra.id_dec a a0 in
                    if s1 then sterm_dec s s0 else false
                 then smap_dec l1 l2
                 else false)
  
  (** val sterms_dec : sterm list -> sterm list -> bool **)
  
  let rec sterms_dec l0 ts0 =
    match l0 with
      | [] -> (match ts0 with
                 | [] -> true
                 | s::l1 -> false)
      | y::l1 ->
          (match ts0 with
             | [] -> false
             | s::l2 -> if sterm_dec y s then sterms_dec l1 l2 else false)
  
  (** val sstate_dec : sstate -> sstate -> bool **)
  
  let sstate_dec sts1 sts2 =
    let { coq_STerms = x; coq_SMem = x0; coq_SFrame = x1; coq_SEffects =
      x2 } = sts1
    in
    let { coq_STerms = sTerms1; coq_SMem = sMem1; coq_SFrame = sFrame1;
      coq_SEffects = sEffects1 } = sts2
    in
    if smap_dec x sTerms1
    then if smem_dec x0 sMem1
         then if sframe_dec x1 sFrame1
              then sterms_dec x2 sEffects1
              else false
         else false
    else false
 end

