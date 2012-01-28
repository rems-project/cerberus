open Bool
open Coqlib
open Datatypes
open Iteration
open Kildall
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Peano
open Specif
open Analysis
open Dtree
open Infrastructure
open Primitives
open Syntax

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val cmds_from_block :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.cmds option **)

let cmds_from_block f lbl =
  match LLVMinfra.lookupBlockViaLabelFromFdef f lbl with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
        Some
        (filter (fun c ->
          match LLVMinfra.getCmdID c with
            | Some i -> true
            | None -> false) cs)
    | None -> None

type rhs =
  | Coq_rhs_bop of LLVMsyntax.bop * LLVMsyntax.sz * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_fbop of LLVMsyntax.fbop * LLVMsyntax.floating_point
     * LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_extractvalue of LLVMsyntax.typ * LLVMsyntax.value
     * LLVMsyntax.list_const
  | Coq_rhs_insertvalue of LLVMsyntax.typ * LLVMsyntax.value * 
     LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.list_const
  | Coq_rhs_malloc of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_free of LLVMsyntax.typ * LLVMsyntax.value
  | Coq_rhs_alloca of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_load of LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_store of LLVMsyntax.typ * LLVMsyntax.value * 
     LLVMsyntax.value * LLVMsyntax.align
  | Coq_rhs_gep of LLVMsyntax.inbounds * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.list_sz_value
  | Coq_rhs_trunc of LLVMsyntax.truncop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_ext of LLVMsyntax.extop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_cast of LLVMsyntax.castop * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.typ
  | Coq_rhs_icmp of LLVMsyntax.cond * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_fcmp of LLVMsyntax.fcond * LLVMsyntax.floating_point
     * LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_select of LLVMsyntax.value * LLVMsyntax.typ * 
     LLVMsyntax.value * LLVMsyntax.value
  | Coq_rhs_call of LLVMsyntax.noret * LLVMsyntax.clattrs * 
     LLVMsyntax.typ * LLVMsyntax.value * LLVMsyntax.params

(** val rhs_rect :
    (LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value
    -> 'a1) -> (LLVMsyntax.fbop -> LLVMsyntax.floating_point ->
    LLVMsyntax.value -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value -> 'a1)
    -> (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.list_sz_value -> 'a1) ->
    (LLVMsyntax.truncop -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.cond -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.value -> 'a1) -> (LLVMsyntax.fcond ->
    LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1)
    -> (LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.value -> 'a1) -> (LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) -> rhs ->
    'a1 **)

let rhs_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | Coq_rhs_bop (x, x0, x1, x2) -> f x x0 x1 x2
  | Coq_rhs_fbop (x, x0, x1, x2) -> f0 x x0 x1 x2
  | Coq_rhs_extractvalue (x, x0, x1) -> f1 x x0 x1
  | Coq_rhs_insertvalue (x, x0, x1, x2, x3) -> f2 x x0 x1 x2 x3
  | Coq_rhs_malloc (x, x0, x1) -> f3 x x0 x1
  | Coq_rhs_free (x, x0) -> f4 x x0
  | Coq_rhs_alloca (x, x0, x1) -> f5 x x0 x1
  | Coq_rhs_load (x, x0, x1) -> f6 x x0 x1
  | Coq_rhs_store (x, x0, x1, x2) -> f7 x x0 x1 x2
  | Coq_rhs_gep (x, x0, x1, x2) -> f8 x x0 x1 x2
  | Coq_rhs_trunc (x, x0, x1, x2) -> f9 x x0 x1 x2
  | Coq_rhs_ext (x, x0, x1, x2) -> f10 x x0 x1 x2
  | Coq_rhs_cast (x, x0, x1, x2) -> f11 x x0 x1 x2
  | Coq_rhs_icmp (x, x0, x1, x2) -> f12 x x0 x1 x2
  | Coq_rhs_fcmp (x, x0, x1, x2) -> f13 x x0 x1 x2
  | Coq_rhs_select (x, x0, x1, x2) -> f14 x x0 x1 x2
  | Coq_rhs_call (x, x0, x1, x2, x3) -> f15 x x0 x1 x2 x3

(** val rhs_rec :
    (LLVMsyntax.bop -> LLVMsyntax.sz -> LLVMsyntax.value -> LLVMsyntax.value
    -> 'a1) -> (LLVMsyntax.fbop -> LLVMsyntax.floating_point ->
    LLVMsyntax.value -> LLVMsyntax.value -> 'a1) -> (LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.list_const -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.typ -> LLVMsyntax.value -> 'a1)
    -> (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.align -> 'a1) ->
    (LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.value ->
    LLVMsyntax.align -> 'a1) -> (LLVMsyntax.inbounds -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.list_sz_value -> 'a1) ->
    (LLVMsyntax.truncop -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.extop -> LLVMsyntax.typ ->
    LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) -> (LLVMsyntax.castop ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ -> 'a1) ->
    (LLVMsyntax.cond -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.value -> 'a1) -> (LLVMsyntax.fcond ->
    LLVMsyntax.floating_point -> LLVMsyntax.value -> LLVMsyntax.value -> 'a1)
    -> (LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value ->
    LLVMsyntax.value -> 'a1) -> (LLVMsyntax.noret -> LLVMsyntax.clattrs ->
    LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) -> rhs ->
    'a1 **)

let rhs_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | Coq_rhs_bop (x, x0, x1, x2) -> f x x0 x1 x2
  | Coq_rhs_fbop (x, x0, x1, x2) -> f0 x x0 x1 x2
  | Coq_rhs_extractvalue (x, x0, x1) -> f1 x x0 x1
  | Coq_rhs_insertvalue (x, x0, x1, x2, x3) -> f2 x x0 x1 x2 x3
  | Coq_rhs_malloc (x, x0, x1) -> f3 x x0 x1
  | Coq_rhs_free (x, x0) -> f4 x x0
  | Coq_rhs_alloca (x, x0, x1) -> f5 x x0 x1
  | Coq_rhs_load (x, x0, x1) -> f6 x x0 x1
  | Coq_rhs_store (x, x0, x1, x2) -> f7 x x0 x1 x2
  | Coq_rhs_gep (x, x0, x1, x2) -> f8 x x0 x1 x2
  | Coq_rhs_trunc (x, x0, x1, x2) -> f9 x x0 x1 x2
  | Coq_rhs_ext (x, x0, x1, x2) -> f10 x x0 x1 x2
  | Coq_rhs_cast (x, x0, x1, x2) -> f11 x x0 x1 x2
  | Coq_rhs_icmp (x, x0, x1, x2) -> f12 x x0 x1 x2
  | Coq_rhs_fcmp (x, x0, x1, x2) -> f13 x x0 x1 x2
  | Coq_rhs_select (x, x0, x1, x2) -> f14 x x0 x1 x2
  | Coq_rhs_call (x, x0, x1, x2, x3) -> f15 x x0 x1 x2 x3

(** val rhs_of_cmd : LLVMsyntax.cmd -> rhs **)

let rhs_of_cmd = function
  | LLVMsyntax.Coq_insn_bop (i, bop0, sz0, v1, v2) -> Coq_rhs_bop (bop0, sz0,
      v1, v2)
  | LLVMsyntax.Coq_insn_fbop (i, fbop0, fp0, v1, v2) -> Coq_rhs_fbop (fbop0,
      fp0, v1, v2)
  | LLVMsyntax.Coq_insn_extractvalue (i, t0, v, cnts) -> Coq_rhs_extractvalue
      (t0, v, cnts)
  | LLVMsyntax.Coq_insn_insertvalue (i, t1, v1, t2, v2, cnts) ->
      Coq_rhs_insertvalue (t1, v1, t2, v2, cnts)
  | LLVMsyntax.Coq_insn_malloc (i, t0, v, al) -> Coq_rhs_malloc (t0, v, al)
  | LLVMsyntax.Coq_insn_free (i, t0, v) -> Coq_rhs_free (t0, v)
  | LLVMsyntax.Coq_insn_alloca (i, t0, v, al) -> Coq_rhs_alloca (t0, v, al)
  | LLVMsyntax.Coq_insn_load (i, t0, v, al) -> Coq_rhs_load (t0, v, al)
  | LLVMsyntax.Coq_insn_store (i, t1, v1, v2, al) -> Coq_rhs_store (t1, v1,
      v2, al)
  | LLVMsyntax.Coq_insn_gep (i, ib0, t0, v, vs) -> Coq_rhs_gep (ib0, t0, v,
      vs)
  | LLVMsyntax.Coq_insn_trunc (i, top0, t1, v1, t2) -> Coq_rhs_trunc (top0,
      t1, v1, t2)
  | LLVMsyntax.Coq_insn_ext (i, eop0, t1, v1, t2) -> Coq_rhs_ext (eop0, t1,
      v1, t2)
  | LLVMsyntax.Coq_insn_cast (i, cop0, t1, v1, t2) -> Coq_rhs_cast (cop0, t1,
      v1, t2)
  | LLVMsyntax.Coq_insn_icmp (i, t0, cnd0, v1, v2) -> Coq_rhs_icmp (t0, cnd0,
      v1, v2)
  | LLVMsyntax.Coq_insn_fcmp (i, fcond0, fp0, v1, v2) -> Coq_rhs_fcmp
      (fcond0, fp0, v1, v2)
  | LLVMsyntax.Coq_insn_select (i, v0, t0, v1, v2) -> Coq_rhs_select (v0, t0,
      v1, v2)
  | LLVMsyntax.Coq_insn_call (i, noret0, cl0, t1, v1, ps) -> Coq_rhs_call
      (noret0, cl0, t1, v1, ps)

(** val rhs_dec : rhs -> rhs -> bool **)

let rhs_dec r1 r2 =
  match r1 with
    | Coq_rhs_bop (b, s, v, v0) ->
        (match r2 with
           | Coq_rhs_bop (b0, s0, v1, v2) ->
               let s1 = LLVMinfra.bop_dec b b0 in
               if s1
               then let s2 = LLVMsyntax.Size.dec s s0 in
                    if s2
                    then let s3 = LLVMinfra.value_dec v v1 in
                         if s3 then LLVMinfra.value_dec v0 v2 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_fbop (f, f0, v, v0) ->
        (match r2 with
           | Coq_rhs_fbop (f1, f2, v1, v2) ->
               let s = LLVMinfra.fbop_dec f f1 in
               if s
               then let s0 = LLVMinfra.floating_point_dec f0 f2 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v1 in
                         if s1 then LLVMinfra.value_dec v0 v2 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_extractvalue (t0, v, l0) ->
        (match r2 with
           | Coq_rhs_extractvalue (t1, v0, l1) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s
               then let s0 = LLVMinfra.value_dec v v0 in
                    if s0 then LLVMinfra.list_const_dec l0 l1 else false
               else false
           | _ -> false)
    | Coq_rhs_insertvalue (t0, v, t1, v0, l0) ->
        (match r2 with
           | Coq_rhs_insertvalue (t2, v1, t3, v2, l1) ->
               let s = LLVMinfra.typ_dec t0 t2 in
               if s
               then let s0 = LLVMinfra.value_dec v v1 in
                    if s0
                    then let s1 = LLVMinfra.typ_dec t1 t3 in
                         if s1
                         then let s2 = LLVMinfra.value_dec v0 v2 in
                              if s2
                              then LLVMinfra.list_const_dec l0 l1
                              else false
                         else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_malloc (t0, v, a) ->
        (match r2 with
           | Coq_rhs_malloc (t1, v0, a0) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s
               then let s0 = LLVMinfra.value_dec v v0 in
                    if s0 then LLVMsyntax.Align.dec a a0 else false
               else false
           | _ -> false)
    | Coq_rhs_free (t0, v) ->
        (match r2 with
           | Coq_rhs_free (t1, v0) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s then LLVMinfra.value_dec v v0 else false
           | _ -> false)
    | Coq_rhs_alloca (t0, v, a) ->
        (match r2 with
           | Coq_rhs_alloca (t1, v0, a0) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s
               then let s0 = LLVMinfra.value_dec v v0 in
                    if s0 then LLVMsyntax.Align.dec a a0 else false
               else false
           | _ -> false)
    | Coq_rhs_load (t0, v, a) ->
        (match r2 with
           | Coq_rhs_load (t1, v0, a0) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s
               then let s0 = LLVMsyntax.Align.dec a a0 in
                    if s0 then LLVMinfra.value_dec v v0 else false
               else false
           | _ -> false)
    | Coq_rhs_store (t0, v, v0, a) ->
        (match r2 with
           | Coq_rhs_store (t1, v1, v2, a0) ->
               let s = LLVMinfra.typ_dec t0 t1 in
               if s
               then let s0 = LLVMinfra.value_dec v v1 in
                    if s0
                    then let s1 = LLVMsyntax.Align.dec a a0 in
                         if s1 then LLVMinfra.value_dec v0 v2 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_gep (i0, t0, v, l0) ->
        (match r2 with
           | Coq_rhs_gep (i1, t1, v0, l1) ->
               let s = LLVMinfra.inbounds_dec i0 i1 in
               if s
               then let s0 = LLVMinfra.typ_dec t0 t1 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v0 in
                         if s1 then LLVMinfra.list_value_dec l0 l1 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_trunc (t0, t1, v, t2) ->
        (match r2 with
           | Coq_rhs_trunc (t3, t4, v0, t5) ->
               let s = LLVMinfra.truncop_dec t0 t3 in
               if s
               then let s0 = LLVMinfra.typ_dec t1 t4 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v0 in
                         if s1 then LLVMinfra.typ_dec t2 t5 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_ext (e, t0, v, t1) ->
        (match r2 with
           | Coq_rhs_ext (e0, t2, v0, t3) ->
               let s = LLVMinfra.extop_dec e e0 in
               if s
               then let s0 = LLVMinfra.typ_dec t0 t2 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v0 in
                         if s1 then LLVMinfra.typ_dec t1 t3 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_cast (c, t0, v, t1) ->
        (match r2 with
           | Coq_rhs_cast (c0, t2, v0, t3) ->
               let s = LLVMinfra.castop_dec c c0 in
               if s
               then let s0 = LLVMinfra.typ_dec t0 t2 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v0 in
                         if s1 then LLVMinfra.typ_dec t1 t3 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_icmp (c, t0, v, v0) ->
        (match r2 with
           | Coq_rhs_icmp (c0, t1, v1, v2) ->
               let s = LLVMinfra.cond_dec c c0 in
               if s
               then let s0 = LLVMinfra.typ_dec t0 t1 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v1 in
                         if s1 then LLVMinfra.value_dec v0 v2 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_fcmp (f, f0, v, v0) ->
        (match r2 with
           | Coq_rhs_fcmp (f1, f2, v1, v2) ->
               let s = LLVMinfra.fcond_dec f f1 in
               if s
               then let s0 = LLVMinfra.floating_point_dec f0 f2 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v v1 in
                         if s1 then LLVMinfra.value_dec v0 v2 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_select (v, t0, v0, v1) ->
        (match r2 with
           | Coq_rhs_select (v2, t1, v3, v4) ->
               let s = LLVMinfra.value_dec v v2 in
               if s
               then let s0 = LLVMinfra.typ_dec t0 t1 in
                    if s0
                    then let s1 = LLVMinfra.value_dec v0 v3 in
                         if s1 then LLVMinfra.value_dec v1 v4 else false
                    else false
               else false
           | _ -> false)
    | Coq_rhs_call (n, c, t0, v, p) ->
        (match r2 with
           | Coq_rhs_call (n0, c0, t1, v0, p0) ->
               let s = LLVMinfra.value_dec v v0 in
               if s
               then let s0 = LLVMinfra.noret_dec n n0 in
                    if s0
                    then let LLVMsyntax.Coq_clattrs_intro (t2, c1, a, a0) = c
                         in
                         let LLVMsyntax.Coq_clattrs_intro (
                           t3, c2, a1, a2) = c0
                         in
                         let s1 = LLVMinfra.tailc_dec t2 t3 in
                         if s1
                         then let s2 = LLVMinfra.typ_dec t0 t1 in
                              if s2
                              then let s3 = LLVMinfra.callconv_dec c1 c2 in
                                   if s3
                                   then let s4 =
                                          LLVMinfra.attributes_dec a a1
                                        in
                                        if s4
                                        then let s5 =
                                               LLVMinfra.attributes_dec a0 a2
                                             in
                                             if s5
                                             then LLVMinfra.params_dec p p0
                                             else false
                                        else false
                                   else false
                              else false
                         else false
                    else false
               else false
           | _ -> false)

(** val pure_cmd : LLVMsyntax.cmd -> bool **)

let pure_cmd = function
  | LLVMsyntax.Coq_insn_malloc (i, t0, v, a) -> false
  | LLVMsyntax.Coq_insn_free (i, t0, v) -> false
  | LLVMsyntax.Coq_insn_alloca (i, t0, v, a) -> false
  | LLVMsyntax.Coq_insn_load (i, t0, v, a) -> false
  | LLVMsyntax.Coq_insn_store (i, t0, v, v0, a) -> false
  | LLVMsyntax.Coq_insn_call (i, n, c0, t0, v, p) -> false
  | _ -> true

(** val const_list_value :
    LLVMsyntax.list_sz_value -> LLVMsyntax.list_const option **)

let rec const_list_value = function
  | LLVMsyntax.Nil_list_sz_value -> Some LLVMsyntax.Nil_list_const
  | LLVMsyntax.Cons_list_sz_value (s, v, vs') ->
      (match v with
         | LLVMsyntax.Coq_value_id i -> None
         | LLVMsyntax.Coq_value_const c ->
             (match const_list_value vs' with
                | Some cs' -> Some (LLVMsyntax.Cons_list_const (c, cs'))
                | None -> None))

(** val const_cmd : LLVMsyntax.cmd -> LLVMsyntax.const option **)

let const_cmd = function
  | LLVMsyntax.Coq_insn_bop (i, bop0, s, v, v0) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c2 -> Some
                    (LLVMsyntax.Coq_const_bop (bop0, c1, c2))))
  | LLVMsyntax.Coq_insn_fbop (i, fbop0, f, v, v0) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c2 -> Some
                    (LLVMsyntax.Coq_const_fbop (fbop0, c1, c2))))
  | LLVMsyntax.Coq_insn_extractvalue (i, t0, v, cnts) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c0 -> Some
             (LLVMsyntax.Coq_const_extractvalue (c0, cnts)))
  | LLVMsyntax.Coq_insn_insertvalue (i, t0, v, t1, v0, cnts) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c2 -> Some
                    (LLVMsyntax.Coq_const_insertvalue (c1, c2, cnts))))
  | LLVMsyntax.Coq_insn_gep (i, ib0, t0, v, vs) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c0 ->
             (match const_list_value vs with
                | Some cnts -> Some (LLVMsyntax.Coq_const_gep (ib0, c0,
                    cnts))
                | None -> None))
  | LLVMsyntax.Coq_insn_trunc (i, top0, t0, v, t1) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 -> Some
             (LLVMsyntax.Coq_const_truncop (top0, c1, t1)))
  | LLVMsyntax.Coq_insn_ext (i, eop0, t0, v, t1) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 -> Some (LLVMsyntax.Coq_const_extop
             (eop0, c1, t1)))
  | LLVMsyntax.Coq_insn_cast (i, cop0, t0, v, t1) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 -> Some (LLVMsyntax.Coq_const_castop
             (cop0, c1, t1)))
  | LLVMsyntax.Coq_insn_icmp (i, cond0, t0, v, v0) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c2 -> Some
                    (LLVMsyntax.Coq_const_icmp (cond0, c1, c2))))
  | LLVMsyntax.Coq_insn_fcmp (i, fcond0, f, v, v0) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c1 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c2 -> Some
                    (LLVMsyntax.Coq_const_fcmp (fcond0, c1, c2))))
  | LLVMsyntax.Coq_insn_select (i, v, t0, v0, v1) ->
      (match v with
         | LLVMsyntax.Coq_value_id i0 -> None
         | LLVMsyntax.Coq_value_const c0 ->
             (match v0 with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const c1 ->
                    (match v1 with
                       | LLVMsyntax.Coq_value_id i0 -> None
                       | LLVMsyntax.Coq_value_const c2 -> Some
                           (LLVMsyntax.Coq_const_select (c0, c1, c2)))))
  | _ -> None

(** val const_in_list_value_l :
    LLVMsyntax.const -> LLVMsyntax.list_value_l -> bool **)

let rec const_in_list_value_l cst0 = function
  | LLVMsyntax.Nil_list_value_l -> true
  | LLVMsyntax.Cons_list_value_l (v, l0, vls') ->
      (match v with
         | LLVMsyntax.Coq_value_id i -> false
         | LLVMsyntax.Coq_value_const cst ->
             if proj_sumbool (LLVMinfra.const_dec cst cst0)
             then const_in_list_value_l cst0 vls'
             else false)

(** val const_phinode : LLVMsyntax.phinode -> LLVMsyntax.const option **)

let const_phinode = function
  | LLVMsyntax.Coq_insn_phi (i, t0, l0) ->
      (match l0 with
         | LLVMsyntax.Nil_list_value_l -> None
         | LLVMsyntax.Cons_list_value_l (v, l1, vls) ->
             (match v with
                | LLVMsyntax.Coq_value_id i0 -> None
                | LLVMsyntax.Coq_value_const cnt ->
                    if const_in_list_value_l cnt vls then Some cnt else None))

type lcmds = (LLVMsyntax.l*LLVMsyntax.cmd) list

(** val lookup_redundant_exp : lcmds -> rhs -> LLVMsyntax.id option **)

let rec lookup_redundant_exp inscope r =
  match inscope with
    | [] -> None
    | p::inscope' ->
        let l0,c = p in
        (match LLVMinfra.getCmdID c with
           | Some id0 ->
               if rhs_dec r (rhs_of_cmd c)
               then Some id0
               else lookup_redundant_exp inscope' r
           | None -> lookup_redundant_exp inscope' r)

(** val mem_effect :
    LLVMsyntax.cmd -> (LLVMsyntax.value*LLVMsyntax.typ) option **)

let mem_effect = function
  | LLVMsyntax.Coq_insn_free (i, t0, pv) -> Some (pv,t0)
  | LLVMsyntax.Coq_insn_store (i, t0, v, pv, a) -> Some (pv,t0)
  | _ -> None

(** val is_no_alias_id : LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let is_no_alias_id = Transforms_aux.is_no_alias

(** val is_no_alias :
    LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ
    -> bool **)

let is_no_alias pv1 t1 pv2 t2 =
  match pv1 with
    | LLVMsyntax.Coq_value_id id1 ->
        (match pv2 with
           | LLVMsyntax.Coq_value_id id2 -> is_no_alias_id id1 id2
           | LLVMsyntax.Coq_value_const c -> false)
    | LLVMsyntax.Coq_value_const c ->
        (match c with
           | LLVMsyntax.Coq_const_gid (t0, id1) ->
               (match pv2 with
                  | LLVMsyntax.Coq_value_id i -> false
                  | LLVMsyntax.Coq_value_const c0 ->
                      (match c0 with
                         | LLVMsyntax.Coq_const_gid (
                             t3, id2) ->
                             negb (proj_sumbool (LLVMinfra.id_dec id1 id2))
                         | _ -> false))
           | _ -> false)

(** val kill_aliased_loadstores :
    lcmds -> LLVMsyntax.value -> LLVMsyntax.typ -> lcmds **)

let kill_aliased_loadstores inscope pv1 t1 =
  filter (fun data ->
    let y,y0 = data in
    (match y0 with
       | LLVMsyntax.Coq_insn_load (i, t2, pv2, a) ->
           is_no_alias pv1 t1 pv2 t2
       | LLVMsyntax.Coq_insn_store (i, t2, v, pv2, a) ->
           is_no_alias pv1 t1 pv2 t2
       | _ -> true)) inscope

(** val is_must_alias_id : LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let is_must_alias_id = Transforms_aux.is_must_alias

(** val is_must_alias :
    LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.typ
    -> bool **)

let is_must_alias pv1 t1 pv2 t2 =
  match pv1 with
    | LLVMsyntax.Coq_value_id id1 ->
        (match pv2 with
           | LLVMsyntax.Coq_value_id id2 ->
               if LLVMinfra.id_dec id1 id2
               then true
               else is_must_alias_id id1 id2
           | LLVMsyntax.Coq_value_const c -> false)
    | LLVMsyntax.Coq_value_const c ->
        (match c with
           | LLVMsyntax.Coq_const_gid (t0, id1) ->
               (match pv2 with
                  | LLVMsyntax.Coq_value_id i -> false
                  | LLVMsyntax.Coq_value_const c0 ->
                      (match c0 with
                         | LLVMsyntax.Coq_const_gid (
                             t3, id2) ->
                             proj_sumbool (LLVMinfra.id_dec id1 id2)
                         | _ -> false))
           | _ -> false)

(** val lookup_redundant_load :
    lcmds -> LLVMsyntax.typ -> LLVMsyntax.value ->
    ((LLVMsyntax.l*LLVMsyntax.id)*LLVMsyntax.value) option **)

let rec lookup_redundant_load inscope t1 pv1 =
  match inscope with
    | [] -> None
    | p::inscope' ->
        let l0,c = p in
        (match c with
           | LLVMsyntax.Coq_insn_load (i, t1', pv1', a) ->
               if if is_must_alias pv1' t1' pv1 t1
                  then LLVMinfra.typEqB t1 t1'
                  else false
               then Some
                      ((l0,(LLVMinfra.getCmdLoc c)),(LLVMsyntax.Coq_value_id
                      (LLVMinfra.getCmdLoc c)))
               else lookup_redundant_load inscope' t1 pv1
           | LLVMsyntax.Coq_insn_store (id0, t1', v0', pv1', a) ->
               if if is_must_alias pv1' t1' pv1 t1
                  then LLVMinfra.typEqB t1 t1'
                  else false
               then Some ((l0,id0),v0')
               else lookup_redundant_load inscope' t1 pv1
           | _ -> lookup_redundant_load inscope' t1 pv1)

(** val block_doesnt_kill :
    LLVMsyntax.block -> LLVMsyntax.value -> LLVMsyntax.typ -> bool **)

let block_doesnt_kill b pv1 t1 =
  let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
  fold_left (fun acc c ->
    if acc
    then (match mem_effect c with
            | Some p0 -> let pv2,t2 = p0 in is_no_alias pv1 t1 pv2 t2
            | None ->
                (match c with
                   | LLVMsyntax.Coq_insn_call (i, n, c0, t2, v, p0) -> false
                   | _ -> true))
    else acc) cs true

(** val split_cmds : LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmds **)

let rec split_cmds cs id1 =
  match cs with
    | [] -> []
    | c::cs' ->
        if LLVMinfra.id_dec id1 (LLVMinfra.getCmdLoc c)
        then cs'
        else split_cmds cs' id1

(** val cmds_doesnt_kill :
    LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.typ
    -> bool **)

let cmds_doesnt_kill b id1 pv1 t1 =
  let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
  fold_left (fun acc c ->
    if acc
    then (match mem_effect c with
            | Some p0 -> let pv2,t2 = p0 in is_no_alias pv1 t1 pv2 t2
            | None -> true)
    else acc) (split_cmds cs id1) true

module LBooleanInv = 
 struct 
  type t = bool
  
  (** val beq : t -> t -> bool **)
  
  let beq =
    eqb
  
  (** val bot : bool **)
  
  let bot =
    true
  
  (** val top : bool **)
  
  let top =
    false
  
  (** val lub : t -> t -> bool **)
  
  let lub x y =
    if x then y else false
 end

module AvailableDS = Dataflow_Solver(LBooleanInv)(AtomNodeSet)

(** val available_transf :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.typ -> LLVMsyntax.l -> bool -> bool **)

let available_transf f src tgt id1 pv1 t1 curr input =
  if LLVMinfra.l_dec curr src
  then true
  else if LLVMinfra.l_dec curr tgt
       then (match LLVMinfra.lookupBlockViaLabelFromFdef f curr with
               | Some b ->
                   if cmds_doesnt_kill b id1 pv1 t1 then input else false
               | None -> false)
       else (match LLVMinfra.lookupBlockViaLabelFromFdef f curr with
               | Some b ->
                   if block_doesnt_kill b pv1 t1 then input else false
               | None -> false)

(** val available_init_aux :
    LLVMsyntax.blocks -> LLVMsyntax.l -> (LLVMsyntax.l*bool) list ->
    (LLVMsyntax.l*bool) list **)

let rec available_init_aux bs src acc =
  match bs with
    | [] -> acc
    | b::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t0) = b in
        available_init_aux bs' src
          ((l0,(if LLVMinfra.l_dec l0 src then true else false))::acc)

(** val available_init :
    LLVMsyntax.fdef -> LLVMsyntax.l -> (LLVMsyntax.l*bool) list **)

let available_init f src =
  let LLVMsyntax.Coq_fdef_intro (f0, bs) = f in available_init_aux bs src []

(** val available_aux :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.typ -> bool AMap.t option **)

let available_aux f src tgt id1 pv1 t1 =
  AvailableDS.fixpoint (successors f) (available_transf f src tgt id1 pv1 t1)
    ((src,LBooleanInv.bot)::[])

(** val fdef_doesnt_kill :
    LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.typ -> bool **)

let fdef_doesnt_kill f src tgt id1 pv1 t1 =
  match available_aux f src tgt id1 pv1 t1 with
    | Some rs -> AMap.get tgt rs
    | None -> false

(** val fdef_doesnt_kill_aux_func :
    (LLVMsyntax.fdef, (LLVMsyntax.ls ATree.t, (LLVMsyntax.l list,
    (LLVMsyntax.l, (LLVMsyntax.l, (LLVMsyntax.l, (LLVMsyntax.id,
    (LLVMsyntax.value, LLVMsyntax.typ) sigT) sigT) sigT) sigT) sigT) sigT)
    sigT) sigT -> bool **)

let rec fdef_doesnt_kill_aux_func x =
  let f = projT1 x in
  let preds = projT1 (projT2 x) in
  let nvisited = projT1 (projT2 (projT2 x)) in
  let src = projT1 (projT2 (projT2 (projT2 x))) in
  let curr = projT1 (projT2 (projT2 (projT2 (projT2 x)))) in
  let target = projT1 (projT2 (projT2 (projT2 (projT2 (projT2 x))))) in
  let id1 = projT1 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 x)))))) in
  let pv1 =
    projT1 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 x)))))))
  in
  let t1 =
    projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 (projT2 x)))))))
  in
  let fdef_doesnt_kill_aux0 =
    fun f0 preds0 nvisited0 src0 curr0 target0 id2 pv2 t2 ->
    let y = Coq_existT (f0, (Coq_existT (preds0, (Coq_existT (nvisited0,
      (Coq_existT (src0, (Coq_existT (curr0, (Coq_existT (target0,
      (Coq_existT (id2, (Coq_existT (pv2, t2)))))))))))))))
    in
    fdef_doesnt_kill_aux_func y
  in
  let init =
    if LLVMinfra.l_dec curr src
    then true
    else if LLVMinfra.l_dec curr target
         then let filtered_var = LLVMinfra.lookupBlockViaLabelFromFdef f curr
              in
              let branch_0 = fun _ -> false in
              let branch_1 = fun b -> cmds_doesnt_kill b id1 pv1 t1 in
              (match filtered_var with
                 | Some b -> branch_1 b
                 | None -> branch_0 __)
         else let filtered_var = LLVMinfra.lookupBlockViaLabelFromFdef f curr
              in
              let branch_0 = fun _ -> false in
              let branch_1 = fun b -> block_doesnt_kill b pv1 t1 in
              (match filtered_var with
                 | Some b -> branch_1 b
                 | None -> branch_0 __)
  in
  let filtered_var = ATree.get curr preds in
  let branch_0 = fun _ -> init in
  let branch_1 = fun nexts ->
    fold_left (fun acc next ->
      if acc
      then if in_dec AtomImpl.eq_atom_dec next nvisited
           then fdef_doesnt_kill_aux0 f preds
                  (remove AtomImpl.eq_atom_dec next nvisited) src next target
                  id1 pv1 t1
           else acc
      else acc) nexts init
  in
  (match filtered_var with
     | Some nexts -> branch_1 nexts
     | None -> branch_0 __)

(** val fdef_doesnt_kill_aux :
    LLVMsyntax.fdef -> LLVMsyntax.ls ATree.t -> LLVMsyntax.l list ->
    LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.l -> LLVMsyntax.id ->
    LLVMsyntax.value -> LLVMsyntax.typ -> bool **)

let fdef_doesnt_kill_aux f preds nvisited src curr target id1 pv1 t1 =
  fdef_doesnt_kill_aux_func (Coq_existT (f, (Coq_existT (preds, (Coq_existT
    (nvisited, (Coq_existT (src, (Coq_existT (curr, (Coq_existT (target,
    (Coq_existT (id1, (Coq_existT (pv1, t1))))))))))))))))

(** val kill_loadstores : lcmds -> lcmds **)

let kill_loadstores inscope =
  filter (fun data ->
    let y,y0 = data in
    (match y0 with
       | LLVMsyntax.Coq_insn_load (i, t0, v, a) -> false
       | LLVMsyntax.Coq_insn_store (i, t0, v, v0, a) -> false
       | _ -> true)) inscope

(** val does_load_elim : unit -> bool **)

let does_load_elim = Transforms_aux.does_load_elim

(** val gvn_cmd :
    ((LLVMsyntax.fdef*bool)*lcmds) -> LLVMsyntax.l -> LLVMsyntax.cmd ->
    (LLVMsyntax.fdef*bool)*lcmds **)

let gvn_cmd st l1 c =
  let p,inscope = st in
  let f,changed = p in
  if pure_cmd c
  then (match LLVMinfra.getCmdID c with
          | Some id0 ->
              (match const_cmd c with
                 | Some cst0 ->
                     ((remove_fdef id0 (csubst_fdef id0 cst0 f)),true),inscope
                 | None ->
                     (match lookup_redundant_exp inscope (rhs_of_cmd c) with
                        | Some id1 ->
                            ((remove_fdef id0 (isubst_fdef id0 id1 f)),true),inscope
                        | None -> (f,changed),((l1,c)::inscope)))
          | None -> (f,changed),inscope)
  else (match c with
          | LLVMsyntax.Coq_insn_load (id1, t1, pv1, al1) ->
              if does_load_elim ()
              then (match lookup_redundant_load inscope t1 pv1 with
                      | Some p0 ->
                          let p1,v0 = p0 in
                          let l0,id0 = p1 in
                          if fdef_doesnt_kill f l0 l1 id1 pv1 t1
                          then ((remove_fdef id1 (subst_fdef id1 v0 f)),true),inscope
                          else (f,changed),((l1,c)::inscope)
                      | None -> (f,changed),((l1,c)::inscope))
              else (f,changed),((l1,c)::inscope)
          | _ ->
              (match mem_effect c with
                 | Some p0 ->
                     let pv,t0 = p0 in
                     (match c with
                        | LLVMsyntax.Coq_insn_store (
                            i, t1, v, v0, a) ->
                            (f,changed),((l1,c)::(kill_aliased_loadstores
                                                  inscope pv t0))
                        | _ ->
                            (f,changed),(kill_aliased_loadstores inscope pv
                                          t0))
                 | None ->
                     (match c with
                        | LLVMsyntax.Coq_insn_call (
                            i, n, c0, t0, v, p0) ->
                            (f,changed),(kill_loadstores inscope)
                        | _ -> (f,changed),inscope)))

(** val gvn_cmds :
    ((LLVMsyntax.fdef*bool)*lcmds) -> LLVMsyntax.l -> nat ->
    (LLVMsyntax.fdef*bool)*lcmds **)

let rec gvn_cmds st l1 n =
  let p,inscope = st in
  let f,changed = p in
  (match LLVMinfra.lookupBlockViaLabelFromFdef f l1 with
     | Some b ->
         let LLVMsyntax.Coq_block_intro (l0, p0, cs, t0) = b in
         (match nth_error (rev cs) n with
            | Some c ->
                let st' = gvn_cmd st l1 c in
                (match n with
                   | O -> st'
                   | S n' -> gvn_cmds st' l1 n')
            | None -> st)
     | None -> st)

(** val gvn_phis :
    LLVMsyntax.fdef -> bool -> LLVMsyntax.phinodes -> LLVMsyntax.fdef*bool **)

let rec gvn_phis f changed = function
  | [] -> f,changed
  | p::ps' ->
      let id0 = LLVMinfra.getPhiNodeID p in
      (match const_phinode p with
         | Some cst0 ->
             let f' = remove_fdef id0 (csubst_fdef id0 cst0 f) in
             let changed' = true in
             gvn_phis f' (if changed then true else changed') ps'
         | None ->
             let changed' = false in
             gvn_phis f (if changed then true else changed') ps')

(** val gvn_fdef_dtree :
    LLVMsyntax.fdef -> bool -> lcmds -> coq_DTree -> LLVMsyntax.fdef*bool **)

let rec gvn_fdef_dtree f changed inscope = function
  | DT_node (l0, dts) ->
      (match LLVMinfra.lookupBlockViaLabelFromFdef f l0 with
         | Some b ->
             let LLVMsyntax.Coq_block_intro (l1, ps, cs, t0) = b in
             let p,inscope2 =
               gvn_cmds ((gvn_phis f changed ps),inscope) l0
                 (minus (length cs) (S O))
             in
             let f2,changed2 = p in gvn_fdef_dtrees f2 changed2 inscope2 dts
         | None -> f,changed)

(** val gvn_fdef_dtrees :
    LLVMsyntax.fdef -> bool -> lcmds -> coq_DTrees -> LLVMsyntax.fdef*bool **)

and gvn_fdef_dtrees f changed inscope = function
  | DT_nil -> f,changed
  | DT_cons (dt, dts') ->
      let f',changed' = gvn_fdef_dtree f changed inscope dt in
      gvn_fdef_dtrees f' changed' inscope dts'

(** val lookup_predundant_exp_from_cmds :
    LLVMsyntax.cmds -> rhs -> LLVMsyntax.cmd option **)

let rec lookup_predundant_exp_from_cmds cs r =
  match cs with
    | [] -> None
    | c::cs' ->
        (match LLVMinfra.getCmdID c with
           | Some i ->
               if rhs_dec r (rhs_of_cmd c)
               then Some c
               else lookup_predundant_exp_from_cmds cs' r
           | None -> lookup_predundant_exp_from_cmds cs' r)

(** val lookup_predundant_exp_for_id :
    LLVMsyntax.fdef -> LLVMsyntax.l list -> AtomImpl.atom set -> Dominators.t
    AMap.t -> LLVMsyntax.l -> rhs -> (LLVMsyntax.l*LLVMsyntax.cmd) option **)

let rec lookup_predundant_exp_for_id f ndom bd res l1 r =
  match ndom with
    | [] -> None
    | l0::ndom' ->
        if in_dec AtomImpl.eq_atom_dec l1 (AMap.get l0 res)
        then lookup_predundant_exp_for_id f ndom' bd res l1 r
        else (match LLVMinfra.lookupBlockViaLabelFromFdef f l0 with
                | Some b ->
                    let LLVMsyntax.Coq_block_intro (l2, p, cs, t0) = b in
                    (match lookup_predundant_exp_from_cmds cs r with
                       | Some c0 -> Some (l0,c0)
                       | None ->
                           lookup_predundant_exp_for_id f ndom' bd res l1 r)
                | None -> None)

(** val lookup_predundant_exp :
    LLVMsyntax.fdef -> AtomImpl.atom set -> Dominators.t AMap.t ->
    LLVMsyntax.l list -> LLVMsyntax.l list ->
    (((LLVMsyntax.l*LLVMsyntax.id)*LLVMsyntax.l)*LLVMsyntax.cmd) option **)

let rec lookup_predundant_exp f bd res rd0 = function
  | [] -> None
  | l1::rd' ->
      (match LLVMinfra.lookupBlockViaLabelFromFdef f l1 with
         | Some b ->
             let LLVMsyntax.Coq_block_intro (l0, p, cs, t0) = b in
             let ndom =
               set_diff LLVMinfra.id_dec
                 (set_inter LLVMinfra.id_dec rd0 (bound_fdef f))
                 (l1::(AMap.get l1 res))
             in
             (match fold_left (fun acc c ->
                      match acc with
                        | Some y -> acc
                        | None ->
                            (match LLVMinfra.getCmdID c with
                               | Some id1 ->
                                   if pure_cmd c
                                   then (match lookup_predundant_exp_for_id f
                                                 ndom bd res l1
                                                 (rhs_of_cmd c) with
                                           | Some p0 ->
                                               let l2,c0 = p0 in
                                               Some (((l1,id1),l2),c0)
                                           | None -> None)
                                   else None
                               | None -> None)) cs None with
                | Some re -> Some re
                | None -> lookup_predundant_exp f bd res rd0 rd')
         | None -> None)

(** val find_gcd_dom :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    -> LLVMsyntax.l option **)

let find_gcd_dom bd res l1 l2 =
  match set_inter LLVMinfra.id_dec (AMap.get l1 res) (AMap.get l2 res) with
    | [] -> None
    | l0::dts0 -> find_idom_aux bd res l0 dts0

(** val pre_fdef :
    LLVMsyntax.fdef -> AtomImpl.atom set -> Dominators.t AMap.t ->
    LLVMsyntax.l list -> LLVMsyntax.fdef*bool **)

let pre_fdef f bd res rd =
  match lookup_predundant_exp f bd res rd rd with
    | Some p ->
        let p0,c0 = p in
        let p1,l0 = p0 in
        let l1,id1 = p1 in
        (match find_gcd_dom bd res l1 l0 with
           | Some l2 ->
               (match LLVMinfra.lookupBlockViaLabelFromFdef f l2 with
                  | Some b ->
                      let LLVMsyntax.Coq_block_intro (l3, p2, cs, t0) = b in
                      (remove_fdef id1
                        (isubst_fdef id1 (LLVMinfra.getCmdLoc c0)
                          (motion_fdef l2 (plus (length cs) (S O)) c0 f))),true
                  | None -> f,false)
           | None -> f,false)
    | None -> f,false

(** val does_pre : unit -> bool **)

let does_pre = Transforms_aux.does_pre

(** val opt_step :
    coq_DTree -> AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l
    list -> LLVMsyntax.fdef -> (LLVMsyntax.fdef, LLVMsyntax.fdef) sum **)

let opt_step dt bd res rd f =
  let f1,changed1 = gvn_fdef_dtree f false [] dt in
  if changed1
  then Coq_inr f1
  else if does_pre ()
       then let f2,changed2 = pre_fdef f1 bd res rd in
            if changed2 then Coq_inr f2 else Coq_inl f2
       else Coq_inl f1

(** val dce_block :
    LLVMsyntax.fdef -> LLVMsyntax.block -> LLVMsyntax.fdef **)

let dce_block f = function
  | LLVMsyntax.Coq_block_intro (l0, ps, cs, t0) ->
      fold_left (fun f3 c ->
        match LLVMinfra.getCmdID c with
          | Some id0 ->
              if pure_cmd c
              then if used_in_fdef id0 f3 then f3 else remove_fdef id0 f3
              else f3
          | None -> f3) cs
        (fold_left (fun f2 p ->
          let id0 = LLVMinfra.getPhiNodeID p in
          if used_in_fdef id0 f2 then f2 else remove_fdef id0 f2) ps f)

(** val dce_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let dce_fdef f = match f with
  | LLVMsyntax.Coq_fdef_intro (fh, bs) ->
      fold_left (fun f1 b -> dce_block f1 b) bs f

(** val read_aa_from_fun : LLVMsyntax.id -> bool **)

let read_aa_from_fun = Transforms_aux.read_aa_from_fun

(** val opt_fdef : LLVMsyntax.fdef -> LLVMsyntax.fdef **)

let opt_fdef f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        let LLVMsyntax.Coq_block_intro (root, p, c, t0) = b in
        (match reachablity_analysis f with
           | Some rd ->
               let b0 = bound_fdef f in
               let dts = dom_analyze f in
               let chains = compute_sdom_chains b0 dts rd in
               let dt =
                 fold_left (fun acc elt ->
                   let y,chain = elt in create_dtree_from_chain acc chain)
                   chains (DT_node (root, DT_nil))
               in
               if if if if print_reachablity rd
                        then print_dominators b0 dts
                        else false
                     then print_dtree dt
                     else false
                  then read_aa_from_fun (LLVMinfra.getFdefID f)
                  else false
               then (match fix_temporary_fdef
                             (SafePrimIter.iterate 
                               (opt_step dt b0 dts rd) 
                               (dce_fdef f)) with
                       | Some f' -> f'
                       | None -> f)
               else f
           | None -> f)
    | None -> f

(** val open_aa_db : unit -> bool **)

let open_aa_db = Transforms_aux.open_aa_db

(** val opt : LLVMsyntax.coq_module -> LLVMsyntax.coq_module **)

let opt m = match m with
  | LLVMsyntax.Coq_module_intro (los, nts, ps) ->
      if open_aa_db ()
      then LLVMsyntax.Coq_module_intro (los, nts,
             (rev
               (fold_left (fun acc p ->
                 (match p with
                    | LLVMsyntax.Coq_product_fdef f ->
                        LLVMsyntax.Coq_product_fdef 
                        (opt_fdef f)
                    | _ -> p)::acc) ps [])))
      else m

