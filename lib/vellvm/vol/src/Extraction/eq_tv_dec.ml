open Bool
open MetatheoryAtom
open Infrastructure
open Symexe_def
open Syntax

type sterm_dec_prop = SimpleSE.sterm -> bool

type list_sterm_dec_prop = SimpleSE.list_sterm -> bool

type list_sterm_l_dec_prop = SimpleSE.list_sterm_l -> bool

type smem_dec_prop = SimpleSE.smem -> bool

type sframe_dec_prop = SimpleSE.sframe -> bool

(** val se_dec :
    ((((SimpleSE.sterm -> sterm_dec_prop)*(SimpleSE.list_sterm ->
    list_sterm_dec_prop))*(SimpleSE.list_sterm_l ->
    list_sterm_l_dec_prop))*(SimpleSE.smem ->
    smem_dec_prop))*(SimpleSE.sframe -> sframe_dec_prop) **)

let se_dec =
  SimpleSE.se_mutrec (fun v st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_val v0 -> LLVMinfra.value_dec v v0
      | _ -> false) (fun b s s0 h s1 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_bop (b0, s2, st2_1, st2_2) ->
          let s3 = LLVMinfra.bop_dec b b0 in
          if s3
          then let s4 = LLVMsyntax.Size.dec s s2 in
               if s4
               then let s5 = h st2_1 in if s5 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun f f0 s h s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_fbop (f1, f2, st2_1, st2_2) ->
          let s1 = LLVMinfra.fbop_dec f f1 in
          if s1
          then let s2 = LLVMinfra.floating_point_dec f0 f2 in
               if s2
               then let s3 = h st2_1 in if s3 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t s h l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_extractvalue (t0, st3, l1) ->
          let s0 = LLVMinfra.typ_dec t t0 in
          if s0
          then let s1 = h st3 in
               if s1 then LLVMinfra.list_const_dec l0 l1 else false
          else false
      | _ -> false) (fun t s h t0 s0 h0 l0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_insertvalue (t1, st2_1, t2, st2_2, l1) ->
          let s1 = LLVMinfra.typ_dec t t1 in
          if s1
          then let s2 = h st2_1 in
               if s2
               then let s3 = LLVMinfra.typ_dec t0 t2 in
                    if s3
                    then let s4 = h0 st2_2 in
                         if s4 then LLVMinfra.list_const_dec l0 l1 else false
                    else false
               else false
          else false
      | _ -> false) (fun s h t s0 h0 a st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_malloc (s1, t0, st3, a0) ->
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
      | SimpleSE.Coq_sterm_alloca (s1, t0, st3, a0) ->
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
      | SimpleSE.Coq_sterm_load (s1, t0, st3, a0) ->
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
      | SimpleSE.Coq_sterm_gep (i1, t0, st3, l1) ->
          let s0 = bool_dec i0 i1 in
          if s0
          then let s1 = LLVMinfra.typ_dec t t0 in
               if s1
               then let s2 = h st3 in if s2 then h0 l1 else false
               else false
          else false
      | _ -> false) (fun t t0 s h t1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_trunc (t2, t3, st3, t4) ->
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
      | SimpleSE.Coq_sterm_ext (e0, t1, st3, t2) ->
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
      | SimpleSE.Coq_sterm_cast (c0, t1, st3, t2) ->
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
      | SimpleSE.Coq_sterm_icmp (c0, t0, st2_1, st2_2) ->
          let s1 = LLVMinfra.cond_dec c c0 in
          if s1
          then let s2 = LLVMinfra.typ_dec t t0 in
               if s2
               then let s3 = h st2_1 in if s3 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun f f0 s h s0 h0 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_fcmp (f1, f2, st2_1, st2_2) ->
          let s1 = LLVMinfra.fcond_dec f f1 in
          if s1
          then let s2 = LLVMinfra.floating_point_dec f0 f2 in
               if s2
               then let s3 = h st2_1 in if s3 then h0 st2_2 else false
               else false
          else false
      | _ -> false) (fun t l0 h st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_phi (t0, l1) ->
          let s = LLVMinfra.typ_dec t t0 in if s then h l1 else false
      | _ -> false) (fun s h t s0 h0 s1 h1 st2 ->
    match st2 with
      | SimpleSE.Coq_sterm_select (st2_1, t0, st2_2, st2_3) ->
          let s2 = LLVMinfra.typ_dec t t0 in
          if s2
          then let s3 = h st2_1 in
               if s3
               then let s4 = h0 st2_2 in if s4 then h1 st2_3 else false
               else false
          else false
      | _ -> false) (fun sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> true
      | SimpleSE.Cons_list_sterm (s, s0, sts3) -> false)
    (fun s s0 h l0 h0 sts2 ->
    match sts2 with
      | SimpleSE.Nil_list_sterm -> false
      | SimpleSE.Cons_list_sterm (s1, s2, sts3) ->
          let s3 = LLVMsyntax.Size.dec s s1 in
          if s3
          then let s4 = h s2 in if s4 then h0 sts3 else false
          else false) (fun stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> true
      | SimpleSE.Cons_list_sterm_l (s, l0, stls3) -> false)
    (fun s h l0 l1 h0 stls2 ->
    match stls2 with
      | SimpleSE.Nil_list_sterm_l -> false
      | SimpleSE.Cons_list_sterm_l (s0, l2, stls3) ->
          let s1 = h s0 in
          if s1
          then let s2 = LLVMinfra.l_dec l0 l2 in
               if s2 then h0 stls3 else false
          else false) (fun sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_init -> true
      | _ -> false) (fun s h t s0 h0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_malloc (sm3, t0, s1, a0) ->
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
      | SimpleSE.Coq_smem_free (sm3, t0, s1) ->
          let s2 = h sm3 in
          if s2
          then let s3 = LLVMinfra.typ_dec t t0 in if s3 then h0 s1 else false
          else false
      | _ -> false) (fun s h t s0 h0 a sm2 ->
    match sm2 with
      | SimpleSE.Coq_smem_alloca (sm3, t0, s1, a0) ->
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
      | SimpleSE.Coq_smem_load (sm3, t0, s1, a0) ->
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
      | SimpleSE.Coq_smem_store (sm3, t0, s2, s3, a0) ->
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
      | _ -> false) (fun sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> true
      | SimpleSE.Coq_sframe_alloca (s, sf3, t, s0, a) -> false)
    (fun s h s0 h0 t s1 h1 a sf2 ->
    match sf2 with
      | SimpleSE.Coq_sframe_init -> false
      | SimpleSE.Coq_sframe_alloca (s2, sf3, t0, s3, a0) ->
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

(** val sterm_dec : SimpleSE.sterm -> SimpleSE.sterm -> bool **)

let sterm_dec =
  let p,x = se_dec in let p0,x0 = p in let p1,x1 = p0 in let h,l0 = p1 in h

(** val list_sterm_dec :
    SimpleSE.list_sterm -> SimpleSE.list_sterm -> bool **)

let list_sterm_dec =
  let p,x = se_dec in let p0,x0 = p in let p1,x1 = p0 in let s,h = p1 in h

(** val list_sterm_l_dec :
    SimpleSE.list_sterm_l -> SimpleSE.list_sterm_l -> bool **)

let list_sterm_l_dec =
  let p,x = se_dec in let p0,x0 = p in let p1,h = p0 in h

(** val smem_dec : SimpleSE.smem -> SimpleSE.smem -> bool **)

let smem_dec =
  let p,x = se_dec in let p0,h = p in h

(** val sframe_dec : SimpleSE.sframe -> SimpleSE.sframe -> bool **)

let sframe_dec =
  let p,h = se_dec in h

(** val sterminator_dec :
    SimpleSE.sterminator -> SimpleSE.sterminator -> bool **)

let sterminator_dec st1 st2 =
  match st1 with
    | SimpleSE.Coq_stmn_return (x, x0, x1) ->
        (match st2 with
           | SimpleSE.Coq_stmn_return (i1, t0, s0) ->
               if AtomImpl.eq_atom_dec x i1
               then if LLVMinfra.typ_dec x0 t0
                    then sterm_dec x1 s0
                    else false
               else false
           | _ -> false)
    | SimpleSE.Coq_stmn_return_void x ->
        (match st2 with
           | SimpleSE.Coq_stmn_return_void i1 -> AtomImpl.eq_atom_dec x i1
           | _ -> false)
    | SimpleSE.Coq_stmn_br (x, x0, x1, x2) ->
        (match st2 with
           | SimpleSE.Coq_stmn_br (i1, s0, l2, l3) ->
               if AtomImpl.eq_atom_dec x i1
               then if sterm_dec x0 s0
                    then if AtomImpl.eq_atom_dec x1 l2
                         then AtomImpl.eq_atom_dec x2 l3
                         else false
                    else false
               else false
           | _ -> false)
    | SimpleSE.Coq_stmn_br_uncond (x, x0) ->
        (match st2 with
           | SimpleSE.Coq_stmn_br_uncond (i1, l1) ->
               if AtomImpl.eq_atom_dec x i1
               then AtomImpl.eq_atom_dec x0 l1
               else false
           | _ -> false)
    | SimpleSE.Coq_stmn_unreachable x ->
        (match st2 with
           | SimpleSE.Coq_stmn_unreachable i1 -> AtomImpl.eq_atom_dec x i1
           | _ -> false)

(** val list_typ_sterm_dec :
    (LLVMsyntax.typ*SimpleSE.sterm) list -> (LLVMsyntax.typ*SimpleSE.sterm)
    list -> bool **)

let rec list_typ_sterm_dec l l0 =
  match l with
    | [] -> (match l0 with
               | [] -> true
               | p::l1 -> false)
    | y::l1 ->
        (match l0 with
           | [] -> false
           | p::l3 ->
               if let t,s = y in
                  let t0,s0 = p in
                  let s1 = LLVMinfra.typ_dec t t0 in
                  if s1 then sterm_dec s s0 else false
               then list_typ_sterm_dec l1 l3
               else false)

(** val smap_dec : SimpleSE.smap -> SimpleSE.smap -> bool **)

let rec smap_dec l sm0 =
  match l with
    | [] -> (match sm0 with
               | [] -> true
               | p::l0 -> false)
    | y::l0 ->
        (match sm0 with
           | [] -> false
           | p::l1 ->
               if let a,s = y in
                  let a0,s0 = p in
                  let s1 = LLVMinfra.id_dec a a0 in
                  if s1 then sterm_dec s s0 else false
               then smap_dec l0 l1
               else false)

(** val sterms_dec : SimpleSE.sterm list -> SimpleSE.sterm list -> bool **)

let rec sterms_dec l ts0 =
  match l with
    | [] -> (match ts0 with
               | [] -> true
               | s::l0 -> false)
    | y::l0 ->
        (match ts0 with
           | [] -> false
           | s::l1 -> if sterm_dec y s then sterms_dec l0 l1 else false)

(** val sstate_dec : SimpleSE.sstate -> SimpleSE.sstate -> bool **)

let sstate_dec sts1 sts2 =
  let { SimpleSE.coq_STerms = x; SimpleSE.coq_SMem = x0;
    SimpleSE.coq_SFrame = x1; SimpleSE.coq_SEffects = x2 } = sts1
  in
  let { SimpleSE.coq_STerms = sTerms1; SimpleSE.coq_SMem = sMem1;
    SimpleSE.coq_SFrame = sFrame1; SimpleSE.coq_SEffects = sEffects1 } = sts2
  in
  if smap_dec x sTerms1
  then if smem_dec x0 sMem1
       then if sframe_dec x1 sFrame1 then sterms_dec x2 sEffects1 else false
       else false
  else false

