open AST
open BinInt
open Bool
open CoqEqDec
open Datatypes
open List0
open ListSet
open MetatheoryAtom
open Peano
open Alist
open Monad
open Syntax
open Targetdata

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module LLVMinfra = 
 struct 
  (** val id_dec : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let id_dec =
    AtomImpl.eq_atom_dec
  
  (** val l_dec : LLVMsyntax.l -> LLVMsyntax.l -> bool **)
  
  let l_dec =
    AtomImpl.eq_atom_dec
  
  (** val inbounds_dec :
      LLVMsyntax.inbounds -> LLVMsyntax.inbounds -> bool **)
  
  let inbounds_dec = (=)
  
  (** val tailc_dec : LLVMsyntax.tailc -> LLVMsyntax.tailc -> bool **)
  
  let tailc_dec = (=)
  
  (** val varg_dec : LLVMsyntax.varg -> LLVMsyntax.varg -> bool **)
  
  let varg_dec =
    bool_dec
  
  (** val noret_dec : LLVMsyntax.noret -> LLVMsyntax.noret -> bool **)
  
  let noret_dec = (=)
  
  (** val lempty_set : LLVMsyntax.l set **)
  
  let lempty_set =
    empty_set
  
  (** val lset_add : LLVMsyntax.l -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_add l1 ls2 =
    set_add (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)) l1 ls2
  
  (** val lset_union : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_union ls1 ls2 =
    set_union (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)) ls1 ls2
  
  (** val lset_inter : LLVMsyntax.ls -> LLVMsyntax.ls -> LLVMsyntax.l set **)
  
  let lset_inter ls1 ls2 =
    set_inter (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)) ls1 ls2
  
  (** val lset_eqb : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_eqb ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> true
      | l0::l1 -> false
  
  (** val lset_neqb : LLVMsyntax.ls -> LLVMsyntax.ls -> bool **)
  
  let lset_neqb ls1 ls2 =
    match lset_inter ls1 ls2 with
      | [] -> false
      | l0::l1 -> true
  
  (** val lset_single : LLVMsyntax.l -> LLVMsyntax.l set **)
  
  let lset_single l0 =
    lset_add l0 lempty_set
  
  (** val lset_mem : LLVMsyntax.l -> LLVMsyntax.ls -> bool **)
  
  let lset_mem l0 ls0 =
    set_mem (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)) l0 ls0
  
  (** val getCmdLoc : LLVMsyntax.cmd -> LLVMsyntax.id **)
  
  let getCmdLoc = function
    | LLVMsyntax.Coq_insn_bop (id0, b, sz0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_fbop (id0, f, f0, v, v0) -> id0
    | LLVMsyntax.Coq_insn_extractvalue (id0, typs, id1, c1) -> id0
    | LLVMsyntax.Coq_insn_insertvalue (id0, typs, id1, typ1, v1, c2) -> id0
    | LLVMsyntax.Coq_insn_malloc (id0, t, v, a) -> id0
    | LLVMsyntax.Coq_insn_free (id0, t, v) -> id0
    | LLVMsyntax.Coq_insn_alloca (id0, t, v, a) -> id0
    | LLVMsyntax.Coq_insn_load (id0, typ1, v1, a) -> id0
    | LLVMsyntax.Coq_insn_store (id0, typ1, v1, v2, a) -> id0
    | LLVMsyntax.Coq_insn_gep (id0, i1, t, v, l0) -> id0
    | LLVMsyntax.Coq_insn_trunc (id0, t, typ1, v1, typ2) -> id0
    | LLVMsyntax.Coq_insn_ext (id0, e, sz1, v1, sz2) -> id0
    | LLVMsyntax.Coq_insn_cast (id0, c, typ1, v1, typ2) -> id0
    | LLVMsyntax.Coq_insn_icmp (id0, cond0, typ0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_fcmp (id0, cond0, typ0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_select (id0, v0, typ0, v1, v2) -> id0
    | LLVMsyntax.Coq_insn_call (id0, n, c, typ0, v0, paraml) -> id0
  
  (** val getTerminatorID : LLVMsyntax.terminator -> LLVMsyntax.id **)
  
  let getTerminatorID = function
    | LLVMsyntax.Coq_insn_return (id0, t, v) -> id0
    | LLVMsyntax.Coq_insn_return_void id0 -> id0
    | LLVMsyntax.Coq_insn_br (id0, v, l1, l2) -> id0
    | LLVMsyntax.Coq_insn_br_uncond (id0, l0) -> id0
    | LLVMsyntax.Coq_insn_unreachable id0 -> id0
  
  (** val getPhiNodeID : LLVMsyntax.phinode -> LLVMsyntax.id **)
  
  let getPhiNodeID = function
    | LLVMsyntax.Coq_insn_phi (id0, t, l0) -> id0
  
  (** val getValueID : LLVMsyntax.value -> LLVMsyntax.id option **)
  
  let getValueID = function
    | LLVMsyntax.Coq_value_id id0 -> Some id0
    | LLVMsyntax.Coq_value_const c -> None
  
  (** val getInsnLoc : LLVMsyntax.insn -> LLVMsyntax.id **)
  
  let getInsnLoc = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeID p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdLoc c
    | LLVMsyntax.Coq_insn_terminator t -> getTerminatorID t
  
  (** val isPhiNodeB : LLVMsyntax.insn -> bool **)
  
  let isPhiNodeB = function
    | LLVMsyntax.Coq_insn_phinode p -> true
    | _ -> false
  
  (** val getCmdID : LLVMsyntax.cmd -> LLVMsyntax.id option **)
  
  let getCmdID = function
    | LLVMsyntax.Coq_insn_bop (id0, b, sz0, v1, v2) -> Some id0
    | LLVMsyntax.Coq_insn_fbop (id0, f, f0, v, v0) -> Some id0
    | LLVMsyntax.Coq_insn_extractvalue (id0, typs, id1, c1) -> Some id0
    | LLVMsyntax.Coq_insn_insertvalue (id0, typs, id1, typ1, v1, c2) -> Some
        id0
    | LLVMsyntax.Coq_insn_malloc (id0, t, v, a) -> Some id0
    | LLVMsyntax.Coq_insn_alloca (id0, t, v, a) -> Some id0
    | LLVMsyntax.Coq_insn_load (id0, typ1, v1, a) -> Some id0
    | LLVMsyntax.Coq_insn_gep (id0, i1, t, v, l0) -> Some id0
    | LLVMsyntax.Coq_insn_trunc (id0, t, typ1, v1, typ2) -> Some id0
    | LLVMsyntax.Coq_insn_ext (id0, e, sz1, v1, sz2) -> Some id0
    | LLVMsyntax.Coq_insn_cast (id0, c, typ1, v1, typ2) -> Some id0
    | LLVMsyntax.Coq_insn_icmp (id0, cond0, typ0, v1, v2) -> Some id0
    | LLVMsyntax.Coq_insn_fcmp (id0, cond0, typ0, v1, v2) -> Some id0
    | LLVMsyntax.Coq_insn_select (id0, v0, typ0, v1, v2) -> Some id0
    | LLVMsyntax.Coq_insn_call (id0, nr, c, typ0, v0, paraml) ->
        if nr then None else Some id0
    | _ -> None
  
  (** val getCmdsIDs : LLVMsyntax.cmds -> AtomImpl.atom list **)
  
  let rec getCmdsIDs = function
    | [] -> []
    | c::cs' ->
        (match getCmdID c with
           | Some id1 -> id1::(getCmdsIDs cs')
           | None -> getCmdsIDs cs')
  
  (** val getPhiNodesIDs : LLVMsyntax.phinodes -> AtomImpl.atom list **)
  
  let rec getPhiNodesIDs = function
    | [] -> []
    | p::ps' -> (getPhiNodeID p)::(getPhiNodesIDs ps')
  
  (** val getBlockIDs : LLVMsyntax.block -> AtomImpl.atom list **)
  
  let getBlockIDs = function
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t) ->
        app (getPhiNodesIDs ps) (getCmdsIDs cs)
  
  (** val getArgsIDs : LLVMsyntax.args -> AtomImpl.atom list **)
  
  let rec getArgsIDs = function
    | [] -> []
    | p::la' -> let p0,id1 = p in id1::(getArgsIDs la')
  
  (** val getInsnID : LLVMsyntax.insn -> LLVMsyntax.id option **)
  
  let getInsnID = function
    | LLVMsyntax.Coq_insn_phinode p -> Some (getPhiNodeID p)
    | LLVMsyntax.Coq_insn_cmd c -> getCmdID c
    | LLVMsyntax.Coq_insn_terminator t -> None
  
  (** val mgetoffset_aux :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_Z list -> coq_Z ->
      (coq_Z*LLVMsyntax.typ) option **)
  
  let rec mgetoffset_aux = Llvmcaml.TargetData.mgetoffset_aux
  
  (** val mgetoffset :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> coq_Z list ->
      (coq_Z*LLVMsyntax.typ) option **)
  
  let mgetoffset = Llvmcaml.TargetData.mgetoffset
  
  (** val intConsts2Nats :
      LLVMtd.coq_TargetData -> LLVMsyntax.list_const -> coq_Z list option **)
  
  let rec intConsts2Nats tD = function
    | LLVMsyntax.Nil_list_const -> Some []
    | LLVMsyntax.Cons_list_const (c, lv') ->
        (match c with
           | LLVMsyntax.Coq_const_int (sz0, n) ->
               if LLVMsyntax.Size.dec sz0 LLVMsyntax.Size.coq_ThirtyTwo
               then (match intConsts2Nats tD lv' with
                       | Some ns -> Some ((LLVMsyntax.INTEGER.to_Z n)::ns)
                       | None -> None)
               else None
           | _ -> None)
  
  (** val getSubTypFromConstIdxs :
      LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let rec getSubTypFromConstIdxs idxs t =
    match idxs with
      | LLVMsyntax.Nil_list_const -> Some t
      | LLVMsyntax.Cons_list_const (idx, idxs') ->
          (match t with
             | LLVMsyntax.Coq_typ_array (sz0, t') ->
                 getSubTypFromConstIdxs idxs' t'
             | LLVMsyntax.Coq_typ_struct lt ->
                 (match idx with
                    | LLVMsyntax.Coq_const_int (sz0, i0) ->
                        (match LLVMsyntax.nth_list_typ
                                 (LLVMsyntax.INTEGER.to_nat i0) lt with
                           | Some t' -> getSubTypFromConstIdxs idxs' t'
                           | None -> None)
                    | _ -> None)
             | _ -> None)
  
  (** val getConstGEPTyp :
      LLVMsyntax.list_const -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getConstGEPTyp idxs t =
    match idxs with
      | LLVMsyntax.Nil_list_const -> None
      | LLVMsyntax.Cons_list_const (idx, idxs') ->
          (match t with
             | LLVMsyntax.Coq_typ_pointer t0 ->
                 (match getSubTypFromConstIdxs idxs' t0 with
                    | Some t' -> Some (LLVMsyntax.Coq_typ_pointer t')
                    | None -> None)
             | _ -> None)
  
  (** val getSubTypFromValueIdxs :
      LLVMsyntax.list_sz_value -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let rec getSubTypFromValueIdxs idxs t =
    match idxs with
      | LLVMsyntax.Nil_list_sz_value -> Some t
      | LLVMsyntax.Cons_list_sz_value (s, idx, idxs') ->
          (match t with
             | LLVMsyntax.Coq_typ_array (sz0, t') ->
                 getSubTypFromValueIdxs idxs' t'
             | LLVMsyntax.Coq_typ_struct lt ->
                 (match idx with
                    | LLVMsyntax.Coq_value_id i0 -> None
                    | LLVMsyntax.Coq_value_const c ->
                        (match c with
                           | LLVMsyntax.Coq_const_int (
                               sz0, i0) ->
                               (match LLVMsyntax.nth_list_typ
                                        (LLVMsyntax.INTEGER.to_nat i0) lt with
                                  | Some t' ->
                                      getSubTypFromValueIdxs idxs' t'
                                  | None -> None)
                           | _ -> None))
             | _ -> None)
  
  (** val getGEPTyp :
      LLVMsyntax.list_sz_value -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getGEPTyp idxs t =
    match idxs with
      | LLVMsyntax.Nil_list_sz_value -> None
      | LLVMsyntax.Cons_list_sz_value (s, idx, idxs') ->
          (match getSubTypFromValueIdxs idxs' t with
             | Some t' -> Some (LLVMsyntax.Coq_typ_pointer t')
             | None -> None)
  
  (** val getCmdTyp : LLVMsyntax.cmd -> LLVMsyntax.typ option **)
  
  let getCmdTyp = function
    | LLVMsyntax.Coq_insn_bop (i1, b, sz0, v, v0) -> Some
        (LLVMsyntax.Coq_typ_int sz0)
    | LLVMsyntax.Coq_insn_fbop (i1, f, ft, v, v0) -> Some
        (LLVMsyntax.Coq_typ_floatpoint ft)
    | LLVMsyntax.Coq_insn_extractvalue (i1, typ0, v, idxs) ->
        getSubTypFromConstIdxs idxs typ0
    | LLVMsyntax.Coq_insn_insertvalue (i1, typ0, v, t, v0, l0) -> Some typ0
    | LLVMsyntax.Coq_insn_malloc (i1, typ0, v, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_free (i1, typ0, v) -> Some LLVMsyntax.Coq_typ_void
    | LLVMsyntax.Coq_insn_alloca (i1, typ0, v, a) -> Some
        (LLVMsyntax.Coq_typ_pointer typ0)
    | LLVMsyntax.Coq_insn_load (i1, typ0, v, a) -> Some typ0
    | LLVMsyntax.Coq_insn_store (i1, t, v, v0, a) -> Some
        LLVMsyntax.Coq_typ_void
    | LLVMsyntax.Coq_insn_gep (i1, i2, typ0, v, idxs) -> getGEPTyp idxs typ0
    | LLVMsyntax.Coq_insn_trunc (i1, t, t0, v, typ0) -> Some typ0
    | LLVMsyntax.Coq_insn_ext (i1, e, t, v, typ2) -> Some typ2
    | LLVMsyntax.Coq_insn_cast (i1, c, t, v, typ0) -> Some typ0
    | LLVMsyntax.Coq_insn_select (i1, v, typ0, v0, v1) -> Some typ0
    | LLVMsyntax.Coq_insn_call (i1, n, c, typ0, v, p) ->
        if n
        then Some LLVMsyntax.Coq_typ_void
        else (match typ0 with
                | LLVMsyntax.Coq_typ_function (t, l0, v0) -> Some t
                | _ -> None)
    | _ -> Some (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
  
  (** val getTerminatorTyp : LLVMsyntax.terminator -> LLVMsyntax.typ **)
  
  let getTerminatorTyp = function
    | LLVMsyntax.Coq_insn_return (i1, typ0, v) -> typ0
    | _ -> LLVMsyntax.Coq_typ_void
  
  (** val getPhiNodeTyp : LLVMsyntax.phinode -> LLVMsyntax.typ **)
  
  let getPhiNodeTyp = function
    | LLVMsyntax.Coq_insn_phi (i1, typ0, l0) -> typ0
  
  (** val getInsnTyp : LLVMsyntax.insn -> LLVMsyntax.typ option **)
  
  let getInsnTyp = function
    | LLVMsyntax.Coq_insn_phinode p -> Some (getPhiNodeTyp p)
    | LLVMsyntax.Coq_insn_cmd c -> getCmdTyp c
    | LLVMsyntax.Coq_insn_terminator t -> Some (getTerminatorTyp t)
  
  (** val getPointerEltTyp : LLVMsyntax.typ -> LLVMsyntax.typ option **)
  
  let getPointerEltTyp = function
    | LLVMsyntax.Coq_typ_pointer t' -> Some t'
    | _ -> None
  
  (** val getValueIDs : LLVMsyntax.value -> LLVMsyntax.ids **)
  
  let getValueIDs v =
    match getValueID v with
      | Some id0 -> id0::[]
      | None -> []
  
  (** val values2ids : LLVMsyntax.value list -> LLVMsyntax.ids **)
  
  let rec values2ids = function
    | [] -> []
    | v::vs' ->
        (match v with
           | LLVMsyntax.Coq_value_id id0 -> id0::(values2ids vs')
           | LLVMsyntax.Coq_value_const c -> values2ids vs')
  
  (** val getParamsOperand : LLVMsyntax.params -> LLVMsyntax.ids **)
  
  let getParamsOperand lp =
    let l0,vs = split lp in values2ids vs
  
  (** val list_prj1 : ('a1*'a2) list -> 'a1 list **)
  
  let rec list_prj1 = function
    | [] -> []
    | p::ls' -> let x,y = p in x::(list_prj1 ls')
  
  (** val list_prj2 : ('a1*'a2) list -> 'a2 list **)
  
  let rec list_prj2 = function
    | [] -> []
    | p::ls' -> let x,y = p in y::(list_prj2 ls')
  
  (** val getCmdOperands : LLVMsyntax.cmd -> LLVMsyntax.ids **)
  
  let getCmdOperands = function
    | LLVMsyntax.Coq_insn_bop (i1, b, s, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_fbop (i1, f, f0, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_extractvalue (i1, t, v, l0) -> getValueIDs v
    | LLVMsyntax.Coq_insn_insertvalue (i1, t, v1, t0, v2, l0) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_malloc (i1, t, v, a) -> getValueIDs v
    | LLVMsyntax.Coq_insn_free (i1, t, v) -> getValueIDs v
    | LLVMsyntax.Coq_insn_alloca (i1, t, v, a) -> getValueIDs v
    | LLVMsyntax.Coq_insn_load (i1, t, v, a) -> getValueIDs v
    | LLVMsyntax.Coq_insn_store (i1, t, v1, v2, a) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_gep (i1, i2, t, v, vs) ->
        app (getValueIDs v)
          (values2ids (LLVMsyntax.map_list_sz_value (fun x v0 -> v0) vs))
    | LLVMsyntax.Coq_insn_trunc (i1, t, t0, v, t1) -> getValueIDs v
    | LLVMsyntax.Coq_insn_ext (i1, e, t, v1, typ2) -> getValueIDs v1
    | LLVMsyntax.Coq_insn_cast (i1, c, t, v, t0) -> getValueIDs v
    | LLVMsyntax.Coq_insn_icmp (i1, c, t, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_fcmp (i1, f, f0, v1, v2) ->
        app (getValueIDs v1) (getValueIDs v2)
    | LLVMsyntax.Coq_insn_select (i1, v0, t, v1, v2) ->
        app (getValueIDs v0) (app (getValueIDs v1) (getValueIDs v2))
    | LLVMsyntax.Coq_insn_call (i1, n, c, t, v0, lp) ->
        app (getValueIDs v0) (getParamsOperand lp)
  
  (** val getTerminatorOperands : LLVMsyntax.terminator -> LLVMsyntax.ids **)
  
  let getTerminatorOperands = function
    | LLVMsyntax.Coq_insn_return (i1, t, v) -> getValueIDs v
    | LLVMsyntax.Coq_insn_br (i1, v, l0, l1) -> getValueIDs v
    | _ -> []
  
  (** val getPhiNodeOperands : LLVMsyntax.phinode -> LLVMsyntax.ids **)
  
  let getPhiNodeOperands = function
    | LLVMsyntax.Coq_insn_phi (i1, t, ls0) ->
        values2ids (list_prj1 (LLVMsyntax.unmake_list_value_l ls0))
  
  (** val getInsnOperands : LLVMsyntax.insn -> LLVMsyntax.ids **)
  
  let getInsnOperands = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeOperands p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdOperands c
    | LLVMsyntax.Coq_insn_terminator t -> getTerminatorOperands t
  
  (** val getCmdLabels : LLVMsyntax.cmd -> LLVMsyntax.ls **)
  
  let getCmdLabels i0 =
    []
  
  (** val getTerminatorLabels : LLVMsyntax.terminator -> LLVMsyntax.ls **)
  
  let getTerminatorLabels = function
    | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) -> l1::(l2::[])
    | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> l0::[]
    | _ -> []
  
  (** val getPhiNodeLabels : LLVMsyntax.phinode -> LLVMsyntax.ls **)
  
  let getPhiNodeLabels = function
    | LLVMsyntax.Coq_insn_phi (i1, t, ls0) ->
        list_prj2 (LLVMsyntax.unmake_list_value_l ls0)
  
  (** val getInsnLabels : LLVMsyntax.insn -> LLVMsyntax.ls **)
  
  let getInsnLabels = function
    | LLVMsyntax.Coq_insn_phinode p -> getPhiNodeLabels p
    | LLVMsyntax.Coq_insn_cmd c -> getCmdLabels c
    | LLVMsyntax.Coq_insn_terminator tmn -> getTerminatorLabels tmn
  
  (** val args2Typs : LLVMsyntax.args -> LLVMsyntax.list_typ **)
  
  let rec args2Typs = function
    | [] -> LLVMsyntax.Nil_list_typ
    | p::la' ->
        let p0,id0 = p in
        let t,a = p0 in LLVMsyntax.Cons_list_typ (t, (args2Typs la'))
  
  (** val getFheaderTyp : LLVMsyntax.fheader -> LLVMsyntax.typ **)
  
  let getFheaderTyp = function
    | LLVMsyntax.Coq_fheader_intro (f, t, i0, la, va) ->
        LLVMsyntax.Coq_typ_function (t, (args2Typs la), va)
  
  (** val getFdecTyp : LLVMsyntax.fdec -> LLVMsyntax.typ **)
  
  let getFdecTyp fdec0 =
    getFheaderTyp fdec0
  
  (** val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
  
  let getFdefTyp = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, b) -> getFheaderTyp fheader0
  
  (** val getBindingTyp : LLVMsyntax.id_binding -> LLVMsyntax.typ option **)
  
  let getBindingTyp = function
    | LLVMsyntax.Coq_id_binding_none -> None
    | LLVMsyntax.Coq_id_binding_cmd i0 -> getCmdTyp i0
    | LLVMsyntax.Coq_id_binding_phinode i0 -> Some (getPhiNodeTyp i0)
    | LLVMsyntax.Coq_id_binding_terminator i0 -> Some (getTerminatorTyp i0)
    | LLVMsyntax.Coq_id_binding_gvar g ->
        (match g with
           | LLVMsyntax.Coq_gvar_intro (i0, l0, g0, t, c, a) -> Some
               (LLVMsyntax.Coq_typ_pointer t)
           | LLVMsyntax.Coq_gvar_external (i0, g0, t) -> Some
               (LLVMsyntax.Coq_typ_pointer t))
    | LLVMsyntax.Coq_id_binding_fdec fdec0 -> Some (getFdecTyp fdec0)
    | LLVMsyntax.Coq_id_binding_arg a ->
        let p,id0 = a in let t,a0 = p in Some t
  
  (** val getCmdsFromBlock : LLVMsyntax.block -> LLVMsyntax.cmds **)
  
  let getCmdsFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, p, li, t) -> li
  
  (** val getPhiNodesFromBlock : LLVMsyntax.block -> LLVMsyntax.phinodes **)
  
  let getPhiNodesFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, li, c, t) -> li
  
  (** val getTerminatorFromBlock :
      LLVMsyntax.block -> LLVMsyntax.terminator **)
  
  let getTerminatorFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) -> t
  
  (** val getFheaderID : LLVMsyntax.fheader -> LLVMsyntax.id **)
  
  let getFheaderID = function
    | LLVMsyntax.Coq_fheader_intro (f, t, id0, a, v) -> id0
  
  (** val getFdecID : LLVMsyntax.fdec -> LLVMsyntax.id **)
  
  let getFdecID fd =
    getFheaderID fd
  
  (** val getFdefID : LLVMsyntax.fdef -> LLVMsyntax.id **)
  
  let getFdefID = function
    | LLVMsyntax.Coq_fdef_intro (fh, b) -> getFheaderID fh
  
  (** val getLabelViaIDFromList :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let rec getLabelViaIDFromList ls0 branch =
    match ls0 with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l0, ls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id0 ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 branch
                 then Some l0
                 else getLabelViaIDFromList ls' branch
             | LLVMsyntax.Coq_value_const c ->
                 getLabelViaIDFromList ls' branch)
  
  (** val getLabelViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let getLabelViaIDFromPhiNode phi branch =
    let LLVMsyntax.Coq_insn_phi (i0, t, ls0) = phi in
    getLabelViaIDFromList ls0 branch
  
  (** val getLabelsFromIdls : LLVMsyntax.list_value_l -> LLVMsyntax.ls **)
  
  let rec getLabelsFromIdls = function
    | LLVMsyntax.Nil_list_value_l -> lempty_set
    | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
        lset_add l0 (getLabelsFromIdls idls')
  
  (** val getLabelsFromPhiNode : LLVMsyntax.phinode -> LLVMsyntax.ls **)
  
  let getLabelsFromPhiNode = function
    | LLVMsyntax.Coq_insn_phi (i0, t, ls0) -> getLabelsFromIdls ls0
  
  (** val getLabelsFromPhiNodes :
      LLVMsyntax.phinode list -> LLVMsyntax.ls **)
  
  let rec getLabelsFromPhiNodes = function
    | [] -> lempty_set
    | phi::phis' ->
        lset_union (getLabelsFromPhiNode phi) (getLabelsFromPhiNodes phis')
  
  (** val getIDLabelsFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.list_value_l **)
  
  let getIDLabelsFromPhiNode = function
    | LLVMsyntax.Coq_insn_phi (i0, t, idls) -> idls
  
  (** val getLabelViaIDFromIDLabels :
      LLVMsyntax.list_value_l -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let rec getLabelViaIDFromIDLabels idls id0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l0, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
                 then Some l0
                 else getLabelViaIDFromIDLabels idls' id0
             | LLVMsyntax.Coq_value_const c ->
                 getLabelViaIDFromIDLabels idls' id0)
  
  (** val _getLabelViaIDPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let _getLabelViaIDPhiNode p id0 =
    let LLVMsyntax.Coq_insn_phi (i0, t, ls0) = p in
    getLabelViaIDFromIDLabels ls0 id0
  
  (** val getLabelViaIDPhiNode :
      LLVMsyntax.insn -> LLVMsyntax.id -> LLVMsyntax.l option **)
  
  let getLabelViaIDPhiNode phi id0 =
    match phi with
      | LLVMsyntax.Coq_insn_phinode p -> _getLabelViaIDPhiNode p id0
      | _ -> None
  
  (** val getReturnTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
  
  let getReturnTyp = function
    | LLVMsyntax.Coq_fdef_intro (f, b) ->
        let LLVMsyntax.Coq_fheader_intro (f0, t, i0, a, v) = f in t
  
  (** val getGvarID : LLVMsyntax.gvar -> LLVMsyntax.id **)
  
  let getGvarID = function
    | LLVMsyntax.Coq_gvar_intro (id0, l0, g0, t, c, a) -> id0
    | LLVMsyntax.Coq_gvar_external (id0, g0, t) -> id0
  
  (** val getCalledValue : LLVMsyntax.insn -> LLVMsyntax.value option **)
  
  let getCalledValue = function
    | LLVMsyntax.Coq_insn_cmd c ->
        (match c with
           | LLVMsyntax.Coq_insn_call (i1, n, c0, t, v0, p) -> Some v0
           | _ -> None)
    | _ -> None
  
  (** val getCalledValueID : LLVMsyntax.insn -> LLVMsyntax.id option **)
  
  let getCalledValueID i0 =
    match getCalledValue i0 with
      | Some v -> getValueID v
      | None -> None
  
  (** val getCallerReturnID : LLVMsyntax.cmd -> LLVMsyntax.id option **)
  
  let getCallerReturnID = function
    | LLVMsyntax.Coq_insn_call (id0, n, c, t, v, p) ->
        if n then None else Some id0
    | _ -> None
  
  (** val getValueViaLabelFromValuels :
      LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.value option **)
  
  let rec getValueViaLabelFromValuels vls l0 =
    match vls with
      | LLVMsyntax.Nil_list_value_l -> None
      | LLVMsyntax.Cons_list_value_l (v, l1, vls') ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) l1 l0
          then Some v
          else getValueViaLabelFromValuels vls' l0
  
  (** val getValueViaBlockFromValuels :
      LLVMsyntax.list_value_l -> LLVMsyntax.block -> LLVMsyntax.value option **)
  
  let getValueViaBlockFromValuels vls = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) ->
        getValueViaLabelFromValuels vls l0
  
  (** val getValueViaBlockFromPHINode :
      LLVMsyntax.phinode -> LLVMsyntax.block -> LLVMsyntax.value option **)
  
  let getValueViaBlockFromPHINode i0 b =
    let LLVMsyntax.Coq_insn_phi (i1, t, vls) = i0 in
    getValueViaBlockFromValuels vls b
  
  (** val getPHINodesFromBlock :
      LLVMsyntax.block -> LLVMsyntax.phinode list **)
  
  let getPHINodesFromBlock = function
    | LLVMsyntax.Coq_block_intro (l0, lp, c, t) -> lp
  
  (** val getEntryBlock : LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getEntryBlock = function
    | LLVMsyntax.Coq_fdef_intro (f, b0) ->
        (match b0 with
           | [] -> None
           | b::l0 -> Some b)
  
  (** val getEntryCmds : LLVMsyntax.block -> LLVMsyntax.cmds **)
  
  let getEntryCmds = function
    | LLVMsyntax.Coq_block_intro (l0, p, lc, t) -> lc
  
  (** val floating_point_order :
      LLVMsyntax.floating_point -> LLVMsyntax.floating_point -> bool **)
  
  let floating_point_order fp1 fp2 =
    match fp1 with
      | LLVMsyntax.Coq_fp_float ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_float -> false
             | _ -> true)
      | LLVMsyntax.Coq_fp_double ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_float -> false
             | LLVMsyntax.Coq_fp_double -> false
             | _ -> true)
      | LLVMsyntax.Coq_fp_x86_fp80 ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_fp128 -> true
             | LLVMsyntax.Coq_fp_ppc_fp128 -> true
             | _ -> false)
      | _ -> false
  
  (** val wf_fcond : LLVMsyntax.fcond -> bool **)
  
  let wf_fcond = function
    | LLVMsyntax.Coq_fcond_ord -> false
    | LLVMsyntax.Coq_fcond_uno -> false
    | _ -> true
  
  (** val lookupCmdViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.cmd option **)
  
  let rec lookupCmdViaIDFromCmds li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          if AtomImpl.eq_atom_dec id0 (getCmdLoc i0)
          then Some i0
          else lookupCmdViaIDFromCmds li' id0
  
  (** val lookupPhiNodeViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.phinode option **)
  
  let rec lookupPhiNodeViaIDFromPhiNodes li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) 
               (getPhiNodeID i0) id0
          then Some i0
          else lookupPhiNodeViaIDFromPhiNodes li' id0
  
  (** val lookupInsnViaIDFromBlock :
      LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.insn option **)
  
  let lookupInsnViaIDFromBlock b id0 =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t) = b in
    (match lookupPhiNodeViaIDFromPhiNodes ps id0 with
       | Some re -> Some (LLVMsyntax.Coq_insn_phinode re)
       | None ->
           (match lookupCmdViaIDFromCmds cs id0 with
              | Some c -> Some (LLVMsyntax.Coq_insn_cmd c)
              | None -> None))
  
  (** val lookupInsnViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.insn option **)
  
  let rec lookupInsnViaIDFromBlocks lb id0 =
    match lb with
      | [] -> None
      | b::lb' ->
          (match lookupInsnViaIDFromBlock b id0 with
             | Some i0 -> Some i0
             | None -> lookupInsnViaIDFromBlocks lb' id0)
  
  (** val lookupInsnViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.insn option **)
  
  let lookupInsnViaIDFromFdef f id0 =
    let LLVMsyntax.Coq_fdef_intro (f0, bs) = f in
    lookupInsnViaIDFromBlocks bs id0
  
  (** val lookupArgViaIDFromArgs :
      LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.arg option **)
  
  let rec lookupArgViaIDFromArgs la id0 =
    match la with
      | [] -> None
      | p::la' ->
          let p0,id' = p in
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id' id0
          then Some (p0,id')
          else lookupArgViaIDFromArgs la' id0
  
  (** val lookupBlockViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.block option **)
  
  let rec lookupBlockViaIDFromBlocks lb id1 =
    match lb with
      | [] -> None
      | b::lb' ->
          if in_dec (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)) id1
               (getBlockIDs b)
          then Some b
          else lookupBlockViaIDFromBlocks lb' id1
  
  (** val lookupBlockViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.block option **)
  
  let lookupBlockViaIDFromFdef fd id0 =
    let LLVMsyntax.Coq_fdef_intro (fh, lb) = fd in
    lookupBlockViaIDFromBlocks lb id0
  
  (** val lookupFdecViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromProduct p i0 =
    match p with
      | LLVMsyntax.Coq_product_fdec fd ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) (getFdecID fd) i0
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdecViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdecViaIDFromProduct p i0 with
             | Some fd -> Some fd
             | None -> lookupFdecViaIDFromProducts lp' i0)
  
  (** val lookupFdecViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromModule m i0 =
    let LLVMsyntax.Coq_module_intro (os, dts, ps) = m in
    lookupFdecViaIDFromProducts ps i0
  
  (** val lookupFdecViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromModules lm i0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupFdecViaIDFromModule m i0 with
             | Some fd -> Some fd
             | None -> lookupFdecViaIDFromModules lm' i0)
  
  (** val lookupFdecViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromSystem s i0 =
    lookupFdecViaIDFromModules s i0
  
  (** val lookupFdefViaIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromProduct p i0 =
    match p with
      | LLVMsyntax.Coq_product_fdef fd ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) (getFdefID fd) i0
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdefViaIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let rec lookupFdefViaIDFromProducts lp i0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdefViaIDFromProduct p i0 with
             | Some fd -> Some fd
             | None -> lookupFdefViaIDFromProducts lp' i0)
  
  (** val lookupFdefViaIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromModule m i0 =
    let LLVMsyntax.Coq_module_intro (os, dts, ps) = m in
    lookupFdefViaIDFromProducts ps i0
  
  (** val lookupFdefViaIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let rec lookupFdefViaIDFromModules lm i0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupFdefViaIDFromModule m i0 with
             | Some fd -> Some fd
             | None -> lookupFdefViaIDFromModules lm' i0)
  
  (** val lookupFdefViaIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.fdef option **)
  
  let lookupFdefViaIDFromSystem s i0 =
    lookupFdefViaIDFromModules s i0
  
  (** val lookupTypViaIDFromCmd :
      LLVMsyntax.cmd -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromCmd i0 id0 =
    match getCmdTyp i0 with
      | Some t ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 (getCmdLoc i0)
          then Some t
          else None
      | None -> None
  
  (** val lookupTypViaIDFromCmds :
      LLVMsyntax.cmds -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromCmds li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          (match lookupTypViaIDFromCmd i0 id0 with
             | Some t -> Some t
             | None -> lookupTypViaIDFromCmds li' id0)
  
  (** val lookupTypViaIDFromPhiNode :
      LLVMsyntax.phinode -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromPhiNode i0 id0 =
    if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 (getPhiNodeID i0)
    then Some (getPhiNodeTyp i0)
    else None
  
  (** val lookupTypViaIDFromPhiNodes :
      LLVMsyntax.phinodes -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromPhiNodes li id0 =
    match li with
      | [] -> None
      | i0::li' ->
          (match lookupTypViaIDFromPhiNode i0 id0 with
             | Some t -> Some t
             | None -> lookupTypViaIDFromPhiNodes li' id0)
  
  (** val lookupTypViaIDFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromTerminator i0 id0 =
    if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 (getTerminatorID i0)
    then Some (getTerminatorTyp i0)
    else None
  
  (** val lookupTypViaIDFromBlock :
      LLVMsyntax.block -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromBlock b id0 =
    let LLVMsyntax.Coq_block_intro (l0, ps, cs, t) = b in
    (match lookupTypViaIDFromPhiNodes ps id0 with
       | Some t0 -> Some t0
       | None ->
           (match lookupTypViaIDFromCmds cs id0 with
              | Some t0 -> Some t0
              | None -> lookupTypViaIDFromTerminator t id0))
  
  (** val lookupTypViaIDFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromBlocks lb id0 =
    match lb with
      | [] -> None
      | b::lb' ->
          (match lookupTypViaIDFromBlock b id0 with
             | Some t -> Some t
             | None -> lookupTypViaIDFromBlocks lb' id0)
  
  (** val lookupTypViaIDFromArgs :
      LLVMsyntax.args -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaIDFromArgs la id0 =
    match la with
      | [] -> None
      | p::la' ->
          let p0,id1 = p in
          let t1,a = p0 in
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
          then Some t1
          else lookupTypViaIDFromArgs la' id0
  
  (** val lookupTypViaIDFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaIDFromFdef fd id0 =
    let LLVMsyntax.Coq_fdef_intro (f, lb) = fd in
    let LLVMsyntax.Coq_fheader_intro (f0, t, i0, la, v) = f in
    (match lookupTypViaIDFromArgs la id0 with
       | Some t0 -> Some t0
       | None -> lookupTypViaIDFromBlocks lb id0)
  
  (** val lookupTypViaGIDFromProduct :
      LLVMsyntax.product -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaGIDFromProduct p id0 =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          (match g with
             | LLVMsyntax.Coq_gvar_intro (id1, l0, spec, t, c, a) ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
                 then Some t
                 else None
             | LLVMsyntax.Coq_gvar_external (id1, spec, t) ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
                 then Some t
                 else None)
      | _ -> None
  
  (** val lookupTypViaGIDFromProducts :
      LLVMsyntax.products -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaGIDFromProducts lp id0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupTypViaGIDFromProduct p id0 with
             | Some t -> Some t
             | None -> lookupTypViaGIDFromProducts lp' id0)
  
  (** val lookupTypViaGIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaGIDFromModule m id0 =
    let LLVMsyntax.Coq_module_intro (os, dts, ps) = m in
    lookupTypViaGIDFromProducts ps id0
  
  (** val lookupTypViaGIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaGIDFromModules lm id0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupTypViaGIDFromModule m id0 with
             | Some t -> Some t
             | None -> lookupTypViaGIDFromModules lm' id0)
  
  (** val lookupTypViaGIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaGIDFromSystem s id0 =
    lookupTypViaGIDFromModules s id0
  
  (** val lookupTypViaTIDFromNamedts :
      LLVMsyntax.namedts -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaTIDFromNamedts nts id0 =
    match nts with
      | [] -> None
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id1, typ1) = n in
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id1
          then Some typ1
          else lookupTypViaTIDFromNamedts nts' id0
  
  (** val lookupTypViaTIDFromModule :
      LLVMsyntax.coq_module -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaTIDFromModule m id0 =
    let LLVMsyntax.Coq_module_intro (os, dts, ps) = m in
    lookupTypViaTIDFromNamedts dts id0
  
  (** val lookupTypViaTIDFromModules :
      LLVMsyntax.modules -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let rec lookupTypViaTIDFromModules lm id0 =
    match lm with
      | [] -> None
      | m::lm' ->
          (match lookupTypViaTIDFromModule m id0 with
             | Some t -> Some t
             | None -> lookupTypViaTIDFromModules lm' id0)
  
  (** val lookupTypViaTIDFromSystem :
      LLVMsyntax.system -> LLVMsyntax.id -> LLVMsyntax.typ option **)
  
  let lookupTypViaTIDFromSystem s id0 =
    lookupTypViaTIDFromModules s id0
  
  type l2block = (LLVMsyntax.l*LLVMsyntax.block) list
  
  (** val genLabel2Block_block : LLVMsyntax.block -> l2block **)
  
  let genLabel2Block_block b = match b with
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) -> (l0,b)::[]
  
  (** val genLabel2Block_blocks : LLVMsyntax.blocks -> l2block **)
  
  let rec genLabel2Block_blocks = function
    | [] -> []
    | b::bs' -> app (genLabel2Block_block b) (genLabel2Block_blocks bs')
  
  (** val genLabel2Block_fdef : LLVMsyntax.fdef -> l2block **)
  
  let genLabel2Block_fdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        genLabel2Block_blocks blocks0
  
  (** val genLabel2Block_product : LLVMsyntax.product -> l2block **)
  
  let rec genLabel2Block_product = function
    | LLVMsyntax.Coq_product_fdef f -> genLabel2Block_fdef f
    | _ -> []
  
  (** val genLabel2Block_products : LLVMsyntax.products -> l2block **)
  
  let rec genLabel2Block_products = function
    | [] -> []
    | p::ps' -> app (genLabel2Block_product p) (genLabel2Block_products ps')
  
  (** val genLabel2Block : LLVMsyntax.coq_module -> l2block **)
  
  let genLabel2Block = function
    | LLVMsyntax.Coq_module_intro (os, dts, ps) -> genLabel2Block_products ps
  
  (** val getNonEntryOfFdef : LLVMsyntax.fdef -> LLVMsyntax.blocks **)
  
  let getNonEntryOfFdef = function
    | LLVMsyntax.Coq_fdef_intro (fheader0, blocks0) ->
        (match blocks0 with
           | [] -> []
           | b::blocks' -> blocks')
  
  (** val lookupBlockViaLabelFromBlocks :
      LLVMsyntax.blocks -> LLVMsyntax.l -> LLVMsyntax.block option **)
  
  let lookupBlockViaLabelFromBlocks bs l0 =
    lookupAL (genLabel2Block_blocks bs) l0
  
  (** val lookupBlockViaLabelFromFdef :
      LLVMsyntax.fdef -> LLVMsyntax.l -> LLVMsyntax.block option **)
  
  let lookupBlockViaLabelFromFdef f l0 =
    lookupAL (genLabel2Block_fdef f) l0
  
  (** val getLabelsFromBlocks : LLVMsyntax.blocks -> LLVMsyntax.ls **)
  
  let rec getLabelsFromBlocks = function
    | [] -> lempty_set
    | b::lb' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t) = b in
        lset_add l0 (getLabelsFromBlocks lb')
  
  (** val update_udb :
      LLVMsyntax.usedef_block -> LLVMsyntax.l -> LLVMsyntax.l ->
      LLVMsyntax.usedef_block **)
  
  let update_udb udb lu ld =
    let ls0 = match lookupAL udb ld with
                | Some ls0 -> ls0
                | None -> [] in
    if in_dec l_dec lu ls0 then udb else updateAddAL udb ld (lu::ls0)
  
  (** val genBlockUseDef_block :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_block b udb =
    let LLVMsyntax.Coq_block_intro (l0, p, c, tmn2) = b in
    (match tmn2 with
       | LLVMsyntax.Coq_insn_br (i0, v, l1, l2) ->
           update_udb (update_udb udb l0 l2) l0 l1
       | LLVMsyntax.Coq_insn_br_uncond (i0, l1) -> update_udb udb l0 l1
       | _ -> udb)
  
  (** val genBlockUseDef_blocks :
      LLVMsyntax.block list -> LLVMsyntax.usedef_block ->
      LLVMsyntax.usedef_block **)
  
  let rec genBlockUseDef_blocks bs udb =
    match bs with
      | [] -> udb
      | b::bs' -> genBlockUseDef_blocks bs' (genBlockUseDef_block b udb)
  
  (** val genBlockUseDef_fdef :
      LLVMsyntax.fdef -> LLVMsyntax.usedef_block **)
  
  let genBlockUseDef_fdef = function
    | LLVMsyntax.Coq_fdef_intro (f, lb2) -> genBlockUseDef_blocks lb2 []
  
  (** val getBlockLabel : LLVMsyntax.block -> LLVMsyntax.l **)
  
  let getBlockLabel = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) -> l0
  
  (** val getBlockUseDef :
      LLVMsyntax.usedef_block -> LLVMsyntax.block -> LLVMsyntax.l list option **)
  
  let getBlockUseDef udb b =
    lookupAL udb (getBlockLabel b)
  
  (** val getTerminator : LLVMsyntax.block -> LLVMsyntax.terminator **)
  
  let getTerminator = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) -> t
  
  (** val getLabelsFromSwitchCases :
      (LLVMsyntax.const*LLVMsyntax.l) list -> LLVMsyntax.ls **)
  
  let rec getLabelsFromSwitchCases = function
    | [] -> lempty_set
    | p::cs' -> let c,l0 = p in lset_add l0 (getLabelsFromSwitchCases cs')
  
  (** val getLabelsFromTerminator :
      LLVMsyntax.terminator -> LLVMsyntax.ls **)
  
  let getLabelsFromTerminator = function
    | LLVMsyntax.Coq_insn_br (i1, v, l1, l2) ->
        lset_add l1 (lset_add l2 lempty_set)
    | LLVMsyntax.Coq_insn_br_uncond (i1, l0) -> lset_add l0 lempty_set
    | _ -> empty_set
  
  (** val getBlocksFromLabels :
      LLVMsyntax.ls -> l2block -> LLVMsyntax.blocks **)
  
  let rec getBlocksFromLabels ls0 l2b =
    match ls0 with
      | [] -> []
      | l0::ls0' ->
          (match lookupAL l2b l0 with
             | Some b -> b::(getBlocksFromLabels ls0' l2b)
             | None -> getBlocksFromLabels ls0' l2b)
  
  (** val succOfBlock :
      LLVMsyntax.block -> LLVMsyntax.coq_module -> LLVMsyntax.blocks **)
  
  let succOfBlock b m =
    getBlocksFromLabels (getLabelsFromTerminator (getTerminator b))
      (genLabel2Block m)
  
  (** val predOfBlock :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> LLVMsyntax.l list **)
  
  let predOfBlock b udb =
    match lookupAL udb (getBlockLabel b) with
      | Some re -> re
      | None -> []
  
  (** val hasSinglePredecessor :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool **)
  
  let hasSinglePredecessor b udb =
    match predOfBlock b udb with
      | [] -> false
      | l0::l1 -> (match l1 with
                     | [] -> true
                     | l2::l3 -> false)
  
  (** val hasNonePredecessor :
      LLVMsyntax.block -> LLVMsyntax.usedef_block -> bool **)
  
  let hasNonePredecessor b udb =
    match predOfBlock b udb with
      | [] -> true
      | l0::l1 -> false
  
  (** val successors_terminator : LLVMsyntax.terminator -> LLVMsyntax.ls **)
  
  let successors_terminator = function
    | LLVMsyntax.Coq_insn_br (i0, v, l1, l2) -> l1::(l2::[])
    | LLVMsyntax.Coq_insn_br_uncond (i0, l1) -> l1::[]
    | _ -> []
  
  (** val isPointerTypB : LLVMsyntax.typ -> bool **)
  
  let isPointerTypB = function
    | LLVMsyntax.Coq_typ_pointer t0 -> true
    | _ -> false
  
  (** val isFunctionPointerTypB : LLVMsyntax.typ -> bool **)
  
  let isFunctionPointerTypB = function
    | LLVMsyntax.Coq_typ_pointer t0 ->
        (match t0 with
           | LLVMsyntax.Coq_typ_function (t1, l0, v) -> true
           | _ -> false)
    | _ -> false
  
  (** val isArrayTypB : LLVMsyntax.typ -> bool **)
  
  let isArrayTypB = function
    | LLVMsyntax.Coq_typ_array (s, t0) -> true
    | _ -> false
  
  (** val isReturnInsnB : LLVMsyntax.terminator -> bool **)
  
  let isReturnInsnB = function
    | LLVMsyntax.Coq_insn_return (i1, t, v) -> true
    | LLVMsyntax.Coq_insn_return_void i1 -> true
    | _ -> false
  
  (** val _isCallInsnB : LLVMsyntax.cmd -> bool **)
  
  let _isCallInsnB = function
    | LLVMsyntax.Coq_insn_call (i1, n, c, t, v, p) -> true
    | _ -> false
  
  (** val isCallInsnB : LLVMsyntax.insn -> bool **)
  
  let isCallInsnB = function
    | LLVMsyntax.Coq_insn_cmd c -> _isCallInsnB c
    | _ -> false
  
  (** val isNotValidReturnTypB : LLVMsyntax.typ -> bool **)
  
  let isNotValidReturnTypB = function
    | LLVMsyntax.Coq_typ_label -> true
    | LLVMsyntax.Coq_typ_metadata -> true
    | _ -> false
  
  (** val isValidReturnTypB : LLVMsyntax.typ -> bool **)
  
  let isValidReturnTypB t =
    negb (isNotValidReturnTypB t)
  
  (** val isNotFirstClassTypB : LLVMsyntax.typ -> bool **)
  
  let isNotFirstClassTypB = function
    | LLVMsyntax.Coq_typ_void -> true
    | LLVMsyntax.Coq_typ_function (t0, l0, v) -> true
    | _ -> false
  
  (** val isFirstClassTypB : LLVMsyntax.typ -> bool **)
  
  let isFirstClassTypB t =
    negb (isNotFirstClassTypB t)
  
  (** val isValidArgumentTypB : LLVMsyntax.typ -> bool **)
  
  let isValidArgumentTypB t =
    isFirstClassTypB t
  
  (** val isNotValidElementTypB : LLVMsyntax.typ -> bool **)
  
  let isNotValidElementTypB = function
    | LLVMsyntax.Coq_typ_void -> true
    | LLVMsyntax.Coq_typ_label -> true
    | LLVMsyntax.Coq_typ_metadata -> true
    | LLVMsyntax.Coq_typ_function (t0, l0, v) -> true
    | _ -> false
  
  (** val isValidElementTypB : LLVMsyntax.typ -> bool **)
  
  let isValidElementTypB t =
    negb (isNotValidElementTypB t)
  
  (** val isBindingFdecB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingFdecB = function
    | LLVMsyntax.Coq_id_binding_fdec fdec0 -> true
    | _ -> false
  
  (** val isBindingGvarB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingGvarB = function
    | LLVMsyntax.Coq_id_binding_gvar g -> true
    | _ -> false
  
  (** val isBindingArgB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingArgB = function
    | LLVMsyntax.Coq_id_binding_arg arg0 -> true
    | _ -> false
  
  (** val isBindingCmdB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingCmdB = function
    | LLVMsyntax.Coq_id_binding_cmd c -> true
    | _ -> false
  
  (** val isBindingTerminatorB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingTerminatorB = function
    | LLVMsyntax.Coq_id_binding_terminator t -> true
    | _ -> false
  
  (** val isBindingPhiNodeB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingPhiNodeB = function
    | LLVMsyntax.Coq_id_binding_phinode p -> true
    | _ -> false
  
  (** val isBindingInsnB : LLVMsyntax.id_binding -> bool **)
  
  let isBindingInsnB ib =
    if if isBindingCmdB ib then true else isBindingTerminatorB ib
    then true
    else isBindingPhiNodeB ib
  
  (** val isBindingFdec : LLVMsyntax.id_binding -> LLVMsyntax.fdec option **)
  
  let isBindingFdec = function
    | LLVMsyntax.Coq_id_binding_fdec f -> Some f
    | _ -> None
  
  (** val isBindingArg : LLVMsyntax.id_binding -> LLVMsyntax.arg option **)
  
  let isBindingArg = function
    | LLVMsyntax.Coq_id_binding_arg a -> Some a
    | _ -> None
  
  (** val isBindingGvar : LLVMsyntax.id_binding -> LLVMsyntax.gvar option **)
  
  let isBindingGvar = function
    | LLVMsyntax.Coq_id_binding_gvar g -> Some g
    | _ -> None
  
  (** val isBindingCmd : LLVMsyntax.id_binding -> LLVMsyntax.cmd option **)
  
  let isBindingCmd = function
    | LLVMsyntax.Coq_id_binding_cmd c -> Some c
    | _ -> None
  
  (** val isBindingPhiNode :
      LLVMsyntax.id_binding -> LLVMsyntax.phinode option **)
  
  let isBindingPhiNode = function
    | LLVMsyntax.Coq_id_binding_phinode p -> Some p
    | _ -> None
  
  (** val isBindingTerminator :
      LLVMsyntax.id_binding -> LLVMsyntax.terminator option **)
  
  let isBindingTerminator = function
    | LLVMsyntax.Coq_id_binding_terminator tmn -> Some tmn
    | _ -> None
  
  (** val isBindingInsn : LLVMsyntax.id_binding -> LLVMsyntax.insn option **)
  
  let isBindingInsn = function
    | LLVMsyntax.Coq_id_binding_cmd c -> Some (LLVMsyntax.Coq_insn_cmd c)
    | LLVMsyntax.Coq_id_binding_phinode p -> Some
        (LLVMsyntax.Coq_insn_phinode p)
    | LLVMsyntax.Coq_id_binding_terminator tmn -> Some
        (LLVMsyntax.Coq_insn_terminator tmn)
    | _ -> None
  
  (** val getCmdsLocs : LLVMsyntax.cmd list -> LLVMsyntax.ids **)
  
  let rec getCmdsLocs = function
    | [] -> []
    | c::cs' -> (getCmdLoc c)::(getCmdsLocs cs')
  
  (** val getBlockLocs : LLVMsyntax.block -> LLVMsyntax.ids **)
  
  let getBlockLocs = function
    | LLVMsyntax.Coq_block_intro (l0, ps, cs, t) ->
        app (getPhiNodesIDs ps)
          (app (getCmdsLocs cs) ((getTerminatorID t)::[]))
  
  (** val getBlocksLocs : LLVMsyntax.block list -> LLVMsyntax.ids **)
  
  let rec getBlocksLocs = function
    | [] -> []
    | b::bs' -> app (getBlockLocs b) (getBlocksLocs bs')
  
  (** val getBlocksLabels : LLVMsyntax.block list -> LLVMsyntax.ls **)
  
  let rec getBlocksLabels = function
    | [] -> []
    | y::bs' ->
        let LLVMsyntax.Coq_block_intro (l0, p, c, t) = y in
        l0::(getBlocksLabels bs')
  
  (** val getProductID : LLVMsyntax.product -> LLVMsyntax.id **)
  
  let getProductID = function
    | LLVMsyntax.Coq_product_gvar g -> getGvarID g
    | LLVMsyntax.Coq_product_fdec f -> getFdecID f
    | LLVMsyntax.Coq_product_fdef f -> getFdefID f
  
  (** val getProductsIDs : LLVMsyntax.product list -> LLVMsyntax.ids **)
  
  let rec getProductsIDs = function
    | [] -> []
    | p::ps' -> (getProductID p)::(getProductsIDs ps')
  
  (** val getNamedtsIDs : LLVMsyntax.namedt list -> LLVMsyntax.ids **)
  
  let rec getNamedtsIDs = function
    | [] -> []
    | y::dts' ->
        let LLVMsyntax.Coq_namedt_intro (id0, t) = y in
        id0::(getNamedtsIDs dts')
  
  (** val sumbool2bool : bool -> bool **)
  
  let sumbool2bool = function
    | true -> true
    | false -> false
  
  (** val floating_point_dec :
      LLVMsyntax.floating_point -> LLVMsyntax.floating_point -> bool **)
  
  let floating_point_dec fp1 fp2 =
    match fp1 with
      | LLVMsyntax.Coq_fp_float ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_float -> true
             | _ -> false)
      | LLVMsyntax.Coq_fp_double ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_double -> true
             | _ -> false)
      | LLVMsyntax.Coq_fp_fp128 ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_fp128 -> true
             | _ -> false)
      | LLVMsyntax.Coq_fp_x86_fp80 ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_x86_fp80 -> true
             | _ -> false)
      | LLVMsyntax.Coq_fp_ppc_fp128 ->
          (match fp2 with
             | LLVMsyntax.Coq_fp_ppc_fp128 -> true
             | _ -> false)
  
  type typ_dec_prop = LLVMsyntax.typ -> bool
  
  type list_typ_dec_prop = LLVMsyntax.list_typ -> bool
  
  (** val typ_mutrec_dec :
      (LLVMsyntax.typ -> typ_dec_prop)*(LLVMsyntax.list_typ ->
      list_typ_dec_prop) **)
  
  let typ_mutrec_dec =
    LLVMsyntax.typ_mutrec (fun s t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_int s0 -> LLVMsyntax.Size.dec s s0
        | _ -> false) (fun f t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_floatpoint f0 -> floating_point_dec f f0
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_void -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_label -> true
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_metadata -> true
        | _ -> false) (fun s t h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_array (s0, t3) ->
            let s1 = h t3 in if s1 then LLVMsyntax.Size.dec s s0 else false
        | _ -> false) (fun t h l0 h0 v t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_function (t3, l1, v0) ->
            let s = h t3 in
            if s
            then let s0 = varg_dec v v0 in if s0 then h0 l1 else false
            else false
        | _ -> false) (fun l0 h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_struct l1 -> h l1
        | _ -> false) (fun t h t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_pointer t3 -> h t3
        | _ -> false) (fun t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_opaque -> true
        | _ -> false) (fun i0 t2 ->
      match t2 with
        | LLVMsyntax.Coq_typ_namedt i1 -> id_dec i0 i1
        | _ -> false) (fun lt2 ->
      match lt2 with
        | LLVMsyntax.Nil_list_typ -> true
        | LLVMsyntax.Cons_list_typ (t, lt3) -> false) (fun t h l0 h0 lt2 ->
      match lt2 with
        | LLVMsyntax.Nil_list_typ -> false
        | LLVMsyntax.Cons_list_typ (t0, lt3) ->
            let s = h t0 in if s then h0 lt3 else false)
  
  (** val typ_dec : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typ_dec =
    let t,l0 = typ_mutrec_dec in t
  
  (** val list_typ_dec :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typ_dec =
    let t,l0 = typ_mutrec_dec in l0
  
  (** val bop_dec : LLVMsyntax.bop -> LLVMsyntax.bop -> bool **)
  
  let bop_dec b1 b2 =
    match b1 with
      | LLVMsyntax.Coq_bop_add ->
          (match b2 with
             | LLVMsyntax.Coq_bop_add -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_sub ->
          (match b2 with
             | LLVMsyntax.Coq_bop_sub -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_mul ->
          (match b2 with
             | LLVMsyntax.Coq_bop_mul -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_udiv ->
          (match b2 with
             | LLVMsyntax.Coq_bop_udiv -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_sdiv ->
          (match b2 with
             | LLVMsyntax.Coq_bop_sdiv -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_urem ->
          (match b2 with
             | LLVMsyntax.Coq_bop_urem -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_srem ->
          (match b2 with
             | LLVMsyntax.Coq_bop_srem -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_shl ->
          (match b2 with
             | LLVMsyntax.Coq_bop_shl -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_lshr ->
          (match b2 with
             | LLVMsyntax.Coq_bop_lshr -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_ashr ->
          (match b2 with
             | LLVMsyntax.Coq_bop_ashr -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_and ->
          (match b2 with
             | LLVMsyntax.Coq_bop_and -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_or ->
          (match b2 with
             | LLVMsyntax.Coq_bop_or -> true
             | _ -> false)
      | LLVMsyntax.Coq_bop_xor ->
          (match b2 with
             | LLVMsyntax.Coq_bop_xor -> true
             | _ -> false)
  
  (** val fbop_dec : LLVMsyntax.fbop -> LLVMsyntax.fbop -> bool **)
  
  let fbop_dec b1 b2 =
    match b1 with
      | LLVMsyntax.Coq_fbop_fadd ->
          (match b2 with
             | LLVMsyntax.Coq_fbop_fadd -> true
             | _ -> false)
      | LLVMsyntax.Coq_fbop_fsub ->
          (match b2 with
             | LLVMsyntax.Coq_fbop_fsub -> true
             | _ -> false)
      | LLVMsyntax.Coq_fbop_fmul ->
          (match b2 with
             | LLVMsyntax.Coq_fbop_fmul -> true
             | _ -> false)
      | LLVMsyntax.Coq_fbop_fdiv ->
          (match b2 with
             | LLVMsyntax.Coq_fbop_fdiv -> true
             | _ -> false)
      | LLVMsyntax.Coq_fbop_frem ->
          (match b2 with
             | LLVMsyntax.Coq_fbop_frem -> true
             | _ -> false)
  
  (** val extop_dec : LLVMsyntax.extop -> LLVMsyntax.extop -> bool **)
  
  let extop_dec e1 e2 =
    match e1 with
      | LLVMsyntax.Coq_extop_z ->
          (match e2 with
             | LLVMsyntax.Coq_extop_z -> true
             | _ -> false)
      | LLVMsyntax.Coq_extop_s ->
          (match e2 with
             | LLVMsyntax.Coq_extop_s -> true
             | _ -> false)
      | LLVMsyntax.Coq_extop_fp ->
          (match e2 with
             | LLVMsyntax.Coq_extop_fp -> true
             | _ -> false)
  
  (** val castop_dec : LLVMsyntax.castop -> LLVMsyntax.castop -> bool **)
  
  let castop_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_castop_fptoui ->
          (match c2 with
             | LLVMsyntax.Coq_castop_fptoui -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_fptosi ->
          (match c2 with
             | LLVMsyntax.Coq_castop_fptosi -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_uitofp ->
          (match c2 with
             | LLVMsyntax.Coq_castop_uitofp -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_sitofp ->
          (match c2 with
             | LLVMsyntax.Coq_castop_sitofp -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_ptrtoint ->
          (match c2 with
             | LLVMsyntax.Coq_castop_ptrtoint -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_inttoptr ->
          (match c2 with
             | LLVMsyntax.Coq_castop_inttoptr -> true
             | _ -> false)
      | LLVMsyntax.Coq_castop_bitcast ->
          (match c2 with
             | LLVMsyntax.Coq_castop_bitcast -> true
             | _ -> false)
  
  (** val cond_dec : LLVMsyntax.cond -> LLVMsyntax.cond -> bool **)
  
  let cond_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_cond_eq ->
          (match c2 with
             | LLVMsyntax.Coq_cond_eq -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ne ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ne -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ugt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ugt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_uge ->
          (match c2 with
             | LLVMsyntax.Coq_cond_uge -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ult ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ult -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_ule ->
          (match c2 with
             | LLVMsyntax.Coq_cond_ule -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sgt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sgt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sge ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sge -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_slt ->
          (match c2 with
             | LLVMsyntax.Coq_cond_slt -> true
             | _ -> false)
      | LLVMsyntax.Coq_cond_sle ->
          (match c2 with
             | LLVMsyntax.Coq_cond_sle -> true
             | _ -> false)
  
  (** val fcond_dec : LLVMsyntax.fcond -> LLVMsyntax.fcond -> bool **)
  
  let fcond_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_fcond_false ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_false -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_oeq ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_oeq -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ogt ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ogt -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_oge ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_oge -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_olt ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_olt -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ole ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ole -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_one ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_one -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ord ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ord -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ueq ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ueq -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ugt ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ugt -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_uge ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_uge -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ult ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ult -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_ule ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_ule -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_une ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_une -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_uno ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_uno -> true
             | _ -> false)
      | LLVMsyntax.Coq_fcond_true ->
          (match c2 with
             | LLVMsyntax.Coq_fcond_true -> true
             | _ -> false)
  
  (** val truncop_dec : LLVMsyntax.truncop -> LLVMsyntax.truncop -> bool **)
  
  let truncop_dec t1 t2 =
    match t1 with
      | LLVMsyntax.Coq_truncop_int ->
          (match t2 with
             | LLVMsyntax.Coq_truncop_int -> true
             | LLVMsyntax.Coq_truncop_fp -> false)
      | LLVMsyntax.Coq_truncop_fp ->
          (match t2 with
             | LLVMsyntax.Coq_truncop_int -> false
             | LLVMsyntax.Coq_truncop_fp -> true)
  
  type const_dec_prop = LLVMsyntax.const -> bool
  
  type list_const_dec_prop = LLVMsyntax.list_const -> bool
  
  (** val const_mutrec_dec :
      (LLVMsyntax.const -> const_dec_prop)*(LLVMsyntax.list_const ->
      list_const_dec_prop) **)
  
  let const_mutrec_dec =
    LLVMsyntax.const_mutrec (fun t c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_zeroinitializer t0 -> typ_dec t t0
        | _ -> false) (fun s i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_int (s0, i1) ->
            let s1 = LLVMsyntax.INTEGER.dec i0 i1 in
            if s1 then LLVMsyntax.Size.dec s s0 else false
        | _ -> false) (fun f f0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_floatpoint (f1, f2) ->
            let s = LLVMsyntax.FLOAT.dec f0 f2 in
            if s then floating_point_dec f f1 else false
        | _ -> false) (fun t c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_undef t0 -> typ_dec t t0
        | _ -> false) (fun t c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_null t0 -> typ_dec t t0
        | _ -> false) (fun t l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_arr (t0, l1) ->
            let s = typ_dec t t0 in if s then h l1 else false
        | _ -> false) (fun l0 h c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_struct l1 -> h l1
        | _ -> false) (fun t i0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_gid (t0, i1) ->
            let s = typ_dec t t0 in if s then id_dec i0 i1 else false
        | _ -> false) (fun t c h t0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_truncop (t1, c3, t2) ->
            let s = truncop_dec t t1 in
            if s
            then let s0 = typ_dec t0 t2 in if s0 then h c3 else false
            else false
        | _ -> false) (fun e c h t c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_extop (e0, c3, t0) ->
            let s = extop_dec e e0 in
            if s
            then let s0 = typ_dec t t0 in if s0 then h c3 else false
            else false
        | _ -> false) (fun c c0 h t c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_castop (c1, c3, t0) ->
            let s = castop_dec c c1 in
            if s
            then let s0 = typ_dec t t0 in if s0 then h c3 else false
            else false
        | _ -> false) (fun i0 c h l0 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_gep (i1, c3, l1) ->
            let s = inbounds_dec i0 i1 in
            if s then let s0 = h c3 in if s0 then h0 l1 else false else false
        | _ -> false) (fun c h c0 h0 c1 h1 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_select (c2_1, c2_2, c2_3) ->
            let s = h c2_1 in
            if s
            then let s0 = h0 c2_2 in if s0 then h1 c2_3 else false
            else false
        | _ -> false) (fun c c0 h c1 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_icmp (c3, c2_1, c2_2) ->
            let s = cond_dec c c3 in
            if s
            then let s0 = h c2_1 in if s0 then h0 c2_2 else false
            else false
        | _ -> false) (fun f c h c0 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_fcmp (f0, c2_1, c2_2) ->
            let s = fcond_dec f f0 in
            if s
            then let s0 = h c2_1 in if s0 then h0 c2_2 else false
            else false
        | _ -> false) (fun c h l0 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_extractvalue (c3, l1) ->
            let s = h c3 in if s then h0 l1 else false
        | _ -> false) (fun c h c0 h0 l0 h1 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_insertvalue (c2_1, c2_2, l1) ->
            let s = h c2_1 in
            if s
            then let s0 = h0 c2_2 in if s0 then h1 l1 else false
            else false
        | _ -> false) (fun b c h c0 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_bop (b0, c2_1, c2_2) ->
            let s = bop_dec b b0 in
            if s
            then let s0 = h c2_1 in if s0 then h0 c2_2 else false
            else false
        | _ -> false) (fun f c h c0 h0 c2 ->
      match c2 with
        | LLVMsyntax.Coq_const_fbop (f0, c2_1, c2_2) ->
            let s = fbop_dec f f0 in
            if s
            then let s0 = h c2_1 in if s0 then h0 c2_2 else false
            else false
        | _ -> false) (fun lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> true
        | LLVMsyntax.Cons_list_const (c, lc3) -> false) (fun c h l0 h0 lc2 ->
      match lc2 with
        | LLVMsyntax.Nil_list_const -> false
        | LLVMsyntax.Cons_list_const (c0, lc3) ->
            let s = h c0 in if s then h0 lc3 else false)
  
  (** val const_dec : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let const_dec =
    let c,l0 = const_mutrec_dec in c
  
  (** val list_const_dec :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_const_dec =
    let c,l0 = const_mutrec_dec in l0
  
  (** val value_dec : LLVMsyntax.value -> LLVMsyntax.value -> bool **)
  
  let value_dec v1 v2 =
    match v1 with
      | LLVMsyntax.Coq_value_id x ->
          (match v2 with
             | LLVMsyntax.Coq_value_id i1 -> AtomImpl.eq_atom_dec x i1
             | LLVMsyntax.Coq_value_const c -> false)
      | LLVMsyntax.Coq_value_const x ->
          (match v2 with
             | LLVMsyntax.Coq_value_id i0 -> false
             | LLVMsyntax.Coq_value_const c0 -> const_dec x c0)
  
  (** val attribute_dec :
      LLVMsyntax.attribute -> LLVMsyntax.attribute -> bool **)
  
  let attribute_dec attr1 attr2 =
    match attr1 with
      | LLVMsyntax.Coq_attribute_zext ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_zext -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_sext ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_sext -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_noreturn ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_noreturn -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_inreg ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_inreg -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_structret ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_structret -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_nounwind ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_nounwind -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_noalias ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_noalias -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_byval ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_byval -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_nest ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_nest -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_readnone ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_readnone -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_readonly ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_readonly -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_noinline ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_noinline -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_alwaysinline ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_alwaysinline -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_optforsize ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_optforsize -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_stackprotect ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_stackprotect -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_stackprotectreq ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_stackprotectreq -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_nocapture ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_nocapture -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_noredzone ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_noredzone -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_implicitfloat ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_implicitfloat -> true
             | _ -> false)
      | LLVMsyntax.Coq_attribute_naked ->
          (match attr2 with
             | LLVMsyntax.Coq_attribute_naked -> true
             | _ -> false)
  
  (** val attributes_dec :
      LLVMsyntax.attributes -> LLVMsyntax.attributes -> bool **)
  
  let rec attributes_dec l0 attrs0 =
    match l0 with
      | [] -> (match attrs0 with
                 | [] -> true
                 | a::l1 -> false)
      | y::l1 ->
          (match attrs0 with
             | [] -> false
             | a0::l2 ->
                 if attribute_dec y a0 then attributes_dec l1 l2 else false)
  
  (** val params_dec : LLVMsyntax.params -> LLVMsyntax.params -> bool **)
  
  let rec params_dec l0 p0 =
    match l0 with
      | [] -> (match p0 with
                 | [] -> true
                 | p::l1 -> false)
      | y::l1 ->
          (match p0 with
             | [] -> false
             | p::l2 ->
                 if let p1,x = y in
                    let t,a = p1 in
                    let p2,x0 = p in
                    let t0,a0 = p2 in
                    let s = typ_dec t t0 in
                    if s
                    then let s0 = attributes_dec a a0 in
                         if s0 then value_dec x x0 else false
                    else false
                 then params_dec l1 l2
                 else false)
  
  (** val list_value_l_dec :
      LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool **)
  
  let rec list_value_l_dec l0 l2 =
    match l0 with
      | LLVMsyntax.Nil_list_value_l ->
          (match l2 with
             | LLVMsyntax.Nil_list_value_l -> true
             | LLVMsyntax.Cons_list_value_l (v, l1, l3) -> false)
      | LLVMsyntax.Cons_list_value_l (v, l1, l3) ->
          (match l2 with
             | LLVMsyntax.Nil_list_value_l -> false
             | LLVMsyntax.Cons_list_value_l (v0, l4, l5) ->
                 let s = value_dec v v0 in
                 if s
                 then let s0 = l_dec l1 l4 in
                      if s0 then list_value_l_dec l3 l5 else false
                 else false)
  
  (** val list_value_dec :
      LLVMsyntax.list_sz_value -> LLVMsyntax.list_sz_value -> bool **)
  
  let rec list_value_dec l0 lv0 =
    match l0 with
      | LLVMsyntax.Nil_list_sz_value ->
          (match lv0 with
             | LLVMsyntax.Nil_list_sz_value -> true
             | LLVMsyntax.Cons_list_sz_value (s, v, l1) -> false)
      | LLVMsyntax.Cons_list_sz_value (s, v, l1) ->
          (match lv0 with
             | LLVMsyntax.Nil_list_sz_value -> false
             | LLVMsyntax.Cons_list_sz_value (s0, v0, l2) ->
                 if LLVMsyntax.Size.dec s s0
                 then if value_dec v v0 then list_value_dec l1 l2 else false
                 else false)
  
  (** val callconv_dec :
      LLVMsyntax.callconv -> LLVMsyntax.callconv -> bool **)
  
  let callconv_dec cc1 cc2 =
    match cc1 with
      | LLVMsyntax.Coq_callconv_ccc ->
          (match cc2 with
             | LLVMsyntax.Coq_callconv_ccc -> true
             | _ -> false)
      | LLVMsyntax.Coq_callconv_fast ->
          (match cc2 with
             | LLVMsyntax.Coq_callconv_fast -> true
             | _ -> false)
      | LLVMsyntax.Coq_callconv_cold ->
          (match cc2 with
             | LLVMsyntax.Coq_callconv_cold -> true
             | _ -> false)
      | LLVMsyntax.Coq_callconv_x86_stdcall ->
          (match cc2 with
             | LLVMsyntax.Coq_callconv_x86_stdcall -> true
             | _ -> false)
      | LLVMsyntax.Coq_callconv_x86_fastcall ->
          (match cc2 with
             | LLVMsyntax.Coq_callconv_x86_fastcall -> true
             | _ -> false)
  
  (** val cmd_dec : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool **)
  
  let cmd_dec c1 c2 =
    match c1 with
      | LLVMsyntax.Coq_insn_bop (i0, b, s, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_bop (i1, b0, s0, v1, v2) ->
                 let s1 = id_dec i0 i1 in
                 if s1
                 then let s2 = bop_dec b b0 in
                      if s2
                      then let s3 = LLVMsyntax.Size.dec s s0 in
                           if s3
                           then let s4 = value_dec v v1 in
                                if s4 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_fbop (i0, f, f0, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_fbop (i1, f1, f2, v1, v2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = fbop_dec f f1 in
                      if s0
                      then let s1 = floating_point_dec f0 f2 in
                           if s1
                           then let s2 = value_dec v v1 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_extractvalue (i0, t, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_extractvalue (i1, t0, v0, l1) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0
                      then let s1 = value_dec v v0 in
                           if s1 then list_const_dec l0 l1 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_insertvalue (i0, t, v, t0, v0, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_insertvalue (i1, t1, v1, t2, v2, l1) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t1 in
                      if s0
                      then let s1 = value_dec v v1 in
                           if s1
                           then let s2 = typ_dec t0 t2 in
                                if s2
                                then let s3 = value_dec v0 v2 in
                                     if s3
                                     then list_const_dec l0 l1
                                     else false
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_malloc (i0, t, v, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_malloc (i1, t0, v0, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0
                      then let s1 = value_dec v v0 in
                           if s1 then LLVMsyntax.Align.dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_free (i0, t, v) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_free (i1, t0, v0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0 then value_dec v v0 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_alloca (i0, t, v, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_alloca (i1, t0, v0, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0
                      then let s1 = value_dec v v0 in
                           if s1 then LLVMsyntax.Align.dec a a0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_load (i0, t, v, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_load (i1, t0, v0, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0
                      then let s1 = LLVMsyntax.Align.dec a a0 in
                           if s1 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_store (i0, t, v, v0, a) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_store (i1, t0, v1, v2, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0
                      then let s1 = value_dec v v1 in
                           if s1
                           then let s2 = LLVMsyntax.Align.dec a a0 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_gep (i0, i1, t, v, l0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_gep (i2, i3, t0, v0, l1) ->
                 let s = id_dec i0 i2 in
                 if s
                 then let s0 = inbounds_dec i1 i3 in
                      if s0
                      then let s1 = typ_dec t t0 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then list_value_dec l0 l1 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_trunc (i0, t, t0, v, t1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_trunc (i1, t2, t3, v0, t4) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = truncop_dec t t2 in
                      if s0
                      then let s1 = typ_dec t0 t3 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then typ_dec t1 t4 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_ext (i0, e, t, v, t0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_ext (i1, e0, t1, v0, t2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = extop_dec e e0 in
                      if s0
                      then let s1 = typ_dec t t1 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then typ_dec t0 t2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_cast (i0, c, t, v, t0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_cast (i1, c0, t1, v0, t2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = castop_dec c c0 in
                      if s0
                      then let s1 = typ_dec t t1 in
                           if s1
                           then let s2 = value_dec v v0 in
                                if s2 then typ_dec t0 t2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_icmp (i0, c, t, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_icmp (i1, c0, t0, v1, v2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = cond_dec c c0 in
                      if s0
                      then let s1 = typ_dec t t0 in
                           if s1
                           then let s2 = value_dec v v1 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_fcmp (i0, f, f0, v, v0) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_fcmp (i1, f1, f2, v1, v2) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = fcond_dec f f1 in
                      if s0
                      then let s1 = floating_point_dec f0 f2 in
                           if s1
                           then let s2 = value_dec v v1 in
                                if s2 then value_dec v0 v2 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_select (i0, v, t, v0, v1) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_select (i1, v2, t0, v3, v4) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = value_dec v v2 in
                      if s0
                      then let s1 = typ_dec t t0 in
                           if s1
                           then let s2 = value_dec v0 v3 in
                                if s2 then value_dec v1 v4 else false
                           else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_call (i0, n, c, t, v, p) ->
          (match c2 with
             | LLVMsyntax.Coq_insn_call (i1, n0, c0, t0, v0, p0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = value_dec v v0 in
                      if s0
                      then let s1 = noret_dec n n0 in
                           if s1
                           then let LLVMsyntax.Coq_clattrs_intro
                                  (t1, c3, a, a0) = c
                                in
                                let LLVMsyntax.Coq_clattrs_intro
                                  (t2, c4, a1, a2) = c0
                                in
                                let s2 = tailc_dec t1 t2 in
                                if s2
                                then let s3 = typ_dec t t0 in
                                     if s3
                                     then let s4 = callconv_dec c3 c4 in
                                          if s4
                                          then let s5 = attributes_dec a a1
                                               in
                                               if s5
                                               then 
                                                 let s6 =
                                                  attributes_dec a0 a2
                                                 in
                                                 if s6
                                                 then params_dec p p0
                                                 else false
                                               else false
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
             | _ -> false)
  
  (** val terminator_dec :
      LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool **)
  
  let terminator_dec tmn1 tmn2 =
    match tmn1 with
      | LLVMsyntax.Coq_insn_return (i0, t, v) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_return (i1, t0, v0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = typ_dec t t0 in
                      if s0 then value_dec v v0 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_return_void i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_return_void i1 -> id_dec i0 i1
             | _ -> false)
      | LLVMsyntax.Coq_insn_br (i0, v, l0, l1) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br (i1, v0, l2, l3) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = l_dec l0 l2 in
                      if s0
                      then let s1 = l_dec l1 l3 in
                           if s1 then value_dec v v0 else false
                      else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_br_uncond (i0, l0) ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_br_uncond (i1, l1) ->
                 let s = id_dec i0 i1 in if s then l_dec l0 l1 else false
             | _ -> false)
      | LLVMsyntax.Coq_insn_unreachable i0 ->
          (match tmn2 with
             | LLVMsyntax.Coq_insn_unreachable i1 -> id_dec i0 i1
             | _ -> false)
  
  (** val phinode_dec : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)
  
  let phinode_dec p1 p2 =
    let LLVMsyntax.Coq_insn_phi (i0, t, l0) = p1 in
    let LLVMsyntax.Coq_insn_phi (i1, t0, l1) = p2 in
    let s = id_dec i0 i1 in
    if s
    then let s0 = typ_dec t t0 in
         if s0 then list_value_l_dec l0 l1 else false
    else false
  
  (** val insn_dec : LLVMsyntax.insn -> LLVMsyntax.insn -> bool **)
  
  let insn_dec i1 i2 =
    match i1 with
      | LLVMsyntax.Coq_insn_phinode p ->
          (match i2 with
             | LLVMsyntax.Coq_insn_phinode p0 -> phinode_dec p p0
             | _ -> false)
      | LLVMsyntax.Coq_insn_cmd c ->
          (match i2 with
             | LLVMsyntax.Coq_insn_cmd c0 -> cmd_dec c c0
             | _ -> false)
      | LLVMsyntax.Coq_insn_terminator t ->
          (match i2 with
             | LLVMsyntax.Coq_insn_terminator t0 -> terminator_dec t t0
             | _ -> false)
  
  (** val cmds_dec : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool **)
  
  let rec cmds_dec l0 cs2 =
    match l0 with
      | [] -> (match cs2 with
                 | [] -> true
                 | c::cs3 -> false)
      | y::l1 ->
          (match cs2 with
             | [] -> false
             | c::cs3 ->
                 let s = cmd_dec y c in if s then cmds_dec l1 cs3 else false)
  
  (** val phinodes_dec :
      LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool **)
  
  let rec phinodes_dec l0 ps2 =
    match l0 with
      | [] -> (match ps2 with
                 | [] -> true
                 | p::ps3 -> false)
      | y::l1 ->
          (match ps2 with
             | [] -> false
             | p::ps3 ->
                 let s = phinode_dec y p in
                 if s then phinodes_dec l1 ps3 else false)
  
  (** val block_dec : LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let block_dec b1 b2 =
    let LLVMsyntax.Coq_block_intro (l0, p, c, t) = b1 in
    let LLVMsyntax.Coq_block_intro (l1, p0, c0, t0) = b2 in
    let s = id_dec l0 l1 in
    if s
    then let s0 = phinodes_dec p p0 in
         if s0
         then let s1 = cmds_dec c c0 in
              if s1 then terminator_dec t t0 else false
         else false
    else false
  
  (** val arg_dec : LLVMsyntax.arg -> LLVMsyntax.arg -> bool **)
  
  let arg_dec a1 a2 =
    let p,i0 = a1 in
    let p0,i1 = a2 in
    let s = id_dec i0 i1 in
    if s
    then let t,a = p in
         let t0,a0 = p0 in
         let s0 = attributes_dec a a0 in if s0 then typ_dec t t0 else false
    else false
  
  (** val args_dec : LLVMsyntax.args -> LLVMsyntax.args -> bool **)
  
  let rec args_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | p::l3 -> false)
      | y::l1 ->
          (match l2 with
             | [] -> false
             | p::l3 ->
                 let s = arg_dec y p in if s then args_dec l1 l3 else false)
  
  (** val visibility_dec :
      LLVMsyntax.visibility -> LLVMsyntax.visibility -> bool **)
  
  let visibility_dec vb1 vb2 =
    match vb1 with
      | LLVMsyntax.Coq_visibility_default ->
          (match vb2 with
             | LLVMsyntax.Coq_visibility_default -> true
             | _ -> false)
      | LLVMsyntax.Coq_visibility_hidden ->
          (match vb2 with
             | LLVMsyntax.Coq_visibility_hidden -> true
             | _ -> false)
      | LLVMsyntax.Coq_visibility_protected ->
          (match vb2 with
             | LLVMsyntax.Coq_visibility_protected -> true
             | _ -> false)
  
  (** val linkage_dec : LLVMsyntax.linkage -> LLVMsyntax.linkage -> bool **)
  
  let linkage_dec lk1 lk2 =
    match lk1 with
      | LLVMsyntax.Coq_linkage_external ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_external -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_available_externally ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_available_externally -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_link_once ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_link_once -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_link_once_odr ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_link_once_odr -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_weak ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_weak -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_weak_odr ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_weak_odr -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_appending ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_appending -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_internal ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_internal -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_private ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_private -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_linker_private ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_linker_private -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_dllimport ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_dllimport -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_dllexport ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_dllexport -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_external_weak ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_external_weak -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_ghost ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_ghost -> true
             | _ -> false)
      | LLVMsyntax.Coq_linkage_common ->
          (match lk2 with
             | LLVMsyntax.Coq_linkage_common -> true
             | _ -> false)
  
  (** val fheader_dec : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool **)
  
  let fheader_dec f1 f2 =
    let LLVMsyntax.Coq_fheader_intro (f, t, i0, a, v) = f1 in
    let LLVMsyntax.Coq_fheader_intro (f0, t0, i1, a0, v0) = f2 in
    let s = typ_dec t t0 in
    if s
    then let s0 = id_dec i0 i1 in
         if s0
         then let LLVMsyntax.Coq_fnattrs_intro (l0, v1, c, a1, a2) = f in
              let LLVMsyntax.Coq_fnattrs_intro (l1, v2, c0, a3, a4) = f0 in
              let s1 = visibility_dec v1 v2 in
              if s1
              then let s2 = varg_dec v v0 in
                   if s2
                   then let s3 = attributes_dec a1 a3 in
                        if s3
                        then let s4 = attributes_dec a2 a4 in
                             if s4
                             then let s5 = callconv_dec c c0 in
                                  if s5
                                  then let s6 = linkage_dec l0 l1 in
                                       if s6 then args_dec a a0 else false
                                  else false
                             else false
                        else false
                   else false
              else false
         else false
    else false
  
  (** val blocks_dec : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)
  
  let rec blocks_dec l0 lb' =
    match l0 with
      | [] -> (match lb' with
                 | [] -> true
                 | b::lb'0 -> false)
      | y::l1 ->
          (match lb' with
             | [] -> false
             | b::lb'0 ->
                 let s = block_dec y b in
                 if s then blocks_dec l1 lb'0 else false)
  
  (** val fdec_dec : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)
  
  let fdec_dec f1 f2 =
    fheader_dec f1 f2
  
  (** val fdef_dec : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)
  
  let fdef_dec f1 f2 =
    let LLVMsyntax.Coq_fdef_intro (f, b) = f1 in
    let LLVMsyntax.Coq_fdef_intro (f0, b0) = f2 in
    let s = fheader_dec f f0 in if s then blocks_dec b b0 else false
  
  (** val gvar_spec_dec :
      LLVMsyntax.gvar_spec -> LLVMsyntax.gvar_spec -> bool **)
  
  let gvar_spec_dec g1 g2 =
    match g1 with
      | LLVMsyntax.Coq_gvar_spec_global ->
          (match g2 with
             | LLVMsyntax.Coq_gvar_spec_global -> true
             | LLVMsyntax.Coq_gvar_spec_constant -> false)
      | LLVMsyntax.Coq_gvar_spec_constant ->
          (match g2 with
             | LLVMsyntax.Coq_gvar_spec_global -> false
             | LLVMsyntax.Coq_gvar_spec_constant -> true)
  
  (** val gvar_dec : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool **)
  
  let gvar_dec g1 g2 =
    match g1 with
      | LLVMsyntax.Coq_gvar_intro (i0, l0, g, t, c, a) ->
          (match g2 with
             | LLVMsyntax.Coq_gvar_intro (i1, l1, g0, t0, c0, a0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = linkage_dec l0 l1 in
                      if s0
                      then let s1 = gvar_spec_dec g g0 in
                           if s1
                           then let s2 = typ_dec t t0 in
                                if s2
                                then let s3 = const_dec c c0 in
                                     if s3
                                     then LLVMsyntax.Align.dec a a0
                                     else false
                                else false
                           else false
                      else false
                 else false
             | LLVMsyntax.Coq_gvar_external (i1, g0, t0) -> false)
      | LLVMsyntax.Coq_gvar_external (i0, g, t) ->
          (match g2 with
             | LLVMsyntax.Coq_gvar_intro (i1, l0, g0, t0, c, a) -> false
             | LLVMsyntax.Coq_gvar_external (i1, g0, t0) ->
                 let s = id_dec i0 i1 in
                 if s
                 then let s0 = gvar_spec_dec g g0 in
                      if s0 then typ_dec t t0 else false
                 else false)
  
  (** val product_dec : LLVMsyntax.product -> LLVMsyntax.product -> bool **)
  
  let product_dec p p' =
    match p with
      | LLVMsyntax.Coq_product_gvar g ->
          (match p' with
             | LLVMsyntax.Coq_product_gvar g0 -> gvar_dec g g0
             | _ -> false)
      | LLVMsyntax.Coq_product_fdec f ->
          (match p' with
             | LLVMsyntax.Coq_product_fdec f0 -> fdec_dec f f0
             | _ -> false)
      | LLVMsyntax.Coq_product_fdef f ->
          (match p' with
             | LLVMsyntax.Coq_product_fdef f0 -> fdef_dec f f0
             | _ -> false)
  
  (** val products_dec :
      LLVMsyntax.products -> LLVMsyntax.products -> bool **)
  
  let rec products_dec l0 lp' =
    match l0 with
      | [] -> (match lp' with
                 | [] -> true
                 | p::lp'0 -> false)
      | y::l1 ->
          (match lp' with
             | [] -> false
             | p::lp'0 ->
                 let s = product_dec y p in
                 if s then products_dec l1 lp'0 else false)
  
  (** val namedt_dec : LLVMsyntax.namedt -> LLVMsyntax.namedt -> bool **)
  
  let namedt_dec nt1 nt2 =
    let LLVMsyntax.Coq_namedt_intro (i0, t) = nt1 in
    let LLVMsyntax.Coq_namedt_intro (i1, t0) = nt2 in
    let s = id_dec i0 i1 in if s then typ_dec t t0 else false
  
  (** val namedts_dec : LLVMsyntax.namedts -> LLVMsyntax.namedts -> bool **)
  
  let rec namedts_dec l0 nts' =
    match l0 with
      | [] -> (match nts' with
                 | [] -> true
                 | n::nts'0 -> false)
      | y::l1 ->
          (match nts' with
             | [] -> false
             | n::nts'0 ->
                 let s = namedt_dec y n in
                 if s then namedts_dec l1 nts'0 else false)
  
  (** val layout_dec : LLVMsyntax.layout -> LLVMsyntax.layout -> bool **)
  
  let layout_dec l1 l2 =
    match l1 with
      | LLVMsyntax.Coq_layout_be ->
          (match l2 with
             | LLVMsyntax.Coq_layout_be -> true
             | _ -> false)
      | LLVMsyntax.Coq_layout_le ->
          (match l2 with
             | LLVMsyntax.Coq_layout_le -> true
             | _ -> false)
      | LLVMsyntax.Coq_layout_ptr (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_ptr (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_int (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_int (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_float (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_float (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_aggr (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_aggr (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_stack (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_stack (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
      | LLVMsyntax.Coq_layout_vector (s, a, a0) ->
          (match l2 with
             | LLVMsyntax.Coq_layout_vector (s0, a1, a2) ->
                 let s1 = LLVMsyntax.Size.dec s s0 in
                 if s1
                 then let s2 = LLVMsyntax.Align.dec a a1 in
                      if s2 then LLVMsyntax.Align.dec a0 a2 else false
                 else false
             | _ -> false)
  
  (** val layouts_dec : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool **)
  
  let rec layouts_dec l0 l2 =
    match l0 with
      | [] -> (match l2 with
                 | [] -> true
                 | l1::l3 -> false)
      | y::l1 ->
          (match l2 with
             | [] -> false
             | l3::l4 ->
                 let s = layout_dec y l3 in
                 if s then layouts_dec l1 l4 else false)
  
  (** val module_dec :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)
  
  let module_dec m m' =
    let LLVMsyntax.Coq_module_intro (l0, n, p) = m in
    let LLVMsyntax.Coq_module_intro (l1, n0, p0) = m' in
    let s = layouts_dec l0 l1 in
    if s
    then let s0 = namedts_dec n n0 in if s0 then products_dec p p0 else false
    else false
  
  (** val modules_dec : LLVMsyntax.modules -> LLVMsyntax.modules -> bool **)
  
  let rec modules_dec l0 lm' =
    match l0 with
      | [] -> (match lm' with
                 | [] -> true
                 | m::lm'0 -> false)
      | y::l1 ->
          (match lm' with
             | [] -> false
             | m::lm'0 ->
                 let s = module_dec y m in
                 if s then modules_dec l1 lm'0 else false)
  
  (** val system_dec : LLVMsyntax.system -> LLVMsyntax.system -> bool **)
  
  let system_dec =
    modules_dec
  
  (** val typEqB : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)
  
  let typEqB t1 t2 =
    sumbool2bool (typ_dec t1 t2)
  
  (** val list_typEqB :
      LLVMsyntax.list_typ -> LLVMsyntax.list_typ -> bool **)
  
  let list_typEqB lt1 lt2 =
    sumbool2bool (list_typ_dec lt1 lt2)
  
  (** val idEqB : LLVMsyntax.id -> LLVMsyntax.id -> bool **)
  
  let idEqB i0 i' =
    sumbool2bool (id_dec i0 i')
  
  (** val constEqB : LLVMsyntax.const -> LLVMsyntax.const -> bool **)
  
  let constEqB c1 c2 =
    sumbool2bool (const_dec c1 c2)
  
  (** val list_constEqB :
      LLVMsyntax.list_const -> LLVMsyntax.list_const -> bool **)
  
  let list_constEqB lc1 lc2 =
    sumbool2bool (list_const_dec lc1 lc2)
  
  (** val valueEqB : LLVMsyntax.value -> LLVMsyntax.value -> bool **)
  
  let valueEqB v v' =
    sumbool2bool (value_dec v v')
  
  (** val paramsEqB : LLVMsyntax.params -> LLVMsyntax.params -> bool **)
  
  let paramsEqB lp lp' =
    sumbool2bool (params_dec lp lp')
  
  (** val lEqB : LLVMsyntax.l -> LLVMsyntax.l -> bool **)
  
  let lEqB i0 i' =
    sumbool2bool (l_dec i0 i')
  
  (** val list_value_lEqB :
      LLVMsyntax.list_value_l -> LLVMsyntax.list_value_l -> bool **)
  
  let list_value_lEqB idls idls' =
    sumbool2bool (list_value_l_dec idls idls')
  
  (** val list_valueEqB :
      LLVMsyntax.list_sz_value -> LLVMsyntax.list_sz_value -> bool **)
  
  let list_valueEqB idxs idxs' =
    sumbool2bool (list_value_dec idxs idxs')
  
  (** val bopEqB : LLVMsyntax.bop -> LLVMsyntax.bop -> bool **)
  
  let bopEqB op op' =
    sumbool2bool (bop_dec op op')
  
  (** val extopEqB : LLVMsyntax.extop -> LLVMsyntax.extop -> bool **)
  
  let extopEqB op op' =
    sumbool2bool (extop_dec op op')
  
  (** val condEqB : LLVMsyntax.cond -> LLVMsyntax.cond -> bool **)
  
  let condEqB c c' =
    sumbool2bool (cond_dec c c')
  
  (** val castopEqB : LLVMsyntax.castop -> LLVMsyntax.castop -> bool **)
  
  let castopEqB c c' =
    sumbool2bool (castop_dec c c')
  
  (** val cmdEqB : LLVMsyntax.cmd -> LLVMsyntax.cmd -> bool **)
  
  let cmdEqB i0 i' =
    sumbool2bool (cmd_dec i0 i')
  
  (** val cmdsEqB : LLVMsyntax.cmd list -> LLVMsyntax.cmd list -> bool **)
  
  let cmdsEqB cs1 cs2 =
    sumbool2bool (cmds_dec cs1 cs2)
  
  (** val terminatorEqB :
      LLVMsyntax.terminator -> LLVMsyntax.terminator -> bool **)
  
  let terminatorEqB i0 i' =
    sumbool2bool (terminator_dec i0 i')
  
  (** val phinodeEqB : LLVMsyntax.phinode -> LLVMsyntax.phinode -> bool **)
  
  let phinodeEqB i0 i' =
    sumbool2bool (phinode_dec i0 i')
  
  (** val phinodesEqB :
      LLVMsyntax.phinode list -> LLVMsyntax.phinode list -> bool **)
  
  let phinodesEqB ps1 ps2 =
    sumbool2bool (phinodes_dec ps1 ps2)
  
  (** val blockEqB : LLVMsyntax.block -> LLVMsyntax.block -> bool **)
  
  let blockEqB b1 b2 =
    sumbool2bool (block_dec b1 b2)
  
  (** val blocksEqB : LLVMsyntax.blocks -> LLVMsyntax.blocks -> bool **)
  
  let blocksEqB lb lb' =
    sumbool2bool (blocks_dec lb lb')
  
  (** val argsEqB : LLVMsyntax.args -> LLVMsyntax.args -> bool **)
  
  let argsEqB la la' =
    sumbool2bool (args_dec la la')
  
  (** val fheaderEqB : LLVMsyntax.fheader -> LLVMsyntax.fheader -> bool **)
  
  let fheaderEqB fh fh' =
    sumbool2bool (fheader_dec fh fh')
  
  (** val fdecEqB : LLVMsyntax.fdec -> LLVMsyntax.fdec -> bool **)
  
  let fdecEqB fd fd' =
    sumbool2bool (fdec_dec fd fd')
  
  (** val fdefEqB : LLVMsyntax.fdef -> LLVMsyntax.fdef -> bool **)
  
  let fdefEqB fd fd' =
    sumbool2bool (fdef_dec fd fd')
  
  (** val gvarEqB : LLVMsyntax.gvar -> LLVMsyntax.gvar -> bool **)
  
  let gvarEqB gv gv' =
    sumbool2bool (gvar_dec gv gv')
  
  (** val productEqB : LLVMsyntax.product -> LLVMsyntax.product -> bool **)
  
  let productEqB p p' =
    sumbool2bool (product_dec p p')
  
  (** val productsEqB :
      LLVMsyntax.products -> LLVMsyntax.products -> bool **)
  
  let productsEqB lp lp' =
    sumbool2bool (products_dec lp lp')
  
  (** val layoutEqB : LLVMsyntax.layout -> LLVMsyntax.layout -> bool **)
  
  let layoutEqB o o' =
    sumbool2bool (layout_dec o o')
  
  (** val layoutsEqB : LLVMsyntax.layouts -> LLVMsyntax.layouts -> bool **)
  
  let layoutsEqB lo lo' =
    sumbool2bool (layouts_dec lo lo')
  
  (** val moduleEqB :
      LLVMsyntax.coq_module -> LLVMsyntax.coq_module -> bool **)
  
  let moduleEqB m m' =
    sumbool2bool (module_dec m m')
  
  (** val modulesEqB : LLVMsyntax.modules -> LLVMsyntax.modules -> bool **)
  
  let modulesEqB lm lm' =
    sumbool2bool (modules_dec lm lm')
  
  (** val systemEqB : LLVMsyntax.system -> LLVMsyntax.system -> bool **)
  
  let systemEqB s s' =
    sumbool2bool (system_dec s s')
  
  (** val attributeEqB :
      LLVMsyntax.attribute -> LLVMsyntax.attribute -> bool **)
  
  let attributeEqB attr attr' =
    sumbool2bool (attribute_dec attr attr')
  
  (** val attributesEqB :
      LLVMsyntax.attributes -> LLVMsyntax.attributes -> bool **)
  
  let attributesEqB attrs attrs' =
    sumbool2bool (attributes_dec attrs attrs')
  
  (** val linkageEqB : LLVMsyntax.linkage -> LLVMsyntax.linkage -> bool **)
  
  let linkageEqB lk lk' =
    sumbool2bool (linkage_dec lk lk')
  
  (** val visibilityEqB :
      LLVMsyntax.visibility -> LLVMsyntax.visibility -> bool **)
  
  let visibilityEqB v v' =
    sumbool2bool (visibility_dec v v')
  
  (** val callconvEqB :
      LLVMsyntax.callconv -> LLVMsyntax.callconv -> bool **)
  
  let callconvEqB cc cc' =
    sumbool2bool (callconv_dec cc cc')
  
  (** val coq_InCmdsB : LLVMsyntax.cmd -> LLVMsyntax.cmds -> bool **)
  
  let rec coq_InCmdsB i0 = function
    | [] -> false
    | i'::li' -> if cmdEqB i0 i' then true else coq_InCmdsB i0 li'
  
  (** val coq_InPhiNodesB :
      LLVMsyntax.phinode -> LLVMsyntax.phinodes -> bool **)
  
  let rec coq_InPhiNodesB i0 = function
    | [] -> false
    | i'::li' -> if phinodeEqB i0 i' then true else coq_InPhiNodesB i0 li'
  
  (** val cmdInBlockB : LLVMsyntax.cmd -> LLVMsyntax.block -> bool **)
  
  let cmdInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, p, cmds0, t) -> coq_InCmdsB i0 cmds0
  
  (** val phinodeInBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.block -> bool **)
  
  let phinodeInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, ps, c, t) -> coq_InPhiNodesB i0 ps
  
  (** val terminatorInBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.block -> bool **)
  
  let terminatorInBlockB i0 = function
    | LLVMsyntax.Coq_block_intro (l0, p, c, t) -> terminatorEqB i0 t
  
  (** val coq_InArgsB : LLVMsyntax.arg -> LLVMsyntax.args -> bool **)
  
  let rec coq_InArgsB a = function
    | [] -> false
    | a'::la' ->
        if let p,id0 = a in
           let t,attrs = p in
           let p0,id' = a' in
           let t',attrs' = p0 in
           if if typEqB t t' then attributesEqB attrs attrs' else false
           then idEqB id0 id'
           else false
        then true
        else coq_InArgsB a la'
  
  (** val argInFheaderB : LLVMsyntax.arg -> LLVMsyntax.fheader -> bool **)
  
  let argInFheaderB a = function
    | LLVMsyntax.Coq_fheader_intro (f, t, id0, la, v) -> coq_InArgsB a la
  
  (** val argInFdecB : LLVMsyntax.arg -> LLVMsyntax.fdec -> bool **)
  
  let argInFdecB a fd =
    argInFheaderB a fd
  
  (** val argInFdefB : LLVMsyntax.arg -> LLVMsyntax.fdef -> bool **)
  
  let argInFdefB a = function
    | LLVMsyntax.Coq_fdef_intro (fh, lb) -> argInFheaderB a fh
  
  (** val coq_InBlocksB : LLVMsyntax.block -> LLVMsyntax.blocks -> bool **)
  
  let rec coq_InBlocksB b = function
    | [] -> false
    | b'::lb' -> if blockEqB b b' then true else coq_InBlocksB b lb'
  
  (** val blockInFdefB : LLVMsyntax.block -> LLVMsyntax.fdef -> bool **)
  
  let blockInFdefB b = function
    | LLVMsyntax.Coq_fdef_intro (fh, lb) -> coq_InBlocksB b lb
  
  (** val coq_InProductsB :
      LLVMsyntax.product -> LLVMsyntax.products -> bool **)
  
  let rec coq_InProductsB p = function
    | [] -> false
    | p'::lp' -> if productEqB p p' then true else coq_InProductsB p lp'
  
  (** val productInModuleB :
      LLVMsyntax.product -> LLVMsyntax.coq_module -> bool **)
  
  let productInModuleB p = function
    | LLVMsyntax.Coq_module_intro (os, nts, ps) -> coq_InProductsB p ps
  
  (** val coq_InModulesB :
      LLVMsyntax.coq_module -> LLVMsyntax.modules -> bool **)
  
  let rec coq_InModulesB m = function
    | [] -> false
    | m'::lm' -> if moduleEqB m m' then true else coq_InModulesB m lm'
  
  (** val moduleInSystemB :
      LLVMsyntax.coq_module -> LLVMsyntax.system -> bool **)
  
  let moduleInSystemB m s =
    coq_InModulesB m s
  
  (** val productInSystemModuleB :
      LLVMsyntax.product -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      bool **)
  
  let productInSystemModuleB p s m =
    if moduleInSystemB m s then productInModuleB p m else false
  
  (** val blockInSystemModuleFdefB :
      LLVMsyntax.block -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> bool **)
  
  let blockInSystemModuleFdefB b s m f =
    if blockInFdefB b f
    then productInSystemModuleB (LLVMsyntax.Coq_product_fdef f) s m
    else false
  
  (** val cmdInSystemModuleFdefBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let cmdInSystemModuleFdefBlockB i0 s m f b =
    if cmdInBlockB i0 b then blockInSystemModuleFdefB b s m f else false
  
  (** val phinodeInSystemModuleFdefBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let phinodeInSystemModuleFdefBlockB i0 s m f b =
    if phinodeInBlockB i0 b then blockInSystemModuleFdefB b s m f else false
  
  (** val terminatorInSystemModuleFdefBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let terminatorInSystemModuleFdefBlockB i0 s m f b =
    if terminatorInBlockB i0 b
    then blockInSystemModuleFdefB b s m f
    else false
  
  (** val insnInSystemModuleFdefBlockB :
      LLVMsyntax.insn -> LLVMsyntax.system -> LLVMsyntax.coq_module ->
      LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let insnInSystemModuleFdefBlockB i0 s m f b =
    match i0 with
      | LLVMsyntax.Coq_insn_phinode p ->
          phinodeInSystemModuleFdefBlockB p s m f b
      | LLVMsyntax.Coq_insn_cmd c -> cmdInSystemModuleFdefBlockB c s m f b
      | LLVMsyntax.Coq_insn_terminator t ->
          terminatorInSystemModuleFdefBlockB t s m f b
  
  (** val insnInBlockB : LLVMsyntax.insn -> LLVMsyntax.block -> bool **)
  
  let insnInBlockB i0 b =
    match i0 with
      | LLVMsyntax.Coq_insn_phinode p -> phinodeInBlockB p b
      | LLVMsyntax.Coq_insn_cmd c -> cmdInBlockB c b
      | LLVMsyntax.Coq_insn_terminator t -> terminatorInBlockB t b
  
  (** val cmdInFdefBlockB :
      LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let cmdInFdefBlockB i0 f b =
    if cmdInBlockB i0 b then blockInFdefB b f else false
  
  (** val phinodeInFdefBlockB :
      LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let phinodeInFdefBlockB i0 f b =
    if phinodeInBlockB i0 b then blockInFdefB b f else false
  
  (** val terminatorInFdefBlockB :
      LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let terminatorInFdefBlockB i0 f b =
    if terminatorInBlockB i0 b then blockInFdefB b f else false
  
  (** val insnInFdefBlockB :
      LLVMsyntax.insn -> LLVMsyntax.fdef -> LLVMsyntax.block -> bool **)
  
  let insnInFdefBlockB i0 f b =
    match i0 with
      | LLVMsyntax.Coq_insn_phinode p ->
          if phinodeInBlockB p b then blockInFdefB b f else false
      | LLVMsyntax.Coq_insn_cmd c ->
          if cmdInBlockB c b then blockInFdefB b f else false
      | LLVMsyntax.Coq_insn_terminator t ->
          if terminatorInBlockB t b then blockInFdefB b f else false
  
  (** val cmdInBlockB_dec : LLVMsyntax.cmd -> LLVMsyntax.block -> bool **)
  
  let cmdInBlockB_dec i0 b =
    let b0 = cmdInBlockB i0 b in if b0 then true else false
  
  (** val phinodeInBlockB_dec :
      LLVMsyntax.phinode -> LLVMsyntax.block -> bool **)
  
  let phinodeInBlockB_dec i0 b =
    let b0 = phinodeInBlockB i0 b in if b0 then true else false
  
  (** val terminatorInBlockB_dec :
      LLVMsyntax.terminator -> LLVMsyntax.block -> bool **)
  
  let terminatorInBlockB_dec i0 b =
    let b0 = terminatorInBlockB i0 b in if b0 then true else false
  
  (** val getParentOfCmdFromBlocks :
      LLVMsyntax.cmd -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if cmdInBlockB_dec i0 b
        then Some b
        else getParentOfCmdFromBlocks i0 lb'
  
  (** val getParentOfCmdFromFdef :
      LLVMsyntax.cmd -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) -> getParentOfCmdFromBlocks i0 lb
  
  (** val getParentOfCmdFromProduct :
      LLVMsyntax.cmd -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfCmdFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfCmdFromProducts :
      LLVMsyntax.cmd -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfCmdFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfCmdFromProducts i0 lp')
  
  (** val getParentOfCmdFromModule :
      LLVMsyntax.cmd -> LLVMsyntax.coq_module -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, nts, ps) ->
        getParentOfCmdFromProducts i0 ps
  
  (** val getParentOfCmdFromModules :
      LLVMsyntax.cmd -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfCmdFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfCmdFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfCmdFromModules i0 lm')
  
  (** val getParentOfCmdFromSystem :
      LLVMsyntax.cmd -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfCmdFromSystem i0 s =
    getParentOfCmdFromModules i0 s
  
  (** val cmdHasParent : LLVMsyntax.cmd -> LLVMsyntax.system -> bool **)
  
  let cmdHasParent i0 s =
    match getParentOfCmdFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val getParentOfPhiNodeFromBlocks :
      LLVMsyntax.phinode -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if phinodeInBlockB_dec i0 b
        then Some b
        else getParentOfPhiNodeFromBlocks i0 lb'
  
  (** val getParentOfPhiNodeFromFdef :
      LLVMsyntax.phinode -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) -> getParentOfPhiNodeFromBlocks i0 lb
  
  (** val getParentOfPhiNodeFromProduct :
      LLVMsyntax.phinode -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfPhiNodeFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfPhiNodeFromProducts :
      LLVMsyntax.phinode -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfPhiNodeFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfPhiNodeFromProducts i0 lp')
  
  (** val getParentOfPhiNodeFromModule :
      LLVMsyntax.phinode -> LLVMsyntax.coq_module -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, nts, ps) ->
        getParentOfPhiNodeFromProducts i0 ps
  
  (** val getParentOfPhiNodeFromModules :
      LLVMsyntax.phinode -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfPhiNodeFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfPhiNodeFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfPhiNodeFromModules i0 lm')
  
  (** val getParentOfPhiNodeFromSystem :
      LLVMsyntax.phinode -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfPhiNodeFromSystem i0 s =
    getParentOfPhiNodeFromModules i0 s
  
  (** val phinodeHasParent :
      LLVMsyntax.phinode -> LLVMsyntax.system -> bool **)
  
  let phinodeHasParent i0 s =
    match getParentOfPhiNodeFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val getParentOfTerminatorFromBlocks :
      LLVMsyntax.terminator -> LLVMsyntax.blocks -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromBlocks i0 = function
    | [] -> None
    | b::lb' ->
        if terminatorInBlockB_dec i0 b
        then Some b
        else getParentOfTerminatorFromBlocks i0 lb'
  
  (** val getParentOfTerminatorFromFdef :
      LLVMsyntax.terminator -> LLVMsyntax.fdef -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromFdef i0 = function
    | LLVMsyntax.Coq_fdef_intro (f, lb) ->
        getParentOfTerminatorFromBlocks i0 lb
  
  (** val getParentOfTerminatorFromProduct :
      LLVMsyntax.terminator -> LLVMsyntax.product -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromProduct i0 = function
    | LLVMsyntax.Coq_product_fdef fd -> getParentOfTerminatorFromFdef i0 fd
    | _ -> None
  
  (** val getParentOfTerminatorFromProducts :
      LLVMsyntax.terminator -> LLVMsyntax.products -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromProducts i0 = function
    | [] -> None
    | p::lp' ->
        (match getParentOfTerminatorFromProduct i0 p with
           | Some b -> Some b
           | None -> getParentOfTerminatorFromProducts i0 lp')
  
  (** val getParentOfTerminatorFromModule :
      LLVMsyntax.terminator -> LLVMsyntax.coq_module -> LLVMsyntax.block
      option **)
  
  let getParentOfTerminatorFromModule i0 = function
    | LLVMsyntax.Coq_module_intro (os, nts, ps) ->
        getParentOfTerminatorFromProducts i0 ps
  
  (** val getParentOfTerminatorFromModules :
      LLVMsyntax.terminator -> LLVMsyntax.modules -> LLVMsyntax.block option **)
  
  let rec getParentOfTerminatorFromModules i0 = function
    | [] -> None
    | m::lm' ->
        (match getParentOfTerminatorFromModule i0 m with
           | Some b -> Some b
           | None -> getParentOfTerminatorFromModules i0 lm')
  
  (** val getParentOfTerminatorFromSystem :
      LLVMsyntax.terminator -> LLVMsyntax.system -> LLVMsyntax.block option **)
  
  let getParentOfTerminatorFromSystem i0 s =
    getParentOfTerminatorFromModules i0 s
  
  (** val terminatoreHasParent :
      LLVMsyntax.terminator -> LLVMsyntax.system -> bool **)
  
  let terminatoreHasParent i0 s =
    match getParentOfTerminatorFromSystem i0 s with
      | Some b -> true
      | None -> false
  
  (** val productInModuleB_dec :
      LLVMsyntax.product -> LLVMsyntax.coq_module -> bool **)
  
  let productInModuleB_dec b m =
    let b0 = productInModuleB b m in if b0 then true else false
  
  (** val getParentOfFdefFromModules :
      LLVMsyntax.fdef -> LLVMsyntax.modules -> LLVMsyntax.coq_module option **)
  
  let rec getParentOfFdefFromModules fd = function
    | [] -> None
    | m::lm' ->
        if productInModuleB_dec (LLVMsyntax.Coq_product_fdef fd) m
        then Some m
        else getParentOfFdefFromModules fd lm'
  
  (** val getParentOfFdefFromSystem :
      LLVMsyntax.fdef -> LLVMsyntax.system -> LLVMsyntax.coq_module option **)
  
  let getParentOfFdefFromSystem fd s =
    getParentOfFdefFromModules fd s
  
  (** val lookupIdsViaLabelFromIdls :
      LLVMsyntax.list_value_l -> LLVMsyntax.l -> LLVMsyntax.id list **)
  
  let rec lookupIdsViaLabelFromIdls idls l0 =
    match idls with
      | LLVMsyntax.Nil_list_value_l -> []
      | LLVMsyntax.Cons_list_value_l (v, l1, idls') ->
          (match v with
             | LLVMsyntax.Coq_value_id id1 ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) l0 l1
                 then set_add (eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom))
                        id1 (lookupIdsViaLabelFromIdls idls' l0)
                 else lookupIdsViaLabelFromIdls idls' l0
             | LLVMsyntax.Coq_value_const c ->
                 lookupIdsViaLabelFromIdls idls' l0)
  
  module type SigValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigUser = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
   end
  
  module type SigConstant = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
   end
  
  module type SigGlobalValue = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
   end
  
  module type SigFunction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option
    
    val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val def_arg_size : LLVMsyntax.fdef -> nat
    
    val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ
    
    val dec_arg_size : LLVMsyntax.fdec -> nat
   end
  
  module type SigInstruction = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigReturnInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val hasReturnType : LLVMsyntax.terminator -> bool
    
    val getReturnType : LLVMsyntax.terminator -> LLVMsyntax.typ option
   end
  
  module type SigCallSite = 
   sig 
    val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ
    
    val arg_size : LLVMsyntax.fdef -> nat
    
    val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option
    
    val getArgumentType : LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCallInst = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
   end
  
  module type SigBinaryOperator = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getFirstOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getSecondOperandType :
      LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option
    
    val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option
   end
  
  module type SigPHINode = 
   sig 
    val getNumOperands : LLVMsyntax.insn -> nat
    
    val isCallInst : LLVMsyntax.cmd -> bool
    
    val getNumIncomingValues : LLVMsyntax.phinode -> nat
    
    val getIncomingValueType :
      LLVMsyntax.fdef -> LLVMsyntax.phinode -> LLVMsyntax.i -> LLVMsyntax.typ
      option
   end
  
  module type SigType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigDerivedType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigFunctionType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val getNumParams : LLVMsyntax.typ -> nat option
    
    val isVarArg : LLVMsyntax.typ -> bool
    
    val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option
   end
  
  module type SigCompositeType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
   end
  
  module type SigSequentialType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
   end
  
  module type SigArrayType = 
   sig 
    val isIntOrIntVector : LLVMsyntax.typ -> bool
    
    val isInteger : LLVMsyntax.typ -> bool
    
    val isSized : LLVMsyntax.typ -> bool
    
    val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz
    
    val hasElementType : LLVMsyntax.typ -> bool
    
    val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option
    
    val getNumElements : LLVMsyntax.typ -> nat
   end
  
  module Value = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
   end
  
  module User = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
   end
  
  module Constant = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_zeroinitializer t -> Some t
      | LLVMsyntax.Coq_const_int (sz0, i0) -> Some (LLVMsyntax.Coq_typ_int
          sz0)
      | LLVMsyntax.Coq_const_floatpoint (fp, f) -> Some
          (LLVMsyntax.Coq_typ_floatpoint fp)
      | LLVMsyntax.Coq_const_undef t -> Some t
      | LLVMsyntax.Coq_const_null t -> Some (LLVMsyntax.Coq_typ_pointer t)
      | LLVMsyntax.Coq_const_arr (t, lc) -> Some
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array
                 (LLVMsyntax.Size.coq_Zero, t)
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((LLVMsyntax.Size.from_nat
                    (length (LLVMsyntax.unmake_list_const lc))), t))
      | LLVMsyntax.Coq_const_struct lc ->
          (match getList_typ lc with
             | Some lt -> Some (LLVMsyntax.Coq_typ_struct lt)
             | None -> None)
      | LLVMsyntax.Coq_const_gid (t, i0) -> Some (LLVMsyntax.Coq_typ_pointer
          t)
      | LLVMsyntax.Coq_const_truncop (t0, c0, t) -> Some t
      | LLVMsyntax.Coq_const_extop (e, c0, t) -> Some t
      | LLVMsyntax.Coq_const_castop (c0, c1, t) -> Some t
      | LLVMsyntax.Coq_const_gep (i0, c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getConstGEPTyp idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_select (c0, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_extractvalue (c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getSubTypFromConstIdxs idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_insertvalue (c0, c', lc) -> getTyp c0
      | LLVMsyntax.Coq_const_bop (b, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_fbop (f, c1, c2) -> getTyp c1
      | _ -> Some (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
    
    (** val getList_typ :
        LLVMsyntax.list_const -> LLVMsyntax.list_typ option **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') ->
          let o = getTyp c in
          let o0 = getList_typ cs' in
          (match o with
             | Some t ->
                 (match o0 with
                    | Some ts' -> Some (LLVMsyntax.Cons_list_typ (t, ts'))
                    | None -> None)
             | None -> None)
    
    (** val gen_utyp_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let rec gen_utyp_maps_aux cid m t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (gen_utyps_maps_aux cid m ts0))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (gen_utyps_maps_aux cid m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          (match gen_utyp_maps_aux cid m t0 with
             | Some ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0)
             | None ->
                 (match t0 with
                    | LLVMsyntax.Coq_typ_namedt i0 ->
                        if AtomImpl.eq_atom_dec i0 cid then Some t else None
                    | _ -> None))
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val gen_utyps_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.list_typ -> LLVMsyntax.list_typ option **)
    
    and gen_utyps_maps_aux cid m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (gen_utyps_maps_aux cid m ts0)) (gen_utyp_maps_aux cid m t0)
    
    (** val gen_utyp_maps :
        LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec gen_utyp_maps = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id0, t) = n in
          let results = gen_utyp_maps nts' in
          (match gen_utyp_maps_aux id0 results t with
             | Some r -> (id0,r)::results
             | None -> results)
    
    (** val typ2utyp_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ ->
        LLVMsyntax.typ option **)
    
    let rec typ2utyp_aux m = function
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (typs2utyps_aux m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val typs2utyps_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ option **)
    
    and typs2utyps_aux m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
    
    (** val typ2utyp' :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp' nts t =
      let m = gen_utyp_maps (rev nts) in typ2utyp_aux m t
    
    (** val subst_typ :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ i' t' t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) -> LLVMsyntax.Coq_typ_array (s,
          (subst_typ i' t' t0))
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          LLVMsyntax.Coq_typ_function ((subst_typ i' t' t0),
          (subst_typs i' t' ts0), va)
      | LLVMsyntax.Coq_typ_struct ts0 -> LLVMsyntax.Coq_typ_struct
          (subst_typs i' t' ts0)
      | LLVMsyntax.Coq_typ_pointer t0 -> LLVMsyntax.Coq_typ_pointer
          (subst_typ i' t' t0)
      | LLVMsyntax.Coq_typ_namedt i0 ->
          if AtomImpl.eq_atom_dec i0 i' then t' else t
      | _ -> t
    
    (** val subst_typs :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ **)
    
    and subst_typs i' t' = function
      | LLVMsyntax.Nil_list_typ -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) -> LLVMsyntax.Cons_list_typ
          ((subst_typ i' t' t0), (subst_typs i' t' ts0))
    
    (** val subst_typ_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ_by_nts nts t =
      match nts with
        | [] -> t
        | n::nts' ->
            let LLVMsyntax.Coq_namedt_intro (id', t') = n in
            subst_typ_by_nts nts' (subst_typ id' t' t)
    
    (** val subst_nts_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.namedts ->
        (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec subst_nts_by_nts nts0 = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id', t') = n in
          (id',(subst_typ_by_nts nts0 t'))::(subst_nts_by_nts nts0 nts')
    
    (** val typ2utyp :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp nts t =
      let m = subst_nts_by_nts nts nts in typ2utyp_aux m t
   end
  
  module GlobalValue = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_zeroinitializer t -> Some t
      | LLVMsyntax.Coq_const_int (sz0, i0) -> Some (LLVMsyntax.Coq_typ_int
          sz0)
      | LLVMsyntax.Coq_const_floatpoint (fp, f) -> Some
          (LLVMsyntax.Coq_typ_floatpoint fp)
      | LLVMsyntax.Coq_const_undef t -> Some t
      | LLVMsyntax.Coq_const_null t -> Some (LLVMsyntax.Coq_typ_pointer t)
      | LLVMsyntax.Coq_const_arr (t, lc) -> Some
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array
                 (LLVMsyntax.Size.coq_Zero, t)
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((LLVMsyntax.Size.from_nat
                    (length (LLVMsyntax.unmake_list_const lc))), t))
      | LLVMsyntax.Coq_const_struct lc ->
          (match getList_typ lc with
             | Some lt -> Some (LLVMsyntax.Coq_typ_struct lt)
             | None -> None)
      | LLVMsyntax.Coq_const_gid (t, i0) -> Some (LLVMsyntax.Coq_typ_pointer
          t)
      | LLVMsyntax.Coq_const_truncop (t0, c0, t) -> Some t
      | LLVMsyntax.Coq_const_extop (e, c0, t) -> Some t
      | LLVMsyntax.Coq_const_castop (c0, c1, t) -> Some t
      | LLVMsyntax.Coq_const_gep (i0, c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getConstGEPTyp idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_select (c0, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_extractvalue (c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getSubTypFromConstIdxs idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_insertvalue (c0, c', lc) -> getTyp c0
      | LLVMsyntax.Coq_const_bop (b, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_fbop (f, c1, c2) -> getTyp c1
      | _ -> Some (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
    
    (** val getList_typ :
        LLVMsyntax.list_const -> LLVMsyntax.list_typ option **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') ->
          let o = getTyp c in
          let o0 = getList_typ cs' in
          (match o with
             | Some t ->
                 (match o0 with
                    | Some ts' -> Some (LLVMsyntax.Cons_list_typ (t, ts'))
                    | None -> None)
             | None -> None)
    
    (** val gen_utyp_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let rec gen_utyp_maps_aux cid m t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (gen_utyps_maps_aux cid m ts0))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (gen_utyps_maps_aux cid m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          (match gen_utyp_maps_aux cid m t0 with
             | Some ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0)
             | None ->
                 (match t0 with
                    | LLVMsyntax.Coq_typ_namedt i0 ->
                        if AtomImpl.eq_atom_dec i0 cid then Some t else None
                    | _ -> None))
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val gen_utyps_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.list_typ -> LLVMsyntax.list_typ option **)
    
    and gen_utyps_maps_aux cid m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (gen_utyps_maps_aux cid m ts0)) (gen_utyp_maps_aux cid m t0)
    
    (** val gen_utyp_maps :
        LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec gen_utyp_maps = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id0, t) = n in
          let results = gen_utyp_maps nts' in
          (match gen_utyp_maps_aux id0 results t with
             | Some r -> (id0,r)::results
             | None -> results)
    
    (** val typ2utyp_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ ->
        LLVMsyntax.typ option **)
    
    let rec typ2utyp_aux m = function
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (typs2utyps_aux m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val typs2utyps_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ option **)
    
    and typs2utyps_aux m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
    
    (** val typ2utyp' :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp' nts t =
      let m = gen_utyp_maps (rev nts) in typ2utyp_aux m t
    
    (** val subst_typ :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ i' t' t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) -> LLVMsyntax.Coq_typ_array (s,
          (subst_typ i' t' t0))
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          LLVMsyntax.Coq_typ_function ((subst_typ i' t' t0),
          (subst_typs i' t' ts0), va)
      | LLVMsyntax.Coq_typ_struct ts0 -> LLVMsyntax.Coq_typ_struct
          (subst_typs i' t' ts0)
      | LLVMsyntax.Coq_typ_pointer t0 -> LLVMsyntax.Coq_typ_pointer
          (subst_typ i' t' t0)
      | LLVMsyntax.Coq_typ_namedt i0 ->
          if AtomImpl.eq_atom_dec i0 i' then t' else t
      | _ -> t
    
    (** val subst_typs :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ **)
    
    and subst_typs i' t' = function
      | LLVMsyntax.Nil_list_typ -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) -> LLVMsyntax.Cons_list_typ
          ((subst_typ i' t' t0), (subst_typs i' t' ts0))
    
    (** val subst_typ_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ_by_nts nts t =
      match nts with
        | [] -> t
        | n::nts' ->
            let LLVMsyntax.Coq_namedt_intro (id', t') = n in
            subst_typ_by_nts nts' (subst_typ id' t' t)
    
    (** val subst_nts_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.namedts ->
        (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec subst_nts_by_nts nts0 = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id', t') = n in
          (id',(subst_typ_by_nts nts0 t'))::(subst_nts_by_nts nts0 nts')
    
    (** val typ2utyp :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp nts t =
      let m = subst_nts_by_nts nts nts in typ2utyp_aux m t
   end
  
  module Function = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val getTyp : LLVMsyntax.const -> LLVMsyntax.typ option **)
    
    let rec getTyp = function
      | LLVMsyntax.Coq_const_zeroinitializer t -> Some t
      | LLVMsyntax.Coq_const_int (sz0, i0) -> Some (LLVMsyntax.Coq_typ_int
          sz0)
      | LLVMsyntax.Coq_const_floatpoint (fp, f) -> Some
          (LLVMsyntax.Coq_typ_floatpoint fp)
      | LLVMsyntax.Coq_const_undef t -> Some t
      | LLVMsyntax.Coq_const_null t -> Some (LLVMsyntax.Coq_typ_pointer t)
      | LLVMsyntax.Coq_const_arr (t, lc) -> Some
          (match lc with
             | LLVMsyntax.Nil_list_const -> LLVMsyntax.Coq_typ_array
                 (LLVMsyntax.Size.coq_Zero, t)
             | LLVMsyntax.Cons_list_const (c', lc') ->
                 LLVMsyntax.Coq_typ_array
                 ((LLVMsyntax.Size.from_nat
                    (length (LLVMsyntax.unmake_list_const lc))), t))
      | LLVMsyntax.Coq_const_struct lc ->
          (match getList_typ lc with
             | Some lt -> Some (LLVMsyntax.Coq_typ_struct lt)
             | None -> None)
      | LLVMsyntax.Coq_const_gid (t, i0) -> Some (LLVMsyntax.Coq_typ_pointer
          t)
      | LLVMsyntax.Coq_const_truncop (t0, c0, t) -> Some t
      | LLVMsyntax.Coq_const_extop (e, c0, t) -> Some t
      | LLVMsyntax.Coq_const_castop (c0, c1, t) -> Some t
      | LLVMsyntax.Coq_const_gep (i0, c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getConstGEPTyp idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_select (c0, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_extractvalue (c0, idxs) ->
          (match getTyp c0 with
             | Some t -> getSubTypFromConstIdxs idxs t
             | None -> None)
      | LLVMsyntax.Coq_const_insertvalue (c0, c', lc) -> getTyp c0
      | LLVMsyntax.Coq_const_bop (b, c1, c2) -> getTyp c1
      | LLVMsyntax.Coq_const_fbop (f, c1, c2) -> getTyp c1
      | _ -> Some (LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_One)
    
    (** val getList_typ :
        LLVMsyntax.list_const -> LLVMsyntax.list_typ option **)
    
    and getList_typ = function
      | LLVMsyntax.Nil_list_const -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_const (c, cs') ->
          let o = getTyp c in
          let o0 = getList_typ cs' in
          (match o with
             | Some t ->
                 (match o0 with
                    | Some ts' -> Some (LLVMsyntax.Cons_list_typ (t, ts'))
                    | None -> None)
             | None -> None)
    
    (** val gen_utyp_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let rec gen_utyp_maps_aux cid m t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (gen_utyps_maps_aux cid m ts0))
            (gen_utyp_maps_aux cid m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (gen_utyps_maps_aux cid m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          (match gen_utyp_maps_aux cid m t0 with
             | Some ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0)
             | None ->
                 (match t0 with
                    | LLVMsyntax.Coq_typ_namedt i0 ->
                        if AtomImpl.eq_atom_dec i0 cid then Some t else None
                    | _ -> None))
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val gen_utyps_maps_aux :
        LLVMsyntax.id -> (LLVMsyntax.id*LLVMsyntax.typ) list ->
        LLVMsyntax.list_typ -> LLVMsyntax.list_typ option **)
    
    and gen_utyps_maps_aux cid m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (gen_utyps_maps_aux cid m ts0)) (gen_utyp_maps_aux cid m t0)
    
    (** val gen_utyp_maps :
        LLVMsyntax.namedts -> (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec gen_utyp_maps = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id0, t) = n in
          let results = gen_utyp_maps nts' in
          (match gen_utyp_maps_aux id0 results t with
             | Some r -> (id0,r)::results
             | None -> results)
    
    (** val typ2utyp_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.typ ->
        LLVMsyntax.typ option **)
    
    let rec typ2utyp_aux m = function
      | LLVMsyntax.Coq_typ_array (s, t0) ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_array (s, ut0)))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_function (ut0, uts0,
              va))) (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_struct ts0 ->
          mbind (fun uts0 -> Some (LLVMsyntax.Coq_typ_struct uts0))
            (typs2utyps_aux m ts0)
      | LLVMsyntax.Coq_typ_pointer t0 ->
          mbind (fun ut0 -> Some (LLVMsyntax.Coq_typ_pointer ut0))
            (typ2utyp_aux m t0)
      | LLVMsyntax.Coq_typ_namedt i0 -> lookupAL m i0
      | x -> Some x
    
    (** val typs2utyps_aux :
        (LLVMsyntax.id*LLVMsyntax.typ) list -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ option **)
    
    and typs2utyps_aux m = function
      | LLVMsyntax.Nil_list_typ -> Some LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) ->
          mbind (fun ut0 ->
            mbind (fun uts0 -> Some (LLVMsyntax.Cons_list_typ (ut0, uts0)))
              (typs2utyps_aux m ts0)) (typ2utyp_aux m t0)
    
    (** val typ2utyp' :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp' nts t =
      let m = gen_utyp_maps (rev nts) in typ2utyp_aux m t
    
    (** val subst_typ :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ i' t' t = match t with
      | LLVMsyntax.Coq_typ_array (s, t0) -> LLVMsyntax.Coq_typ_array (s,
          (subst_typ i' t' t0))
      | LLVMsyntax.Coq_typ_function (t0, ts0, va) ->
          LLVMsyntax.Coq_typ_function ((subst_typ i' t' t0),
          (subst_typs i' t' ts0), va)
      | LLVMsyntax.Coq_typ_struct ts0 -> LLVMsyntax.Coq_typ_struct
          (subst_typs i' t' ts0)
      | LLVMsyntax.Coq_typ_pointer t0 -> LLVMsyntax.Coq_typ_pointer
          (subst_typ i' t' t0)
      | LLVMsyntax.Coq_typ_namedt i0 ->
          if AtomImpl.eq_atom_dec i0 i' then t' else t
      | _ -> t
    
    (** val subst_typs :
        LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.list_typ ->
        LLVMsyntax.list_typ **)
    
    and subst_typs i' t' = function
      | LLVMsyntax.Nil_list_typ -> LLVMsyntax.Nil_list_typ
      | LLVMsyntax.Cons_list_typ (t0, ts0) -> LLVMsyntax.Cons_list_typ
          ((subst_typ i' t' t0), (subst_typs i' t' ts0))
    
    (** val subst_typ_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ **)
    
    let rec subst_typ_by_nts nts t =
      match nts with
        | [] -> t
        | n::nts' ->
            let LLVMsyntax.Coq_namedt_intro (id', t') = n in
            subst_typ_by_nts nts' (subst_typ id' t' t)
    
    (** val subst_nts_by_nts :
        LLVMsyntax.namedts -> LLVMsyntax.namedts ->
        (LLVMsyntax.id*LLVMsyntax.typ) list **)
    
    let rec subst_nts_by_nts nts0 = function
      | [] -> []
      | n::nts' ->
          let LLVMsyntax.Coq_namedt_intro (id', t') = n in
          (id',(subst_typ_by_nts nts0 t'))::(subst_nts_by_nts nts0 nts')
    
    (** val typ2utyp :
        LLVMsyntax.namedts -> LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let typ2utyp nts t =
      let m = subst_nts_by_nts nts nts in typ2utyp_aux m t
    
    (** val getDefReturnType : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getDefReturnType = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (f0, t, i0, a, v) = f in t
    
    (** val getDefFunctionType : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getDefFunctionType fd =
      getFdefTyp fd
    
    (** val def_arg_size : LLVMsyntax.fdef -> nat **)
    
    let def_arg_size = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (f0, t, i0, la, v) = f in
          length la
    
    (** val getDecReturnType : LLVMsyntax.fdec -> LLVMsyntax.typ **)
    
    let getDecReturnType = function
      | LLVMsyntax.Coq_fheader_intro (f, t, i0, a, v) -> t
    
    (** val getDecFunctionType : LLVMsyntax.fdec -> LLVMsyntax.typ **)
    
    let getDecFunctionType fd =
      getFdecTyp fd
    
    (** val dec_arg_size : LLVMsyntax.fdec -> nat **)
    
    let dec_arg_size = function
      | LLVMsyntax.Coq_fheader_intro (f, t, i0, la, v) -> length la
   end
  
  module Instruction = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
   end
  
  module ReturnInst = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val hasReturnType : LLVMsyntax.terminator -> bool **)
    
    let hasReturnType = function
      | LLVMsyntax.Coq_insn_return (i1, t, v) -> true
      | _ -> false
    
    (** val getReturnType :
        LLVMsyntax.terminator -> LLVMsyntax.typ option **)
    
    let getReturnType = function
      | LLVMsyntax.Coq_insn_return (i1, t, v) -> Some t
      | _ -> None
   end
  
  module CallSite = 
   struct 
    (** val getFdefTyp : LLVMsyntax.fdef -> LLVMsyntax.typ **)
    
    let getFdefTyp fd =
      getFdefTyp fd
    
    (** val arg_size : LLVMsyntax.fdef -> nat **)
    
    let arg_size = function
      | LLVMsyntax.Coq_fdef_intro (f, b) ->
          let LLVMsyntax.Coq_fheader_intro (f0, t, i0, la, v) = f in
          length la
    
    (** val getArgument : LLVMsyntax.fdef -> nat -> LLVMsyntax.arg option **)
    
    let getArgument fd i0 =
      let LLVMsyntax.Coq_fdef_intro (f, b) = fd in
      let LLVMsyntax.Coq_fheader_intro (f0, t, i1, la, v) = f in
      nth_error la i0
    
    (** val getArgumentType :
        LLVMsyntax.fdef -> nat -> LLVMsyntax.typ option **)
    
    let getArgumentType fd i0 =
      match getArgument fd i0 with
        | Some a -> let p,i1 = a in let t,a0 = p in Some t
        | None -> None
   end
  
  module CallInst = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
   end
  
  module BinaryOperator = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val getFirstOperandType :
        LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getFirstOperandType f = function
      | LLVMsyntax.Coq_insn_bop (i1, b, s, v1, v) ->
          (match v1 with
             | LLVMsyntax.Coq_value_id id1 -> lookupTypViaIDFromFdef f id1
             | LLVMsyntax.Coq_value_const c -> Constant.getTyp c)
      | _ -> None
    
    (** val getSecondOperandType :
        LLVMsyntax.fdef -> LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getSecondOperandType f = function
      | LLVMsyntax.Coq_insn_bop (i1, b, s, v, v2) ->
          (match v2 with
             | LLVMsyntax.Coq_value_id id2 -> lookupTypViaIDFromFdef f id2
             | LLVMsyntax.Coq_value_const c -> Constant.getTyp c)
      | _ -> None
    
    (** val getResultType : LLVMsyntax.cmd -> LLVMsyntax.typ option **)
    
    let getResultType i0 =
      getCmdTyp i0
   end
  
  module PHINode = 
   struct 
    (** val getNumOperands : LLVMsyntax.insn -> nat **)
    
    let getNumOperands i0 =
      length (getInsnOperands i0)
    
    (** val isCallInst : LLVMsyntax.cmd -> bool **)
    
    let isCallInst i0 =
      _isCallInsnB i0
    
    (** val getNumIncomingValues : LLVMsyntax.phinode -> nat **)
    
    let getNumIncomingValues = function
      | LLVMsyntax.Coq_insn_phi (i1, t, ln) ->
          length (LLVMsyntax.unmake_list_value_l ln)
    
    (** val getIncomingValueType :
        LLVMsyntax.fdef -> LLVMsyntax.phinode -> nat -> LLVMsyntax.typ option **)
    
    let getIncomingValueType f i0 n =
      let LLVMsyntax.Coq_insn_phi (i1, t, ln) = i0 in
      (match LLVMsyntax.nth_list_value_l n ln with
         | Some p ->
             let v,l0 = p in
             (match v with
                | LLVMsyntax.Coq_value_id id0 -> lookupTypViaIDFromFdef f id0
                | LLVMsyntax.Coq_value_const c -> Constant.getTyp c)
         | None -> None)
   end
  
  module Typ = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
   end
  
  module DerivedType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
   end
  
  module FunctionType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
    
    (** val getNumParams : LLVMsyntax.typ -> nat option **)
    
    let getNumParams = function
      | LLVMsyntax.Coq_typ_function (t0, lt, v) -> Some
          (length (LLVMsyntax.unmake_list_typ lt))
      | _ -> None
    
    (** val isVarArg : LLVMsyntax.typ -> bool **)
    
    let isVarArg t =
      false
    
    (** val getParamType : LLVMsyntax.typ -> nat -> LLVMsyntax.typ option **)
    
    let getParamType t i0 =
      match t with
        | LLVMsyntax.Coq_typ_function (t0, lt, v) ->
            LLVMsyntax.nth_list_typ i0 lt
        | _ -> None
   end
  
  module CompositeType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
   end
  
  module SequentialType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
    
    (** val hasElementType : LLVMsyntax.typ -> bool **)
    
    let hasElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> true
      | _ -> false
    
    (** val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let getElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> Some t'
      | _ -> None
   end
  
  module ArrayType = 
   struct 
    (** val isIntOrIntVector : LLVMsyntax.typ -> bool **)
    
    let isIntOrIntVector = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isInteger : LLVMsyntax.typ -> bool **)
    
    let isInteger = function
      | LLVMsyntax.Coq_typ_int s -> true
      | _ -> false
    
    (** val isSized : LLVMsyntax.typ -> bool **)
    
    let rec isSized = function
      | LLVMsyntax.Coq_typ_int s -> true
      | LLVMsyntax.Coq_typ_floatpoint f -> true
      | LLVMsyntax.Coq_typ_array (s, t') -> isSized t'
      | LLVMsyntax.Coq_typ_struct lt -> isSizedListTyp lt
      | LLVMsyntax.Coq_typ_pointer t0 -> true
      | _ -> false
    
    (** val isSizedListTyp : LLVMsyntax.list_typ -> bool **)
    
    and isSizedListTyp = function
      | LLVMsyntax.Nil_list_typ -> true
      | LLVMsyntax.Cons_list_typ (t, lt') ->
          if isSized t then isSizedListTyp lt' else false
    
    (** val getPrimitiveSizeInBits : LLVMsyntax.typ -> LLVMsyntax.sz **)
    
    let getPrimitiveSizeInBits = function
      | LLVMsyntax.Coq_typ_int sz0 -> sz0
      | _ -> LLVMsyntax.Size.coq_Zero
    
    (** val hasElementType : LLVMsyntax.typ -> bool **)
    
    let hasElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> true
      | _ -> false
    
    (** val getElementType : LLVMsyntax.typ -> LLVMsyntax.typ option **)
    
    let getElementType = function
      | LLVMsyntax.Coq_typ_array (s, t') -> Some t'
      | _ -> None
    
    (** val getNumElements : LLVMsyntax.typ -> nat **)
    
    let getNumElements = function
      | LLVMsyntax.Coq_typ_array (n, t0) -> LLVMsyntax.Size.to_nat n
      | _ -> O
   end
  
  (** val typ2memory_chunk : LLVMsyntax.typ -> memory_chunk option **)
  
  let typ2memory_chunk = function
    | LLVMsyntax.Coq_typ_int bsz -> Some (Mint
        (minus (LLVMsyntax.Size.to_nat bsz) (S O)))
    | LLVMsyntax.Coq_typ_floatpoint f ->
        (match f with
           | LLVMsyntax.Coq_fp_float -> Some Mfloat32
           | LLVMsyntax.Coq_fp_double -> Some Mfloat64
           | _ -> None)
    | LLVMsyntax.Coq_typ_pointer t0 -> Some (Mint (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))
    | _ -> None
  
  type reflect =
    | ReflectT
    | ReflectF
  
  (** val reflect_rect :
      (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)
  
  let reflect_rect f f0 b = function
    | ReflectT -> f __
    | ReflectF -> f0 __
  
  (** val reflect_rec :
      (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)
  
  let reflect_rec f f0 b = function
    | ReflectT -> f __
    | ReflectF -> f0 __
 end

