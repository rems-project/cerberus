open BinInt
open BinPos
open CoqEqDec
open Coqlib
open Datatypes
open List0
open Metatheory
open MetatheoryAtom
open Alist
open Genericvalues
open Infrastructure
open Monad
open Sub_symexe
open Syntax
open Targetdata

(** val eq_value : LLVMsyntax.value -> LLVMsyntax.value -> bool **)

let eq_value v v' =
  LLVMinfra.sumbool2bool (LLVMinfra.value_dec v v')

(** val tv_typ : LLVMsyntax.typ -> LLVMsyntax.typ -> bool **)

let tv_typ t0 t' =
  LLVMinfra.sumbool2bool (LLVMinfra.typ_dec t0 t')

(** val tv_align : LLVMsyntax.align -> LLVMsyntax.align -> bool **)

let tv_align a a' =
  LLVMinfra.sumbool2bool (LLVMsyntax.Align.dec a a')

(** val eq_sterm : SBSE.sterm -> SBSE.sterm -> bool **)

let eq_sterm st st' =
  LLVMinfra.sumbool2bool (SBSE.sterm_dec st st')

(** val eq_smem : SBSE.smem -> SBSE.smem -> bool **)

let eq_smem sm sm' =
  LLVMinfra.sumbool2bool (SBSE.smem_dec sm sm')

(** val eq_id : LLVMsyntax.id -> LLVMsyntax.id -> bool **)

let eq_id i i' =
  LLVMinfra.sumbool2bool (LLVMinfra.id_dec i i')

(** val eq_const : LLVMsyntax.const -> LLVMsyntax.const -> bool **)

let eq_const c c' =
  LLVMinfra.sumbool2bool (LLVMinfra.const_dec c c')

(** val eq_l : LLVMsyntax.l -> LLVMsyntax.l -> bool **)

let eq_l l1 l2 =
  LLVMinfra.sumbool2bool (LLVMinfra.l_dec l1 l2)

(** val bzeq : coq_Z -> coq_Z -> bool **)

let bzeq x y =
  LLVMinfra.sumbool2bool (zeq x y)

(** val eq_INT_Z : LLVMsyntax.coq_Int -> coq_Z -> bool **)

let eq_INT_Z = Symexe_aux.eq_INT_Z

module SBsyntax = 
 struct 
  type call =
    | Coq_insn_call_nptr of LLVMsyntax.id * LLVMsyntax.noret
       * LLVMsyntax.clattrs * LLVMsyntax.typ * LLVMsyntax.value
       * LLVMsyntax.params
    | Coq_insn_call_ptr of LLVMsyntax.id * LLVMsyntax.noret
       * LLVMsyntax.clattrs * LLVMsyntax.typ * LLVMsyntax.value
       * LLVMsyntax.params * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.const * 
       LLVMsyntax.const * LLVMsyntax.const
  
  (** val call_rect :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) ->
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const ->
      LLVMsyntax.const -> LLVMsyntax.const -> 'a1) -> call -> 'a1 **)
  
  let call_rect f f0 = function
    | Coq_insn_call_nptr (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
    | Coq_insn_call_ptr
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
        f0 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
  
  (** val call_rec :
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params -> 'a1) ->
      (LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value -> LLVMsyntax.params ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const ->
      LLVMsyntax.const -> LLVMsyntax.const -> 'a1) -> call -> 'a1 **)
  
  let call_rec f f0 = function
    | Coq_insn_call_nptr (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
    | Coq_insn_call_ptr
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) ->
        f0 x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
  
  (** val sz32 : LLVMsyntax.Size.t **)
  
  let sz32 =
    LLVMsyntax.Size.coq_ThirtyTwo
  
  (** val i32 : LLVMsyntax.typ **)
  
  let i32 =
    LLVMsyntax.Coq_typ_int sz32
  
  (** val i8 : LLVMsyntax.typ **)
  
  let i8 =
    LLVMsyntax.Coq_typ_int LLVMsyntax.Size.coq_Eight
  
  (** val p32 : LLVMsyntax.typ **)
  
  let p32 =
    LLVMsyntax.Coq_typ_pointer i32
  
  (** val p8 : LLVMsyntax.typ **)
  
  let p8 =
    LLVMsyntax.Coq_typ_pointer i8
  
  (** val pp32 : LLVMsyntax.typ **)
  
  let pp32 =
    LLVMsyntax.Coq_typ_pointer p32
  
  (** val pp8 : LLVMsyntax.typ **)
  
  let pp8 =
    LLVMsyntax.Coq_typ_pointer p8
  
  (** val cpars :
      LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.list_sz_value **)
  
  let cpars c1 c2 =
    LLVMsyntax.Cons_list_sz_value (sz32, (LLVMsyntax.Coq_value_const c1),
      (LLVMsyntax.Cons_list_sz_value (sz32, (LLVMsyntax.Coq_value_const c2),
      LLVMsyntax.Nil_list_sz_value)))
  
  (** val call_ptr :
      LLVMsyntax.id -> LLVMsyntax.noret -> LLVMsyntax.clattrs ->
      LLVMsyntax.typ -> LLVMsyntax.value ->
      ((LLVMsyntax.typ*LLVMsyntax.attribute list)*LLVMsyntax.value) list ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.id -> LLVMsyntax.const ->
      LLVMsyntax.const -> LLVMsyntax.const -> call*LLVMsyntax.cmd list **)
  
  let call_ptr rid nr tc t0 v p sid id1 id2 id3 id4 id5 id6 c0 c1 c2 =
    let vret = LLVMsyntax.Coq_value_id sid in
    let tret = LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_struct
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer t0),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      LLVMsyntax.Nil_list_typ)))))))
    in
    (Coq_insn_call_nptr (rid, nr, tc, t0, v,
    (((tret,[]),vret)::p))),((LLVMsyntax.Coq_insn_gep (id1, false, tret,
    vret, (cpars c0 c0)))::((LLVMsyntax.Coq_insn_load (id2, pp32,
    (LLVMsyntax.Coq_value_id id1),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id3, false, tret,
    vret, (cpars c0 c1)))::((LLVMsyntax.Coq_insn_load (id4, pp32,
    (LLVMsyntax.Coq_value_id id3),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id5, false, tret,
    vret, (cpars c0 c2)))::((LLVMsyntax.Coq_insn_load (id6, pp32,
    (LLVMsyntax.Coq_value_id id5), LLVMsyntax.Align.coq_One))::[]))))))
  
  type subblock = { coq_NBs : SBSE.nbranch list; call_cmd : call }
  
  (** val subblock_rect :
      (SBSE.nbranch list -> call -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rect f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0
  
  (** val subblock_rec :
      (SBSE.nbranch list -> call -> 'a1) -> subblock -> 'a1 **)
  
  let subblock_rec f s =
    let { coq_NBs = x; call_cmd = x0 } = s in f x x0
  
  (** val coq_NBs : subblock -> SBSE.nbranch list **)
  
  let coq_NBs x = x.coq_NBs
  
  (** val call_cmd : subblock -> call **)
  
  let call_cmd x = x.call_cmd
  
  type iterminator =
    | Coq_insn_return_ptr of LLVMsyntax.id * LLVMsyntax.typ * 
       LLVMsyntax.id * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.value * LLVMsyntax.id * LLVMsyntax.id * 
       LLVMsyntax.value * LLVMsyntax.id * LLVMsyntax.value * 
       LLVMsyntax.id * LLVMsyntax.const * LLVMsyntax.const * 
       LLVMsyntax.const
  
  (** val iterminator_rect :
      (LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id
      -> LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const -> 'a1) ->
      iterminator -> 'a1 **)
  
  let iterminator_rect f = function
    | Coq_insn_return_ptr
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
        f x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
  
  (** val iterminator_rec :
      (LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id
      -> LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const -> 'a1) ->
      iterminator -> 'a1 **)
  
  let iterminator_rec f = function
    | Coq_insn_return_ptr
        (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
        f x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
  
  (** val ret_ptr :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id
      -> LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const ->
      LLVMsyntax.cmd list*LLVMsyntax.terminator **)
  
  let ret_ptr sid t0 id1 id2 id30 v3 id4 id50 v5 id60 v6 id7 c0 c1 c2 =
    let vret = LLVMsyntax.Coq_value_id sid in
    let tret = LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_struct
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer t0),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      LLVMsyntax.Nil_list_typ)))))))
    in
    ((LLVMsyntax.Coq_insn_gep (id1, false, tret, vret,
    (cpars c0 c0)))::((LLVMsyntax.Coq_insn_gep (id2, false, tret, vret,
    (cpars c0 c1)))::((LLVMsyntax.Coq_insn_store (id30, p8, v3,
    (LLVMsyntax.Coq_value_id id2),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id4, false, tret,
    vret, (cpars c0 c2)))::((LLVMsyntax.Coq_insn_store (id50, p8, v5,
    (LLVMsyntax.Coq_value_id id4),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_store (id60,
    (LLVMsyntax.Coq_typ_pointer t0), v6, (LLVMsyntax.Coq_value_id id1),
    LLVMsyntax.Align.coq_One))::[])))))),(LLVMsyntax.Coq_insn_return_void
    id7)
  
  type block =
    | Coq_block_common of LLVMsyntax.l * LLVMsyntax.phinodes * 
       subblock list * SBSE.nbranch list * LLVMsyntax.terminator
    | Coq_block_ret_ptr of LLVMsyntax.l * LLVMsyntax.phinodes * 
       subblock list * SBSE.nbranch list * iterminator
  
  (** val block_rect :
      (LLVMsyntax.l -> LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch
      list -> LLVMsyntax.terminator -> 'a1) -> (LLVMsyntax.l ->
      LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch list ->
      iterminator -> 'a1) -> block -> 'a1 **)
  
  let block_rect f f0 = function
    | Coq_block_common (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_block_ret_ptr (x, x0, x1, x2, x3) -> f0 x x0 x1 x2 x3
  
  (** val block_rec :
      (LLVMsyntax.l -> LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch
      list -> LLVMsyntax.terminator -> 'a1) -> (LLVMsyntax.l ->
      LLVMsyntax.phinodes -> subblock list -> SBSE.nbranch list ->
      iterminator -> 'a1) -> block -> 'a1 **)
  
  let block_rec f f0 = function
    | Coq_block_common (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_block_ret_ptr (x, x0, x1, x2, x3) -> f0 x x0 x1 x2 x3
  
  type blocks = block list
  
  type fdef =
    | Coq_fdef_intro of LLVMsyntax.fheader * blocks
  
  (** val fdef_rect :
      (LLVMsyntax.fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rect f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  (** val fdef_rec : (LLVMsyntax.fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rec f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  type product =
    | Coq_product_gvar of LLVMsyntax.gvar
    | Coq_product_fdec of LLVMsyntax.fdec
    | Coq_product_fdef of fdef
  
  (** val product_rect :
      (LLVMsyntax.gvar -> 'a1) -> (LLVMsyntax.fdec -> 'a1) -> (fdef -> 'a1)
      -> product -> 'a1 **)
  
  let product_rect f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  (** val product_rec :
      (LLVMsyntax.gvar -> 'a1) -> (LLVMsyntax.fdec -> 'a1) -> (fdef -> 'a1)
      -> product -> 'a1 **)
  
  let product_rec f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of LLVMsyntax.layouts * LLVMsyntax.namedts * products
  
  (** val module_rect :
      (LLVMsyntax.layouts -> LLVMsyntax.namedts -> products -> 'a1) ->
      coq_module -> 'a1 **)
  
  let module_rect f = function
    | Coq_module_intro (x, x0, x1) -> f x x0 x1
  
  (** val module_rec :
      (LLVMsyntax.layouts -> LLVMsyntax.namedts -> products -> 'a1) ->
      coq_module -> 'a1 **)
  
  let module_rec f = function
    | Coq_module_intro (x, x0, x1) -> f x x0 x1
  
  type modules = coq_module list
  
  type system = modules
  
  (** val isCall_inv :
      LLVMsyntax.cmd ->
      ((((LLVMsyntax.id*LLVMsyntax.noret)*LLVMsyntax.clattrs)*LLVMsyntax.typ)*LLVMsyntax.value)*LLVMsyntax.params **)
  
  let isCall_inv = function
    | LLVMsyntax.Coq_insn_call (i0, n, c0, t0, v, p) ->
        ((((i0,n),c0),t0),v),p
    | _ -> assert false (* absurd case *)
  
  (** val get_named_ret_typs :
      LLVMsyntax.namedt list -> LLVMsyntax.id ->
      ((LLVMsyntax.typ*LLVMsyntax.typ)*LLVMsyntax.typ) option **)
  
  let rec get_named_ret_typs nts tid =
    match nts with
      | [] -> None
      | y::nts' ->
          let LLVMsyntax.Coq_namedt_intro (tid', t') = y in
          if eq_id tid tid'
          then (match t' with
                  | LLVMsyntax.Coq_typ_struct l0 ->
                      (match l0 with
                         | LLVMsyntax.Nil_list_typ -> None
                         | LLVMsyntax.Cons_list_typ (
                             t01, l1) ->
                             (match t01 with
                                | LLVMsyntax.Coq_typ_pointer t0 ->
                                    (match l1 with
                                       | LLVMsyntax.Nil_list_typ -> None
                                       | LLVMsyntax.Cons_list_typ
                                           (t02, l2) ->
                                           (match t02 with
                                              | LLVMsyntax.Coq_typ_pointer
                                                  t1 ->
                                                  (
                                                  match l2 with
                                                    | 
                                                  LLVMsyntax.Nil_list_typ ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_typ
                                                  (t03, l3) ->
                                                  (match t03 with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t2 ->
                                                  (match l3 with
                                                    | 
                                                  LLVMsyntax.Nil_list_typ ->
                                                  Some ((t01,t02),t03)
                                                    | 
                                                  LLVMsyntax.Cons_list_typ
                                                  (t3, l4) -> None)
                                                    | 
                                                  _ -> None))
                                              | _ -> None))
                                | _ -> None))
                  | LLVMsyntax.Coq_typ_namedt t0 ->
                      get_named_ret_typs nts' tid
                  | _ -> None)
          else get_named_ret_typs nts' tid
  
  (** val get_ret_typs :
      LLVMsyntax.namedt list -> LLVMsyntax.typ ->
      ((LLVMsyntax.typ*LLVMsyntax.typ)*LLVMsyntax.typ) option **)
  
  let rec get_ret_typs nts = function
    | LLVMsyntax.Coq_typ_struct l0 ->
        (match l0 with
           | LLVMsyntax.Nil_list_typ -> None
           | LLVMsyntax.Cons_list_typ (t01, l1) ->
               (match t01 with
                  | LLVMsyntax.Coq_typ_pointer t1 ->
                      (match l1 with
                         | LLVMsyntax.Nil_list_typ -> None
                         | LLVMsyntax.Cons_list_typ (
                             t02, l2) ->
                             (match t02 with
                                | LLVMsyntax.Coq_typ_pointer t2 ->
                                    (match l2 with
                                       | LLVMsyntax.Nil_list_typ -> None
                                       | LLVMsyntax.Cons_list_typ
                                           (t03, l3) ->
                                           (match t03 with
                                              | LLVMsyntax.Coq_typ_pointer
                                                  t3 ->
                                                  (
                                                  match l3 with
                                                    | 
                                                  LLVMsyntax.Nil_list_typ ->
                                                  Some ((t01,t02),t03)
                                                    | 
                                                  LLVMsyntax.Cons_list_typ
                                                  (t4, l4) -> None)
                                              | _ -> None))
                                | _ -> None))
                  | _ -> None))
    | LLVMsyntax.Coq_typ_namedt tid -> get_named_ret_typs nts tid
    | _ -> None
  
  (** val gen_icall :
      LLVMsyntax.namedt list ->
      ((LLVMsyntax.typ*LLVMsyntax.attributes)*LLVMsyntax.value) list ->
      LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd ->
      LLVMsyntax.cmd -> LLVMsyntax.cmd ->
      (((((((((((LLVMsyntax.params*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.typ)
      option **)
  
  let gen_icall nts pa1 c1 c2 c3 c4 c5 c6 =
    match c1 with
      | LLVMsyntax.Coq_insn_gep (id11, i, t1, v, l0) ->
          (match v with
             | LLVMsyntax.Coq_value_id id12 ->
                 (match l0 with
                    | LLVMsyntax.Nil_list_sz_value -> None
                    | LLVMsyntax.Cons_list_sz_value (
                        s, v0, l1) ->
                        (match v0 with
                           | LLVMsyntax.Coq_value_id i0 -> None
                           | LLVMsyntax.Coq_value_const c11 ->
                               (match c11 with
                                  | LLVMsyntax.Coq_const_int (
                                      s0, i11) ->
                                      (match l1 with
                                         | LLVMsyntax.Nil_list_sz_value ->
                                             None
                                         | LLVMsyntax.Cons_list_sz_value
                                             (s1, v1, l2) ->
                                             (match v1 with
                                                | LLVMsyntax.Coq_value_id
                                                  i0 -> None
                                                | LLVMsyntax.Coq_value_const
                                                  c12 ->
                                                  (match c12 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s2, i12) ->
                                                  (match l2 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c2 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_load
                                                  (id21, t2, v2, a) ->
                                                  (match v2 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id22 ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_gep
                                                  (id31, i0, t3, v3, l3) ->
                                                  (match v3 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id32 ->
                                                  (match l3 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s3, v4, l4) ->
                                                  (match v4 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c31 ->
                                                  (match c31 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s4, i31) ->
                                                  (match l4 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s5, v5, l5) ->
                                                  (match v5 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c32 ->
                                                  (match c32 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s6, i33) ->
                                                  (match l5 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c4 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_load
                                                  (id41, t4, v6, a0) ->
                                                  (match v6 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id42 ->
                                                  (match c5 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_gep
                                                  (id51, i1, t5, v7, l6) ->
                                                  (match v7 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id52 ->
                                                  (match l6 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s7, v8, l7) ->
                                                  (match v8 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i2 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c51 ->
                                                  (match c51 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s8, i51) ->
                                                  (match l7 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s9, v9, l8) ->
                                                  (match v9 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i2 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c52 ->
                                                  (match c52 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s10, i52) ->
                                                  (match l8 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c6 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_load
                                                  (id61, t6, v10, a1) ->
                                                  (match v10 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id62 ->
                                                  (match pa1 with
                                                    | 
                                                  [] -> None
                                                    | 
                                                  y::pa1' ->
                                                  let y0,y1 = y in
                                                  let y2,y3 = y0 in
                                                  (
                                                  match y2 with
                                                    | 
                                                  LLVMsyntax.Coq_typ_pointer
                                                  t0 ->
                                                  (match y1 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id0 ->
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if tv_typ t1 t3
                                                  then tv_typ t3 t5
                                                  else false
                                                  then tv_typ t5 t0
                                                  else false
                                                  then eq_id id0 id12
                                                  else false
                                                  then eq_id id0 id32
                                                  else false
                                                  then eq_id id0 id52
                                                  else false
                                                  then eq_id id11 id22
                                                  else false
                                                  then eq_id id31 id42
                                                  else false
                                                  then eq_id id51 id62
                                                  else false
                                                  then eq_const c11 c12
                                                  else false
                                                  then eq_const c11 c31
                                                  else false
                                                  then eq_const c11 c51
                                                  else false
                                                  then eq_INT_Z i11 Z0
                                                  else false
                                                  then 
                                                  eq_INT_Z i33 (Zpos Coq_xH)
                                                  else false
                                                  then 
                                                  eq_INT_Z i52 (Zpos (Coq_xO
                                                  Coq_xH))
                                                  else false
                                                  then 
                                                  (match 
                                                  get_ret_typs nts t0 with
                                                    | 
                                                  Some p ->
                                                  let p0,t03 = p in
                                                  let t01,t02 = p0 in
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if tv_typ t2 t01
                                                  then tv_typ t4 t02
                                                  else false
                                                  then tv_typ t6 t03
                                                  else false
                                                  then tv_typ t02 t03
                                                  else false
                                                  then 
                                                  tv_typ t02
                                                  (LLVMsyntax.Coq_typ_pointer
                                                  (LLVMsyntax.Coq_typ_int
                                                  LLVMsyntax.Size.coq_Eight))
                                                  else false
                                                  then 
                                                  Some
                                                  (((((((((((pa1',id12),id11),id21),id31),id41),id51),id61),c12),c32),c52),t01)
                                                  else None
                                                    | 
                                                  None -> None)
                                                  else None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None))
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s11, v10, l9) -> None)
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s7, v6, l6) -> None)
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s3, v2, l3) -> None)
                                                    | 
                                                  _ -> None)))
                                  | _ -> None)))
             | LLVMsyntax.Coq_value_const c -> None)
      | _ -> None
  
  (** val of_llvm_cmds :
      LLVMsyntax.namedts -> LLVMsyntax.cmds -> subblock list*SBSE.nbranch
      list **)
  
  let rec of_llvm_cmds nts = function
    | [] -> [],[]
    | c::cs' ->
        if SBSE.isCall_dec c
        then let l0,nbs0 = of_llvm_cmds nts cs' in
             (match l0 with
                | [] -> [],(c::nbs0)
                | s::sbs' ->
                    let { coq_NBs = nbs; call_cmd = call0 } = s in
                    ({ coq_NBs = (c::nbs); call_cmd = call0 }::sbs'),nbs0)
        else let p,pa1 = isCall_inv c in
             let p0,v1 = p in
             let p1,t1 = p0 in
             let p2,tc1 = p1 in
             let id1,nr1 = p2 in
             if tv_typ t1 LLVMsyntax.Coq_typ_void
             then (match cs' with
                     | [] ->
                         let p3 = of_llvm_cmds nts cs' in
                         let ic = Coq_insn_call_nptr (id1, nr1, tc1, t1, v1,
                           pa1)
                         in
                         let sbs,nbs0 = p3 in
                         ({ coq_NBs = []; call_cmd = ic }::sbs),nbs0
                     | c1::l0 ->
                         (match l0 with
                            | [] ->
                                let p3 = of_llvm_cmds nts cs' in
                                let ic = Coq_insn_call_nptr (id1, nr1, tc1,
                                  t1, v1, pa1)
                                in
                                let sbs,nbs0 = p3 in
                                ({ coq_NBs = []; call_cmd = ic }::sbs),nbs0
                            | c2::l1 ->
                                (match l1 with
                                   | [] ->
                                       let p3 = of_llvm_cmds nts cs' in
                                       let ic = Coq_insn_call_nptr (id1, nr1,
                                         tc1, t1, v1, pa1)
                                       in
                                       let sbs,nbs0 = p3 in
                                       ({ coq_NBs = []; call_cmd =
                                       ic }::sbs),nbs0
                                   | c3::l2 ->
                                       (match l2 with
                                          | [] ->
                                              let p3 = of_llvm_cmds nts cs'
                                              in
                                              let ic = Coq_insn_call_nptr
                                                (id1, nr1, tc1, t1, v1, pa1)
                                              in
                                              let sbs,nbs0 = p3 in
                                              ({ coq_NBs = []; call_cmd =
                                              ic }::sbs),nbs0
                                          | c4::l3 ->
                                              (match l3 with
                                                 | 
                                               [] ->
                                                 let p3 =
                                                  of_llvm_cmds nts cs'
                                                 in
                                                 let ic = Coq_insn_call_nptr
                                                  (id1, nr1, tc1, t1, v1,
                                                  pa1)
                                                 in
                                                 let sbs,nbs0 = p3 in
                                                 ({ coq_NBs = []; call_cmd =
                                                 ic }::sbs),nbs0
                                                 | 
                                               c5::l4 ->
                                                 (match l4 with
                                                    | 
                                                  [] ->
                                                  let p3 =
                                                  of_llvm_cmds nts cs'
                                                  in
                                                  let ic = Coq_insn_call_nptr
                                                  (id1, nr1, tc1, t1, v1,
                                                  pa1)
                                                  in
                                                  let sbs,nbs0 = p3 in
                                                  ({ coq_NBs = []; call_cmd =
                                                  ic }::sbs),nbs0
                                                    | 
                                                  c6::cs'' ->
                                                  (match 
                                                  gen_icall nts pa1 c1 c2 c3
                                                  c4 c5 c6 with
                                                    | 
                                                  Some p3 ->
                                                  let p4,rt = p3 in
                                                  let p5,cst2 = p4 in
                                                  let p6,cst1 = p5 in
                                                  let p7,cst0 = p6 in
                                                  let p9,id61 = p7 in
                                                  let p10,id51 = p9 in
                                                  let p11,id41 = p10 in
                                                  let p12,id31 = p11 in
                                                  let p13,id21 = p12 in
                                                  let p14,id11 = p13 in
                                                  let pa1',id12 = p14 in
                                                  let p15 =
                                                  of_llvm_cmds nts cs''
                                                  in
                                                  let ic = Coq_insn_call_ptr
                                                  (id1, nr1, tc1, rt, v1,
                                                  pa1', id12, id11, id21,
                                                  id31, id41, id51, id61,
                                                  cst0, cst1, cst2)
                                                  in
                                                  let sbs,nbs0 = p15 in
                                                  ({ coq_NBs = []; call_cmd =
                                                  ic }::sbs),nbs0
                                                    | 
                                                  None ->
                                                  let p3 =
                                                  of_llvm_cmds nts cs'
                                                  in
                                                  let ic = Coq_insn_call_nptr
                                                  (id1, nr1, tc1, t1, v1,
                                                  pa1)
                                                  in
                                                  let sbs,nbs0 = p3 in
                                                  ({ coq_NBs = []; call_cmd =
                                                  ic }::sbs),nbs0)))))))
             else let p3 = of_llvm_cmds nts cs' in
                  let ic = Coq_insn_call_nptr (id1, nr1, tc1, t1, v1, pa1) in
                  let sbs,nbs0 = p3 in
                  ({ coq_NBs = []; call_cmd = ic }::sbs),nbs0
  
  (** val gen_iret :
      LLVMsyntax.namedt list -> LLVMsyntax.typ -> LLVMsyntax.id ->
      LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.cmd ->
      LLVMsyntax.cmd -> LLVMsyntax.cmd -> LLVMsyntax.id ->
      ((((((((((((((LLVMsyntax.id*LLVMsyntax.typ)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.value)*LLVMsyntax.id)*LLVMsyntax.const)*LLVMsyntax.const)*LLVMsyntax.const)
      option **)
  
  let gen_iret nts t0 id0 c1 c2 c3 c4 c5 c6 id7 =
    match c1 with
      | LLVMsyntax.Coq_insn_gep (id11, i, t1, v, l0) ->
          (match v with
             | LLVMsyntax.Coq_value_id id12 ->
                 (match l0 with
                    | LLVMsyntax.Nil_list_sz_value -> None
                    | LLVMsyntax.Cons_list_sz_value (
                        s, v0, l1) ->
                        (match v0 with
                           | LLVMsyntax.Coq_value_id i0 -> None
                           | LLVMsyntax.Coq_value_const c11 ->
                               (match c11 with
                                  | LLVMsyntax.Coq_const_int (
                                      s0, i11) ->
                                      (match l1 with
                                         | LLVMsyntax.Nil_list_sz_value ->
                                             None
                                         | LLVMsyntax.Cons_list_sz_value
                                             (s1, v1, l2) ->
                                             (match v1 with
                                                | LLVMsyntax.Coq_value_id
                                                  i0 -> None
                                                | LLVMsyntax.Coq_value_const
                                                  c12 ->
                                                  (match c12 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s2, i12) ->
                                                  (match l2 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c2 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_gep
                                                  (id21, i0, t2, v2, l3) ->
                                                  (match v2 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id22 ->
                                                  (match l3 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s3, v3, l4) ->
                                                  (match v3 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c21 ->
                                                  (match c21 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s4, i21) ->
                                                  (match l4 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s5, v4, l5) ->
                                                  (match v4 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i1 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c22 ->
                                                  (match c22 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s6, i22) ->
                                                  (match l5 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c3 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_store
                                                  (id31, t3, v5, v6, a) ->
                                                  (match v6 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id32 ->
                                                  (match c4 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_gep
                                                  (id41, i1, t4, v7, l6) ->
                                                  (match v7 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id42 ->
                                                  (match l6 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s7, v8, l7) ->
                                                  (match v8 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i2 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c41 ->
                                                  (match c41 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s8, i41) ->
                                                  (match l7 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  None
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s9, v9, l8) ->
                                                  (match v9 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  i2 -> None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c42 ->
                                                  (match c42 with
                                                    | 
                                                  LLVMsyntax.Coq_const_int
                                                  (s10, i42) ->
                                                  (match l8 with
                                                    | 
                                                  LLVMsyntax.Nil_list_sz_value ->
                                                  (match c5 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_store
                                                  (id51, t5, v10, v11, a0) ->
                                                  (match v11 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id52 ->
                                                  (match c6 with
                                                    | 
                                                  LLVMsyntax.Coq_insn_store
                                                  (id61, t6, v12, v13, a1) ->
                                                  (match v13 with
                                                    | 
                                                  LLVMsyntax.Coq_value_id
                                                  id62 ->
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  tv_typ t0
                                                  (LLVMsyntax.Coq_typ_pointer
                                                  t1)
                                                  then tv_typ t1 t2
                                                  else false
                                                  then tv_typ t2 t4
                                                  else false
                                                  then eq_id id0 id12
                                                  else false
                                                  then eq_id id12 id22
                                                  else false
                                                  then eq_id id22 id42
                                                  else false
                                                  then eq_id id11 id62
                                                  else false
                                                  then eq_id id21 id32
                                                  else false
                                                  then eq_id id41 id52
                                                  else false
                                                  then eq_const c11 c12
                                                  else false
                                                  then eq_const c11 c21
                                                  else false
                                                  then eq_const c11 c41
                                                  else false
                                                  then eq_INT_Z i11 Z0
                                                  else false
                                                  then 
                                                  eq_INT_Z i22 (Zpos Coq_xH)
                                                  else false
                                                  then 
                                                  eq_INT_Z i42 (Zpos (Coq_xO
                                                  Coq_xH))
                                                  else false
                                                  then 
                                                  (match 
                                                  get_ret_typs nts t1 with
                                                    | 
                                                  Some p ->
                                                  let p0,t03 = p in
                                                  let t01,t02 = p0 in
                                                  if 
                                                  if 
                                                  if 
                                                  if 
                                                  if tv_typ t6 t01
                                                  then tv_typ t3 t02
                                                  else false
                                                  then tv_typ t5 t03
                                                  else false
                                                  then tv_typ t02 t03
                                                  else false
                                                  then 
                                                  tv_typ t02
                                                  (LLVMsyntax.Coq_typ_pointer
                                                  (LLVMsyntax.Coq_typ_int
                                                  LLVMsyntax.Size.coq_Eight))
                                                  else false
                                                  then 
                                                  Some
                                                  ((((((((((((((id12,t6),id11),id21),id31),v5),id41),id51),v10),id61),v12),id7),c12),c22),c42)
                                                  else None
                                                    | 
                                                  None -> None)
                                                  else None
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s11, v10, l9) -> None)
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s7, v5, l6) -> None)
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  _ -> None)))
                                                    | 
                                                  LLVMsyntax.Coq_value_const
                                                  c -> None)
                                                    | 
                                                  _ -> None)
                                                    | 
                                                  LLVMsyntax.Cons_list_sz_value
                                                  (s3, v2, l3) -> None)
                                                    | 
                                                  _ -> None)))
                                  | _ -> None)))
             | LLVMsyntax.Coq_value_const c -> None)
      | _ -> None
  
  (** val get_last_six_insns :
      LLVMsyntax.cmds ->
      LLVMsyntax.cmds*(((((LLVMsyntax.cmd*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)*LLVMsyntax.cmd)
      option **)
  
  let get_last_six_insns cs =
    match rev cs with
      | [] -> cs,None
      | c6::l0 ->
          (match l0 with
             | [] -> cs,None
             | c5::l1 ->
                 (match l1 with
                    | [] -> cs,None
                    | c4::l2 ->
                        (match l2 with
                           | [] -> cs,None
                           | c3::l3 ->
                               (match l3 with
                                  | [] -> cs,None
                                  | c2::l4 ->
                                      (match l4 with
                                         | [] -> cs,None
                                         | c1::cs' -> 
                                             (rev cs'),(Some
                                             (((((c1,c2),c3),c4),c5),c6)))))))
  
  (** val of_llvm_block :
      (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.fheader ->
      LLVMsyntax.block -> block **)
  
  let of_llvm_block tD fd b =
    let los,nts = tD in
    let LLVMsyntax.Coq_block_intro (l1, ps1, cs1, tmn1) = b in
    let LLVMsyntax.Coq_fheader_intro (f, t0, i, a, v) = fd in
    (match a with
       | [] ->
           let op = None in
           let sbs2,cs2 = of_llvm_cmds nts cs1 in
           (match op with
              | Some p ->
                  let p0,cst2 = p in
                  let p1,cst1 = p0 in
                  let p2,cst0 = p1 in
                  let p3,id7 = p2 in
                  let p4,v6 = p3 in
                  let p5,id60 = p4 in
                  let p6,v5 = p5 in
                  let p7,id50 = p6 in
                  let p9,id4 = p7 in
                  let p10,v3 = p9 in
                  let p11,id30 = p10 in
                  let p12,id2 = p11 in
                  let p13,id1 = p12 in
                  let sid,t1 = p13 in
                  Coq_block_ret_ptr (l1, ps1, sbs2, cs2, (Coq_insn_return_ptr
                  (sid, t1, id1, id2, id30, v3, id4, id50, v5, id60, v6, id7,
                  cst0, cst1, cst2)))
              | None -> Coq_block_common (l1, ps1, sbs2, cs2, tmn1))
       | p::l0 ->
           let p0,id2 = p in
           let t2,a0 = p0 in
           (match tmn1 with
              | LLVMsyntax.Coq_insn_return (i0, t1, v0) ->
                  let op = None in
                  let sbs2,cs2 = of_llvm_cmds nts cs1 in
                  (match op with
                     | Some p1 ->
                         let p2,cst2 = p1 in
                         let p3,cst1 = p2 in
                         let p4,cst0 = p3 in
                         let p5,id7 = p4 in
                         let p6,v6 = p5 in
                         let p7,id60 = p6 in
                         let p9,v5 = p7 in
                         let p10,id50 = p9 in
                         let p11,id4 = p10 in
                         let p12,v3 = p11 in
                         let p13,id30 = p12 in
                         let p14,id3 = p13 in
                         let p15,id1 = p14 in
                         let sid,t3 = p15 in
                         Coq_block_ret_ptr (l1, ps1, sbs2, cs2,
                         (Coq_insn_return_ptr (sid, t3, id1, id3, id30, v3,
                         id4, id50, v5, id60, v6, id7, cst0, cst1, cst2)))
                     | None -> Coq_block_common (l1, ps1, sbs2, cs2, tmn1))
              | LLVMsyntax.Coq_insn_return_void id7 ->
                  let cs1',opcs6 = get_last_six_insns cs1 in
                  (match opcs6 with
                     | Some p1 ->
                         let p2,c6 = p1 in
                         let p3,c5 = p2 in
                         let p4,c4 = p3 in
                         let p5,c3 = p4 in
                         let c1,c2 = p5 in
                         (match gen_iret nts t2 id2 c1 c2 c3 c4 c5 c6 id7 with
                            | Some p6 ->
                                let op = Some p6 in
                                let sbs2,cs2 = of_llvm_cmds nts cs1' in
                                (match op with
                                   | Some p7 ->
                                       let p9,cst2 = p7 in
                                       let p10,cst1 = p9 in
                                       let p11,cst0 = p10 in
                                       let p12,id8 = p11 in
                                       let p13,v6 = p12 in
                                       let p14,id60 = p13 in
                                       let p15,v5 = p14 in
                                       let p16,id50 = p15 in
                                       let p17,id4 = p16 in
                                       let p18,v3 = p17 in
                                       let p19,id30 = p18 in
                                       let p20,id3 = p19 in
                                       let p21,id1 = p20 in
                                       let sid,t1 = p21 in
                                       Coq_block_ret_ptr (l1, ps1, sbs2, cs2,
                                       (Coq_insn_return_ptr (sid, t1, id1,
                                       id3, id30, v3, id4, id50, v5, id60,
                                       v6, id8, cst0, cst1, cst2)))
                                   | None -> Coq_block_common (l1, ps1, sbs2,
                                       cs2, tmn1))
                            | None ->
                                let op = None in
                                let sbs2,cs2 = of_llvm_cmds nts cs1 in
                                (match op with
                                   | Some p6 ->
                                       let p7,cst2 = p6 in
                                       let p9,cst1 = p7 in
                                       let p10,cst0 = p9 in
                                       let p11,id8 = p10 in
                                       let p12,v6 = p11 in
                                       let p13,id60 = p12 in
                                       let p14,v5 = p13 in
                                       let p15,id50 = p14 in
                                       let p16,id4 = p15 in
                                       let p17,v3 = p16 in
                                       let p18,id30 = p17 in
                                       let p19,id3 = p18 in
                                       let p20,id1 = p19 in
                                       let sid,t1 = p20 in
                                       Coq_block_ret_ptr (l1, ps1, sbs2, cs2,
                                       (Coq_insn_return_ptr (sid, t1, id1,
                                       id3, id30, v3, id4, id50, v5, id60,
                                       v6, id8, cst0, cst1, cst2)))
                                   | None -> Coq_block_common (l1, ps1, sbs2,
                                       cs2, tmn1)))
                     | None ->
                         let op = None in
                         let sbs2,cs2 = of_llvm_cmds nts cs1 in
                         (match op with
                            | Some p1 ->
                                let p2,cst2 = p1 in
                                let p3,cst1 = p2 in
                                let p4,cst0 = p3 in
                                let p5,id8 = p4 in
                                let p6,v6 = p5 in
                                let p7,id60 = p6 in
                                let p9,v5 = p7 in
                                let p10,id50 = p9 in
                                let p11,id4 = p10 in
                                let p12,v3 = p11 in
                                let p13,id30 = p12 in
                                let p14,id3 = p13 in
                                let p15,id1 = p14 in
                                let sid,t1 = p15 in
                                Coq_block_ret_ptr (l1, ps1, sbs2, cs2,
                                (Coq_insn_return_ptr (sid, t1, id1, id3,
                                id30, v3, id4, id50, v5, id60, v6, id8, cst0,
                                cst1, cst2)))
                            | None -> Coq_block_common (l1, ps1, sbs2, cs2,
                                tmn1)))
              | _ ->
                  let op = None in
                  let sbs2,cs2 = of_llvm_cmds nts cs1 in
                  (match op with
                     | Some p1 ->
                         let p2,cst2 = p1 in
                         let p3,cst1 = p2 in
                         let p4,cst0 = p3 in
                         let p5,id7 = p4 in
                         let p6,v6 = p5 in
                         let p7,id60 = p6 in
                         let p9,v5 = p7 in
                         let p10,id50 = p9 in
                         let p11,id4 = p10 in
                         let p12,v3 = p11 in
                         let p13,id30 = p12 in
                         let p14,id3 = p13 in
                         let p15,id1 = p14 in
                         let sid,t1 = p15 in
                         Coq_block_ret_ptr (l1, ps1, sbs2, cs2,
                         (Coq_insn_return_ptr (sid, t1, id1, id3, id30, v3,
                         id4, id50, v5, id60, v6, id7, cst0, cst1, cst2)))
                     | None -> Coq_block_common (l1, ps1, sbs2, cs2, tmn1))))
  
  (** val of_llvm_fdef :
      (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.fdef -> fdef **)
  
  let of_llvm_fdef tD = function
    | LLVMsyntax.Coq_fdef_intro (f0, lb) -> Coq_fdef_intro (f0,
        (map (of_llvm_block tD f0) lb))
  
  (** val of_llvm_products :
      (LLVMsyntax.layouts*LLVMsyntax.namedts) -> LLVMsyntax.products ->
      products **)
  
  let rec of_llvm_products tD = function
    | [] -> []
    | p::ps' ->
        (match p with
           | LLVMsyntax.Coq_product_gvar g -> (Coq_product_gvar
               g)::(of_llvm_products tD ps')
           | LLVMsyntax.Coq_product_fdec f -> (Coq_product_fdec
               f)::(of_llvm_products tD ps')
           | LLVMsyntax.Coq_product_fdef f -> (Coq_product_fdef
               (of_llvm_fdef tD f))::(of_llvm_products tD ps'))
  
  (** val of_llvm_module : LLVMsyntax.coq_module -> coq_module **)
  
  let of_llvm_module = function
    | LLVMsyntax.Coq_module_intro (los, nts, ps) -> Coq_module_intro (los,
        nts, (of_llvm_products (los,nts) ps))
  
  (** val of_llvm_system : LLVMsyntax.system -> system **)
  
  let of_llvm_system s =
    map of_llvm_module s
  
  (** val call_to_llvm_cmds : call -> LLVMsyntax.cmds **)
  
  let call_to_llvm_cmds = function
    | Coq_insn_call_nptr (rid, nr, ca, t0, v, p) ->
        EnvImpl.one (LLVMsyntax.Coq_insn_call (rid, nr, ca, t0, v, p))
    | Coq_insn_call_ptr
        (rid, nr, tc, t0, v, p, sid, id1, id2, id3, id4, id5, id6, c0, c1, c2) ->
        let vret = LLVMsyntax.Coq_value_id sid in
        let tret = LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_struct
          (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer t0),
          (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
          (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
          LLVMsyntax.Nil_list_typ)))))))
        in
        (LLVMsyntax.Coq_insn_call (rid, nr, tc, t0, v,
        (((tret,[]),vret)::p)))::((LLVMsyntax.Coq_insn_gep (id1, false, tret,
        vret, (cpars c0 c0)))::((LLVMsyntax.Coq_insn_load (id2, pp32,
        (LLVMsyntax.Coq_value_id id1),
        LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id3, false,
        tret, vret, (cpars c0 c1)))::((LLVMsyntax.Coq_insn_load (id4, pp32,
        (LLVMsyntax.Coq_value_id id3),
        LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id5, false,
        tret, vret, (cpars c0 c2)))::((LLVMsyntax.Coq_insn_load (id6, pp32,
        (LLVMsyntax.Coq_value_id id5), LLVMsyntax.Align.coq_One))::[]))))))
  
  (** val subblock_to_llvm_cmds : subblock -> LLVMsyntax.cmds **)
  
  let subblock_to_llvm_cmds sb =
    let { coq_NBs = cs; call_cmd = c } = sb in
    app (map SBSE.nbranching_cmd cs) (call_to_llvm_cmds c)
  
  (** val ret_ptr_to_tmn :
      LLVMsyntax.id -> LLVMsyntax.typ -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.id ->
      LLVMsyntax.value -> LLVMsyntax.id -> LLVMsyntax.value -> LLVMsyntax.id
      -> LLVMsyntax.const -> LLVMsyntax.const -> LLVMsyntax.const ->
      LLVMsyntax.cmd list*LLVMsyntax.terminator **)
  
  let ret_ptr_to_tmn sid t0 id1 id2 id30 v3 id4 id50 v5 id60 v6 id7 c0 c1 c2 =
    let vret = LLVMsyntax.Coq_value_id sid in
    let tret = LLVMsyntax.Coq_typ_pointer (LLVMsyntax.Coq_typ_struct
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer t0),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      (LLVMsyntax.Cons_list_typ ((LLVMsyntax.Coq_typ_pointer p8),
      LLVMsyntax.Nil_list_typ)))))))
    in
    ((LLVMsyntax.Coq_insn_gep (id1, false, tret, vret,
    (cpars c0 c0)))::((LLVMsyntax.Coq_insn_gep (id2, false, tret, vret,
    (cpars c0 c1)))::((LLVMsyntax.Coq_insn_store (id30, p8, v3,
    (LLVMsyntax.Coq_value_id id2),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_gep (id4, false, tret,
    vret, (cpars c0 c2)))::((LLVMsyntax.Coq_insn_store (id50, p8, v5,
    (LLVMsyntax.Coq_value_id id4),
    LLVMsyntax.Align.coq_One))::((LLVMsyntax.Coq_insn_store (id60,
    (LLVMsyntax.Coq_typ_pointer t0), v6, (LLVMsyntax.Coq_value_id id1),
    LLVMsyntax.Align.coq_One))::[])))))),(LLVMsyntax.Coq_insn_return_void
    id7)
  
  (** val itmn_to_llvm_tmn :
      iterminator -> LLVMsyntax.cmds*LLVMsyntax.terminator **)
  
  let itmn_to_llvm_tmn = function
    | Coq_insn_return_ptr
        (i0, t0, i1, i2, i3, v, i4, i5, v0, i6, v1, i7, c, c0, c1) ->
        ret_ptr_to_tmn i0 t0 i1 i2 i3 v i4 i5 v0 i6 v1 i7 c c0 c1
  
  (** val to_llvm_block : block -> LLVMsyntax.block **)
  
  let to_llvm_block = function
    | Coq_block_common (l1, ps1, sbs, cs, tmn) -> LLVMsyntax.Coq_block_intro
        (l1, ps1,
        (app
          (fold_left (fun accum sb -> app accum (subblock_to_llvm_cmds sb))
            sbs []) (map SBSE.nbranching_cmd cs)), tmn)
    | Coq_block_ret_ptr (l1, ps1, sbs, cs, tmn) ->
        let cs0,tmn0 = itmn_to_llvm_tmn tmn in
        LLVMsyntax.Coq_block_intro (l1, ps1,
        (app
          (fold_left (fun accum sb -> app accum (subblock_to_llvm_cmds sb))
            sbs []) (app (map SBSE.nbranching_cmd cs) cs0)), tmn0)
  
  (** val to_llvm_fdef : fdef -> LLVMsyntax.fdef **)
  
  let to_llvm_fdef = function
    | Coq_fdef_intro (fh, bs) -> LLVMsyntax.Coq_fdef_intro (fh,
        (map to_llvm_block bs))
  
  (** val to_llvm_product : product -> LLVMsyntax.product **)
  
  let to_llvm_product = function
    | Coq_product_gvar g -> LLVMsyntax.Coq_product_gvar g
    | Coq_product_fdec f -> LLVMsyntax.Coq_product_fdec f
    | Coq_product_fdef f -> LLVMsyntax.Coq_product_fdef (to_llvm_fdef f)
  
  (** val to_llvm_products : products -> LLVMsyntax.products **)
  
  let to_llvm_products ps =
    map to_llvm_product ps
  
  (** val to_llvm_module : coq_module -> LLVMsyntax.coq_module **)
  
  let to_llvm_module = function
    | Coq_module_intro (los, nts, ps) -> LLVMsyntax.Coq_module_intro (los,
        nts, (to_llvm_products ps))
  
  (** val to_llvm_system : system -> LLVMsyntax.system **)
  
  let to_llvm_system s =
    map to_llvm_module s
  
  (** val getFheader : fdef -> LLVMsyntax.fheader **)
  
  let getFheader = function
    | Coq_fdef_intro (fh, b) -> fh
  
  type l2block = (LLVMsyntax.l*block) list
  
  (** val genLabel2Block_block : block -> l2block **)
  
  let genLabel2Block_block b = match b with
    | Coq_block_common (l0, p, l1, l2, t0) -> (l0,b)::[]
    | Coq_block_ret_ptr (l0, p, l1, l2, i) -> (l0,b)::[]
  
  (** val genLabel2Block_blocks : blocks -> l2block **)
  
  let rec genLabel2Block_blocks = function
    | [] -> []
    | b::bs' -> app (genLabel2Block_block b) (genLabel2Block_blocks bs')
  
  (** val genLabel2Block_fdef : fdef -> l2block **)
  
  let genLabel2Block_fdef = function
    | Coq_fdef_intro (fheader0, blocks0) -> genLabel2Block_blocks blocks0
  
  (** val lookupBlockViaLabelFromFdef :
      fdef -> LLVMsyntax.l -> block option **)
  
  let lookupBlockViaLabelFromFdef f l0 =
    lookupAL (genLabel2Block_fdef f) l0
  
  (** val getPHINodesFromBlock : block -> LLVMsyntax.phinode list **)
  
  let getPHINodesFromBlock = function
    | Coq_block_common (l0, lp, l1, l2, t0) -> lp
    | Coq_block_ret_ptr (l0, lp, l1, l2, i) -> lp
  
  (** val getValueViaBlockFromValuels :
      LLVMsyntax.list_value_l -> block -> LLVMsyntax.value option **)
  
  let getValueViaBlockFromValuels vls = function
    | Coq_block_common (l0, p, l1, l2, t0) ->
        LLVMinfra.getValueViaLabelFromValuels vls l0
    | Coq_block_ret_ptr (l0, p, l1, l2, i) ->
        LLVMinfra.getValueViaLabelFromValuels vls l0
  
  (** val getValueViaBlockFromPHINode :
      LLVMsyntax.phinode -> block -> LLVMsyntax.value option **)
  
  let getValueViaBlockFromPHINode i b =
    let LLVMsyntax.Coq_insn_phi (i0, t0, vls) = i in
    getValueViaBlockFromValuels vls b
  
  (** val getIncomingValuesForBlockFromPHINodes :
      LLVMtd.coq_TargetData -> LLVMsyntax.phinode list -> block ->
      LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap ->
      (LLVMsyntax.id*LLVMgv.coq_GenericValue) list option **)
  
  let rec getIncomingValuesForBlockFromPHINodes tD pNs b globals locals =
    match pNs with
      | [] -> Some []
      | p::pNs0 ->
          let LLVMsyntax.Coq_insn_phi (id0, t0, vls) = p in
          (match getValueViaBlockFromPHINode (LLVMsyntax.Coq_insn_phi (id0,
                   t0, vls)) b with
             | Some v ->
                 (match v with
                    | LLVMsyntax.Coq_value_id id1 ->
                        let o = lookupAL locals id1 in
                        let o0 =
                          getIncomingValuesForBlockFromPHINodes tD pNs0 b
                            globals locals
                        in
                        (match o with
                           | Some gv1 ->
                               (match o0 with
                                  | Some idgvs -> Some ((id0,gv1)::idgvs)
                                  | None -> None)
                           | None -> None)
                    | LLVMsyntax.Coq_value_const c ->
                        let o = LLVMgv.const2GV tD globals c in
                        let o0 =
                          getIncomingValuesForBlockFromPHINodes tD pNs0 b
                            globals locals
                        in
                        (match o with
                           | Some gv1 ->
                               (match o0 with
                                  | Some idgvs -> Some ((id0,gv1)::idgvs)
                                  | None -> None)
                           | None -> None))
             | None -> None)
  
  (** val updateValuesForNewBlock :
      (LLVMsyntax.id*LLVMgv.coq_GenericValue) list -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap **)
  
  let rec updateValuesForNewBlock resultValues locals =
    match resultValues with
      | [] -> locals
      | p::resultValues' ->
          let id0,v = p in
          updateAddAL (updateValuesForNewBlock resultValues' locals) id0 v
  
  (** val switchToNewBasicBlock :
      LLVMtd.coq_TargetData -> block -> block -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap option **)
  
  let switchToNewBasicBlock tD dest prevBB globals locals =
    let pNs = getPHINodesFromBlock dest in
    (match getIncomingValuesForBlockFromPHINodes tD pNs prevBB globals locals with
       | Some resultValues -> Some
           (updateValuesForNewBlock resultValues locals)
       | None -> None)
  
  (** val lookupFdecViaIDFromProduct :
      product -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let lookupFdecViaIDFromProduct p i =
    match p with
      | Coq_product_fdec fd ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)
               (LLVMinfra.getFdecID fd) i
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdecViaIDFromProducts :
      products -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecViaIDFromProducts lp i =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdecViaIDFromProduct p i with
             | Some fd -> Some fd
             | None -> lookupFdecViaIDFromProducts lp' i)
  
  (** val getFdefID : fdef -> LLVMsyntax.id **)
  
  let getFdefID = function
    | Coq_fdef_intro (fh, b) -> LLVMinfra.getFheaderID fh
  
  (** val lookupFdefViaIDFromProduct :
      product -> LLVMsyntax.id -> fdef option **)
  
  let lookupFdefViaIDFromProduct p i =
    match p with
      | Coq_product_fdef fd ->
          if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) (getFdefID fd) i
          then Some fd
          else None
      | _ -> None
  
  (** val lookupFdefViaIDFromProducts :
      products -> LLVMsyntax.id -> fdef option **)
  
  let rec lookupFdefViaIDFromProducts lp i =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupFdefViaIDFromProduct p i with
             | Some fd -> Some fd
             | None -> lookupFdefViaIDFromProducts lp' i)
  
  (** val lookupFdefViaGVFromFunTable :
      LLVMgv.coq_GVMap -> LLVMgv.coq_GenericValue -> LLVMsyntax.id option **)
  
  let rec lookupFdefViaGVFromFunTable fs fptr =
    match fs with
      | [] -> None
      | p::fs' ->
          let id0,gv0 = p in
          if LLVMgv.eq_gv gv0 fptr
          then Some id0
          else lookupFdefViaGVFromFunTable fs' fptr
  
  (** val lookupExFdecViaGV :
      LLVMtd.coq_TargetData -> products -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.value ->
      LLVMsyntax.fdec option **)
  
  let lookupExFdecViaGV tD ps gl lc fs fv =
    mbind (fun fptr ->
      mbind (fun fn ->
        match lookupFdefViaIDFromProducts ps fn with
          | Some f -> None
          | None -> lookupFdecViaIDFromProducts ps fn)
        (lookupFdefViaGVFromFunTable fs fptr))
      (LLVMgv.getOperandValue tD fv lc gl)
  
  (** val lookupFdefViaGV :
      LLVMtd.coq_TargetData -> products -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap -> LLVMsyntax.value -> fdef option **)
  
  let lookupFdefViaGV tD ps gl lc fs fv =
    match LLVMgv.getOperandValue tD fv lc gl with
      | Some fptr ->
          (match Opsem.OpsemAux.lookupFdefViaGVFromFunTable fs fptr with
             | Some fn -> lookupFdefViaIDFromProducts ps fn
             | None -> None)
      | None -> None
  
  (** val getEntryBlock : fdef -> block option **)
  
  let getEntryBlock = function
    | Coq_fdef_intro (f, b0) ->
        (match b0 with
           | [] -> None
           | b::l0 -> Some b)
  
  (** val lookupGvarViaIDFromProducts :
      products -> LLVMsyntax.id -> LLVMsyntax.gvar option **)
  
  let rec lookupGvarViaIDFromProducts lp i =
    match lp with
      | [] -> None
      | p::lp' ->
          (match p with
             | Coq_product_gvar gv ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom)
                      (LLVMinfra.getGvarID gv) i
                 then Some gv
                 else lookupGvarViaIDFromProducts lp' i
             | _ -> lookupGvarViaIDFromProducts lp' i)
  
  (** val lookupGvarFromProduct :
      product -> LLVMsyntax.id -> LLVMsyntax.gvar option **)
  
  let lookupGvarFromProduct p id0 =
    match p with
      | Coq_product_gvar g ->
          (match g with
             | LLVMsyntax.Coq_gvar_intro (id', lk, spec, t0, c, a) ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id'
                 then Some (LLVMsyntax.Coq_gvar_intro (id', lk, spec, t0, c,
                        a))
                 else None
             | LLVMsyntax.Coq_gvar_external (id', spec, t0) ->
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id0 id'
                 then Some (LLVMsyntax.Coq_gvar_external (id', spec, t0))
                 else None)
      | _ -> None
  
  (** val lookupGvarFromProducts :
      products -> LLVMsyntax.id -> LLVMsyntax.gvar option **)
  
  let rec lookupGvarFromProducts lp id0 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match lookupGvarFromProduct p id0 with
             | Some g -> Some g
             | None -> lookupGvarFromProducts lp' id0)
  
  (** val lookupFdecFromProducts :
      products -> LLVMsyntax.id -> LLVMsyntax.fdec option **)
  
  let rec lookupFdecFromProducts lp id1 =
    match lp with
      | [] -> None
      | p::lp' ->
          (match p with
             | Coq_product_fdec f ->
                 let LLVMsyntax.Coq_fheader_intro (f0, t0, fid, a, v) = f in
                 if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) id1 fid
                 then Some f
                 else lookupFdecFromProducts lp' id1
             | _ -> lookupFdecFromProducts lp' id1)
 end

module SBopsem = 
 struct 
  (** val exCallUpdateLocals :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool -> LLVMsyntax.id ->
      LLVMgv.coq_GenericValue option -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap
      option **)
  
  let exCallUpdateLocals tD ft noret0 rid oResult lc =
    if noret0
    then Some lc
    else (match oResult with
            | Some result ->
                (match ft with
                   | LLVMsyntax.Coq_typ_function (t0, l0, v) ->
                       (match LLVMgv.fit_gv tD t0 result with
                          | Some gr -> Some
                              (updateAddAL lc rid (LLVMgv.cgv2gv gr t0))
                          | None -> None)
                   | _ -> None)
            | None -> None)
  
  type coq_ExecutionContext = { coq_CurBB : SBsyntax.block;
                                coq_Locals : LLVMgv.coq_GVMap;
                                coq_Allocas : LLVMgv.mblock list }
  
  (** val coq_ExecutionContext_rect :
      (SBsyntax.block -> LLVMgv.coq_GVMap -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rect f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_ExecutionContext_rec :
      (SBsyntax.block -> LLVMgv.coq_GVMap -> LLVMgv.mblock list -> 'a1) ->
      coq_ExecutionContext -> 'a1 **)
  
  let coq_ExecutionContext_rec f e =
    let { coq_CurBB = x; coq_Locals = x0; coq_Allocas = x1 } = e in f x x0 x1
  
  (** val coq_CurBB : coq_ExecutionContext -> SBsyntax.block **)
  
  let coq_CurBB x = x.coq_CurBB
  
  (** val coq_Locals : coq_ExecutionContext -> LLVMgv.coq_GVMap **)
  
  let coq_Locals x = x.coq_Locals
  
  (** val coq_Allocas : coq_ExecutionContext -> LLVMgv.mblock list **)
  
  let coq_Allocas x = x.coq_Allocas
  
  type coq_State = { coq_Frame : coq_ExecutionContext; coq_Mem : LLVMgv.mem }
  
  (** val coq_State_rect :
      (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rect f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_State_rec :
      (coq_ExecutionContext -> LLVMgv.mem -> 'a1) -> coq_State -> 'a1 **)
  
  let coq_State_rec f s =
    let { coq_Frame = x; coq_Mem = x0 } = s in f x x0
  
  (** val coq_Frame : coq_State -> coq_ExecutionContext **)
  
  let coq_Frame x = x.coq_Frame
  
  (** val coq_Mem : coq_State -> LLVMgv.mem **)
  
  let coq_Mem x = x.coq_Mem
  
  (** val callUpdateLocals :
      LLVMtd.coq_TargetData -> LLVMsyntax.typ -> bool -> LLVMsyntax.id ->
      LLVMsyntax.value option -> LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap ->
      LLVMgv.coq_GVMap -> LLVMgv.coq_GVMap option **)
  
  let callUpdateLocals tD ft noret0 rid oResult lc lc' gl =
    if noret0
    then (match oResult with
            | Some result ->
                (match LLVMgv.getOperandValue tD result lc' gl with
                   | Some gr -> Some lc
                   | None -> None)
            | None -> Some lc)
    else (match oResult with
            | Some result ->
                (match LLVMgv.getOperandValue tD result lc' gl with
                   | Some gr ->
                       (match ft with
                          | LLVMsyntax.Coq_typ_function (
                              t0, l0, v) ->
                              (match LLVMgv.fit_gv tD t0 gr with
                                 | Some gr' -> Some
                                     (updateAddAL lc rid
                                       (LLVMgv.cgv2gv gr' t0))
                                 | None -> None)
                          | _ -> None)
                   | None -> None)
            | None -> None)
 end

