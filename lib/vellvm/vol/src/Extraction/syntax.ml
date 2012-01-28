open BinInt
open Datatypes
open Alist

module LLVMsyntax = 
 struct 
  (** val last_opt : 'a1 list -> 'a1 option **)
  
  let rec last_opt = function
    | [] -> None
    | a::l' -> (match l' with
                  | [] -> Some a
                  | a0::l1 -> last_opt l')
  
  module Size = 
   struct 
    type t = int
    
    (** val dec : t -> t -> bool **)
    
    let dec = ( = )
    
    (** val coq_Zero : t **)
    
    let coq_Zero = 0
    
    (** val coq_One : t **)
    
    let coq_One = 1
    
    (** val coq_Two : t **)
    
    let coq_Two = 2
    
    (** val coq_Four : t **)
    
    let coq_Four = 4
    
    (** val coq_Eight : t **)
    
    let coq_Eight = 8
    
    (** val coq_Sixteen : t **)
    
    let coq_Sixteen = 16
    
    (** val coq_ThirtyTwo : t **)
    
    let coq_ThirtyTwo = 32
    
    (** val coq_SixtyFour : t **)
    
    let coq_SixtyFour = 64
    
    (** val from_nat : nat -> t **)
    
    let from_nat = Camlcoq.camlint_of_nat
    
    (** val to_nat : t -> nat **)
    
    let to_nat = fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)
    
    (** val to_Z : t -> coq_Z **)
    
    let to_Z = fun x -> Camlcoq.z_of_camlint (Int32.of_int x)
    
    (** val from_Z : coq_Z -> t **)
    
    let from_Z = fun x -> Int32.to_int (Camlcoq.camlint_of_z x)
    
    (** val add : t -> t -> t **)
    
    let add = ( + )
    
    (** val sub : t -> t -> t **)
    
    let sub = ( - )
    
    (** val mul : t -> t -> t **)
    
    let mul = ( * )
    
    (** val div : t -> t -> t **)
    
    let div = ( / )
   end
  
  module Align = 
   struct 
    type t = int
    
    (** val dec : t -> t -> bool **)
    
    let dec = ( = )
    
    (** val coq_Zero : t **)
    
    let coq_Zero = 0
    
    (** val coq_One : t **)
    
    let coq_One = 1
    
    (** val coq_Two : t **)
    
    let coq_Two = 2
    
    (** val coq_Four : t **)
    
    let coq_Four = 4
    
    (** val coq_Eight : t **)
    
    let coq_Eight = 8
    
    (** val coq_Sixteen : t **)
    
    let coq_Sixteen = 16
    
    (** val coq_ThirtyTwo : t **)
    
    let coq_ThirtyTwo = 32
    
    (** val coq_SixtyFour : t **)
    
    let coq_SixtyFour = 64
    
    (** val from_nat : nat -> t **)
    
    let from_nat = Camlcoq.camlint_of_nat
    
    (** val to_nat : t -> nat **)
    
    let to_nat = fun x -> Camlcoq.nat_of_camlint(Int32.of_int x)
    
    (** val to_Z : t -> coq_Z **)
    
    let to_Z = fun x -> Camlcoq.z_of_camlint (Int32.of_int x)
    
    (** val from_Z : coq_Z -> t **)
    
    let from_Z = fun x -> Int32.to_int (Camlcoq.camlint_of_z x)
    
    (** val add : t -> t -> t **)
    
    let add = ( + )
    
    (** val sub : t -> t -> t **)
    
    let sub = ( - )
    
    (** val mul : t -> t -> t **)
    
    let mul = ( * )
    
    (** val div : t -> t -> t **)
    
    let div = ( / )
   end
  
  module INTEGER = 
   struct 
    type t = Llvm.APInt.t
    
    (** val dec : t -> t -> bool **)
    
    let dec = Llvm.APInt.compare
    
    (** val to_nat : t -> nat **)
    
    let to_nat = Camlcoq.llapint2nat
    
    (** val to_Z : t -> coq_Z **)
    
    let to_Z = Camlcoq.llapint2z
    
    (** val of_Z : coq_Z -> coq_Z -> bool -> t **)
    
    let of_Z = Camlcoq.z2llapint
   end
  
  module FLOAT = 
   struct 
    type t = Llvm.APFloat.t
    
    (** val dec : t -> t -> bool **)
    
    let dec = Llvm.APFloat.bcompare
   end
  
  type coq_Int = INTEGER.t
  
  type coq_Float = FLOAT.t
  
  type sz = Size.t
  
  type id = String.t
  
  type l = String.t
  
  type align = Align.t
  
  type i = nat
  
  type floating_point =
    | Coq_fp_float
    | Coq_fp_double
    | Coq_fp_fp128
    | Coq_fp_x86_fp80
    | Coq_fp_ppc_fp128
  
  (** val floating_point_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> floating_point -> 'a1 **)
  
  let floating_point_rect f f0 f1 f2 f3 = function
    | Coq_fp_float -> f
    | Coq_fp_double -> f0
    | Coq_fp_fp128 -> f1
    | Coq_fp_x86_fp80 -> f2
    | Coq_fp_ppc_fp128 -> f3
  
  (** val floating_point_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> floating_point -> 'a1 **)
  
  let floating_point_rec f f0 f1 f2 f3 = function
    | Coq_fp_float -> f
    | Coq_fp_double -> f0
    | Coq_fp_fp128 -> f1
    | Coq_fp_x86_fp80 -> f2
    | Coq_fp_ppc_fp128 -> f3
  
  type varg = bool
  
  type typ =
    | Coq_typ_int of sz
    | Coq_typ_floatpoint of floating_point
    | Coq_typ_void
    | Coq_typ_label
    | Coq_typ_metadata
    | Coq_typ_array of sz * typ
    | Coq_typ_function of typ * list_typ * varg
    | Coq_typ_struct of list_typ
    | Coq_typ_pointer of typ
    | Coq_typ_opaque
    | Coq_typ_namedt of id
  and list_typ =
    | Nil_list_typ
    | Cons_list_typ of typ * list_typ
  
  (** val typ_rect :
      (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz ->
      typ -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> varg -> 'a1) ->
      (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) -> typ
      -> 'a1 **)
  
  let rec typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
    | Coq_typ_int s -> f s
    | Coq_typ_floatpoint f10 -> f0 f10
    | Coq_typ_void -> f1
    | Coq_typ_label -> f2
    | Coq_typ_metadata -> f3
    | Coq_typ_array (s, t1) ->
        f4 s t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
    | Coq_typ_function (t1, l0, v) ->
        f5 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1) l0 v
    | Coq_typ_struct l0 -> f6 l0
    | Coq_typ_pointer t1 ->
        f7 t1 (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
    | Coq_typ_opaque -> f8
    | Coq_typ_namedt i0 -> f9 i0
  
  (** val typ_rec :
      (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz ->
      typ -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> varg -> 'a1) ->
      (list_typ -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1) -> typ
      -> 'a1 **)
  
  let rec typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
    | Coq_typ_int s -> f s
    | Coq_typ_floatpoint f10 -> f0 f10
    | Coq_typ_void -> f1
    | Coq_typ_label -> f2
    | Coq_typ_metadata -> f3
    | Coq_typ_array (s, t1) ->
        f4 s t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
    | Coq_typ_function (t1, l0, v) ->
        f5 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1) l0 v
    | Coq_typ_struct l0 -> f6 l0
    | Coq_typ_pointer t1 ->
        f7 t1 (typ_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 t1)
    | Coq_typ_opaque -> f8
    | Coq_typ_namedt i0 -> f9 i0
  
  (** val list_typ_rect :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rect f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t0, l1) -> f0 t0 l1 (list_typ_rect f f0 l1)
  
  (** val list_typ_rec :
      'a1 -> (typ -> list_typ -> 'a1 -> 'a1) -> list_typ -> 'a1 **)
  
  let rec list_typ_rec f f0 = function
    | Nil_list_typ -> f
    | Cons_list_typ (t0, l1) -> f0 t0 l1 (list_typ_rec f f0 l1)
  
  type cond =
    | Coq_cond_eq
    | Coq_cond_ne
    | Coq_cond_ugt
    | Coq_cond_uge
    | Coq_cond_ult
    | Coq_cond_ule
    | Coq_cond_sgt
    | Coq_cond_sge
    | Coq_cond_slt
    | Coq_cond_sle
  
  (** val cond_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      cond -> 'a1 **)
  
  let cond_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_cond_eq -> f
    | Coq_cond_ne -> f0
    | Coq_cond_ugt -> f1
    | Coq_cond_uge -> f2
    | Coq_cond_ult -> f3
    | Coq_cond_ule -> f4
    | Coq_cond_sgt -> f5
    | Coq_cond_sge -> f6
    | Coq_cond_slt -> f7
    | Coq_cond_sle -> f8
  
  (** val cond_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      cond -> 'a1 **)
  
  let cond_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
    | Coq_cond_eq -> f
    | Coq_cond_ne -> f0
    | Coq_cond_ugt -> f1
    | Coq_cond_uge -> f2
    | Coq_cond_ult -> f3
    | Coq_cond_ule -> f4
    | Coq_cond_sgt -> f5
    | Coq_cond_sge -> f6
    | Coq_cond_slt -> f7
    | Coq_cond_sle -> f8
  
  type fcond =
    | Coq_fcond_false
    | Coq_fcond_oeq
    | Coq_fcond_ogt
    | Coq_fcond_oge
    | Coq_fcond_olt
    | Coq_fcond_ole
    | Coq_fcond_one
    | Coq_fcond_ord
    | Coq_fcond_ueq
    | Coq_fcond_ugt
    | Coq_fcond_uge
    | Coq_fcond_ult
    | Coq_fcond_ule
    | Coq_fcond_une
    | Coq_fcond_uno
    | Coq_fcond_true
  
  (** val fcond_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fcond -> 'a1 **)
  
  let fcond_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
    | Coq_fcond_false -> f
    | Coq_fcond_oeq -> f0
    | Coq_fcond_ogt -> f1
    | Coq_fcond_oge -> f2
    | Coq_fcond_olt -> f3
    | Coq_fcond_ole -> f4
    | Coq_fcond_one -> f5
    | Coq_fcond_ord -> f6
    | Coq_fcond_ueq -> f7
    | Coq_fcond_ugt -> f8
    | Coq_fcond_uge -> f9
    | Coq_fcond_ult -> f10
    | Coq_fcond_ule -> f11
    | Coq_fcond_une -> f12
    | Coq_fcond_uno -> f13
    | Coq_fcond_true -> f14
  
  (** val fcond_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fcond -> 'a1 **)
  
  let fcond_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
    | Coq_fcond_false -> f
    | Coq_fcond_oeq -> f0
    | Coq_fcond_ogt -> f1
    | Coq_fcond_oge -> f2
    | Coq_fcond_olt -> f3
    | Coq_fcond_ole -> f4
    | Coq_fcond_one -> f5
    | Coq_fcond_ord -> f6
    | Coq_fcond_ueq -> f7
    | Coq_fcond_ugt -> f8
    | Coq_fcond_uge -> f9
    | Coq_fcond_ult -> f10
    | Coq_fcond_ule -> f11
    | Coq_fcond_une -> f12
    | Coq_fcond_uno -> f13
    | Coq_fcond_true -> f14
  
  type bop =
    | Coq_bop_add
    | Coq_bop_sub
    | Coq_bop_mul
    | Coq_bop_udiv
    | Coq_bop_sdiv
    | Coq_bop_urem
    | Coq_bop_srem
    | Coq_bop_shl
    | Coq_bop_lshr
    | Coq_bop_ashr
    | Coq_bop_and
    | Coq_bop_or
    | Coq_bop_xor
  
  (** val bop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> bop -> 'a1 **)
  
  let bop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_bop_add -> f
    | Coq_bop_sub -> f0
    | Coq_bop_mul -> f1
    | Coq_bop_udiv -> f2
    | Coq_bop_sdiv -> f3
    | Coq_bop_urem -> f4
    | Coq_bop_srem -> f5
    | Coq_bop_shl -> f6
    | Coq_bop_lshr -> f7
    | Coq_bop_ashr -> f8
    | Coq_bop_and -> f9
    | Coq_bop_or -> f10
    | Coq_bop_xor -> f11
  
  (** val bop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> bop -> 'a1 **)
  
  let bop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
    | Coq_bop_add -> f
    | Coq_bop_sub -> f0
    | Coq_bop_mul -> f1
    | Coq_bop_udiv -> f2
    | Coq_bop_sdiv -> f3
    | Coq_bop_urem -> f4
    | Coq_bop_srem -> f5
    | Coq_bop_shl -> f6
    | Coq_bop_lshr -> f7
    | Coq_bop_ashr -> f8
    | Coq_bop_and -> f9
    | Coq_bop_or -> f10
    | Coq_bop_xor -> f11
  
  type fbop =
    | Coq_fbop_fadd
    | Coq_fbop_fsub
    | Coq_fbop_fmul
    | Coq_fbop_fdiv
    | Coq_fbop_frem
  
  (** val fbop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbop -> 'a1 **)
  
  let fbop_rect f f0 f1 f2 f3 = function
    | Coq_fbop_fadd -> f
    | Coq_fbop_fsub -> f0
    | Coq_fbop_fmul -> f1
    | Coq_fbop_fdiv -> f2
    | Coq_fbop_frem -> f3
  
  (** val fbop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbop -> 'a1 **)
  
  let fbop_rec f f0 f1 f2 f3 = function
    | Coq_fbop_fadd -> f
    | Coq_fbop_fsub -> f0
    | Coq_fbop_fmul -> f1
    | Coq_fbop_fdiv -> f2
    | Coq_fbop_frem -> f3
  
  type extop =
    | Coq_extop_z
    | Coq_extop_s
    | Coq_extop_fp
  
  (** val extop_rect : 'a1 -> 'a1 -> 'a1 -> extop -> 'a1 **)
  
  let extop_rect f f0 f1 = function
    | Coq_extop_z -> f
    | Coq_extop_s -> f0
    | Coq_extop_fp -> f1
  
  (** val extop_rec : 'a1 -> 'a1 -> 'a1 -> extop -> 'a1 **)
  
  let extop_rec f f0 f1 = function
    | Coq_extop_z -> f
    | Coq_extop_s -> f0
    | Coq_extop_fp -> f1
  
  type castop =
    | Coq_castop_fptoui
    | Coq_castop_fptosi
    | Coq_castop_uitofp
    | Coq_castop_sitofp
    | Coq_castop_ptrtoint
    | Coq_castop_inttoptr
    | Coq_castop_bitcast
  
  (** val castop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1 **)
  
  let castop_rect f f0 f1 f2 f3 f4 f5 = function
    | Coq_castop_fptoui -> f
    | Coq_castop_fptosi -> f0
    | Coq_castop_uitofp -> f1
    | Coq_castop_sitofp -> f2
    | Coq_castop_ptrtoint -> f3
    | Coq_castop_inttoptr -> f4
    | Coq_castop_bitcast -> f5
  
  (** val castop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> castop -> 'a1 **)
  
  let castop_rec f f0 f1 f2 f3 f4 f5 = function
    | Coq_castop_fptoui -> f
    | Coq_castop_fptosi -> f0
    | Coq_castop_uitofp -> f1
    | Coq_castop_sitofp -> f2
    | Coq_castop_ptrtoint -> f3
    | Coq_castop_inttoptr -> f4
    | Coq_castop_bitcast -> f5
  
  type inbounds = bool
  
  type truncop =
    | Coq_truncop_int
    | Coq_truncop_fp
  
  (** val truncop_rect : 'a1 -> 'a1 -> truncop -> 'a1 **)
  
  let truncop_rect f f0 = function
    | Coq_truncop_int -> f
    | Coq_truncop_fp -> f0
  
  (** val truncop_rec : 'a1 -> 'a1 -> truncop -> 'a1 **)
  
  let truncop_rec f f0 = function
    | Coq_truncop_int -> f
    | Coq_truncop_fp -> f0
  
  type const =
    | Coq_const_zeroinitializer of typ
    | Coq_const_int of sz * coq_Int
    | Coq_const_floatpoint of floating_point * coq_Float
    | Coq_const_undef of typ
    | Coq_const_null of typ
    | Coq_const_arr of typ * list_const
    | Coq_const_struct of list_const
    | Coq_const_gid of typ * id
    | Coq_const_truncop of truncop * const * typ
    | Coq_const_extop of extop * const * typ
    | Coq_const_castop of castop * const * typ
    | Coq_const_gep of inbounds * const * list_const
    | Coq_const_select of const * const * const
    | Coq_const_icmp of cond * const * const
    | Coq_const_fcmp of fcond * const * const
    | Coq_const_extractvalue of const * list_const
    | Coq_const_insertvalue of const * const * list_const
    | Coq_const_bop of bop * const * const
    | Coq_const_fbop of fbop * const * const
  and list_const =
    | Nil_list_const
    | Cons_list_const of const * list_const
  
  (** val const_rect :
      (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float
      -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a1)
      -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const ->
      'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop
      -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 ->
      list_const -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 ->
      'a1) -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond ->
      const -> 'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const ->
      'a1) -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a1) -> (bop ->
      const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const
      -> 'a1 -> 'a1) -> const -> 'a1 **)
  
  let rec const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 = function
    | Coq_const_zeroinitializer t0 -> f t0
    | Coq_const_int (s, i0) -> f0 s i0
    | Coq_const_floatpoint (f18, f19) -> f1 f18 f19
    | Coq_const_undef t0 -> f2 t0
    | Coq_const_null t0 -> f3 t0
    | Coq_const_arr (t0, l0) -> f4 t0 l0
    | Coq_const_struct l0 -> f5 l0
    | Coq_const_gid (t0, i0) -> f6 t0 i0
    | Coq_const_truncop (t0, c0, t1) ->
        f7 t0 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) t1
    | Coq_const_extop (e, c0, t0) ->
        f8 e c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) t0
    | Coq_const_castop (c0, c1, t0) ->
        f9 c0 c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) t0
    | Coq_const_gep (i0, c0, l0) ->
        f10 i0 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) l0
    | Coq_const_select (c0, c1, c2) ->
        f11 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) c2
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c2)
    | Coq_const_icmp (c0, c1, c2) ->
        f12 c0 c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) c2
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c2)
    | Coq_const_fcmp (f18, c0, c1) ->
        f13 f18 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
    | Coq_const_extractvalue (c0, l0) ->
        f14 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) l0
    | Coq_const_insertvalue (c0, c1, l0) ->
        f15 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) l0
    | Coq_const_bop (b, c0, c1) ->
        f16 b c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
    | Coq_const_fbop (f18, c0, c1) ->
        f17 f18 c0
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
  
  (** val const_rec :
      (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float
      -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a1)
      -> (list_const -> 'a1) -> (typ -> id -> 'a1) -> (truncop -> const ->
      'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) -> (castop
      -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 ->
      list_const -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const -> 'a1 ->
      'a1) -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond ->
      const -> 'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const ->
      'a1) -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a1) -> (bop ->
      const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const -> 'a1 -> const
      -> 'a1 -> 'a1) -> const -> 'a1 **)
  
  let rec const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 = function
    | Coq_const_zeroinitializer t0 -> f t0
    | Coq_const_int (s, i0) -> f0 s i0
    | Coq_const_floatpoint (f18, f19) -> f1 f18 f19
    | Coq_const_undef t0 -> f2 t0
    | Coq_const_null t0 -> f3 t0
    | Coq_const_arr (t0, l0) -> f4 t0 l0
    | Coq_const_struct l0 -> f5 l0
    | Coq_const_gid (t0, i0) -> f6 t0 i0
    | Coq_const_truncop (t0, c0, t1) ->
        f7 t0 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) t1
    | Coq_const_extop (e, c0, t0) ->
        f8 e c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) t0
    | Coq_const_castop (c0, c1, t0) ->
        f9 c0 c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) t0
    | Coq_const_gep (i0, c0, l0) ->
        f10 i0 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) l0
    | Coq_const_select (c0, c1, c2) ->
        f11 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) c2
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c2)
    | Coq_const_icmp (c0, c1, c2) ->
        f12 c0 c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) c2
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c2)
    | Coq_const_fcmp (f18, c0, c1) ->
        f13 f18 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
    | Coq_const_extractvalue (c0, l0) ->
        f14 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) l0
    | Coq_const_insertvalue (c0, c1, l0) ->
        f15 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1) l0
    | Coq_const_bop (b, c0, c1) ->
        f16 b c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
    | Coq_const_fbop (f18, c0, c1) ->
        f17 f18 c0
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c0) c1
          (const_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
            f16 f17 c1)
  
  (** val list_const_rect :
      'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1 **)
  
  let rec list_const_rect f f0 = function
    | Nil_list_const -> f
    | Cons_list_const (c, l1) -> f0 c l1 (list_const_rect f f0 l1)
  
  (** val list_const_rec :
      'a1 -> (const -> list_const -> 'a1 -> 'a1) -> list_const -> 'a1 **)
  
  let rec list_const_rec f f0 = function
    | Nil_list_const -> f
    | Cons_list_const (c, l1) -> f0 c l1 (list_const_rec f f0 l1)
  
  type attribute =
    | Coq_attribute_zext
    | Coq_attribute_sext
    | Coq_attribute_noreturn
    | Coq_attribute_inreg
    | Coq_attribute_structret
    | Coq_attribute_nounwind
    | Coq_attribute_noalias
    | Coq_attribute_byval
    | Coq_attribute_nest
    | Coq_attribute_readnone
    | Coq_attribute_readonly
    | Coq_attribute_noinline
    | Coq_attribute_alwaysinline
    | Coq_attribute_optforsize
    | Coq_attribute_stackprotect
    | Coq_attribute_stackprotectreq
    | Coq_attribute_nocapture
    | Coq_attribute_noredzone
    | Coq_attribute_implicitfloat
    | Coq_attribute_naked
  
  (** val attribute_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      attribute -> 'a1 **)
  
  let attribute_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 = function
    | Coq_attribute_zext -> f
    | Coq_attribute_sext -> f0
    | Coq_attribute_noreturn -> f1
    | Coq_attribute_inreg -> f2
    | Coq_attribute_structret -> f3
    | Coq_attribute_nounwind -> f4
    | Coq_attribute_noalias -> f5
    | Coq_attribute_byval -> f6
    | Coq_attribute_nest -> f7
    | Coq_attribute_readnone -> f8
    | Coq_attribute_readonly -> f9
    | Coq_attribute_noinline -> f10
    | Coq_attribute_alwaysinline -> f11
    | Coq_attribute_optforsize -> f12
    | Coq_attribute_stackprotect -> f13
    | Coq_attribute_stackprotectreq -> f14
    | Coq_attribute_nocapture -> f15
    | Coq_attribute_noredzone -> f16
    | Coq_attribute_implicitfloat -> f17
    | Coq_attribute_naked -> f18
  
  (** val attribute_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      attribute -> 'a1 **)
  
  let attribute_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 = function
    | Coq_attribute_zext -> f
    | Coq_attribute_sext -> f0
    | Coq_attribute_noreturn -> f1
    | Coq_attribute_inreg -> f2
    | Coq_attribute_structret -> f3
    | Coq_attribute_nounwind -> f4
    | Coq_attribute_noalias -> f5
    | Coq_attribute_byval -> f6
    | Coq_attribute_nest -> f7
    | Coq_attribute_readnone -> f8
    | Coq_attribute_readonly -> f9
    | Coq_attribute_noinline -> f10
    | Coq_attribute_alwaysinline -> f11
    | Coq_attribute_optforsize -> f12
    | Coq_attribute_stackprotect -> f13
    | Coq_attribute_stackprotectreq -> f14
    | Coq_attribute_nocapture -> f15
    | Coq_attribute_noredzone -> f16
    | Coq_attribute_implicitfloat -> f17
    | Coq_attribute_naked -> f18
  
  type value =
    | Coq_value_id of id
    | Coq_value_const of const
  
  (** val value_rect : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1 **)
  
  let value_rect f f0 = function
    | Coq_value_id x -> f x
    | Coq_value_const x -> f0 x
  
  (** val value_rec : (id -> 'a1) -> (const -> 'a1) -> value -> 'a1 **)
  
  let value_rec f f0 = function
    | Coq_value_id x -> f x
    | Coq_value_const x -> f0 x
  
  type attributes = attribute list
  
  type param = (typ*attributes)*value
  
  type tailc = bool
  
  type callconv =
    | Coq_callconv_ccc
    | Coq_callconv_fast
    | Coq_callconv_cold
    | Coq_callconv_x86_stdcall
    | Coq_callconv_x86_fastcall
  
  (** val callconv_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> callconv -> 'a1 **)
  
  let callconv_rect f f0 f1 f2 f3 = function
    | Coq_callconv_ccc -> f
    | Coq_callconv_fast -> f0
    | Coq_callconv_cold -> f1
    | Coq_callconv_x86_stdcall -> f2
    | Coq_callconv_x86_fastcall -> f3
  
  (** val callconv_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> callconv -> 'a1 **)
  
  let callconv_rec f f0 f1 f2 f3 = function
    | Coq_callconv_ccc -> f
    | Coq_callconv_fast -> f0
    | Coq_callconv_cold -> f1
    | Coq_callconv_x86_stdcall -> f2
    | Coq_callconv_x86_fastcall -> f3
  
  type noret = bool
  
  type params = ((typ*attributes)*value) list
  
  type clattrs =
    | Coq_clattrs_intro of tailc * callconv * attributes * attributes
  
  (** val clattrs_rect :
      (tailc -> callconv -> attributes -> attributes -> 'a1) -> clattrs ->
      'a1 **)
  
  let clattrs_rect f = function
    | Coq_clattrs_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val clattrs_rec :
      (tailc -> callconv -> attributes -> attributes -> 'a1) -> clattrs ->
      'a1 **)
  
  let clattrs_rec f = function
    | Coq_clattrs_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  type list_sz_value =
    | Nil_list_sz_value
    | Cons_list_sz_value of sz * value * list_sz_value
  
  (** val list_sz_value_rect :
      'a1 -> (sz -> value -> list_sz_value -> 'a1 -> 'a1) -> list_sz_value ->
      'a1 **)
  
  let rec list_sz_value_rect f f0 = function
    | Nil_list_sz_value -> f
    | Cons_list_sz_value (s, v, l1) -> f0 s v l1 (list_sz_value_rect f f0 l1)
  
  (** val list_sz_value_rec :
      'a1 -> (sz -> value -> list_sz_value -> 'a1 -> 'a1) -> list_sz_value ->
      'a1 **)
  
  let rec list_sz_value_rec f f0 = function
    | Nil_list_sz_value -> f
    | Cons_list_sz_value (s, v, l1) -> f0 s v l1 (list_sz_value_rec f f0 l1)
  
  type list_value_l =
    | Nil_list_value_l
    | Cons_list_value_l of value * l * list_value_l
  
  (** val list_value_l_rect :
      'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l ->
      'a1 **)
  
  let rec list_value_l_rect f f0 = function
    | Nil_list_value_l -> f
    | Cons_list_value_l (v, l1, l2) -> f0 v l1 l2 (list_value_l_rect f f0 l2)
  
  (** val list_value_l_rec :
      'a1 -> (value -> l -> list_value_l -> 'a1 -> 'a1) -> list_value_l ->
      'a1 **)
  
  let rec list_value_l_rec f f0 = function
    | Nil_list_value_l -> f
    | Cons_list_value_l (v, l1, l2) -> f0 v l1 l2 (list_value_l_rec f f0 l2)
  
  type cmd =
    | Coq_insn_bop of id * bop * sz * value * value
    | Coq_insn_fbop of id * fbop * floating_point * value * value
    | Coq_insn_extractvalue of id * typ * value * list_const
    | Coq_insn_insertvalue of id * typ * value * typ * value * list_const
    | Coq_insn_malloc of id * typ * value * align
    | Coq_insn_free of id * typ * value
    | Coq_insn_alloca of id * typ * value * align
    | Coq_insn_load of id * typ * value * align
    | Coq_insn_store of id * typ * value * value * align
    | Coq_insn_gep of id * inbounds * typ * value * list_sz_value
    | Coq_insn_trunc of id * truncop * typ * value * typ
    | Coq_insn_ext of id * extop * typ * value * typ
    | Coq_insn_cast of id * castop * typ * value * typ
    | Coq_insn_icmp of id * cond * typ * value * value
    | Coq_insn_fcmp of id * fcond * floating_point * value * value
    | Coq_insn_select of id * value * typ * value * value
    | Coq_insn_call of id * noret * clattrs * typ * value * params
  
  (** val cmd_rect :
      (id -> bop -> sz -> value -> value -> 'a1) -> (id -> fbop ->
      floating_point -> value -> value -> 'a1) -> (id -> typ -> value ->
      list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
      -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value
      -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value
      -> align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) ->
      (id -> inbounds -> typ -> value -> list_sz_value -> 'a1) -> (id ->
      truncop -> typ -> value -> typ -> 'a1) -> (id -> extop -> typ -> value
      -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id
      -> cond -> typ -> value -> value -> 'a1) -> (id -> fcond ->
      floating_point -> value -> value -> 'a1) -> (id -> value -> typ ->
      value -> value -> 'a1) -> (id -> noret -> clattrs -> typ -> value ->
      params -> 'a1) -> cmd -> 'a1 **)
  
  let cmd_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_fbop (x, x0, x1, x2, x3) -> f0 x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f2 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f3 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f4 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f5 x x0 x1 x2
    | Coq_insn_load (x, x0, x1, x2) -> f6 x x0 x1 x2
    | Coq_insn_store (x, x0, x1, x2, x3) -> f7 x x0 x1 x2 x3
    | Coq_insn_gep (x, x0, x1, x2, x3) -> f8 x x0 x1 x2 x3
    | Coq_insn_trunc (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 x3
    | Coq_insn_ext (x, x0, x1, x2, x3) -> f10 x x0 x1 x2 x3
    | Coq_insn_cast (x, x0, x1, x2, x3) -> f11 x x0 x1 x2 x3
    | Coq_insn_icmp (x, x0, x1, x2, x3) -> f12 x x0 x1 x2 x3
    | Coq_insn_fcmp (x, x0, x1, x2, x3) -> f13 x x0 x1 x2 x3
    | Coq_insn_select (x, x0, x1, x2, x3) -> f14 x x0 x1 x2 x3
    | Coq_insn_call (x, x0, x1, x2, x3, x4) -> f15 x x0 x1 x2 x3 x4
  
  (** val cmd_rec :
      (id -> bop -> sz -> value -> value -> 'a1) -> (id -> fbop ->
      floating_point -> value -> value -> 'a1) -> (id -> typ -> value ->
      list_const -> 'a1) -> (id -> typ -> value -> typ -> value -> list_const
      -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value
      -> 'a1) -> (id -> typ -> value -> align -> 'a1) -> (id -> typ -> value
      -> align -> 'a1) -> (id -> typ -> value -> value -> align -> 'a1) ->
      (id -> inbounds -> typ -> value -> list_sz_value -> 'a1) -> (id ->
      truncop -> typ -> value -> typ -> 'a1) -> (id -> extop -> typ -> value
      -> typ -> 'a1) -> (id -> castop -> typ -> value -> typ -> 'a1) -> (id
      -> cond -> typ -> value -> value -> 'a1) -> (id -> fcond ->
      floating_point -> value -> value -> 'a1) -> (id -> value -> typ ->
      value -> value -> 'a1) -> (id -> noret -> clattrs -> typ -> value ->
      params -> 'a1) -> cmd -> 'a1 **)
  
  let cmd_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
    | Coq_insn_bop (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
    | Coq_insn_fbop (x, x0, x1, x2, x3) -> f0 x x0 x1 x2 x3
    | Coq_insn_extractvalue (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_insertvalue (x, x0, x1, x2, x3, x4) -> f2 x x0 x1 x2 x3 x4
    | Coq_insn_malloc (x, x0, x1, x2) -> f3 x x0 x1 x2
    | Coq_insn_free (x, x0, x1) -> f4 x x0 x1
    | Coq_insn_alloca (x, x0, x1, x2) -> f5 x x0 x1 x2
    | Coq_insn_load (x, x0, x1, x2) -> f6 x x0 x1 x2
    | Coq_insn_store (x, x0, x1, x2, x3) -> f7 x x0 x1 x2 x3
    | Coq_insn_gep (x, x0, x1, x2, x3) -> f8 x x0 x1 x2 x3
    | Coq_insn_trunc (x, x0, x1, x2, x3) -> f9 x x0 x1 x2 x3
    | Coq_insn_ext (x, x0, x1, x2, x3) -> f10 x x0 x1 x2 x3
    | Coq_insn_cast (x, x0, x1, x2, x3) -> f11 x x0 x1 x2 x3
    | Coq_insn_icmp (x, x0, x1, x2, x3) -> f12 x x0 x1 x2 x3
    | Coq_insn_fcmp (x, x0, x1, x2, x3) -> f13 x x0 x1 x2 x3
    | Coq_insn_select (x, x0, x1, x2, x3) -> f14 x x0 x1 x2 x3
    | Coq_insn_call (x, x0, x1, x2, x3, x4) -> f15 x x0 x1 x2 x3 x4
  
  type phinode =
    | Coq_insn_phi of id * typ * list_value_l
  
  (** val phinode_rect :
      (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rect f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  (** val phinode_rec :
      (id -> typ -> list_value_l -> 'a1) -> phinode -> 'a1 **)
  
  let phinode_rec f = function
    | Coq_insn_phi (x, x0, x1) -> f x x0 x1
  
  type arg = (typ*attributes)*id
  
  type visibility =
    | Coq_visibility_default
    | Coq_visibility_hidden
    | Coq_visibility_protected
  
  (** val visibility_rect : 'a1 -> 'a1 -> 'a1 -> visibility -> 'a1 **)
  
  let visibility_rect f f0 f1 = function
    | Coq_visibility_default -> f
    | Coq_visibility_hidden -> f0
    | Coq_visibility_protected -> f1
  
  (** val visibility_rec : 'a1 -> 'a1 -> 'a1 -> visibility -> 'a1 **)
  
  let visibility_rec f f0 f1 = function
    | Coq_visibility_default -> f
    | Coq_visibility_hidden -> f0
    | Coq_visibility_protected -> f1
  
  type linkage =
    | Coq_linkage_external
    | Coq_linkage_available_externally
    | Coq_linkage_link_once
    | Coq_linkage_link_once_odr
    | Coq_linkage_weak
    | Coq_linkage_weak_odr
    | Coq_linkage_appending
    | Coq_linkage_internal
    | Coq_linkage_private
    | Coq_linkage_linker_private
    | Coq_linkage_dllimport
    | Coq_linkage_dllexport
    | Coq_linkage_external_weak
    | Coq_linkage_ghost
    | Coq_linkage_common
  
  (** val linkage_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> linkage -> 'a1 **)
  
  let linkage_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
    | Coq_linkage_external -> f
    | Coq_linkage_available_externally -> f0
    | Coq_linkage_link_once -> f1
    | Coq_linkage_link_once_odr -> f2
    | Coq_linkage_weak -> f3
    | Coq_linkage_weak_odr -> f4
    | Coq_linkage_appending -> f5
    | Coq_linkage_internal -> f6
    | Coq_linkage_private -> f7
    | Coq_linkage_linker_private -> f8
    | Coq_linkage_dllimport -> f9
    | Coq_linkage_dllexport -> f10
    | Coq_linkage_external_weak -> f11
    | Coq_linkage_ghost -> f12
    | Coq_linkage_common -> f13
  
  (** val linkage_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> linkage -> 'a1 **)
  
  let linkage_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
    | Coq_linkage_external -> f
    | Coq_linkage_available_externally -> f0
    | Coq_linkage_link_once -> f1
    | Coq_linkage_link_once_odr -> f2
    | Coq_linkage_weak -> f3
    | Coq_linkage_weak_odr -> f4
    | Coq_linkage_appending -> f5
    | Coq_linkage_internal -> f6
    | Coq_linkage_private -> f7
    | Coq_linkage_linker_private -> f8
    | Coq_linkage_dllimport -> f9
    | Coq_linkage_dllexport -> f10
    | Coq_linkage_external_weak -> f11
    | Coq_linkage_ghost -> f12
    | Coq_linkage_common -> f13
  
  type terminator =
    | Coq_insn_return of id * typ * value
    | Coq_insn_return_void of id
    | Coq_insn_br of id * value * l * l
    | Coq_insn_br_uncond of id * l
    | Coq_insn_unreachable of id
  
  (** val terminator_rect :
      (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
      'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1 **)
  
  let terminator_rect f f0 f1 f2 f3 = function
    | Coq_insn_return (x, x0, x1) -> f x x0 x1
    | Coq_insn_return_void x -> f0 x
    | Coq_insn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_br_uncond (x, x0) -> f2 x x0
    | Coq_insn_unreachable x -> f3 x
  
  (** val terminator_rec :
      (id -> typ -> value -> 'a1) -> (id -> 'a1) -> (id -> value -> l -> l ->
      'a1) -> (id -> l -> 'a1) -> (id -> 'a1) -> terminator -> 'a1 **)
  
  let terminator_rec f f0 f1 f2 f3 = function
    | Coq_insn_return (x, x0, x1) -> f x x0 x1
    | Coq_insn_return_void x -> f0 x
    | Coq_insn_br (x, x0, x1, x2) -> f1 x x0 x1 x2
    | Coq_insn_br_uncond (x, x0) -> f2 x x0
    | Coq_insn_unreachable x -> f3 x
  
  type cmds = cmd list
  
  type phinodes = phinode list
  
  type args = ((typ*attributes)*id) list
  
  type fnattrs =
    | Coq_fnattrs_intro of linkage * visibility * callconv * 
       attributes * attributes
  
  (** val fnattrs_rect :
      (linkage -> visibility -> callconv -> attributes -> attributes -> 'a1)
      -> fnattrs -> 'a1 **)
  
  let fnattrs_rect f = function
    | Coq_fnattrs_intro (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
  
  (** val fnattrs_rec :
      (linkage -> visibility -> callconv -> attributes -> attributes -> 'a1)
      -> fnattrs -> 'a1 **)
  
  let fnattrs_rec f = function
    | Coq_fnattrs_intro (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
  
  type block =
    | Coq_block_intro of l * phinodes * cmds * terminator
  
  (** val block_rect :
      (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1 **)
  
  let block_rect f = function
    | Coq_block_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  (** val block_rec :
      (l -> phinodes -> cmds -> terminator -> 'a1) -> block -> 'a1 **)
  
  let block_rec f = function
    | Coq_block_intro (x, x0, x1, x2) -> f x x0 x1 x2
  
  type fheader =
    | Coq_fheader_intro of fnattrs * typ * id * args * varg
  
  (** val fheader_rect :
      (fnattrs -> typ -> id -> args -> varg -> 'a1) -> fheader -> 'a1 **)
  
  let fheader_rect f = function
    | Coq_fheader_intro (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
  
  (** val fheader_rec :
      (fnattrs -> typ -> id -> args -> varg -> 'a1) -> fheader -> 'a1 **)
  
  let fheader_rec f = function
    | Coq_fheader_intro (x, x0, x1, x2, x3) -> f x x0 x1 x2 x3
  
  type blocks = block list
  
  type gvar_spec =
    | Coq_gvar_spec_global
    | Coq_gvar_spec_constant
  
  (** val gvar_spec_rect : 'a1 -> 'a1 -> gvar_spec -> 'a1 **)
  
  let gvar_spec_rect f f0 = function
    | Coq_gvar_spec_global -> f
    | Coq_gvar_spec_constant -> f0
  
  (** val gvar_spec_rec : 'a1 -> 'a1 -> gvar_spec -> 'a1 **)
  
  let gvar_spec_rec f f0 = function
    | Coq_gvar_spec_global -> f
    | Coq_gvar_spec_constant -> f0
  
  type fdec =
    fheader
    (* singleton inductive, whose constructor was fdec_intro *)
  
  (** val fdec_rect : (fheader -> 'a1) -> fdec -> 'a1 **)
  
  let fdec_rect f f0 =
    f f0
  
  (** val fdec_rec : (fheader -> 'a1) -> fdec -> 'a1 **)
  
  let fdec_rec f f0 =
    f f0
  
  type fdef =
    | Coq_fdef_intro of fheader * blocks
  
  (** val fdef_rect : (fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rect f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  (** val fdef_rec : (fheader -> blocks -> 'a1) -> fdef -> 'a1 **)
  
  let fdef_rec f = function
    | Coq_fdef_intro (x, x0) -> f x x0
  
  type gvar =
    | Coq_gvar_intro of id * linkage * gvar_spec * typ * const * align
    | Coq_gvar_external of id * gvar_spec * typ
  
  (** val gvar_rect :
      (id -> linkage -> gvar_spec -> typ -> const -> align -> 'a1) -> (id ->
      gvar_spec -> typ -> 'a1) -> gvar -> 'a1 **)
  
  let gvar_rect f f0 = function
    | Coq_gvar_intro (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
    | Coq_gvar_external (x, x0, x1) -> f0 x x0 x1
  
  (** val gvar_rec :
      (id -> linkage -> gvar_spec -> typ -> const -> align -> 'a1) -> (id ->
      gvar_spec -> typ -> 'a1) -> gvar -> 'a1 **)
  
  let gvar_rec f f0 = function
    | Coq_gvar_intro (x, x0, x1, x2, x3, x4) -> f x x0 x1 x2 x3 x4
    | Coq_gvar_external (x, x0, x1) -> f0 x x0 x1
  
  type layout =
    | Coq_layout_be
    | Coq_layout_le
    | Coq_layout_ptr of sz * align * align
    | Coq_layout_int of sz * align * align
    | Coq_layout_float of sz * align * align
    | Coq_layout_aggr of sz * align * align
    | Coq_layout_stack of sz * align * align
    | Coq_layout_vector of sz * align * align
  
  (** val layout_rect :
      'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
      'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1)
      -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
      layout -> 'a1 **)
  
  let layout_rect f f0 f1 f2 f3 f4 f5 f6 = function
    | Coq_layout_be -> f
    | Coq_layout_le -> f0
    | Coq_layout_ptr (x, x0, x1) -> f1 x x0 x1
    | Coq_layout_int (x, x0, x1) -> f2 x x0 x1
    | Coq_layout_float (x, x0, x1) -> f3 x x0 x1
    | Coq_layout_aggr (x, x0, x1) -> f4 x x0 x1
    | Coq_layout_stack (x, x0, x1) -> f5 x x0 x1
    | Coq_layout_vector (x, x0, x1) -> f6 x x0 x1
  
  (** val layout_rec :
      'a1 -> 'a1 -> (sz -> align -> align -> 'a1) -> (sz -> align -> align ->
      'a1) -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1)
      -> (sz -> align -> align -> 'a1) -> (sz -> align -> align -> 'a1) ->
      layout -> 'a1 **)
  
  let layout_rec f f0 f1 f2 f3 f4 f5 f6 = function
    | Coq_layout_be -> f
    | Coq_layout_le -> f0
    | Coq_layout_ptr (x, x0, x1) -> f1 x x0 x1
    | Coq_layout_int (x, x0, x1) -> f2 x x0 x1
    | Coq_layout_float (x, x0, x1) -> f3 x x0 x1
    | Coq_layout_aggr (x, x0, x1) -> f4 x x0 x1
    | Coq_layout_stack (x, x0, x1) -> f5 x x0 x1
    | Coq_layout_vector (x, x0, x1) -> f6 x x0 x1
  
  type namedt =
    | Coq_namedt_intro of id * typ
  
  (** val namedt_rect : (id -> typ -> 'a1) -> namedt -> 'a1 **)
  
  let namedt_rect f = function
    | Coq_namedt_intro (x, x0) -> f x x0
  
  (** val namedt_rec : (id -> typ -> 'a1) -> namedt -> 'a1 **)
  
  let namedt_rec f = function
    | Coq_namedt_intro (x, x0) -> f x x0
  
  type product =
    | Coq_product_gvar of gvar
    | Coq_product_fdec of fdec
    | Coq_product_fdef of fdef
  
  (** val product_rect :
      (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1 **)
  
  let product_rect f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  (** val product_rec :
      (gvar -> 'a1) -> (fdec -> 'a1) -> (fdef -> 'a1) -> product -> 'a1 **)
  
  let product_rec f f0 f1 = function
    | Coq_product_gvar x -> f x
    | Coq_product_fdec x -> f0 x
    | Coq_product_fdef x -> f1 x
  
  type layouts = layout list
  
  type namedts = namedt list
  
  type products = product list
  
  type coq_module =
    | Coq_module_intro of layouts * namedts * products
  
  (** val module_rect :
      (layouts -> namedts -> products -> 'a1) -> coq_module -> 'a1 **)
  
  let module_rect f = function
    | Coq_module_intro (x, x0, x1) -> f x x0 x1
  
  (** val module_rec :
      (layouts -> namedts -> products -> 'a1) -> coq_module -> 'a1 **)
  
  let module_rec f = function
    | Coq_module_intro (x, x0, x1) -> f x x0 x1
  
  type insn =
    | Coq_insn_phinode of phinode
    | Coq_insn_cmd of cmd
    | Coq_insn_terminator of terminator
  
  (** val insn_rect :
      (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1 **)
  
  let insn_rect f f0 f1 = function
    | Coq_insn_phinode x -> f x
    | Coq_insn_cmd x -> f0 x
    | Coq_insn_terminator x -> f1 x
  
  (** val insn_rec :
      (phinode -> 'a1) -> (cmd -> 'a1) -> (terminator -> 'a1) -> insn -> 'a1 **)
  
  let insn_rec f f0 f1 = function
    | Coq_insn_phinode x -> f x
    | Coq_insn_cmd x -> f0 x
    | Coq_insn_terminator x -> f1 x
  
  type modules = coq_module list
  
  type ids = id list
  
  type opt_Int = coq_Int option
  
  type opt_l = l option
  
  type opt_id = id option
  
  type opt_typ = typ option
  
  type opt_value = value option
  
  type ls = l list
  
  type insns = insn list
  
  type opt_block = block option
  
  type opt_fdec = fdec option
  
  type opt_fdef = fdef option
  
  type id_binding =
    | Coq_id_binding_none
    | Coq_id_binding_cmd of cmd
    | Coq_id_binding_phinode of phinode
    | Coq_id_binding_terminator of terminator
    | Coq_id_binding_gvar of gvar
    | Coq_id_binding_fdec of fdec
    | Coq_id_binding_arg of arg
  
  (** val id_binding_rect :
      'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
      -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1 **)
  
  let id_binding_rect f f0 f1 f2 f3 f4 f5 = function
    | Coq_id_binding_none -> f
    | Coq_id_binding_cmd x -> f0 x
    | Coq_id_binding_phinode x -> f1 x
    | Coq_id_binding_terminator x -> f2 x
    | Coq_id_binding_gvar x -> f3 x
    | Coq_id_binding_fdec x -> f4 x
    | Coq_id_binding_arg x -> f5 x
  
  (** val id_binding_rec :
      'a1 -> (cmd -> 'a1) -> (phinode -> 'a1) -> (terminator -> 'a1) -> (gvar
      -> 'a1) -> (fdec -> 'a1) -> (arg -> 'a1) -> id_binding -> 'a1 **)
  
  let id_binding_rec f f0 f1 f2 f3 f4 f5 = function
    | Coq_id_binding_none -> f
    | Coq_id_binding_cmd x -> f0 x
    | Coq_id_binding_phinode x -> f1 x
    | Coq_id_binding_terminator x -> f2 x
    | Coq_id_binding_gvar x -> f3 x
    | Coq_id_binding_fdec x -> f4 x
    | Coq_id_binding_arg x -> f5 x
  
  type targetdata = layout list*namedt list
  
  type system = modules
  
  type usedef_block = l list coq_AssocList
  
  type intrinsic_funs = ids
  
  (** val map_list_value_l :
      (value -> l -> 'a1) -> list_value_l -> 'a1 list **)
  
  let rec map_list_value_l f = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (f h0 h1)::(map_list_value_l f tl_)
  
  (** val make_list_value_l : (value*l) list -> list_value_l **)
  
  let rec make_list_value_l = function
    | [] -> Nil_list_value_l
    | p::tl_ ->
        let h0,h1 = p in Cons_list_value_l (h0, h1, (make_list_value_l tl_))
  
  (** val unmake_list_value_l : list_value_l -> (value*l) list **)
  
  let rec unmake_list_value_l = function
    | Nil_list_value_l -> []
    | Cons_list_value_l (h0, h1, tl_) -> (h0,h1)::(unmake_list_value_l tl_)
  
  (** val nth_list_value_l : nat -> list_value_l -> (value*l) option **)
  
  let rec nth_list_value_l n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_value_l -> None
             | Cons_list_value_l (h0, h1, tl_) -> Some (h0,h1))
      | S m ->
          (match l0 with
             | Nil_list_value_l -> None
             | Cons_list_value_l (h0, h1, tl_) -> nth_list_value_l m tl_)
  
  (** val app_list_value_l : list_value_l -> list_value_l -> list_value_l **)
  
  let rec app_list_value_l l0 m =
    match l0 with
      | Nil_list_value_l -> m
      | Cons_list_value_l (h0, h1, tl_) -> Cons_list_value_l (h0, h1,
          (app_list_value_l tl_ m))
  
  (** val map_list_sz_value :
      (sz -> value -> 'a1) -> list_sz_value -> 'a1 list **)
  
  let rec map_list_sz_value f = function
    | Nil_list_sz_value -> []
    | Cons_list_sz_value (h0, h1, tl_) ->
        (f h0 h1)::(map_list_sz_value f tl_)
  
  (** val make_list_sz_value : (sz*value) list -> list_sz_value **)
  
  let rec make_list_sz_value = function
    | [] -> Nil_list_sz_value
    | p::tl_ ->
        let h0,h1 = p in
        Cons_list_sz_value (h0, h1, (make_list_sz_value tl_))
  
  (** val unmake_list_sz_value : list_sz_value -> (sz*value) list **)
  
  let rec unmake_list_sz_value = function
    | Nil_list_sz_value -> []
    | Cons_list_sz_value (h0, h1, tl_) -> (h0,h1)::(unmake_list_sz_value tl_)
  
  (** val nth_list_sz_value : nat -> list_sz_value -> (sz*value) option **)
  
  let rec nth_list_sz_value n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_sz_value -> None
             | Cons_list_sz_value (h0, h1, tl_) -> Some (h0,h1))
      | S m ->
          (match l0 with
             | Nil_list_sz_value -> None
             | Cons_list_sz_value (h0, h1, tl_) -> nth_list_sz_value m tl_)
  
  (** val app_list_sz_value :
      list_sz_value -> list_sz_value -> list_sz_value **)
  
  let rec app_list_sz_value l0 m =
    match l0 with
      | Nil_list_sz_value -> m
      | Cons_list_sz_value (h0, h1, tl_) -> Cons_list_sz_value (h0, h1,
          (app_list_sz_value tl_ m))
  
  (** val map_list_const : (const -> 'a1) -> list_const -> 'a1 list **)
  
  let rec map_list_const f = function
    | Nil_list_const -> []
    | Cons_list_const (h, tl_) -> (f h)::(map_list_const f tl_)
  
  (** val make_list_const : const list -> list_const **)
  
  let rec make_list_const = function
    | [] -> Nil_list_const
    | h::tl_ -> Cons_list_const (h, (make_list_const tl_))
  
  (** val unmake_list_const : list_const -> const list **)
  
  let rec unmake_list_const = function
    | Nil_list_const -> []
    | Cons_list_const (h, tl_) -> h::(unmake_list_const tl_)
  
  (** val nth_list_const : nat -> list_const -> const option **)
  
  let rec nth_list_const n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_const -> None
             | Cons_list_const (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_const -> None
             | Cons_list_const (h, tl_) -> nth_list_const m tl_)
  
  (** val app_list_const : list_const -> list_const -> list_const **)
  
  let rec app_list_const l0 m =
    match l0 with
      | Nil_list_const -> m
      | Cons_list_const (h, tl_) -> Cons_list_const (h,
          (app_list_const tl_ m))
  
  (** val map_list_typ : (typ -> 'a1) -> list_typ -> 'a1 list **)
  
  let rec map_list_typ f = function
    | Nil_list_typ -> []
    | Cons_list_typ (h, tl_) -> (f h)::(map_list_typ f tl_)
  
  (** val make_list_typ : typ list -> list_typ **)
  
  let rec make_list_typ = function
    | [] -> Nil_list_typ
    | h::tl_ -> Cons_list_typ (h, (make_list_typ tl_))
  
  (** val unmake_list_typ : list_typ -> typ list **)
  
  let rec unmake_list_typ = function
    | Nil_list_typ -> []
    | Cons_list_typ (h, tl_) -> h::(unmake_list_typ tl_)
  
  (** val nth_list_typ : nat -> list_typ -> typ option **)
  
  let rec nth_list_typ n l0 =
    match n with
      | O ->
          (match l0 with
             | Nil_list_typ -> None
             | Cons_list_typ (h, tl_) -> Some h)
      | S m ->
          (match l0 with
             | Nil_list_typ -> None
             | Cons_list_typ (h, tl_) -> nth_list_typ m tl_)
  
  (** val app_list_typ : list_typ -> list_typ -> list_typ **)
  
  let rec app_list_typ l0 m =
    match l0 with
      | Nil_list_typ -> m
      | Cons_list_typ (h, tl_) -> Cons_list_typ (h, (app_list_typ tl_ m))
  
  (** val list_const_rec2 :
      (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float
      -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 ->
      'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop ->
      const -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) ->
      (castop -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 ->
      list_const -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const ->
      'a1 -> 'a1) -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond
      -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const
      -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 ->
      'a1) -> (bop -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const
      -> 'a1 -> const -> 'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const ->
      'a2 -> 'a2) -> list_const -> 'a2 **)
  
  let list_const_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 =
    let rec f20 = function
      | Coq_const_zeroinitializer t0 -> f t0
      | Coq_const_int (s, i0) -> f0 s i0
      | Coq_const_floatpoint (f22, f23) -> f1 f22 f23
      | Coq_const_undef t0 -> f2 t0
      | Coq_const_null t0 -> f3 t0
      | Coq_const_arr (t0, l0) -> f4 t0 l0 (f21 l0)
      | Coq_const_struct l0 -> f5 l0 (f21 l0)
      | Coq_const_gid (t0, i0) -> f6 t0 i0
      | Coq_const_truncop (t0, c0, t1) -> f7 t0 c0 (f20 c0) t1
      | Coq_const_extop (e, c0, t0) -> f8 e c0 (f20 c0) t0
      | Coq_const_castop (c0, c1, t0) -> f9 c0 c1 (f20 c1) t0
      | Coq_const_gep (i0, c0, l0) -> f10 i0 c0 (f20 c0) l0 (f21 l0)
      | Coq_const_select (c0, c1, c2) ->
          f11 c0 (f20 c0) c1 (f20 c1) c2 (f20 c2)
      | Coq_const_icmp (c0, c1, c2) -> f12 c0 c1 (f20 c1) c2 (f20 c2)
      | Coq_const_fcmp (f22, c0, c1) -> f13 f22 c0 (f20 c0) c1 (f20 c1)
      | Coq_const_extractvalue (c0, l0) -> f14 c0 (f20 c0) l0 (f21 l0)
      | Coq_const_insertvalue (c0, c1, l0) ->
          f15 c0 (f20 c0) c1 (f20 c1) l0 (f21 l0)
      | Coq_const_bop (b, c0, c1) -> f16 b c0 (f20 c0) c1 (f20 c1)
      | Coq_const_fbop (f22, c0, c1) -> f17 f22 c0 (f20 c0) c1 (f20 c1)
    and f21 = function
      | Nil_list_const -> f18
      | Cons_list_const (c, l1) -> f19 c (f20 c) l1 (f21 l1)
    in f21
  
  (** val const_rec2 :
      (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float
      -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 ->
      'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop ->
      const -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) ->
      (castop -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 ->
      list_const -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const ->
      'a1 -> 'a1) -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond
      -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const
      -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 ->
      'a1) -> (bop -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const
      -> 'a1 -> const -> 'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const ->
      'a2 -> 'a2) -> const -> 'a1 **)
  
  let const_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 =
    let rec f20 = function
      | Coq_const_zeroinitializer t0 -> f t0
      | Coq_const_int (s, i0) -> f0 s i0
      | Coq_const_floatpoint (f22, f23) -> f1 f22 f23
      | Coq_const_undef t0 -> f2 t0
      | Coq_const_null t0 -> f3 t0
      | Coq_const_arr (t0, l0) -> f4 t0 l0 (f21 l0)
      | Coq_const_struct l0 -> f5 l0 (f21 l0)
      | Coq_const_gid (t0, i0) -> f6 t0 i0
      | Coq_const_truncop (t0, c0, t1) -> f7 t0 c0 (f20 c0) t1
      | Coq_const_extop (e, c0, t0) -> f8 e c0 (f20 c0) t0
      | Coq_const_castop (c0, c1, t0) -> f9 c0 c1 (f20 c1) t0
      | Coq_const_gep (i0, c0, l0) -> f10 i0 c0 (f20 c0) l0 (f21 l0)
      | Coq_const_select (c0, c1, c2) ->
          f11 c0 (f20 c0) c1 (f20 c1) c2 (f20 c2)
      | Coq_const_icmp (c0, c1, c2) -> f12 c0 c1 (f20 c1) c2 (f20 c2)
      | Coq_const_fcmp (f22, c0, c1) -> f13 f22 c0 (f20 c0) c1 (f20 c1)
      | Coq_const_extractvalue (c0, l0) -> f14 c0 (f20 c0) l0 (f21 l0)
      | Coq_const_insertvalue (c0, c1, l0) ->
          f15 c0 (f20 c0) c1 (f20 c1) l0 (f21 l0)
      | Coq_const_bop (b, c0, c1) -> f16 b c0 (f20 c0) c1 (f20 c1)
      | Coq_const_fbop (f22, c0, c1) -> f17 f22 c0 (f20 c0) c1 (f20 c1)
    and f21 = function
      | Nil_list_const -> f18
      | Cons_list_const (c, l1) -> f19 c (f20 c) l1 (f21 l1)
    in f20
  
  (** val const_mutrec :
      (typ -> 'a1) -> (sz -> coq_Int -> 'a1) -> (floating_point -> coq_Float
      -> 'a1) -> (typ -> 'a1) -> (typ -> 'a1) -> (typ -> list_const -> 'a2 ->
      'a1) -> (list_const -> 'a2 -> 'a1) -> (typ -> id -> 'a1) -> (truncop ->
      const -> 'a1 -> typ -> 'a1) -> (extop -> const -> 'a1 -> typ -> 'a1) ->
      (castop -> const -> 'a1 -> typ -> 'a1) -> (inbounds -> const -> 'a1 ->
      list_const -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> const ->
      'a1 -> 'a1) -> (cond -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fcond
      -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (const -> 'a1 -> list_const
      -> 'a2 -> 'a1) -> (const -> 'a1 -> const -> 'a1 -> list_const -> 'a2 ->
      'a1) -> (bop -> const -> 'a1 -> const -> 'a1 -> 'a1) -> (fbop -> const
      -> 'a1 -> const -> 'a1 -> 'a1) -> 'a2 -> (const -> 'a1 -> list_const ->
      'a2 -> 'a2) -> (const -> 'a1)*(list_const -> 'a2) **)
  
  let const_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 =
    (const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      h18 h19 h20 h21),(list_const_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
                         h12 h13 h14 h15 h16 h17 h18 h19 h20 h21)
  
  (** val list_typ_rec2 :
      (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz ->
      typ -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
      (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1)
      -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> list_typ -> 'a2 **)
  
  let list_typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
    let rec f12 = function
      | Coq_typ_int s -> f s
      | Coq_typ_floatpoint f14 -> f0 f14
      | Coq_typ_void -> f1
      | Coq_typ_label -> f2
      | Coq_typ_metadata -> f3
      | Coq_typ_array (s, t1) -> f4 s t1 (f12 t1)
      | Coq_typ_function (t1, l0, v) -> f5 t1 (f12 t1) l0 (f13 l0) v
      | Coq_typ_struct l0 -> f6 l0 (f13 l0)
      | Coq_typ_pointer t1 -> f7 t1 (f12 t1)
      | Coq_typ_opaque -> f8
      | Coq_typ_namedt i0 -> f9 i0
    and f13 = function
      | Nil_list_typ -> f10
      | Cons_list_typ (t0, l1) -> f11 t0 (f12 t0) l1 (f13 l1)
    in f13
  
  (** val typ_rec2 :
      (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz ->
      typ -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
      (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1)
      -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> typ -> 'a1 **)
  
  let typ_rec2 f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
    let rec f12 = function
      | Coq_typ_int s -> f s
      | Coq_typ_floatpoint f14 -> f0 f14
      | Coq_typ_void -> f1
      | Coq_typ_label -> f2
      | Coq_typ_metadata -> f3
      | Coq_typ_array (s, t1) -> f4 s t1 (f12 t1)
      | Coq_typ_function (t1, l0, v) -> f5 t1 (f12 t1) l0 (f13 l0) v
      | Coq_typ_struct l0 -> f6 l0 (f13 l0)
      | Coq_typ_pointer t1 -> f7 t1 (f12 t1)
      | Coq_typ_opaque -> f8
      | Coq_typ_namedt i0 -> f9 i0
    and f13 = function
      | Nil_list_typ -> f10
      | Cons_list_typ (t0, l1) -> f11 t0 (f12 t0) l1 (f13 l1)
    in f12
  
  (** val typ_mutrec :
      (sz -> 'a1) -> (floating_point -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (sz ->
      typ -> 'a1 -> 'a1) -> (typ -> 'a1 -> list_typ -> 'a2 -> varg -> 'a1) ->
      (list_typ -> 'a2 -> 'a1) -> (typ -> 'a1 -> 'a1) -> 'a1 -> (id -> 'a1)
      -> 'a2 -> (typ -> 'a1 -> list_typ -> 'a2 -> 'a2) -> (typ ->
      'a1)*(list_typ -> 'a2) **)
  
  let typ_mutrec h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 =
    (typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13),
      (list_typ_rec2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
 end

