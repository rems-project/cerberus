Require Import Coq.Arith.PeanoNat.
From Coq.Lists Require Import List ListSet.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zwf.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
From Coq.Strings Require Import String Byte HexString.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Coq.Program.Wf.
Require Recdef.
Require Import Lia.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

Require Import Capabilities Addr Memory_model Mem_common ErrorWithState Undefined Morello ErrorWithState Location Symbol Implementation Tags Utils Switches AilTypesAux.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Require Import AltBinNotations.
Import ListNotations.
Import MonadNotation.

Module ZMap := FMapAVL.Make(Z_as_OT).

Module CheriMemory
  (C:Capability(MorelloAddr)
       (MoreloOTYPE)
       (MorelloCAP_SEAL_T)
       (MorelloVADDR_INTERVAL)
       (MorelloPermission)
  )
  (IMP: Implementation)
  : Memory(MorelloAddr).

  Include Mem_common(MorelloAddr).
  Include AilTypesAux(IMP).

  Definition name := "CHERI memory model".

  Definition symbolic_storage_instance_id : Set := Z.
  Definition storage_instance_id : Set := Z.

  (* Following types need to be defined *)
  Definition derivecap_op: Set := unit. (* Mem_common.derivecap_op *)
  Definition integer_operator: Set := unit. (* Mem_common.integer_operator *)
  Definition floating_operator: Set := unit. (* Mem_common.floating_operator *)
  Definition intrinsics_signature: Set := unit. (* intrinsics_signature *)

  Inductive provenance : Set :=
  | Prov_none : provenance
  | Prov_some : storage_instance_id -> provenance
  | Prov_symbolic : symbolic_storage_instance_id -> provenance
  | Prov_device : provenance.

  Inductive function_pointer : Set :=
  | FP_valid : Symbol.sym -> function_pointer
  | FP_invalid : C.t -> function_pointer.

  Inductive pointer_value_base : Set :=
  | PVfunction : function_pointer -> pointer_value_base
  | PVconcrete : C.t -> pointer_value_base.

  Inductive pointer_value_ind : Set :=
  | PV : provenance -> pointer_value_base -> pointer_value_ind.

  Definition pointer_value := pointer_value_ind.

  Inductive integer_value_ind : Set :=
  | IV : Z -> integer_value_ind
  | IC : bool -> C.t -> integer_value_ind.

  Definition integer_value := integer_value_ind.

  Definition floating_value : Set := float. (* 64 bit *)

  Inductive mem_value_with_err :=
  | MVEunspecified : Ctype.ctype -> mem_value_with_err
  | MVEinteger :
    Ctype.integerType -> integer_value ->
    mem_value_with_err
  | MVEfloating :
    Ctype.floatingType -> floating_value ->
    mem_value_with_err
  | MVEpointer :
    Ctype.ctype -> pointer_value -> mem_value_with_err
  | MVEarray : list mem_value_with_err -> mem_value_with_err
  | MVEstruct :
    Symbol.sym ->
    list  (Symbol.identifier *  Ctype.ctype * mem_value_with_err) ->
    mem_value_with_err
  | MVEunion :
    Symbol.sym ->
    Symbol.identifier -> mem_value_with_err ->
    mem_value_with_err
  | MVErr : mem_error -> mem_value_with_err.

  Inductive mem_value_ind :=
  | MVunspecified : Ctype.ctype -> mem_value_ind
  | MVinteger :
    Ctype.integerType -> integer_value -> mem_value_ind
  | MVfloating :
    Ctype.floatingType -> floating_value -> mem_value_ind
  | MVpointer :
    Ctype.ctype -> pointer_value -> mem_value_ind
  | MVarray : list mem_value_ind -> mem_value_ind
  | MVstruct :
    Symbol.sym ->
    list
      (Symbol.identifier *
         Ctype.ctype * mem_value_ind) -> mem_value_ind
  | MVunion :
    Symbol.sym ->
    Symbol.identifier -> mem_value_ind -> mem_value_ind.

  Definition mem_value := mem_value_ind.

  Inductive access_intention : Set :=
  | ReadIntent : access_intention
  | WriteIntent : access_intention
  | CallIntent : access_intention.

  Inductive readonly_status : Set :=
  | IsWritable : readonly_status
  | IsReadOnly_string_literal : readonly_status
  | IsReadOnly : readonly_status.

  Inductive allocation_taint :=
  | Exposed
  | Unexposed.

  Definition allocation_taint_eqb (a b: allocation_taint) :=
    match a, b with
    | Exposed, Exposed => true
    | Unexposed, Unexposed => true
    | _, _ => false
    end.

  Inductive taint_ind :=
  | NoTaint: taint_ind
  | NewTaint: list storage_instance_id -> taint_ind.

  Record allocation :=
    {
      prefix : Symbol.prefix;
      base : MorelloAddr.t;
      size : Z;
      ty : option Ctype.ctype;
      is_readonly : readonly_status;
      taint : allocation_taint
    }.

  Record AbsByte :=
    {
      prov : provenance;
      copy_offset : option nat;
      value : option byte
    }.

  Definition absbyte_v prov copy_offset value : AbsByte
    :=
    {| prov := prov; copy_offset := copy_offset; value := value |}.


  Record mem_state_r :=
    {
      next_alloc_id : storage_instance_id;
      next_iota : symbolic_storage_instance_id;
      last_address : MorelloAddr.t;
      allocations : ZMap.t allocation;
      iota_map : ZMap.t
                   ((* `Single *) storage_instance_id +
                      (* `Double *) storage_instance_id * storage_instance_id);
      funptrmap : ZMap.t
                    (digest * string * C.t);
      varargs : ZMap.t
                  (Z * list (Ctype.ctype * pointer_value));
      next_varargs_id : Z;
      bytemap : ZMap.t AbsByte;
      captags : ZMap.t bool;
      dead_allocations : list storage_instance_id;
      dynamic_addrs : list MorelloAddr.t;
      last_used : option storage_instance_id
    }.

  (*
     Copy of the state (for copy-and-pase) in absence of "with" notation

              {|
                next_alloc_id    := st.(next_alloc_id);
                next_iota        := st.(next_iota);
                last_address     := st.(last_address) ;
                allocations      := st.(allocations);
                iota_map         := st.(iota_map);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                captags          := st.(captags);
                dead_allocations := st.(dead_allocations);
                dynamic_addrs    := st.(dynamic_addrs);
                last_used        := st.(last_used);
              |}
   *)

  Definition mem_state := mem_state_r.

  Definition mem_state_with_allocations allocations (r : mem_state)
    :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) allocations r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

  Definition mem_state_with_last_used last_used (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) last_used.


  Definition initial_address := (HexString.to_Z "0xFFFFFFFF").

  Definition DEFAULT_FUEL:nat := 1000%nat. (* TODO maybe needs to be abstracted *)

  Definition initial_mem_state : mem_state :=
    {|
      next_alloc_id := Z0;
      next_iota := Z0;
      last_address := initial_address;
      allocations := ZMap.empty allocation;
      iota_map := ZMap.empty (storage_instance_id + storage_instance_id * storage_instance_id);
      funptrmap := ZMap.empty (digest * string * C.t);
      varargs := ZMap.empty (Z * list (Ctype.ctype * pointer_value));
      next_varargs_id := Z0;
      bytemap := ZMap.empty AbsByte;
      captags := ZMap.empty bool;
      dead_allocations := nil;
      dynamic_addrs := nil;
      last_used := None
    |}.

  (* Unfortunate names of two consturctors are mirroring ones from
     OCaml `Nondeterminism` monad. Third one is used where `failwith` was
     or `assert false` was used in OCaml. *)
  Inductive memMError :=
  | Other: mem_error -> memMError
  | Undef0: location_ocaml -> (list undefined_behaviour) -> memMError
  | InternalErr: string -> memMError.

  Definition memM := errS mem_state memMError.
  #[local] Instance memM_monad: Monad memM.
  Proof.
    typeclasses eauto.
  Qed.

  (* simple string error *)
  Notation serr := (sum string).

  Definition serr2memM {A: Type} (e:serr A): (memM A)
    := match e with
       | inr v => ret v
       | inl msg => raise (InternalErr msg)
       end.

  Local Instance Exception_serr : MonadExc string (serr) :=
    { raise := fun _ v => inl v
    ; catch := fun _ c h => match c with
                         | inl v => h v
                         | inr x => inr x
                         end
    }.

  Definition option2serr {A: Type} (msg:string) (o:option A): (serr A)
    := match o with
       | Some v => ret v
       | None => raise msg
       end.

  Definition sassert (b:bool) (msg:string) : serr unit
    := if b then ret tt else raise msg.

  Definition fail {A:Type} err : memM A :=
    let loc :=
      match err with
      | MerrAccess loc  _  _
      | MerrWriteOnReadOnly _ loc
      | MerrReadUninit loc
      | MerrUndefinedFree loc _
      | MerrFreeNullPtr loc
      | MerrArrayShift loc
      | MerrIntFromPtr loc =>
          loc
      | MerrOutsideLifetime _
      | MerrInternal _
      | MerrOther _
      | MerrPtrdiff
      | MerrUndefinedRealloc
      | MerrPtrFromInt
      | MerrPtrComparison
      | MerrWIP _
      | MerrVIP _ =>
          Loc_other "cherimem"
      | MerrCHERI loc _ =>
          loc
      end
    in
    match undefinedFromMem_error err with
    | Some ub =>
        raise (Undef0 loc [ub])
    | None =>
        raise (Other err)
    end.

  Inductive merr :=
  | OK: merr
  | FAIL: mem_error -> merr.

  Definition merr2memM {A: Type} (v:A) (e:merr): (memM A)
    := match e with
       | OK => ret v
       | FAIL me => fail me
       end.

  Inductive footprint_ind :=
  (* base address, size *)
  | FP: MorelloAddr.t * Z -> footprint_ind.

  Definition footprint := footprint_ind.

  Definition check_overlap a b :=
    match a,b with
    |  (FP (b1, sz1)), (FP (b2, sz2)) =>
         let b1 := b1 in
         let b2 := b2 in
         if andb (Z.eqb b1 b2) (Z.eqb sz1 sz2) then
           ExactOverlap
         else if orb
                   (Z.leb (Z.add b1 sz1) b2)
                   (Z.leb (Z.add b2 sz2) b1)
              then
                Disjoint
              else
                PartialOverlap
    end.


  (* TODO: check if this is correct *)
  Definition Z_integerRem_f := Z.modulo.

  Definition wrapI min_v max_v n :=
    let dlt := Z.succ (Z.sub max_v min_v) in
    let r := Z_integerRem_f n dlt in
    if Z.leb r max_v then r
    else Z.sub r dlt.

  Definition unwrap_cap_value n :=
    let vaddr_bits := (Z.of_nat C.sizeof_vaddr) * 8 in
    let min_v := Z.neg (Z.to_pos (Z.pow 2 (vaddr_bits - 1))) in
    let max_v := Z.sub (Z.pow 2 (vaddr_bits - 1)) 1 in
    if andb (Z.leb n min_v) (Z.leb n max_v)
    then n
    else wrapI min_v max_v n.

  Definition num_of_int x :=
    match x with
    | IV n => n
    | IC is_signed c =>
        let n := C.cap_get_value c in
        if is_signed then unwrap_cap_value n else n
    end.


  (** Invalidate capability tags for memory region starting from
      [addr] with [size].

      All tags which were [true] will be flipped to [false].  For
      addresses which did not have tags set, they will remain
      unspecified.
   *)
  Definition clear_caps
    (addr:MorelloAddr.t)
    (size:Z)
    (captags:ZMap.t bool): ZMap.t bool
    :=
    let align := IMP.get.(alignof_pointer) in
    let lower_a x := Z.mul (Z.quot x align) align in
    let a0 := lower_a addr in
    let a1 := lower_a (Z.pred (Z.add addr size)) in
    ZMap.mapi
      (fun (a:Z) (v:bool) =>
         if (v && Z.geb a a0 && Z.leb a a1)%bool then false
         else v
      ) captags.

  Definition allocator (size:Z) (align:Z) : memM (storage_instance_id * MorelloAddr.t) :=
    get >>= fun st =>
        let alloc_id := st.(next_alloc_id) in
        (
          let z := Z.sub st.(last_address) size in
          let (q,m) := Z.quotrem z align in
          let z' := Z.sub z (Z.abs m) in
          if Z.leb z' 0 then
            fail (MerrOther "CHERI.allocator: failed (out of memory)")
          else
            ret z'
        )
          >>= fun addr =>
            let addr := addr in
            put
              {|
                next_alloc_id    := Z.succ alloc_id;
                next_iota        := st.(next_iota);
                last_address     := addr ;
                allocations      := st.(allocations);
                iota_map         := st.(iota_map);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                (* clear tags in newly allocated region *)
                captags          := clear_caps addr size st.(captags);
                dead_allocations := st.(dead_allocations);
                dynamic_addrs    := st.(dynamic_addrs);
                last_used        := Some alloc_id;
              |}
            ;;
            ret (alloc_id, addr).


  Definition alignof
    (fuel: nat)
    (maybe_tagDefs : option (SymMap.t Ctype.tag_definition))
    : Ctype.ctype -> serr Z
    :=
    let tagDefs :=
      match maybe_tagDefs with
      | Some x => x
      | None => Tags.tagDefs tt
      end in
    let fix alignof_ (fuel: nat) ty  :=
      match fuel with
      | O => raise "alignof out of fuel"
      | S fuel =>
          match ty with
          | Ctype.Ctype _ Ctype.Void => raise "no alignment for void"
          | Ctype.Ctype _ (Ctype.Basic (Ctype.Integer ity)) =>
              ret (IMP.get.(alignof_ity) ity)
          | Ctype.Ctype _ (Ctype.Basic (Ctype.Floating fty)) =>
              ret (IMP.get.(alignof_fty) fty)
          | Ctype.Ctype _ (Ctype.Array elem_ty _) =>
              alignof_ fuel elem_ty
          |
            (Ctype.Ctype _ (Ctype.Function _ _ _) |
              Ctype.Ctype _ (Ctype.FunctionNoParams _)) =>
              raise "no alighment for function types"
          | Ctype.Ctype _ (Ctype.Pointer _ _) =>
              ret (IMP.get.(alignof_pointer))
          | Ctype.Ctype _ (Ctype.Atomic atom_ty) =>
              alignof_ fuel  atom_ty
          | Ctype.Ctype _ (Ctype.Struct tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (Ctype.UnionDef _) =>
                  raise "no alignment for struct with union tag"
              | Some (Ctype.StructDef membrs flexible_opt) =>
                  init <-
                    match flexible_opt with
                    | None => ret 0
                    | Some (Ctype.FlexibleArrayMember _ _ _ elem_ty) =>
                        alignof_ fuel (Ctype.Ctype nil (Ctype.Array elem_ty None))
                    end ;;
                  monadic_fold_left
                    (fun acc '(_, (_, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       ret (Z.max al acc)
                    )
                    membrs
                    init
              | None => raise "could not find struct tag to compute alignment"
              end
          | Ctype.Ctype _ (Ctype.Union tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (Ctype.StructDef _ _) =>
                  raise "no alignment for union with struct tag"
              | Some (Ctype.UnionDef membrs) =>
                  monadic_fold_left
                    (fun acc '(_, (_, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       ret (Z.max al acc)
                    )
                    membrs
                    0
              | None => raise "could not find union tag to compute alignment"
              end
          end
      end
    in alignof_ fuel.

  Fixpoint offsetsof
    (fuel: nat)
    (tagDefs : SymMap.t Ctype.tag_definition)
    (tag_sym : Symbol.sym)
    : serr (list (Symbol.identifier * Ctype.ctype * Z) * Z)
    :=
    match fuel with
    | O => raise "offsetof out of fuel"
    | S fuel =>
        match SymMap.find tag_sym tagDefs with
        | Some (Ctype.StructDef membrs_ flexible_opt) =>
            let membrs :=
              match flexible_opt with
              | None => membrs_
              | Some (Ctype.FlexibleArrayMember attrs ident qs ty) =>
                  List.app membrs_ [ (ident, (attrs, qs, ty)) ]
              end in
            '(xs, maxoffset) <-
              monadic_fold_left
                (fun '(xs, last_offset) '(membr, (_, _, ty))  =>
                   size <- sizeof fuel (Some tagDefs) ty ;;
                   align <- alignof fuel (Some tagDefs) ty ;;
                   let x_value := Z.modulo last_offset align in
                   let pad :=
                     if Z.eqb x_value 0 then
                       0
                     else
                       Z.sub align x_value in
                   ret ((cons (membr, ty, (Z.add last_offset pad)) xs),
                       (Z.add (Z.add last_offset pad) size))
                )
                membrs
                (nil, 0) ;;
            ret ((List.rev xs), maxoffset)
        | Some (Ctype.UnionDef membrs) =>
            ret ((List.map (fun '(ident, (_, _, ty)) => (ident, ty, 0)) membrs), 0)
        | None => raise "could not find tag"
        end
    end
  with sizeof
         (fuel: nat)
         (maybe_tagDefs : option (SymMap.t Ctype.tag_definition))
    : Ctype.ctype -> serr Z
       :=
         match fuel with
         | O => fun _ => raise "sizeof out of fuel"
         | S fuel =>
             let tagDefs :=
               match maybe_tagDefs with
               | Some x => x
               | None => Tags.tagDefs tt
               end in
             fun (function_parameter : Ctype.ctype) =>
               let '(Ctype.Ctype _ ty) as cty := function_parameter in
               match ty with
               |
                 (Ctype.Void | Ctype.Array _ None |
                   Ctype.Function _ _ _ |
                   Ctype.FunctionNoParams _) =>
                   raise "no sizeof for function types"
               | Ctype.Basic (Ctype.Integer ity) =>
                   option2serr "sizeof_ity not defined in Implementation" (IMP.get.(sizeof_ity) ity)
               | Ctype.Basic (Ctype.Floating fty) =>
                   option2serr "sizeof_fty not defined in Implementation" (IMP.get.(sizeof_fty) fty)
               | Ctype.Array elem_ty (Some n_value) =>
                   sz <- (sizeof fuel (Some tagDefs) elem_ty) ;;
                   ret (Z.mul n_value sz)
               | Ctype.Pointer _ _ =>
                   ret (IMP.get.(sizeof_pointer))
               | Ctype.Atomic atom_ty =>
                   sizeof fuel (Some tagDefs) atom_ty
               | Ctype.Struct tag_sym =>
                   '(_, max_offset) <- offsetsof fuel tagDefs tag_sym ;;
                   align <- alignof fuel (Some tagDefs) cty ;;
                   let x_value := Z.modulo max_offset align in
                   ret (if Z.eqb x_value 0 then
                          max_offset
                        else
                          Z.add max_offset (Z.sub align x_value))
               | Ctype.Union tag_sym =>
                   match SymMap.find tag_sym tagDefs with
                   | Some (Ctype.StructDef _ _) =>
                       raise "no alignment for struct with union tag"
                   | Some (Ctype.UnionDef membrs) =>
                       '(max_size, max_align) <-
                         monadic_fold_left
                           (fun '(acc_size, acc_align) '(_, (_, _, ty)) =>
                              sz <- sizeof fuel (Some tagDefs) ty ;;
                              al <- alignof fuel (Some tagDefs) ty ;;
                              ret ((Z.max acc_size sz),(Z.max acc_align al))
                           )
                           membrs (0, 0) ;;
                       let x_value := Z.modulo max_size max_align in
                       ret (if Z.eqb x_value 0 then
                              max_size
                            else
                              Z.add max_size (Z.sub max_align x_value))
                   | None => raise "could not find union tag to compute sizeof"
                   end
               end
         end.

  Definition bits_of_float: float -> Z. Proof. Admitted. (* TODO *)

  (* size is in bytes *)
  Definition bytes_of_Z (is_signed : bool) (size : nat) (i_value : Z) : serr (list byte). Proof. Admitted. (* TODO *)
  (* :=
    let nbits := Z.mul 8 size in
    let '(min, max) :=
      if is_signed then
        ((Z.negate
          (Z.pow_int (Z.of_int 2) (Z.sub nbits 1))),
          (Z.sub
            (Z.pow_int (Z.of_int 2) (Z.sub nbits 1))
            (Z.succ Z.zero)))
      else
        (Z.zero,
          (Z.sub (Z.pow_int (Z.of_int 2) nbits)
            (Z.succ Z.zero))) in
    if
      orb
        (negb
          (andb (le min i_value)
            (le i_value max)))
        (gt nbits 128)
    then
      fail "bytes_of_int failure"
    else
      list_init size
        (fun (n_value : int) =>
          CoqOfOCaml.Stdlib.char_of_int
            (Z.to_int (Z.extract_num i_value (Z.mul 8 n_value) 8))).
   *)

  Definition resolve_function_pointer
    (funptrmap : ZMap.t (digest * string * C.t))
    (fp : function_pointer)
    : ZMap.t (digest * string * C.t) * C.t
    :=
    match fp with
    | FP_valid (Symbol.Symbol file_dig n opt_name) =>
        match ZMap.find n funptrmap with
        | Some (_, _, c) => (funptrmap, c)
        | None =>
            let c := C.alloc_fun (Z.add initial_address n) in
            (match opt_name with
             | Symbol.SD_Id name =>
                 ZMap.add n (file_dig, name, c) funptrmap
             | _ => funptrmap
             end, c)
        end
    | FP_invalid c => (funptrmap, c)
    end.

  Fixpoint repr
    (fuel: nat)
    (funptrmap: ZMap.t (digest * string * C.t))
    (captags : ZMap.t bool)
    (addr : Z)
    (mval : mem_value)
    : serr ((ZMap.t (digest * string * C.t)) * (ZMap.t bool) * (list AbsByte))
    :=
    match fuel with
    | O => raise "out of fuel in repr"
    | S fuel =>
        match mval with
        | MVunspecified ty =>
            sz <- sizeof DEFAULT_FUEL None ty ;;
            ret (funptrmap, (clear_caps addr sz captags),
                (list_init (Z.to_nat sz) (fun _ => absbyte_v Prov_none None None)))
        | MVinteger ity (IV n_value) =>
            iss <- option2serr "Could not get int signedness of a type in repr" (is_signed_ity DEFAULT_FUEL ity) ;;
            sz <- sizeof DEFAULT_FUEL None (Ctype.Ctype nil (Ctype.Basic (Ctype.Integer ity))) ;;
            bs' <- bytes_of_Z iss (Z.to_nat sz) n_value ;;
            let bs := List.map (fun (x : byte) => absbyte_v Prov_none None (Some x)) bs' in
            ret (funptrmap, (clear_caps addr (Z.of_nat (List.length bs)) captags), bs)
        | MVinteger ity (IC _ c_value) =>
            let '(cb, ct) := C.encode true c_value in
            cb'  <- bytes_of_Z false (*TODO: not sure about sign *)
                      (Z.to_nat (IMP.get.(sizeof_pointer)))
                      cb ;;
            ret (funptrmap, (ZMap.add addr ct captags),
                (mapi
                   (fun (i_value : nat) (b_value : byte) =>
                      absbyte_v Prov_none None (Some b_value)) cb'))
        | MVfloating fty fval =>
            sz <- sizeof DEFAULT_FUEL None (Ctype.Ctype nil (Ctype.Basic (Ctype.Floating fty))) ;;
            bs' <- bytes_of_Z true (Z.to_nat sz) (bits_of_float fval) ;;
            let bs := List.map (fun (x : byte) => absbyte_v Prov_none None (Some x)) bs'
            in
            ret (funptrmap, (clear_caps addr (Z.of_nat (List.length bs)) captags), bs)
        | MVpointer ref_ty (PV prov ptrval_) =>
            match ptrval_ with
            | PVfunction
                ((FP_valid (Symbol.Symbol file_dig n_value opt_name)) as
                  fp) =>
                let '(funptrmap, c_value) := resolve_function_pointer funptrmap fp in
                let '(cb, ct) := C.encode true c_value in
                cb'  <- bytes_of_Z false (*TODO: not sure about sign *)
                          (Z.to_nat (IMP.get.(sizeof_pointer)))
                          cb ;;
                ret (funptrmap, (ZMap.add addr ct captags),
                    (mapi
                       (fun (i_value : nat) (b_value : byte) =>
                          absbyte_v prov (Some i_value) (Some b_value)) cb'))
            | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
                let '(cb, ct) := C.encode true c_value in
                cb'  <- bytes_of_Z false (*TODO: not sure about sign *)
                          (Z.to_nat (IMP.get.(sizeof_pointer)))
                          cb ;;
                ret (funptrmap, (ZMap.add addr ct captags),
                    (mapi
                       (fun (i_value : nat) (b_value : byte) =>
                          absbyte_v prov (Some i_value) (Some b_value)) cb'))
            end
        | MVarray mvals =>
            '(funptrmap, captags, _, bs_s) <-
              monadic_fold_left
                (fun '(funptrmap, captags, addr, bs) (mval : mem_value) =>
                   '(funptrmap, captags, bs') <- repr fuel funptrmap captags addr mval ;;
                   let addr := Z.add addr (Z.of_nat (List.length bs')) in
                   ret (funptrmap, captags, addr, (cons bs' bs)))
                mvals (funptrmap, captags, addr, nil) ;;
            ret (funptrmap, captags, (List.concat (List.rev bs_s)))
        | MVstruct tag_sym xs =>
            let padding_byte _ : AbsByte := absbyte_v Prov_none None None in
            '(offs, last_off) <- offsetsof DEFAULT_FUEL (Tags.tagDefs tt) tag_sym ;;
            sz <- sizeof DEFAULT_FUEL None (Ctype.Ctype nil (Ctype.Struct tag_sym)) ;;
            let final_pad := Z.sub sz last_off in
            '(funptrmap, captags, _, bs) <-
              monadic_fold_left2
                (fun (f: ZMap.t (digest * string * C.t) * ZMap.t bool * Z * list AbsByte) =>
                   let '(funptrmap, captags, last_off, acc) := f in
                   fun (f : Symbol.identifier *  Ctype.ctype * Z) =>
                     let '(ident, ty, off) := f in
                     fun (function_parameter :
                           Symbol.identifier *
                             Ctype.ctype * mem_value) =>
                       let '(_, _, mval) := function_parameter in
                       let pad := Z.sub off last_off in
                       '(funptrmap, captags, bs) <-
                         repr fuel funptrmap captags (Z.add addr off) mval ;;
                       sz <- sizeof DEFAULT_FUEL None ty ;;
                       ret (funptrmap, captags, (Z.add off sz),
                           (List.app acc
                              (List.app (list_init (Z.to_nat pad) padding_byte) bs))))
                (funptrmap, captags, 0, nil) offs xs ;;
            ret (funptrmap, captags,
                (List.app bs (list_init (Z.to_nat final_pad) padding_byte)))
        | MVunion tag_sym memb_ident mval =>
            size <- sizeof DEFAULT_FUEL None (Ctype.Ctype nil (Ctype.Union tag_sym)) ;;
            '(funptrmap', captags', bs) <- repr fuel funptrmap captags addr mval ;;
            ret (funptrmap', captags',
                (List.app bs
                   (list_init (Nat.sub (Z.to_nat size) (List.length bs))
                      (fun _ => absbyte_v Prov_none None None))))
        end
    end.


  Definition allocate_object
    (tid:thread_id)
    (pref:Symbol.prefix)
    (int_val:integer_value)
    (ty:Ctype.ctype)
    (init_opt:option mem_value)
    : memM pointer_value
    :=
    let align_n := num_of_int int_val in
    size_n <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;

    let mask := C.representable_alignment_mask size_n in
    let size_n' := C.representable_length size_n in
    let align_n' := Z.max align_n (Z.add (Z.succ (Z.zero)) (MorelloAddr.bitwise_complement mask)) in

    allocator size_n' align_n' >>=
      (fun '(alloc_id, addr) =>
         (match init_opt with
          | None =>
              let alloc := {| prefix := pref; base:= addr; size:= size_n'; ty:= Some ty; is_readonly:= IsWritable; taint:= Unexposed|} in
              update (fun st =>
                        {|
                          next_alloc_id    := st.(next_alloc_id);
                          next_iota        := st.(next_iota);
                          last_address     := st.(last_address) ;
                          allocations      := ZMap.add alloc_id alloc st.(allocations);
                          iota_map         := st.(iota_map);
                          funptrmap        := st.(funptrmap);
                          varargs          := st.(varargs);
                          next_varargs_id  := st.(next_varargs_id);
                          bytemap          := st.(bytemap);
                          captags          := st.(captags);
                          dead_allocations := st.(dead_allocations);
                          dynamic_addrs    := st.(dynamic_addrs);
                          last_used        := st.(last_used);
                        |}) ;; ret false
          | Some mval =>
              let (ro,readonly_status) :=
                match pref with
                | Symbol.PrefStringLiteral _ _ => (true,IsReadOnly_string_literal)
                | _ => (false,IsWritable)
                end
              in
              let alloc := {| prefix:= pref; base:= addr; size:= size_n'; ty:= Some ty; is_readonly:= readonly_status; taint:= Unexposed |} in

              st <- get ;;
              '(funptrmap, captags, pre_bs) <- serr2memM (repr DEFAULT_FUEL st.(funptrmap) st.(captags) addr mval) ;;
              let bs := mapi (fun i b => (Z.add addr (Z.of_nat i), b)) pre_bs in
              put {|
                  next_alloc_id    := st.(next_alloc_id);
                  next_iota        := st.(next_iota);
                  last_address     := st.(last_address) ;
                  allocations      := ZMap.add alloc_id alloc st.(allocations);
                  iota_map         := st.(iota_map);
                  funptrmap        := funptrmap;
                  varargs          := st.(varargs);
                  next_varargs_id  := st.(next_varargs_id);
                  bytemap          := List.fold_left (fun acc '(addr, b) =>
                                                        ZMap.add addr b acc
                                        ) bs st.(bytemap);
                  captags          := captags;
                  dead_allocations := st.(dead_allocations);
                  dynamic_addrs    := st.(dynamic_addrs);
                  last_used        := st.(last_used);
                |}
              ;;
              ret ro
          end)
           >>=
           (fun ro =>
              let c := C.alloc_cap addr size_n' in
              if C.cap_bounds_representable_exactly c (addr, Z.add addr size_n')
              then
                let c :=
                  if ro then
                    let p := C.cap_get_perms c in
                    let p := MorelloPermission.perm_clear_store p in
                    let p := MorelloPermission.perm_clear_store_cap p in
                    let p := MorelloPermission.perm_clear_store_local_cap p in
                    C.cap_narrow_perms c p
                  else c
                in
                ret (PV (Prov_some alloc_id) (PVconcrete c))
              else
                raise (InternalErr "Error settting exeact bounds for allocated region"))).

  Definition allocate_region
    (tid : thread_id)
    (pref : Symbol.prefix)
    (align_int : integer_value)
    (size_int : integer_value)
    : memM pointer_value
    :=
    let align_n := num_of_int align_int in
    let size_n := num_of_int size_int in
    let mask := C.representable_alignment_mask size_n in
    let size_n' := C.representable_length size_n in
    let align_n' :=
      Z.max align_n (Z.succ (MorelloAddr.bitwise_complement mask)) in

    allocator size_n' align_n' >>=
      (fun '(alloc_id, addr) =>
         let alloc :=
           {| prefix := Symbol.PrefMalloc;
             base := addr;
             size := size_n';
             ty := None;
             is_readonly := IsWritable;
             taint := Unexposed |}
         in
         update
           (fun (st : mem_state) =>
              {|
                next_alloc_id    := st.(next_alloc_id);
                next_iota        := st.(next_iota);
                last_address     := st.(last_address) ;
                allocations      := (ZMap.add alloc_id alloc st.(allocations));
                iota_map         := st.(iota_map);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                captags          := st.(captags);
                dead_allocations := st.(dead_allocations);
                dynamic_addrs    := addr::st.(dynamic_addrs);
                last_used        := st.(last_used);
              |})
         ;;
         (let c_value := C.alloc_cap addr size_n' in
          if
            C.cap_bounds_representable_exactly c_value
              (addr, (Z.add addr size_n'))
          then
            ret (PV (Prov_some alloc_id) (PVconcrete c_value))
          else
            raise (InternalErr "Error settting exeact bounds for allocated region"))).

  Definition cap_is_null  (c : C.t) : bool :=
    Z.eqb (C.cap_get_value c) 0.

  Definition is_dynamic addr : memM bool :=
    get >>= fun st =>
        ret (set_mem Z_as_OT.eq_dec addr st.(dynamic_addrs)).

  Definition is_dead (alloc_id : storage_instance_id) : memM bool :=
    get >>= fun st =>
        ret (set_mem Z_as_OT.eq_dec alloc_id st.(dead_allocations)).

  Definition get_allocation (alloc_id : Z) : memM allocation :=
    get >>=
      (fun st =>
         match ZMap.find alloc_id st.(allocations) with
         | Some v => ret v
         | None =>
             fail (MerrOutsideLifetime
                     (String.append "CHERI.get_allocation, alloc_id="
                        (of_Z alloc_id)))
         end
      ).

  (* PNVI-ae-udi *)
  Definition lookup_iota iota :=
    get >>= fun st =>
        match ZMap.find iota st.(iota_map) with
        | Some v => ret v
        | None => raise (InternalErr "lookup_iota failed")
        end.

  (* PNVI-ae-udi *)
  Definition resolve_iota precond iota :=
    lookup_iota iota >>=
      (fun x => match x with
                | inl alloc_id =>
                    (precond alloc_id >>= merr2memM alloc_id)
                | inr (alloc_id1, alloc_id2) =>
                    precond alloc_id1 >>=
                      fun x => match x with
                               | OK =>
                                   ret alloc_id1
                               | FAIL _ =>
                                   precond alloc_id2 >>= merr2memM alloc_id2
                               end
                end)
      >>=
      fun alloc_id =>
        update (fun st =>

                  {|
                    next_alloc_id    := st.(next_alloc_id);
                    next_iota        := st.(next_iota);
                    last_address     := st.(last_address) ;
                    allocations      := st.(allocations);
                    iota_map         := ZMap.add iota (inl alloc_id) st.(iota_map);
                    funptrmap        := st.(funptrmap);
                    varargs          := st.(varargs);
                    next_varargs_id  := st.(next_varargs_id);
                    bytemap          := st.(bytemap);
                    captags          := st.(captags);
                    dead_allocations := st.(dead_allocations);
                    dynamic_addrs    := st.(dynamic_addrs);
                    last_used        := st.(last_used);
                  |}) ;; ret alloc_id.

  (* zap (make unspecified) any pointer in the memory with provenance matching a
     given allocation id *)
  Definition zap_pointers {A:Type} (_:storage_instance_id) : memM A  := raise (InternalErr "zap_pointers is not supported").

  Definition kill
    (loc : location_ocaml)
    (is_dyn : bool)
    (function_parameter : pointer_value)
    : memM unit
    :=
    match function_parameter with
    | PV _ (PVfunction _) =>
        fail (MerrOther "attempted to kill with a function pointer")
    | PV Prov_none (PVconcrete _) =>
        fail (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV Prov_device (PVconcrete _) => ret tt
    | PV (Prov_symbolic iota) (PVconcrete addr) =>
        if andb
             (cap_is_null addr)
             (Switches.has_switch Switches.SW_forbid_nullptr_free)
        then
          fail (MerrFreeNullPtr loc)
        else
          let precondition (z : storage_instance_id) :=
            is_dead z >>=
              (fun x => match x with
                        | true =>
                            ret
                              (FAIL (MerrUndefinedFree loc Free_static_allocation))
                        | false =>
                            get_allocation z >>=
                              (fun alloc =>
                                 if
                                   MorelloAddr.eqb
                                     (C.cap_get_value addr)
                                     alloc.(base)
                                 then
                                   ret OK
                                 else
                                   ret
                                     (FAIL(MerrUndefinedFree loc Free_out_of_bound)))
                        end)
          in
          (if is_dyn then
             (is_dynamic (C.cap_get_value addr)) >>=
               (fun (b : bool) =>
                  if b then ret tt
                  else fail (MerrUndefinedFree loc Free_static_allocation))
           else
             ret tt) ;;
          resolve_iota precondition iota >>=
            (fun alloc_id =>
               update (fun st =>
                         {|
                           next_alloc_id    := st.(next_alloc_id);
                           next_iota        := st.(next_iota);
                           last_address     := st.(last_address) ;
                           allocations      := ZMap.remove alloc_id st.(allocations);
                           iota_map         := st.(iota_map);
                           funptrmap        := st.(funptrmap);
                           varargs          := st.(varargs);
                           next_varargs_id  := st.(next_varargs_id);
                           bytemap          := st.(bytemap);
                           captags          := st.(captags);
                           dead_allocations := alloc_id :: st.(dead_allocations);
                           dynamic_addrs    := st.(dynamic_addrs);
                           last_used        := Some alloc_id;
                         |})
               ;;
               if Switches.has_switch SW_zap_dead_pointers then
                 zap_pointers alloc_id
               else
                 ret tt)
    | PV (Prov_some alloc_id) (PVconcrete addr) =>
        (if andb
              (cap_is_null addr)
              (Switches.has_switch Switches.SW_forbid_nullptr_free)
         then
           fail (MerrFreeNullPtr loc)
         else
           if is_dyn then
             (* this kill is dynamic one (i.e. free() or friends) *)
             is_dynamic (C.cap_get_value addr) >>=
               fun x => match x with
                        | false =>
                            fail (MerrUndefinedFree loc (Free_static_allocation))
                        | true => ret tt
                        end
           else
             ret tt)
        ;;
        is_dead alloc_id >>=
          fun x => match x with
                   | true =>
                       if is_dyn then
                         fail (MerrUndefinedFree loc Free_dead_allocation)
                       else
                         raise (InternalErr "Concrete: FREE was called on a dead allocation")
                   | false =>
                       get_allocation alloc_id >>= fun alloc =>
                           if MorelloAddr.eqb (C.cap_get_value addr) alloc.(base) then
                             update
                               (fun st =>
                                  {|
                                    next_alloc_id    := st.(next_alloc_id);
                                    next_iota        := st.(next_iota);
                                    last_address     := st.(last_address) ;
                                    allocations      := ZMap.remove alloc_id st.(allocations);
                                    iota_map         := st.(iota_map);
                                    funptrmap        := st.(funptrmap);
                                    varargs          := st.(varargs);
                                    next_varargs_id  := st.(next_varargs_id);
                                    bytemap          := st.(bytemap);
                                    captags          := st.(captags);
                                    dead_allocations := alloc_id :: st.(dead_allocations);
                                    dynamic_addrs    := st.(dynamic_addrs);
                                    last_used        := Some alloc_id;
                                  |}) ;;
                             if Switches.has_switch SW_zap_dead_pointers then
                               zap_pointers alloc_id
                             else
                               ret tt
                           else
                             fail (MerrUndefinedFree loc Free_out_of_bound)
                   end
    end.

  Definition is_pointer_algined (p : Z) : bool :=
    let a := IMP.get.(alignof_pointer) in
    let m := Z.rem p a in
    Z.eqb m 0.

  (* Convinience function to be used in breaking let to avoid match *)
  Definition break_PV (p:pointer_value) :=
    match p with
    | PV prov ptrval => (prov,ptrval)
    end.

  (** Helper function to split a list at given position.
      List.split_at in Lem.
   *)
  Definition split_at {A:Type} (n:nat) (l:list A)
    := (List.firstn n l, List.skipn n l).

  Inductive overlap_ind :=
  | NoAlloc: overlap_ind
  | SingleAlloc: storage_instance_id -> overlap_ind
  | DoubleAlloc: storage_instance_id -> storage_instance_id -> overlap_ind.

  Inductive prov_ptr_valid_ind :=
  | NotValidPtrProv
  | ValidPtrProv.

  Inductive prov_valid_ind :=
  | VALID: provenance -> prov_valid_ind
  | INVALID: prov_valid_ind.

  Inductive bytes_ind :=
  | PtrBytes: Z -> bytes_ind
  | OtherBytes: bytes_ind.

  Definition split_bytes (function_parameter : list AbsByte)
    : serr (provenance * prov_ptr_valid_ind * list (option byte))
    :=
    match function_parameter with
    | [] => raise "CHERI.AbsByte.split_bytes: called on an empty list"
    | bs =>
        '(_prov, rev_values, offset_status) <-
          monadic_fold_left
            (fun '(prov_acc, val_acc, offset_acc) b_value =>
               prov_acc' <-
                 match
                   ((prov_acc, b_value.(prov)),
                     match (prov_acc, b_value.(prov)) with
                     | (VALID (Prov_some alloc_id1), Prov_some alloc_id2) =>
                         Z.eqb alloc_id1 alloc_id2
                     | _ => false
                     end,
                     match (prov_acc, b_value.(prov)) with
                     | (VALID (Prov_symbolic iota1), Prov_symbolic iota2) =>
                         Z.eqb iota1 iota2
                     | _ => false
                     end) with
                 |
                   ((VALID (Prov_some alloc_id1), Prov_some alloc_id2), true, _)
                   => ret INVALID
                 |
                   ((VALID (Prov_symbolic iota1), Prov_symbolic iota2), _, true)
                   => ret INVALID
                 | ((VALID (Prov_symbolic iota1), Prov_some alloc_id'), _, _)
                   => raise "TODO(iota) split_bytes 1"
                 | ((VALID (Prov_some alloc_id), Prov_symbolic iota), _, _) =>
                     raise "TODO(iota) split_bytes 2"
                 | ((VALID Prov_none, (Prov_some _) as new_prov), _, _) =>
                     ret (VALID new_prov)
                 | ((VALID Prov_none, (Prov_symbolic _) as new_prov), _, _) =>
                     ret (VALID new_prov)
                 | ((prev_acc, _), _, _) => ret prev_acc
                 end ;;
               let offset_acc' :=
                 match
                   ((offset_acc, b_value.(copy_offset)),
                     match (offset_acc, b_value.(copy_offset)) with
                     | (PtrBytes n1, Some n2) => Z.eqb n1 (Z.of_nat n2)
                     | _ => false
                     end) with
                 | ((PtrBytes n1, Some n2), true) => PtrBytes (Z.add n1 1)
                 | (_, _) => OtherBytes
                 end in
               ret (prov_acc', (cons b_value.(value) val_acc), offset_acc'))
            bs ((VALID Prov_none), nil, (PtrBytes 0)) ;;
        ret (match _prov with
             | INVALID => Prov_none
             | VALID z_value => z_value
             end,
            match offset_status with
            | OtherBytes => NotValidPtrProv
            | _ => ValidPtrProv
            end, (List.rev rev_values))
    end.

  Definition provs_of_bytes (bs : list AbsByte) : taint_ind :=
    let xs :=
      List.fold_left
        (fun (acc : list storage_instance_id) =>
         fun (b_value : AbsByte) =>
           match b_value.(prov) with
           | Prov_none => acc
           | Prov_some alloc_id => cons alloc_id acc
           | Prov_symbolic iota => acc
           | Prov_device => acc
           end) bs nil in
    match xs with
    | [] => NoTaint
    | _ => NewTaint xs
    end.

  Definition extract_unspec {A : Set} (xs : list (option A))
    : option (list A) :=
    List.fold_left
      (fun (acc_opt : option (list A)) =>
       fun (c_opt : option A) =>
         match (acc_opt, c_opt) with
         | (None, _) => None
         | (_, None) => None
         | (Some acc, Some c_value) => Some (cons c_value acc)
         end) (List.rev xs) (Some nil) .

  (** Convert an arbitrary integer value to unsinged cap value *)
  Definition wrap_cap_value (n_value : Z) : Z :=
    if andb (Z.leb n_value C.min_vaddr) (Z.leb n_value C.max_vaddr)
    then n_value
    else  wrapI C.min_vaddr C.max_vaddr n_value.

  Definition Z_of_bytes: bool (* is signed *) -> list byte -> Z. Proof. Admitted. (* TODO *)
  Definition float_of_bits: Z -> float. Proof. Admitted. (* TODO *)

  Fixpoint abst
    (fuel: nat)
    (loc : location_ocaml)
    (find_overlaping : Z -> overlap_ind)
    (funptrmap : ZMap.t (digest * string * C.t))
    (tag_query_f : Z -> option bool)
    (addr : Z)
    (cty : Ctype.ctype)
    (bs : list AbsByte)
    : serr (taint_ind * mem_value_with_err * list AbsByte)
    :=
    match fuel with
    | O => raise "abst out of fuel"
    | S fuel =>
        let '(Ctype.Ctype _ ty) := cty in
        let self f := abst f loc find_overlaping funptrmap tag_query_f in
        sz <- sizeof DEFAULT_FUEL None cty ;;
        sassert (negb (Nat.ltb (List.length bs) (Z.to_nat sz))) "abst, |bs| < sizeof(ty)" ;;
        let merge_taint (x_value : taint_ind) (y_value : taint_ind) : taint_ind :=
          match (x_value, y_value) with
          | (NoTaint, NoTaint) => NoTaint
          | ((NoTaint, NewTaint xs) | (NewTaint xs, NoTaint)) => NewTaint xs
          | (NewTaint xs, NewTaint ys) => NewTaint (List.app xs ys)
          end in
        match ty with
        | (Ctype.Void | Ctype.Array _ None |
            Ctype.Function _ _ _ |
            Ctype.FunctionNoParams _) =>
            raise "abst on function!"
        | (Ctype.Basic (Ctype.Integer ((Ctype.Signed Ctype.Intptr_t) as ity))
          | Ctype.Basic (Ctype.Integer ((Ctype.Unsigned Ctype.Intptr_t) as ity)))
          =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, _, bs1') <- split_bytes bs1 ;;
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            let iss1:bool := iss in (* hack to hint type checker *)
            ret ((provs_of_bytes bs1),
                match extract_unspec bs1' with
                | Some cs =>
                    match tag_query_f addr with
                    | None => MVEunspecified cty
                    | Some tag =>
                        match C.decode (Z_of_bytes false cs) tag with
                        | None => MVErr (MerrCHERI loc CheriErrDecodingCap)
                        | Some c_value =>
                            if iss then
                              let n_value := C.cap_get_value c_value in
                              let c_value := C.cap_set_value c_value (wrap_cap_value n_value) in
                              MVEinteger ity (IC true c_value)
                            else
                              MVEinteger ity (IC false c_value)
                        end
                    end
                | None => MVEunspecified cty
                end, bs2)
        | Ctype.Basic (Ctype.Floating fty) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(_, _, bs1') <- split_bytes bs1 ;;
            ret (NoTaint,
                match extract_unspec bs1' with
                | Some cs => MVEfloating fty (float_of_bits (Z_of_bytes true cs))
                | None => MVEunspecified cty
                end, bs2)
        | Ctype.Basic (Ctype.Integer ity) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, _, bs1') <- split_bytes bs1 ;;
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            ret (provs_of_bytes bs1,
                match extract_unspec bs1' with
                | Some cs => MVEinteger ity (IV (Z_of_bytes iss cs))
                | None => MVEunspecified cty
                end, bs2)
        | Ctype.Array elem_ty (Some n_value) =>
            let fix aux (fuel:nat) (n_value : Z) par (cs : list AbsByte)
              : serr (taint_ind *  mem_value_with_err * list AbsByte)
              :=
              match fuel with
              | O => raise "abst.aux out of fuel"
              | S fuel =>
                  let '(taint_acc, mval_acc) := par in
                  if Z.leb n_value 0 then
                    ret (taint_acc, (MVEarray (List.rev mval_acc)), cs)
                  else
                    sz <- sizeof DEFAULT_FUEL None elem_ty ;;
                    let el_addr := Z.add addr (Z.mul (Z.sub n_value 1) sz) in
                    '(taint, mval, cs') <- self fuel el_addr elem_ty cs ;;
                    aux fuel (Z.sub n_value 1)
                      ((merge_taint taint taint_acc), (cons mval mval_acc)) cs'
              end
            in
            aux fuel n_value (NoTaint, nil) bs
        | Ctype.Pointer _ ref_ty =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, prov_status, bs1') <- split_bytes bs1 ;;
            ret (NoTaint,
                match extract_unspec bs1' with
                | Some cs =>
                    match tag_query_f addr with
                    | None => MVEunspecified cty
                    | Some tag =>
                        match C.decode (Z_of_bytes false cs) tag with
                        | None => MVErr (MerrCHERI loc CheriErrDecodingCap)
                        | Some n_value =>
                            match ref_ty with
                            | Ctype.Ctype _ (Ctype.Function _ _ _) =>
                                match tag_query_f addr with
                                | None => MVEunspecified cty
                                | Some tag =>
                                    match C.decode (Z_of_bytes false cs) tag with
                                    | None => MVErr (MerrCHERI loc CheriErrDecodingCap)
                                    | Some c_value =>
                                        let n_value :=
                                          Z.sub
                                            (C.cap_get_value c_value)
                                            initial_address in
                                        match ZMap.find n_value funptrmap with
                                        | Some (file_dig, name, c') =>
                                            if C.eqb c_value c' then
                                              MVEpointer ref_ty
                                                (PV prov
                                                   (PVfunction
                                                      (FP_valid
                                                         (Symbol.Symbol file_dig
                                                            n_value
                                                            (Symbol.SD_Id name)))))
                                            else
                                              MVEpointer ref_ty
                                                (PV prov (PVfunction (FP_invalid c_value)))
                                        | None =>
                                            MVEpointer ref_ty
                                              (PV prov (PVfunction (FP_invalid c_value)))
                                        end
                                    end
                                end
                            | _ =>
                                let prov :=
                                  match prov_status with
                                  | NotValidPtrProv =>
                                      match
                                        find_overlaping
                                          (C.cap_get_value n_value) with
                                      | NoAlloc => Prov_none
                                      | SingleAlloc alloc_id => Prov_some alloc_id
                                      | DoubleAlloc alloc_id1 alloc_id2 =>
                                          Prov_some alloc_id1
                                      end
                                  | ValidPtrProv => prov
                                  end in
                                MVEpointer ref_ty (PV prov (PVconcrete n_value))
                            end
                        end
                    end
                | None => MVEunspecified (Ctype.Ctype nil (Ctype.Pointer Ctype.no_qualifiers ref_ty))
                end, bs2)
        | Ctype.Atomic atom_ty =>
            self fuel addr atom_ty bs
        | Ctype.Struct tag_sym =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            '(offsets,_) <- offsetsof DEFAULT_FUEL (Tags.tagDefs tt) tag_sym ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(taint, rev_xs, _, bs') <-
              monadic_fold_left
                (fun '(taint_acc, acc_xs, previous_offset, acc_bs) '(memb_ident, memb_ty, memb_offset) =>
                   let pad := Z.sub memb_offset previous_offset in
                   let memb_addr :=
                     Z.add addr memb_offset in
                   '(taint, mval, acc_bs') <-
                     self fuel memb_addr memb_ty (List.skipn (Z.to_nat pad) acc_bs) ;;
                   sz <- sizeof DEFAULT_FUEL None memb_ty ;;
                   ret ((merge_taint taint taint_acc),
                       (cons (memb_ident, memb_ty, mval) acc_xs),
                       (Z.add memb_offset sz), acc_bs'))
                offsets
                (NoTaint, nil, 0, bs1)
            ;;
            ret (taint, (MVEstruct tag_sym (List.rev rev_xs)), bs2)
        | Ctype.Union tag_sym =>
            raise "TODO: abst, Union (as value)"
        end
    end.

  (** Checks if memory region starting from [addr] and
      of size [sz] fits withing interval \[b1,b2) *)
  Definition cap_bounds_check (bounds : Z * Z)
    : Z -> Z -> bool
    :=
    let '(base, limit) := bounds in
    fun (addr : Z) (sz : Z) =>
        andb (Z.leb base addr) (Z.leb (Z.add addr sz) limit).

  Definition cap_check
    (loc : location_ocaml)
    (c : C.t)
    (offset : Z)
    (intent : access_intention)
    (sz : Z)
    : memM unit :=
    if C.cap_is_valid c then
      let addr :=
        Z.add (C.cap_get_value c)
          offset in
      let pcheck :=
        match intent with
        | ReadIntent =>
            MorelloPermission.perm_is_load
        | WriteIntent =>
            MorelloPermission.perm_is_store
        | CallIntent =>
            MorelloPermission.perm_is_execute
        end in
      if pcheck (C.cap_get_perms c) then
        let bounds := C.cap_get_bounds c in
        if cap_bounds_check bounds addr sz then
          ret tt
        else
          fail
            (MerrCHERI loc
               (CheriBoundsErr (bounds, addr, (Z.to_nat sz))))
      else
        fail
          (MerrCHERI loc
             CheriMerrUnsufficientPermissions)
    else
      fail
        (MerrCHERI loc
           CheriMerrInvalidCap).

  Fixpoint mem_value_strip_err
    (x_value : mem_value_with_err)
    : memM mem_value
    :=
    match x_value with
    | MVEunspecified x_value => ret (MVunspecified x_value)
    | MVEinteger x_value y_value => ret (MVinteger x_value y_value)
    | MVEfloating x_value y_value => ret (MVfloating x_value y_value)
    | MVEpointer x_value y_value => ret (MVpointer x_value y_value)
    | MVEarray l_value =>
        mapT mem_value_strip_err l_value >>=
          (fun (x_value : list mem_value) => ret (MVarray x_value))
    | MVEstruct x_value y_value =>
        mapT
          (fun '(x_value, y_value, z_value) =>
             (mem_value_strip_err z_value) >>=
               (fun (z' : mem_value) => ret (x_value, y_value, z')))
          y_value
          >>=
          (fun y' =>ret (MVstruct x_value y'))
    | MVEunion x_value y_value z_value =>
        mem_value_strip_err z_value >>=
          (fun (z' : mem_value) => ret (MVunion x_value y_value z'))
    | MVErr err => fail err
    end.

  Definition fetch_bytes
    (bytemap : ZMap.t AbsByte)
    (base_addr : Z)
    (n_bytes : Z) : list AbsByte
    :=
    List.map
      (fun (addr : Z.t) =>
         match ZMap.find addr bytemap with
         | Some b_value => b_value
         | None => absbyte_v Prov_none None None
         end)
      (list_init (Z.to_nat n_bytes)
         (fun (i : nat) =>
            let offset := Z.of_nat i in
            Z.add base_addr offset)).

  Definition find_overlaping st addr : overlap_ind
    :=
    let (require_exposed, allow_one_past) :=
      match Switches.has_switch_pred (fun x => match x with SW_PNVI _ => true | _ => false end) with
      | Some (Switches.SW_PNVI variant) =>
          match variant with
          | PLAIN => (false, false)
          | AE => (true, false)
          | AE_UDI => (true, true)
          end
      | Some _ => (false, false) (* impossible case *)
      | None => (false, false)
      end
    in
    ZMap.fold (fun alloc_id alloc acc =>
                 let new_opt :=
                   if negb (mem alloc_id st.(dead_allocations))
                      && Z.leb alloc.(base) addr && Z.ltb addr (Z.add alloc.(base) alloc.(size)) then
                     (* PNVI-ae, PNVI-ae-udi *)
                     if require_exposed && (negb (allocation_taint_eqb alloc.(taint) Exposed))
                     then None
                     else Some alloc_id
                   else if allow_one_past then
                          (* PNVI-ae-udi *)
                          if Z.eqb addr (Z.add alloc.(base) alloc.(size))
                             && negb require_exposed && (negb (allocation_taint_eqb alloc.(taint) Exposed))
                          then Some alloc_id
                          else None
                        else None
                 in
                 match acc, new_opt with
                 | _, None => acc
                 | NoAlloc, Some alloc_id => SingleAlloc alloc_id
                 | SingleAlloc alloc_id1, Some alloc_id2 => DoubleAlloc alloc_id1 alloc_id2
                 | DoubleAlloc _ _, Some _ => acc
                 end
      ) st.(allocations) NoAlloc.


  (* TODO: see if could be generalized and moved to Utils.v.  *)
  (** [update key f m] returns a map containing the same bindings as
  [m], except for the binding of [key]. Depending on the value of [y]
  where [y] is [f (find_opt key m)], the binding of [key] is added,
  removed or updated. If [y] is [None], the binding is removed if it
  exists; otherwise, if [y] is [Some z] then key is associated to [z]
  in the resulting map. If [key] was already bound in [m] to a value
  that is physically equal to [z], [m] is returned unchanged (the
  result of the function is then physically equal to [m]). *)
  Definition zmap_update {A:Type}: Z -> (option A -> option A) -> (ZMap.t A) -> (ZMap.t A). Proof. admit. Admitted. (* TODO: implement *)

  Definition expose_allocation (alloc_id : Z)
    : memM unit :=
    update (fun (st: mem_state) =>
              mem_state_with_allocations
                (zmap_update alloc_id
                   (fun (function_parameter : option allocation) =>
                      match function_parameter with
                      | Some alloc => Some
                                       {|
                                         prefix := alloc.(prefix);
                                         base := alloc.(base);
                                         size := alloc.(size);
                                         ty := alloc.(ty);
                                         is_readonly := alloc.(is_readonly);
                                         taint := Exposed
                                       |}
                      | None => None
                      end) st.(allocations)) st).

  Definition expose_allocations (t: taint_ind): memM unit
    := match t with
       | NoTaint => ret tt
       | NewTaint xs =>
           update
             (fun st =>
                mem_state_with_allocations
                  (List.fold_left
                     (fun acc alloc_id =>
                        zmap_update alloc_id
                          (fun x =>
                             match x with
                             | Some alloc => Some
                                              {|
                                                prefix := alloc.(prefix);
                                                base := alloc.(base);
                                                size := alloc.(size);
                                                ty := alloc.(ty);
                                                is_readonly := alloc.(is_readonly);
                                                taint := Exposed
                                              |}
                             | None => None
                             end) acc)
                     xs st.(allocations))
                  st)
       end.

  Definition is_within_bound
    (alloc_id : Z.t)
    (lvalue_ty : Ctype.ctype)
    (addr : Z) : memM bool
    :=
    sz <- serr2memM (sizeof DEFAULT_FUEL None lvalue_ty) ;;
    get_allocation alloc_id >>=
      (fun (alloc : allocation) =>
         ret
           (andb
              (Z.leb alloc.(base) addr)
              (Z.leb
                 (Z.add addr sz)
                 (Z.add alloc.(base) alloc.(size))))).

  Definition device_ranges : list (MorelloAddr.t * MorelloAddr.t) :=
    [ (0x40000000, 0x40000004)
      ; (0xABC, 0XAC0) ].

  Definition is_within_device (ty : Ctype.ctype) (addr : Z) : memM bool
    :=
    sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
    ret
      (List.existsb
         (fun '(min, max) =>
            andb
              (Z.leb min addr)
              (Z.leb (Z.add addr sz) max))
         device_ranges).


  Definition is_atomic_member_access
    (alloc_id : Z.t)
    (lvalue_ty : Ctype.ctype)
    (addr : Z.t)
    : memM bool
    :=
    sz <- sizeof DEFAULT_FUEL None lvalue_ty ;;
    get_allocation alloc_id >>=
      (fun (alloc : allocation) =>
        match
          (alloc.(ty),
            match alloc.(ty) with
            | Some ty => is_atomic ty
            | _ => false
            end) with
        | (Some ty, true) =>
          if
            andb (equiv_decb addr alloc.(base))
              (andb
                (Z.equal sz  alloc.(size))
                (Ctype.ctypeEqual lvalue_ty ty))
          then
            ret false
          else
            ret true
        | (_, _) => ret false
        end).

  Definition load
    (loc: location_ocaml)
    (ty: Ctype.ctype)
    (p:pointer_value): memM (footprint * mem_value)
    :=
    let '(prov, ptrval_) := break_PV p in
    let do_load
          (alloc_id_opt : option storage_instance_id)
          (addr : Z)
          (sz : Z)
      : memM (footprint * mem_value)
      :=
      get >>=
        (fun (st : mem_state) =>
           let bs := fetch_bytes st.(bytemap) addr sz in
           let tag_query (a_value : Z) : option bool :=
             if is_pointer_algined a_value then
               ZMap.find a_value st.(captags)
             else
               raise (InternalErr
                        "An attempt to load capability from not properly aligned addres")
           in
           '(taint, mval, bs') <-
             serr2memM (abst loc (find_overlaping st) st.(funptrmap) tag_query addr ty bs)
           ;;
           mem_value_strip_err mval >>=
             (fun (mval : mem_value) =>
                (if orb
                      (Switches.has_switch (Switches.SW_PNVI AE))
                      (Switches.has_switch (Switches.SW_PNVI AE_UDI))
                 then expose_allocations taint
                 else ret tt) ;;
                (update (fun (st : mem_state) =>
                           mem_state_with_last_used alloc_id_opt st))
                ;;
                (let fp := FP addr (Z.of_int (sizeof None ty)) in
                 match bs' with
                 | [] =>
                     if Switches.has_switch Switches.SW_strict_reads
                     then
                       match mval with
                       | MVunspecified _ =>
                           fail (MerrReadUninit loc)
                       | _ => ret (fp, mval)
                       end
                     else
                       ret (fp, mval)
                 | _ =>
                     fail (MerrWIP "load, bs' <> []")
                 end)))
    in
    let do_load_cap
          (alloc_id_opt : option storage_instance_id)
          (c : C.t)
          (sz : Z)
      : memM (footprint * mem_value)
      :=
      cap_check loc c Z.zero ReadIntent sz ;;
      do_load alloc_id_opt  (C.cap_get_value c) sz
    in
    match (prov, ptrval_) with
    | (_, PVfunction _) =>
        fail (MerrAccess loc LoadAccess FunctionPtr)
    | (Prov_none, _) =>
        fail (MerrAccess loc LoadAccess OutOfBoundPtr)
    | (Prov_device, PVconcrete c) =>
        if cap_is_null c then
          fail (MerrAccess loc LoadAccess NullPtr)
        else
          is_within_device ty (C.cap_get_value c) >>=
            (fun (function_parameter : bool) =>
               match function_parameter with
               | false =>
                   fail
                     (MerrAccess loc
                        LoadAccess
                        OutOfBoundPtr)
               | true => do_load_cap None c (sizeof None ty)
               end)
    | (Prov_symbolic iota, PVconcrete addr) =>
        if cap_is_null addr then
          fail
            (MerrAccess loc
               LoadAccess
               NullPtr)
        else
          let precondition (z_value : storage_instance_id)
            : Eff.eff (* `FAIL *) Mem_cheri.mem_error
                Mem_cheri.mem_error
                (Mem_cheri.mem_constraint integer_value)
                mem_state :=
            is_dead z_value >>=
              (fun (function_parameter : bool) =>
                 match function_parameter with
                 | true =>
                     ret
                       (FAIL
                          (MerrAccess loc
                             LoadAccess
                             DeadPtr))
                 | false =>
                       is_within_bound z_value ty (C.cap_get_value addr) >>=
                       (fun (function_parameter : bool) =>
                          match function_parameter with
                          | false =>
                              ret
                                (FAIL
                                   (MerrAccess loc
                                      LoadAccess
                                      OutOfBoundPtr))
                          | true =>
                              is_atomic_member_access z_value ty
                                   (C.cap_get_value addr) >>=
                                (fun (function_parameter : bool) =>
                                   match function_parameter with
                                   | true =>
                                       ret
                                         (FAIL
                                            (MerrAccess loc
                                               LoadAccess
                                               AtomicMemberof))
                                   | false => ret OK
                                   end)
                          end)
                 end) in
          Eff.op_gtgteq (resolve_iota precondition iota)
            (fun (alloc_id : storage_instance_id) =>
               do_load_cap (Some alloc_id) addr (sizeof None ty))
    | (Prov_some alloc_id, PVconcrete addr) =>
        if cap_is_null addr then
          fail
            (MerrAccess loc
               LoadAccess
               NullPtr)
        else
          Eff.op_gtgt
            (Eff.op_gtgteq (is_dead alloc_id)
               (fun (function_parameter : bool) =>
                  match function_parameter with
                  | true =>
                      fail
                        (MerrAccess loc
                           LoadAccess
                           DeadPtr)
                  | false => ret tt
                  end))
            (Eff.op_gtgteq
               (is_within_bound alloc_id ty
                  (C.cap_get_value addr))
               (fun (function_parameter : bool) =>
                  match function_parameter with
                  | false =>
                      let '_ :=
                        Debug_ocaml.print_debug 1 nil
                          (fun (function_parameter : unit) =>
                             let '_ := function_parameter in
                             String.append "LOAD out of bound, alloc_id="
                               (Z.to_string alloc_id)) in
                      fail
                        (MerrAccess loc
                           LoadAccess
                           OutOfBoundPtr)
                  | true =>
                      Eff.op_gtgteq
                        (is_atomic_member_access alloc_id ty
                           (C.cap_get_value addr))
                        (fun (function_parameter : bool) =>
                           match function_parameter with
                           | true =>
                               fail
                                 (MerrAccess loc
                                    LoadAccess
                                    AtomicMemberof)
                           | false =>
                               do_load_cap (Some alloc_id) addr (sizeof None ty)
                           end)
                  end))
    end.



End CheriMemory.
