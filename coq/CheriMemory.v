Require Import Coq.Arith.PeanoNat.
From Coq.Lists Require Import List ListSet.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
From Coq.Strings Require Import String Ascii HexString.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Require Coq.Program.Wf.
Require Recdef.
Require Import Lia.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

Require Import SimpleError Capabilities Addr Memory_model Mem_common ErrorWithState Undefined Morello ErrorWithState Location Symbol Implementation Tags Utils Switches AilTypesAux.

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
    list (Symbol.identifier * Ctype.ctype * mem_value_ind) -> mem_value_ind
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

  (*
     For copy-paste:

    {|
      prefix      := a.(prefix)      ;
      base        := a.(base)        ;
      size        := a.(size)        ;
      ty          := a.(ty)          ;
      is_readonly := a.(is_readonly) ;
      taint       := a.(taint)       ;
    |}

   *)

  Definition allocation_with_prefix prefix (r : allocation) :=
    Build_allocation prefix r.(base) r.(size) r.(ty) r.(is_readonly) r.(taint).

  Record AbsByte :=
    {
      prov : provenance;
      copy_offset : option nat;
      value : option ascii
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

  Definition mem_state_with_allocations allocations (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) allocations r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

  Definition mem_state_with_last_used last_used (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) last_used.

  Definition mem_state_with_iota_map iota_map (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) iota_map r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

  Definition mem_state_with_next_iota next_iota (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) next_iota r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

  Definition mem_state_with_captags captags (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) captags r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

  Definition mem_state_with_funptrmap funptrmap (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) funptrmap r.(varargs) r.(next_varargs_id) r.(bytemap) r.(captags) r.(dead_allocations) r.(dynamic_addrs) r.(last_used).

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

  Definition serr2memM {A: Type} (e:serr A): (memM A)
    := match e with
       | inr v => ret v
       | inl msg => raise (InternalErr msg)
       end.

  Definition option2memM {A: Type} (msg:string) (o:option A): (memM A)
    := match o with
       | Some v => ret v
       | None => raise (InternalErr msg)
       end.

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
  | FP: MorelloAddr.t -> Z -> footprint_ind.

  Definition footprint := footprint_ind.

  Definition check_overlap a b :=
    match a,b with
    |  FP b1 sz1, FP b2 sz2 =>
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

  Definition wrapI min_v max_v n :=
    let dlt := Z.succ (Z.sub max_v min_v) in
    let r := Z_integerRem_f n dlt in
    if Z.leb r max_v then r
    else Z.sub r dlt.

  Definition unwrap_cap_value n :=
    let vaddr_bits := (Z.of_nat C.sizeof_vaddr) * 8 in
    let min_v := Z.opp (Z.pow 2 (vaddr_bits - 1)) in
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

  (* size is in bytes *)
  Definition bytes_of_Z (is_signed: bool) (size: nat) (i: Z): serr (list ascii)
    :=
    let nbits := Z.mul 8 (Z.of_nat size) in
    let '(min, max) :=
      if is_signed then
        ((Z.opp (Z.pow 2 (Z.sub nbits 1))),
          (Z.sub (Z.pow 2 (Z.sub nbits 1)) 1))
      else
        (0,
          (Z.sub (Z.pow 2 nbits)
             (1))) in
    if
      (negb (Z.leb min i && Z.leb i max)) || (Z.gtb nbits 128)
    then
      raise "bytes_of_Z failure"
    else
      ret (list_init size
             (fun n => byte_of_Z (extract_num i (Z.mul 8 (Z.of_nat n)) 8))).

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
            let bs := List.map (fun (x : ascii) => absbyte_v Prov_none None (Some x)) bs' in
            ret (funptrmap, (clear_caps addr (Z.of_nat (List.length bs)) captags), bs)
        | MVinteger ity (IC _ c_value) =>
            let '(cb, ct) := C.encode true c_value in
            cb'  <- bytes_of_Z false (*TODO: not sure about sign *)
                      (Z.to_nat (IMP.get.(sizeof_pointer)))
                      cb ;;
            ret (funptrmap, (ZMap.add addr ct captags),
                (mapi
                   (fun (i_value : nat) (b_value : ascii) =>
                      absbyte_v Prov_none None (Some b_value)) cb'))
        | MVfloating fty fval =>
            sz <- sizeof DEFAULT_FUEL None (Ctype.Ctype nil (Ctype.Basic (Ctype.Floating fty))) ;;
            bs' <- bytes_of_Z true (Z.to_nat sz) (bits_of_float fval) ;;
            let bs := List.map (fun (x : ascii) => absbyte_v Prov_none None (Some x)) bs'
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
                       (fun (i_value : nat) (b_value : ascii) =>
                          absbyte_v prov (Some i_value) (Some b_value)) cb'))
            | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
                let '(cb, ct) := C.encode true c_value in
                cb'  <- bytes_of_Z false (*TODO: not sure about sign *)
                          (Z.to_nat (IMP.get.(sizeof_pointer)))
                          cb ;;
                ret (funptrmap, (ZMap.add addr ct captags),
                    (mapi
                       (fun (i_value : nat) (b_value : ascii) =>
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
    let align_n' := Z.max align_n (Z.add (Z.succ (0)) (MorelloAddr.bitwise_complement mask)) in

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
    (ptr : pointer_value)
    : memM unit
    :=
    match ptr with
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
    : serr (provenance * prov_ptr_valid_ind * list (option ascii))
    :=
    match function_parameter with
    | [] => raise "CHERI.AbsByte.split_bytes: called on an empty list"
    | bs =>
        '(_prov, rev_values, offset_status) <-
          monadic_fold_left
            (fun '(prov_acc, val_acc, offset_acc) b_value =>
               prov_acc' <-
                 match
                   (prov_acc, b_value.(prov)),
                     match (prov_acc, b_value.(prov)) with
                     | (VALID (Prov_some alloc_id1), Prov_some alloc_id2) =>
                         Z.eqb alloc_id1 alloc_id2
                     | _ => false
                     end,
                     match (prov_acc, b_value.(prov)) with
                     | (VALID (Prov_symbolic iota1), Prov_symbolic iota2) =>
                         Z.eqb iota1 iota2
                     | _ => false
                     end with
                 | (VALID (Prov_some alloc_id1), Prov_some alloc_id2), true, _
                   => ret INVALID
                 | (VALID (Prov_symbolic iota1), Prov_symbolic iota2), _, true
                   => ret INVALID
                 | (VALID (Prov_symbolic iota1), Prov_some alloc_id'), _, _
                   => raise "TODO(iota) split_bytes 1"
                 | (VALID (Prov_some alloc_id), Prov_symbolic iota), _, _ =>
                     raise "TODO(iota) split_bytes 2"
                 | (VALID Prov_none, (Prov_some _) as new_prov), _, _ =>
                     ret (VALID new_prov)
                 | (VALID Prov_none, (Prov_symbolic _) as new_prov), _, _ =>
                     ret (VALID new_prov)
                 | (prev_acc, _), _, _ => ret prev_acc
                 end ;;
               let offset_acc' :=
                 match
                   (offset_acc, b_value.(copy_offset)),
                     match (offset_acc, b_value.(copy_offset)) with
                     | (PtrBytes n1, Some n2) => Z.eqb n1 (Z.of_nat n2)
                     | _ => false
                     end with
                 | (PtrBytes n1, Some n2), true => PtrBytes (Z.add n1 1)
                 | _, _ => OtherBytes
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
            let _:bool := iss in (* hack to hint type checker *)
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
  in the resulting map. *)
  Definition zmap_update
    {A:Type}
    (key: Z)
    (f: option A -> option A)
    (m: ZMap.t A)
    : (ZMap.t A)
    :=
    let y := f (ZMap.find key m) in
    let m' := ZMap.remove key m in (* could be optimized, as removal may be unecessary in some cases *)
    match y with
    | None => m'
    | Some z => ZMap.add key z m'
    end.

  Definition expose_allocation (alloc_id : Z)
    : memM unit :=
    update (fun (st: mem_state) =>
              mem_state_with_allocations
                (zmap_update alloc_id
                   (fun (x : option allocation) =>
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
    sz <- serr2memM (sizeof DEFAULT_FUEL None lvalue_ty) ;;
    get_allocation alloc_id >>=
      (fun (alloc : allocation) =>
         match
           alloc.(ty),
           match alloc.(ty) with
           | Some ty => is_atomic ty
           | _ => false
           end
         with
         | Some ty, true =>
             e <- serr2memM (Ctype.ctypeEqual DEFAULT_FUEL lvalue_ty ty) ;;
             ret
               (negb
                  (Z.eqb addr alloc.(base) && (Z.eqb sz alloc.(size) && e)))
         | _, _ => ret false
         end).

  Definition load
    (loc: location_ocaml)
    (ty: Ctype.ctype)
    (p:pointer_value)
    :
    memM (footprint * mem_value)
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
               (* An attempt to load a capability from not properly
                  aligned address. OCaml handles this with [failwith]
                  but here we just return [None], and [abst] using
                  this function will fail with [MVEunspecified]. But
                  the question what error to raise is moot since this
                  is an internal error which should never happen, and
                  hopefully we will prove so. *)
               None
           in
           '(taint, mval, bs') <-
             serr2memM (abst DEFAULT_FUEL loc (find_overlaping st) st.(funptrmap) tag_query addr ty bs)
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
                sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
                let fp := FP addr sz in
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
                end))
    in
    let do_load_cap
          (alloc_id_opt : option storage_instance_id)
          (c : C.t)
          (sz : Z)
      : memM (footprint * mem_value)
      :=
      cap_check loc c 0 ReadIntent sz ;;
      do_load alloc_id_opt  (C.cap_get_value c) sz
    in
    match prov, ptrval_ with
    | _, PVfunction _ =>
        fail (MerrAccess loc LoadAccess FunctionPtr)
    | Prov_none, _ =>
        fail (MerrAccess loc LoadAccess OutOfBoundPtr)
    | Prov_device, PVconcrete c =>
        if cap_is_null c then
          fail (MerrAccess loc LoadAccess NullPtr)
        else
          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
          is_within_device ty (C.cap_get_value c) >>=
            (fun (function_parameter : bool) =>
               match function_parameter with
               | false =>
                   fail (MerrAccess loc LoadAccess OutOfBoundPtr)
               | true =>
                   do_load_cap None c sz
               end)
    | Prov_symbolic iota, PVconcrete addr =>
        if cap_is_null addr then
          fail
            (MerrAccess loc
               LoadAccess
               NullPtr)
        else
          let precondition (z_value : storage_instance_id) : memM merr
            :=
            is_dead z_value >>=
              (fun (function_parameter : bool) =>
                 if function_parameter
                 then ret (FAIL (MerrAccess loc LoadAccess DeadPtr))
                 else
                   is_within_bound z_value ty (C.cap_get_value addr) >>=
                     (fun (function_parameter : bool) =>
                        match function_parameter with
                        | false =>
                            ret (FAIL (MerrAccess loc LoadAccess OutOfBoundPtr))
                        | true =>
                            is_atomic_member_access z_value ty
                              (C.cap_get_value addr) >>=
                              (fun (function_parameter : bool) =>
                                 match function_parameter with
                                 | true =>
                                     ret (FAIL (MerrAccess loc LoadAccess AtomicMemberof))
                                 | false => ret OK
                                 end)
                        end))
          in
          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
          resolve_iota precondition iota >>=
            (fun (alloc_id : storage_instance_id) =>
               do_load_cap (Some alloc_id) addr sz)
    | Prov_some alloc_id, PVconcrete addr =>
        if cap_is_null addr then
          fail (MerrAccess loc LoadAccess NullPtr)
        else
          (is_dead alloc_id) >>=
            (fun (function_parameter : bool) =>
               match function_parameter with
               | true =>
                   fail (MerrAccess loc LoadAccess DeadPtr)
               | false => ret tt
               end)
          ;;
          is_within_bound alloc_id ty
            (C.cap_get_value addr) >>=
            (fun (function_parameter : bool) =>
               match function_parameter with
               | false =>
                   fail (MerrAccess loc LoadAccess OutOfBoundPtr)
               | true =>
                   is_atomic_member_access alloc_id ty
                     (C.cap_get_value addr) >>=
                     (fun (function_parameter : bool) =>
                        match function_parameter with
                        | true =>
                            fail (MerrAccess loc LoadAccess AtomicMemberof)
                        | false =>
                            sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
                            do_load_cap (Some alloc_id) addr sz
                        end)
               end)
    end.

  Fixpoint typeof (mval : mem_value)
    : serr Ctype.ctype :=
    ct <-
      match mval with
      | MVunspecified (Ctype.Ctype _ ty) => ret ty
      | MVinteger ity _ =>
          ret (Ctype.Basic (Ctype.Integer ity))
      | MVfloating fty _ =>
          ret (Ctype.Basic (Ctype.Floating fty))
      | MVpointer ref_ty _ =>
          ret (Ctype.Pointer Ctype.no_qualifiers ref_ty)
      | MVarray [] =>
          raise "ill-formed value"
      | MVarray ((cons mval _) as mvals) =>
          mt <- typeof mval ;;
          ret (Ctype.Array mt (Some (Z.of_nat (List.length mvals))))
      | MVstruct tag_sym _ => ret (Ctype.Struct tag_sym)
      | MVunion tag_sym _ _ => ret (Ctype.Union tag_sym)
      end ;;
    ret (Ctype.Ctype [] ct).

  Definition store
    (loc : location_ocaml)
    (cty : Ctype.ctype)
    (is_locking : bool)
    (ptr : pointer_value)
    (mval : mem_value)
    : memM  footprint
    :=
    let '(prov,ptrval_) := break_PV ptr in

    cond <- serr2memM (
               mt <- typeof mval ;;
               Ctype.ctypeEqual DEFAULT_FUEL (Ctype.unatomic cty)
                 (Ctype.unatomic mt))
    ;;
    if negb cond
    then fail (MerrOther "store with an ill-typed memory value")
    else
      let do_store_cap
            (alloc_id_opt : option storage_instance_id)
            (c_value : C.t)
        : memM footprint
        :=
        nsz <- serr2memM (sizeof DEFAULT_FUEL None cty) ;;
        cap_check loc c_value 0 WriteIntent nsz ;;
        let addr := C.cap_get_value c_value in
        st <- get ;;
        '(funptrmap, captags, pre_bs) <-
          serr2memM (repr DEFAULT_FUEL st.(funptrmap) st.(captags) addr mval)
        ;;
        let bs :=
          mapi (fun (i_value: nat) (b_value: AbsByte)
                => ((Z.add addr (Z.of_nat i_value)), b_value)) pre_bs
        in
        let bytemap := (List.fold_left
                          (fun (acc : ZMap.t AbsByte) =>
                           fun (function_parameter : Z * AbsByte) =>
                             let '(addr, b_value) := function_parameter in
                             ZMap.add addr b_value acc)
                          bs st.(bytemap)) in

        put {|
            next_alloc_id    := st.(next_alloc_id);
            next_iota        := st.(next_iota);
            last_address     := st.(last_address) ;
            allocations      := st.(allocations);
            iota_map         := st.(iota_map);
            funptrmap        := funptrmap;
            varargs          := st.(varargs);
            next_varargs_id  := st.(next_varargs_id);
            bytemap          := bytemap;
            captags          := captags;
            dead_allocations := st.(dead_allocations);
            dynamic_addrs    := st.(dynamic_addrs);
            last_used        := alloc_id_opt;
          |}
        ;;
        ret (FP addr nsz)
      in
      match prov, ptrval_ with
      | _, PVfunction _ =>
          fail
            (MerrAccess loc
               StoreAccess
               FunctionPtr)
      | Prov_none, _ =>
          fail
            (MerrAccess loc
               StoreAccess
               OutOfBoundPtr)
      | Prov_device, PVconcrete addr =>
          if cap_is_null addr then
            fail
              (MerrAccess loc
                 StoreAccess
                 NullPtr)
          else
            is_within_device cty (C.cap_get_value addr) >>=
              (fun (x : bool) =>
                 if x
                 then do_store_cap None addr
                 else fail (MerrAccess loc StoreAccess OutOfBoundPtr))
      | Prov_symbolic iota, PVconcrete addr =>
          if cap_is_null addr then
            fail
              (MerrAccess loc
                 StoreAccess
                 NullPtr)
          else
            let precondition (z_value : Z) : memM merr
              :=
              is_within_bound z_value cty (C.cap_get_value addr) >>=
                (fun (x : bool) =>
                   match x with
                   | false =>
                       ret (FAIL (MerrAccess loc StoreAccess OutOfBoundPtr))
                   | true =>
                       get_allocation z_value >>=
                         (fun (alloc : allocation) =>
                            match alloc.(is_readonly) with
                            | IsReadOnly =>
                                ret
                                  (FAIL
                                     (MerrWriteOnReadOnly
                                        false loc))
                            | IsReadOnly_string_literal =>
                                ret
                                  (FAIL
                                     (MerrWriteOnReadOnly true
                                        loc))
                            | IsWritable =>
                                is_atomic_member_access z_value cty
                                  (C.cap_get_value addr)
                                  >>=
                                  (fun (x : bool) =>
                                     if x
                                     then ret
                                            (FAIL (MerrAccess loc
                                                     LoadAccess
                                                     AtomicMemberof))
                                     else ret OK)
                            end)
                   end)
            in
            resolve_iota precondition iota >>=
              (fun (alloc_id : storage_instance_id) =>
                 do_store_cap (Some alloc_id) addr >>=
                   (fun (fp : footprint) =>
                      (if is_locking then
                         update
                           (fun (st : mem_state) =>
                              mem_state_with_allocations
                                (zmap_update alloc_id
                                   (fun (x : option allocation) =>
                                      match x with
                                      | Some a =>
                                          Some
                                            {|
                                              prefix      := a.(prefix)      ;
                                              base        := a.(base)        ;
                                              size        := a.(size)        ;
                                              ty          := a.(ty)          ;
                                              is_readonly := IsReadOnly ;
                                              taint       := a.(taint)       ;
                                            |}
                                      | None => None
                                      end) st.(allocations))
                                st)
                       else
                         ret tt)
                      ;;
                      ret fp))
      | Prov_some alloc_id, PVconcrete addr
        =>
          if cap_is_null addr then
            fail (MerrAccess loc StoreAccess NullPtr)
          else
            is_within_bound alloc_id cty (C.cap_get_value addr)
              >>=
              (fun (x : bool) =>
                 match x with
                 | false =>
                     fail (MerrAccess loc StoreAccess OutOfBoundPtr)
                 | true
                   =>
                     get_allocation alloc_id >>=
                       (fun (alloc : allocation) =>
                          match alloc.(is_readonly) with
                          | IsReadOnly =>
                              fail (MerrWriteOnReadOnly false  loc)
                          | IsReadOnly_string_literal =>
                              fail (MerrWriteOnReadOnly true loc)
                          | IsWritable =>
                              is_atomic_member_access alloc_id cty
                                (C.cap_get_value addr) >>=
                                (fun (x : bool) =>
                                   match x with
                                   | true =>
                                       fail
                                         (MerrAccess loc LoadAccess AtomicMemberof)
                                   | false =>
                                       do_store_cap (Some alloc_id) addr >>=
                                         (fun (fp : footprint) =>
                                            if is_locking then
                                              update
                                                (fun (st : mem_state) =>
                                                   mem_state_with_allocations
                                                     (zmap_update
                                                        alloc_id
                                                        (fun (x:option allocation) =>
                                                           match x with
                                                           | Some a =>
                                                               Some {|
                                                                   prefix      := a.(prefix)      ;
                                                                   base        := a.(base)        ;
                                                                   size        := a.(size)        ;
                                                                   ty          := a.(ty)          ;
                                                                   is_readonly := IsReadOnly ;
                                                                   taint       := a.(taint)       ;
                                                                 |}
                                                           | None => None
                                                           end) st.(allocations))
                                                     st)
                                              ;;
                                              ret fp
                                            else
                                              ret fp)
                                   end)
                          end)
                 end)
      end.

  Definition null_ptrval (_:Ctype.ctype) : pointer_value
    :=
    PV Prov_none (PVconcrete (C.cap_c0 tt)).

  Definition fun_ptrval (sym : Symbol.sym)
    : serr pointer_value :=
    ret (PV Prov_none (PVfunction (FP_valid sym))).

  Definition concrete_ptrval : Z -> Z -> serr pointer_value :=
    fun _ _ =>
      raise
      "concrete_ptrval: integer to pointer cast is not supported".

  Definition case_ptrval
    {A: Set}
    (pv : pointer_value)
    (fnull : unit -> A)
    (ffun : option Symbol.sym -> A)
    (fconc : unit -> A)
    (funspecified : unit -> A) : serr A
    :=
    match pv with
    | PV _ (PVfunction (FP_valid sym)) => ret (ffun (Some sym))
    | PV _ (PVfunction (FP_invalid c_value)) =>
        if cap_is_null c_value then
          ret (fnull tt)
        else
          ret (ffun None)
    | PV Prov_none (PVconcrete c_value) =>
        if cap_is_null c_value then
          ret (fconc tt)
        else
          ret (ffun None)
    | PV (Prov_some i_value) (PVconcrete c_value) =>
        if cap_is_null c_value then
          ret (fconc tt)
        else
          ret (ffun None)
    | _ => raise "case_ptrval"
    end.

  Definition case_funsym_opt
    (st : mem_state)
    (ptr : pointer_value)
    : option Symbol.sym
    :=
    let '(_, ptrval) := break_PV ptr in
    match ptrval with
    | PVfunction (FP_valid sym) => Some sym
    | PVfunction (FP_invalid c_value)
    | PVconcrete c_value =>
        let n_value :=
          Z.sub (C.cap_get_value c_value) initial_address in
        match ZMap.find n_value st.(funptrmap) with
        | Some (file_dig, name, _) =>
            Some
              (Symbol.Symbol file_dig n_value
                 (Symbol.SD_Id name))
        | None => None
        end
    end.

  Definition eq_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVfunction (FP_valid sym1), PVfunction (FP_valid sym2) =>
        ret (Symbol.symbolEquality sym1 sym2)
    | PVfunction (FP_invalid c1), PVfunction (FP_invalid c2) =>
        ret (Z.eqb (C.cap_get_value c1) (C.cap_get_value c2))
    | PVfunction (FP_valid sym), PVfunction (FP_invalid c_value)
    | PVfunction (FP_invalid c_value), PVfunction (FP_valid sym) =>
       get >>=
         (fun (st : mem_state) =>
            let n_value :=
              Z.sub (C.cap_get_value c_value) initial_address
            in
            match ZMap.find n_value st.(funptrmap) with
            | Some (file_dig, name, _) =>
                let sym2 := Symbol.Symbol file_dig n_value (Symbol.SD_Id name) in
                ret (Symbol.symbolEquality sym sym2)
            | None =>
                raise (InternalErr
                         "CHERI.eq_ptrval ==> FP_valid failed to resolve function symbol")
            end)
    | PVfunction _, _
    | _, PVfunction _ =>
        ret false
    | PVconcrete c1, PVconcrete c2 =>
        ret (Z.eqb (C.cap_get_value c1) (C.cap_get_value c2))
    end.

  Definition ne_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    eq_ptrval ptr1 ptr2 >>= (fun (x : bool) => ret (negb x)).

  Definition lt_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if orb (cap_is_null addr1) (cap_is_null addr2) then
          fail (MerrWIP "lt_ptrval ==> one null pointer")
        else if Switches.has_switch Switches.SW_strict_pointer_relationals then
               match
                 prov1, prov2,
                 (match prov1, prov2 with
                  | Prov_some alloc1, Prov_some alloc2 =>
                      Z.eqb alloc1 alloc2
                  | _, _ => false
                  end) with
               | Prov_some alloc1, Prov_some alloc2, true =>
                   ret (match C.value_compare addr1 addr2 with
                        | Lt => true
                        | _ => false
                        end)
               | _, _, _ => fail MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Lt => true
                    | _ => false
                    end)
    | _, _ => fail (MerrWIP "lt_ptrval")
    end.

  Definition gt_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if orb (cap_is_null addr1) (cap_is_null addr2) then
          fail (MerrWIP "gt_ptrval ==> one null pointer")
        else if Switches.has_switch Switches.SW_strict_pointer_relationals then
               match
                 prov1, prov2,
                 (match prov1, prov2 with
                  | Prov_some alloc1, Prov_some alloc2 =>
                      Z.eqb alloc1 alloc2
                  | _, _ => false
                  end) with
               | Prov_some alloc1, Prov_some alloc2, true =>
                   ret (match C.value_compare addr1 addr2 with
                        | Gt => true
                        | _ => false
                        end)
               | _, _, _ => fail MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Gt => true
                    | _ => false
                    end)
    | _, _ => fail (MerrWIP "gt_ptrval")
    end.

  Definition le_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if orb (cap_is_null addr1) (cap_is_null addr2) then
          fail (MerrWIP "le_ptrval ==> one null pointer")
        else if Switches.has_switch Switches.SW_strict_pointer_relationals then
               match
                 prov1, prov2,
                 (match prov1, prov2 with
                  | Prov_some alloc1, Prov_some alloc2 =>
                      Z.eqb alloc1 alloc2
                  | _, _ => false
                  end) with
               | Prov_some alloc1, Prov_some alloc2, true =>
                   ret (match C.value_compare addr1 addr2 with
                        | Lt => true
                        | Eq => true
                        | _ => false
                        end)
               | _, _, _ => fail MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Lt => true
                    | Eq => true
                    | _ => false
                    end)
    | _, _ => fail (MerrWIP "le_ptrval")
    end.

  Definition ge_ptrval
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if orb (cap_is_null addr1) (cap_is_null addr2) then
          fail (MerrWIP "ge_ptrval ==> one null pointer")
        else if Switches.has_switch Switches.SW_strict_pointer_relationals then
               match
                 prov1, prov2,
                 (match prov1, prov2 with
                  | Prov_some alloc1, Prov_some alloc2 =>
                      Z.eqb alloc1 alloc2
                  | _, _ => false
                  end) with
               | Prov_some alloc1, Prov_some alloc2, true =>
                   ret (match C.value_compare addr1 addr2 with
                        | Gt => true
                        | Eq => true
                        | _ => false
                        end)
               | _, _, _ => fail MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Gt => true
                    | Eq => true
                    | _ => false
                    end)
    | _, _ => fail (MerrWIP "ge_ptrval")
    end.

  Definition diff_ptrval
    (diff_ty : Ctype.ctype) (ptrval1 ptrval2 : pointer_value)
    : memM integer_value
    :=
    let precond (alloc: allocation) (addr1 addr2: Z): bool
      :=
      Z.leb alloc.(base) addr1 &&
        Z.leb addr1 (Z.add alloc.(base) alloc.(size)) &&
        Z.leb alloc.(base) addr2 &&
        Z.leb addr2 (Z.add alloc.(base) alloc.(size))
    in
    let valid_postcond  (addr1 addr2: Z) : memM integer_value :=
      let diff_ty' :=
        match diff_ty with
        | Ctype.Ctype _ (Ctype.Array elem_ty _) => elem_ty
        | _ => diff_ty
        end in
      sz <- serr2memM (sizeof DEFAULT_FUEL None diff_ty') ;;
      ret (IV (Z.div (Z.sub addr1 addr2) sz))
    in
    let error_postcond := fail MerrPtrdiff
    in

    if Switches.has_switch (Switches.SW_pointer_arith PERMISSIVE)
    then
      match ptrval1, ptrval2 with
      | PV _ (PVconcrete addr1), PV _ (PVconcrete addr2) =>
          valid_postcond (C.cap_get_value addr1)(C.cap_get_value addr2)
      | _, _=> error_postcond
      end
    else
      match ptrval1, ptrval2 with
      | PV (Prov_some alloc_id1) (PVconcrete addr1),
        PV (Prov_some alloc_id2) (PVconcrete addr2) =>
          if Z.eqb alloc_id1 alloc_id2 then
            get_allocation alloc_id1 >>=
              (fun (alloc : allocation) =>
                 if precond alloc (C.cap_get_value addr1) (C.cap_get_value addr2)
                 then
                   valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
                 else
                   error_postcond)
          else
            error_postcond
      | PV (Prov_symbolic iota) (PVconcrete addr1),
        PV (Prov_some alloc_id') (PVconcrete addr2)
      | PV (Prov_some alloc_id') (PVconcrete addr1),
        PV (Prov_symbolic iota) (PVconcrete addr2) =>
          lookup_iota iota >>=
            (fun x =>
               match x with
               | inl alloc_id =>
                   if Z.eqb alloc_id alloc_id' then
                     get_allocation alloc_id >>=
                       (fun (alloc : allocation) =>
                          if
                            precond alloc
                              (C.cap_get_value addr1)
                              (C.cap_get_value addr2)
                          then
                            valid_postcond
                              (C.cap_get_value addr1)
                              (C.cap_get_value addr2)
                          else
                            error_postcond)
                   else
                     error_postcond
               | inr (alloc_id1, alloc_id2) =>
                   if orb (Z.eqb alloc_id1 alloc_id') (Z.eqb alloc_id2 alloc_id')
                   then
                     get_allocation alloc_id' >>=
                       (fun (alloc : allocation) =>
                          if precond alloc
                               (C.cap_get_value addr1)
                               (C.cap_get_value addr2)
                          then
                            (update
                               (fun (st : mem_state) =>
                                  mem_state_with_iota_map
                                    (ZMap.add iota (inl alloc_id')
                                       st.(iota_map)) st))
                            ;;
                            (valid_postcond
                               (C.cap_get_value addr1)
                               (C.cap_get_value addr2))
                          else
                            error_postcond)
                   else
                     error_postcond
               end)
      | PV (Prov_symbolic iota1) (PVconcrete addr1),
        PV (Prov_symbolic iota2) (PVconcrete addr2) =>
          lookup_iota iota1 >>=
            (fun ids1 =>
               lookup_iota iota2 >>=
                 (fun ids2 =>
                    let inter_ids :=
                      match ids1, ids2 with
                      | inl x_value, inl y_value =>
                          if Z.eqb x_value y_value
                          then SingleAlloc x_value
                          else NoAlloc
                      | inl x_value, inr (y_value, z_value)
                      | inr (y_value, z_value), inl x_value =>
                          if Z.eqb x_value y_value || Z.eqb x_value z_value
                          then SingleAlloc x_value
                          else NoAlloc
                      | inr (x1, x2), inr (y1, y2) =>
                          if Z.eqb x1 y1 then
                            if Z.eqb x2 y2
                            then DoubleAlloc x1 x2
                            else SingleAlloc x1
                          else
                            if Z.eqb x2 y2
                            then SingleAlloc x2
                            else NoAlloc
                      end in
                    match inter_ids with
                    | NoAlloc => error_postcond
                    | SingleAlloc alloc_id' =>
                        update
                          (fun (st : mem_state) =>
                             mem_state_with_iota_map
                               (ZMap.add iota1 (inl alloc_id')
                                  (ZMap.add iota2 (inl alloc_id')
                                     st.(iota_map))) st)
                        ;;
                        valid_postcond
                          (C.cap_get_value addr1)
                          (C.cap_get_value addr2)
                    | DoubleAlloc alloc_id1 alloc_id2 =>
                        match C.value_compare addr1 addr2 with
                        | Eq =>
                            valid_postcond
                              (C.cap_get_value addr1)
                              (C.cap_get_value addr2)
                        | _ =>
                            fail
                              (MerrOther
                                 "in `diff_ptrval` invariant of PNVI-ae-udi failed: ambiguous iotas with addr1 <> addr2")
                        end
                    end))
      | _,_ => error_postcond
      end.

  Definition update_prefix
    (x : Symbol.prefix * mem_value)
    : memM unit
    :=
    let '(pref, mval) := x in
    match mval with
    | MVpointer _ (PV (Prov_some alloc_id) _) =>
        let upd_alloc (x : option allocation) : option allocation :=
          match x with
          | Some alloc => Some (allocation_with_prefix pref alloc)
          | None => None
          end
        in
        update
          (fun (st : mem_state) =>
             mem_state_with_allocations (zmap_update alloc_id upd_alloc st.(allocations)) st)
    | _ =>
        ret tt
    end.

  Definition isWellAligned_ptrval
    (ref_ty:  Ctype.ctype) (ptrval : pointer_value)
    : memM bool
    :=
    match Ctype.unatomic_ ref_ty with
    | (Ctype.Void | Ctype.Function _ _ _) =>
        fail
          (MerrOther
             "called isWellAligned_ptrval on void or a function type")
    | _ =>
        match ptrval with
        | PV _ (PVfunction _) =>
            fail
              (MerrOther
                 "called isWellAligned_ptrval on function pointer")
        | PV _ (PVconcrete addr) =>
            sz <- serr2memM (alignof DEFAULT_FUEL None ref_ty) ;;
            ret (Z.eqb (Z.modulo (C.cap_get_value addr) sz) 0)
        end
    end.

  Definition validForDeref_ptrval
    (ref_ty: Ctype.ctype) (ptrval: pointer_value)
    : memM bool
    :=
    let do_test (alloc_id : storage_instance_id): memM bool
      :=
      is_dead alloc_id >>=
        (fun (x : bool) =>
           match x with
           | true => ret false
           | false => isWellAligned_ptrval ref_ty ptrval
           end)
    in
    match ptrval with
    | PV _ (PVfunction _) => ret false
    | (PV Prov_device (PVconcrete c_value)) as ptrval =>
        if cap_is_null c_value then
          ret false
        else
          isWellAligned_ptrval ref_ty ptrval
    | PV (Prov_symbolic iota) (PVconcrete c_value) =>
        if cap_is_null c_value then
          ret false
        else
          lookup_iota iota >>=
            (fun x =>
               match x with
               | inl alloc_id => do_test alloc_id
               | inr (alloc_id1, alloc_id2) =>
                   do_test alloc_id1 >>=
                     (fun (x : bool) =>
                        if x
                        then ret true
                        else do_test alloc_id2)
               end)
    | PV (Prov_some alloc_id) (PVconcrete c_value) =>
        if cap_is_null c_value
        then ret false
        else do_test alloc_id
    | PV Prov_none _ => ret false
    end.

  Definition add_iota
    (alloc_ids: storage_instance_id * storage_instance_id)
    : memM symbolic_storage_instance_id
    :=
    get >>=
      (fun (st : mem_state) =>
         let iota := st.(next_iota) in
         put
           (mem_state_with_iota_map
              (ZMap.add iota (inr alloc_ids) st.(iota_map))
              (mem_state_with_next_iota
                 (Z.succ st.(next_iota)) st)) ;;

        ret iota).

  Definition ptrfromint
    (loc : location_ocaml)
    (int_ty : Ctype.integerType)
    (ref_ty : Ctype.ctype)
    (int_v : integer_value) : memM pointer_value
    :=
    match int_ty, int_v with
    | Ctype.Unsigned Ctype.Intptr_t, IC _ c_value
    | Ctype.Signed Ctype.Intptr_t, IC _ c_value
      =>
        let addr := C.cap_get_value c_value in
        get >>=
          (fun (st : mem_state) =>
             match find_overlaping st addr with
             | NoAlloc => ret Prov_none
             | SingleAlloc alloc_id => ret (Prov_some alloc_id)
             | DoubleAlloc alloc_id1 alloc_id2 =>
                 add_iota (alloc_id1,alloc_id2) >>=
                   (fun (iota : symbolic_storage_instance_id) =>
                      ret (Prov_symbolic iota))
             end >>=
               (fun (prov : provenance) => ret (PV prov (PVconcrete c_value))))
    | Ctype.Unsigned Ctype.Intptr_t, IV _
    | Ctype.Signed Ctype.Intptr_t, IV _ =>
        raise (InternalErr "ptrfromint: invalid encoding for [u]intptr_t")
    | _, IV n_value =>
        if Z.eqb n_value 0
        then ret (PV Prov_none (PVconcrete (C.cap_c0 tt)))
        else
          let addr :=
            let dlt := Z.succ (Z.sub C.max_vaddr  C.min_vaddr) in
            let r_value := Z_integerRem_f n_value dlt in
            if  Z.leb r_value C.max_vaddr
            then r_value
            else Z.sub r_value dlt
          in
          get >>=
            (fun (st : mem_state) =>
               match find_overlaping st addr with
               | NoAlloc => ret Prov_none
               | SingleAlloc alloc_id => ret (Prov_some alloc_id)
               | DoubleAlloc alloc_id1 alloc_id2 =>
                   add_iota (alloc_id1, alloc_id2) >>=
                     (fun (iota : symbolic_storage_instance_id) =>
                        ret (Prov_symbolic iota))
               end >>=
                 (fun (prov : provenance) =>
                    let c_value :=
                      C.cap_set_value
                        (C.cap_c0 tt) addr in
                    ret (PV prov (PVconcrete c_value))))
    | _, IC _ _ =>
        raise (InternalErr
                 "invalid integer value (capability for non- [u]intptr_t")
    end.

  Definition internal_intcast
    (loc : location_ocaml)
    (ity2 : Ctype.integerType)
    (ival : integer_value)
    : serr (sum mem_error integer_value)
    :=
    nbytes <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity2) ;;
    let '(min_ity2, max_ity2) :=
      let nbits := Z.mul 8 nbytes in
      let is_signed := is_signed_ity DEFAULT_FUEL ity2 in
      if is_signed then
        ((Z.opp
            (Z.pow 2 (Z.sub nbits 1))),
          (Z.sub
             (Z.pow 2 (Z.sub nbits 1))
             (1)))
      else
        (0, (Z.sub (Z.pow 2 nbits)(1))) in
    let conv_int_to_ity2 (n_value : Z) : Z :=
      match ity2 with
      | Ctype.Bool =>
          if Z.eqb n_value 0 then
            0
          else
            1
      | _ =>
          if
            andb (Z.leb n_value min_ity2)
              (Z.leb n_value max_ity2)
          then
            n_value
          else
            wrapI min_ity2 max_ity2 n_value
      end in
    match ival, ity2 with
    | IC false _, Ctype.Unsigned Ctype.Intptr_t
    | IC true _, Ctype.Signed Ctype.Intptr_t =>
        ret (inr ival)
    | IC (false as is_signed) cap, Ctype.Signed Ctype.Intptr_t
    | IC (true as is_signed) cap,  Ctype.Unsigned Ctype.Intptr_t =>
        ret (inr  (IC (negb is_signed) cap))
    | IC false cap, _ =>
        let n_value := C.cap_get_value cap in
        ret (inr (IV (conv_int_to_ity2 n_value)))
    | IC true cap, _ =>
        let n_value := C.cap_get_value cap in
        ret (inr (IV (conv_int_to_ity2 (unwrap_cap_value n_value))))
    | IV n_value, Ctype.Unsigned Ctype.Intptr_t
    | IV n_value, Ctype.Signed Ctype.Intptr_t =>
        if Z.eqb n_value 0 then
          ret (inr (IC false (C.cap_c0 tt)))
        else
          let n_value := wrap_cap_value n_value in
          let c_value := C.cap_c0 tt in
          ret (inr (IC false (C.cap_set_value c_value n_value)))
    | IV n_value, _ =>
        ret (inr (IV (conv_int_to_ity2 n_value)))
    end.

  Definition max_ival (ity: Ctype.integerType)
    : serr integer_value
    :=
    let signed_max (n_value : Z) : Z :=
      Z.sub (Z.pow 2 (Z.sub (Z.mul 8 n_value) 1)) 1 in
    let unsigned_max (n_value : Z) : Z :=
      Z.sub (Z.pow 2 (Z.mul 8 n_value)) 1 in
    match ity with
    | Ctype.Signed Ctype.Intptr_t =>
        ret (IV (signed_max (Z.of_nat C.sizeof_vaddr)))
    | Ctype.Unsigned Ctype.Intptr_t =>
        ret (IV (unsigned_max (Z.of_nat C.sizeof_vaddr)))
    | _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        match ity with
        | Ctype.Char =>
            if IMP.get.(Implementation.is_signed_ity) Ctype.Char
            then ret (IV (signed_max n_value))
            else ret (IV (unsigned_max n_value))
        | Ctype.Bool => ret (IV (unsigned_max n_value))
        | Ctype.Size_t
        | Ctype.Wchar_t
        | Ctype.Unsigned _ => ret (IV (unsigned_max n_value))
        | Ctype.Ptrdiff_t
        | Ctype.Wint_t
        | Ctype.Signed _ => ret (IV (signed_max n_value))
        | Ctype.Vaddr_t => ret (IV (unsigned_max n_value))
        | Ctype.Enum _ => ret (IV (signed_max 4))
        end
    end.

  Definition min_ival (ity: Ctype.integerType)
    : serr integer_value
    :=
    let signed_min (n_value: Z) : Z :=
      Z.opp (Z.pow 2 (Z.sub (Z.mul 8 n_value) 1)) in
    match ity with
    | Ctype.Char =>
        if IMP.get.(Implementation.is_signed_ity) Ctype.Char
        then ret (IV (signed_min 8))
        else ret (IV 0)
    | Ctype.Bool
    | Ctype.Size_t
    | Ctype.Wchar_t
    | Ctype.Wint_t
    | Ctype.Unsigned _ => ret (IV 0)
    | Ctype.Signed Ctype.Intptr_t =>
        ret (IV (signed_min (Z.of_nat C.sizeof_vaddr)))
    | Ctype.Ptrdiff_t
    | Ctype.Signed _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        ret (IV (signed_min n_value))
    | Ctype.Vaddr_t => ret (IV 0)
    | Ctype.Enum _ => ret (IV (signed_min 4))
    end.

  Definition intfromptr
    (loc : location_ocaml)
    (_ : Ctype.ctype)
    (ity: Ctype.integerType)
    (ptr: pointer_value)
    : memM integer_value
    :=
    let '(prov,ptrval_) := break_PV ptr in
    let wrap_intcast (ity2 : Ctype.integerType) (ival : integer_value)
      : memM integer_value
      :=
      icr <- serr2memM (internal_intcast loc ity2 ival) ;;
      match icr with
      | inl err => fail err
      | inr ival => ret ival
      end in
    match ptrval_ with
    |
      PVfunction
        (FP_valid ((Symbol.Symbol _ n_value _) as fp)) =>
        get >>=
          (fun (st : mem_state) =>
             match ity with
             |
               (Ctype.Signed Ctype.Intptr_t |
                 Ctype.Unsigned Ctype.Intptr_t) =>
                 match ZMap.find n_value st.(funptrmap) with
                 | Some (file_dig, name, c_value) =>
                     wrap_intcast ity (IC false c_value)
                 | None =>
                     raise (InternalErr "intfromptr: Unknown function")
                 end
             | _ =>
                 ret (IV (Z.add initial_address n_value))
             end)
    | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
        if cap_is_null c_value then
          match ity with
          | Ctype.Signed Ctype.Intptr_t =>
              ret (IC true (C.cap_c0 tt))
          | Ctype.Unsigned Ctype.Intptr_t =>
              ret (IC false (C.cap_c0 tt))
          | _ => ret (IV 0)
          end
        else
          (if Switches.has_switch (Switches.SW_PNVI AE) ||
                Switches.has_switch (Switches.SW_PNVI AE_UDI)
           then
             match prov with
             | Prov_some alloc_id => expose_allocation alloc_id
             | _ => ret tt
             end
           else
             ret tt)
          ;;
          match ity with
          |
            (Ctype.Signed Ctype.Intptr_t |
              Ctype.Unsigned Ctype.Intptr_t) =>
              wrap_intcast ity (IC false c_value)
          | _ =>
              maxival <- serr2memM (max_ival ity) ;;
              minival <- serr2memM (min_ival ity) ;;
              let ity_max := num_of_int maxival in
              let ity_min := num_of_int minival in
              let addr := C.cap_get_value c_value in
              if Z.ltb addr ity_min || Z.ltb ity_max addr
              then fail (MerrIntFromPtr loc)
              else ret (IV addr)
          end
    end.

  Definition derive_cap
    (is_signed : bool)
    (bop : derivecap_op)
    (ival1 ival2 : integer_value) : serr integer_value
    :=
    match bop with
    | DCunary _ =>
        match ival1 with
        | IC _ cap => ret (IC is_signed cap)
        | IV _ =>
            raise
              "derive_cap should not be used for unary operations on non capabilty-carrying types"
        end
    | DCbinary _ =>
        match ival1, ival2 with
        | IC _ cap, _
        | _, IC _ cap => ret (IC is_signed cap)
        | IV _, IV _ =>
            raise
              "derive_cap should not be used for binary operations on non capabilty-carrying types"
        end
    end.

  Definition cap_assign_value
    (loc:location_ocaml)
    (ival_cap: integer_value)
    (ival_n: integer_value): serr integer_value
    :=
    match ival_cap, ival_n with
    | IC is_signed c_value, IV n_value =>
        ret (IC is_signed (C.cap_set_value c_value n_value))
    | _, _ =>
        raise "Unexpected argument types for cap_assign_value"
    end.

  Definition ptr_t_int_value (ptr : integer_value)
    : serr integer_value :=
    match ptr with
    | IC _ _ as ival => ret (IV (num_of_int ival))
    | IV _ =>
        raise "Unexpected argument value in ptr_t_int_value"
    end.

  Definition null_cap (is_signed : bool) : integer_value :=
    IC is_signed (C.cap_c0 tt).

  Definition array_shift_ptrval: pointer_value -> Ctype.ctype -> integer_value ->
                                 serr pointer_value
    := fun _ _ _ => raise "pure array_shift_ptrval not used in CHERI".

  Definition member_shift_ptrval: pointer_value -> Symbol.sym ->
                                  Symbol.identifier -> serr pointer_value
    := fun _ _ _ => raise "members_shift_ptrval (pure) is not supported in CHERI".

  Inductive collapse_ind :=
  | NoCollapse: collapse_ind
  | Collapse: Z -> collapse_ind.

  Definition eff_array_shift_ptrval
    (loc : location_ocaml)
    (ptrval : pointer_value)
    (ty : Ctype.ctype)
    (ival_int : integer_value)
    : memM pointer_value
    :=
    let ival := num_of_int ival_int in
    sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
    let offset := Z.mul sz ival
    in
    match ptrval with
    | PV _ (PVfunction _) =>
        raise (InternalErr "CHERI.eff_array_shift_ptrval, PVfunction")
    | PV ((Prov_symbolic iota) as prov) (PVconcrete c_value) =>
        if cap_is_null c_value then
          raise (InternalErr
                   "TODO(shift a null pointer should be undefined behaviour)")
        else
          let shifted_addr :=
            Z.add (C.cap_get_value c_value)
              offset in
          let precond (z_value : Z.t) : memM bool :=
            if Switches.has_switch (Switches.SW_pointer_arith STRICT)
               || negb (Switches.has_switch (Switches.SW_pointer_arith PERMISSIVE))
            then
              get_allocation z_value >>=
                (fun (alloc : allocation) =>
                   ret (Z.leb alloc.(base) shifted_addr
                        && Z.leb
                             (Z.add shifted_addr sz)
                             (Z.add (Z.add alloc.(base) alloc.(size)) sz)))
            else
              ret true
          in
          lookup_iota iota >>=
            (fun x =>
               match x with
               | inr (alloc_id1, alloc_id2) =>
                   if negb (Z.eqb ival 0) then
                     (precond alloc_id1 >>=
                        (fun (x : bool) =>
                           match x with
                           | true =>
                               precond alloc_id2 >>=
                                 (fun (x : bool) =>
                                    match x with
                                    | true =>
                                        if Switches.has_switch (SW_pointer_arith PERMISSIVE)
                                        then ret NoCollapse
                                        else
                                          fail
                                            (MerrOther
                                               "(PNVI-ae-uid) ambiguous non-zero array shift")
                                    | false => ret (Collapse alloc_id1)
                                    end)
                           | false =>
                               precond alloc_id2 >>=
                                 (fun (function_parameter : bool) =>
                                    match function_parameter with
                                    | true => ret (Collapse alloc_id2)
                                    | false => fail (MerrArrayShift loc)
                                    end)
                           end) >>=
                        (fun x =>
                           match x with
                           | Collapse alloc_id =>
                               update
                                 (fun (st : mem_state) =>
                                    mem_state_with_iota_map
                                      (ZMap.add iota (inl alloc_id)
                                         st.(iota_map)) st)
                           | NoCollapse => ret tt
                           end))
                     ;;
                     let c_value := C.cap_set_value c_value shifted_addr in
                     ret (PV prov (PVconcrete c_value))
                   else
                     precond alloc_id1 >>=
                       (fun (function_parameter : bool) =>
                          match function_parameter with
                          | true => ret tt
                          | false =>
                              precond alloc_id2 >>=
                                (fun (x : bool) =>
                                   match x with
                                   | true => ret tt
                                   | false => fail (MerrArrayShift loc)
                                   end)
                          end)
                     ;;
                     let c_value := C.cap_set_value c_value shifted_addr in
                     ret (PV prov (PVconcrete c_value))
               | inl alloc_id =>
                   precond alloc_id >>=
                     (fun (function_parameter : bool) =>
                        match function_parameter with
                        | true =>
                            let c_value := C.cap_set_value c_value shifted_addr in
                            ret (PV prov (PVconcrete c_value))
                        | false => fail (MerrArrayShift loc)
                        end)
               end)
    | PV (Prov_some alloc_id) (PVconcrete c_value) =>
        let shifted_addr := Z.add (C.cap_get_value c_value) offset in
        if Switches.has_switch (Switches.SW_pointer_arith STRICT)
           || negb (Switches.has_switch (SW_pointer_arith PERMISSIVE))
        then
          get_allocation alloc_id >>=
            (fun (alloc : allocation) =>
               if Z.leb alloc.(base) shifted_addr
                  && Z.leb (Z.add shifted_addr sz)
                       (Z.add (Z.add alloc.(base) alloc.(size)) sz)
               then
                 let c_value := C.cap_set_value c_value shifted_addr in
                 ret (PV (Prov_some alloc_id) (PVconcrete c_value))
               else
                 fail (MerrArrayShift loc))
        else
          let c_value := C.cap_set_value c_value shifted_addr in
          ret (PV (Prov_some alloc_id) (PVconcrete c_value))
    | PV Prov_none (PVconcrete c_value) =>
        let shifted_addr := Z.add (C.cap_get_value c_value) offset in
        if Switches.has_switch (Switches.SW_pointer_arith STRICT)
           || negb (Switches.has_switch (Switches.SW_pointer_arith PERMISSIVE))
        then
          fail (MerrOther "out-of-bound pointer arithmetic (Prov_none)")
        else
          let c_value := C.cap_set_value c_value shifted_addr in
          ret (PV Prov_none (PVconcrete c_value))
    | PV Prov_device (PVconcrete c_value) =>
        let shifted_addr := Z.add (C.cap_get_value c_value) offset in
        let c_value := C.cap_set_value c_value shifted_addr in
        ret (PV Prov_device (PVconcrete c_value))
    end.

  Definition offsetof_ival
    (tagDefs: SymMap.t Ctype.tag_definition)
    (tag_sym : Symbol.sym)
    (memb_ident : Symbol.identifier) : serr integer_value
    :=
    '(xs, _) <- offsetsof DEFAULT_FUEL tagDefs tag_sym ;;
    let pred x : bool :=
      let '(ident, _, _) := x in
      ident_equal ident memb_ident in
    match List.find pred xs with
    | Some (_, _, offset) => ret (IV offset)
    | None =>
        raise "CHERI.offsetof_ival: invalid memb_ident"
    end.

  Definition eff_member_shift_ptrval
    (loc : location_ocaml)
    (ptr : pointer_value)
    (tag_sym: Symbol.sym)
    (memb_ident: Symbol.identifier):  memM pointer_value
    :=
    let '(prov,ptrval_) := break_PV ptr in
    ioff <- serr2memM (offsetof_ival (Tags.tagDefs tt) tag_sym memb_ident) ;;
    offset <-
      match ioff with
      | IV offset => ret (offset)
      | IC _ c_value =>
          raise (InternalErr
                   "CHERI.member_shift_ptrval invalid offset value type")
      end ;;
    match ptrval_ with
    | PVfunction _ =>
        raise (InternalErr "CHERI.member_shift_ptrval, PVfunction")
    | PVconcrete c_value =>
        if cap_is_null c_value then
          if Z.eqb 0 offset
          then ret (PV prov (PVconcrete (C.cap_c0 tt)))
          else raise (InternalErr "CHERI.member_shift_ptrval, shifting NULL")
        else
          let addr := C.cap_get_value c_value in
          let c_value := C.cap_set_value c_value (Z.add addr offset) in
          ret (PV prov (PVconcrete c_value))
    end.

  Definition memcpy
    (ptrval1 ptrval2: pointer_value)
    (size_int: integer_value)
    : memM pointer_value
    :=
    let cap_of_pointer_value (ptr: pointer_value) : serr Z :=
      match ptr with
      | PV _ (PVconcrete c_value)
      | PV _ (PVfunction (FP_invalid c_value)) =>
          ret (C.cap_get_value c_value)
      | _ => raise "memcpy: invalid pointer value"
      end in
    let size_n := num_of_int size_int in
    let loc := Loc_other "memcpy" in
    let fix copy_data (index: nat): memM pointer_value :=
      match index with
      | O => ret ptrval1
      | S index =>
          let i_value := Z.of_nat index in
          eff_array_shift_ptrval loc ptrval1 Ctype.unsigned_char (IV i_value) >>=
            (fun ptrval1' =>
               eff_array_shift_ptrval loc ptrval2 Ctype.unsigned_char (IV i_value) >>=
                 (fun ptrval2' =>
                    load loc Ctype.unsigned_char ptrval2' >>=
                      (fun '(_, mval) =>
                         store loc Ctype.unsigned_char false ptrval1' mval ;;
                         copy_data index)))
      end
    in
    let pointer_sizeof := IMP.get.(sizeof_pointer) in
    let npointer_sizeof := Z.to_nat pointer_sizeof in
    let fix copy_tags (index: nat): memM pointer_value :=
      let copy_tag (dst_p : pointer_value) (src_p : pointer_value)
        : memM unit :=
        dst_a <- serr2memM (cap_of_pointer_value dst_p) ;;
        src_a <- serr2memM (cap_of_pointer_value src_p) ;;
        update
          (fun (st : mem_state) =>
             match ZMap.find src_a st.(captags) with
             | None => st
             | Some t_value =>
                 if negb (is_pointer_algined dst_a)
                 then st
                 else mem_state_with_captags (ZMap.add dst_a t_value st.(captags)) st
             end)
      in
      match index with
      | O => ret ptrval1
      | S index =>
          let i_value := IV (Z.of_nat index) in
          eff_array_shift_ptrval loc ptrval1 Ctype.unsigned_char i_value >>=
            (fun ptrval1' =>
               eff_array_shift_ptrval loc ptrval2 Ctype.unsigned_char i_value >>=
                 (fun ptrval2' =>
                    copy_tag ptrval1' ptrval2' ;;

                    copy_tags (Nat.sub index npointer_sizeof)))
      end
    in
    copy_data (Z.to_nat size_n) ;;
    copy_tags (Z.to_nat (Z.mul (Z.quot size_n pointer_sizeof) pointer_sizeof)).

  Definition memcmp
    (ptrval1 ptrval2 : pointer_value)
    (size_int : integer_value)
    : memM integer_value
    :=
    let size_n := num_of_int size_int in
    let fix get_bytes
          (ptrval : pointer_value)
          (acc : list Z)
          (size : nat)
      : memM (list Z) :=
      match size with
      | O => ret (List.rev acc)
      | S size =>
          let loc := Loc_other "memcmp" in
          load loc Ctype.unsigned_char ptrval >>=
            (fun (x : footprint * mem_value) =>
               match x with
               | (_, MVinteger _ (IV byte_n)) =>
                   eff_array_shift_ptrval loc ptrval
                     Ctype.unsigned_char (IV 1) >>=
                     (fun (ptr' : pointer_value) =>
                        get_bytes ptr' (cons byte_n acc) size)
               | _ =>
                   raise (InternalErr "memcmp load unexpected result")
               end)
      end in
    get_bytes ptrval1 nil (Z.to_nat size_n) >>=
      (fun (bytes1: list Z) =>
         get_bytes ptrval2 nil (Z.to_nat size_n) >>=
           (fun (bytes2: list Z) =>
              ret (IV
                   (List.fold_left
                      (fun (acc : Z) '(n1, n2) =>
                         if Z.eqb acc 0 then
                           match Z.compare n1 n2 with
                           | Eq => 0
                           | Gt => 1
                           | Lt => -1
                           end
                         else
                           acc)
                      (List.combine bytes1 bytes2) 0)))).

  Definition realloc
    (tid : thread_id) (align : integer_value) (ptr : pointer_value)
    (size : integer_value) : memM pointer_value
    :=
    match ptr with
    | PV Prov_none (PVconcrete c_value) =>
        if cap_is_null c_value then
          allocate_region tid (Symbol.PrefOther "realloc") align size
        else
          fail (MerrWIP "realloc no provenance")
    | PV (Prov_some alloc_id) (PVconcrete c_value) =>
        let addr := C.cap_get_value c_value in
        is_dynamic addr >>=
          (fun (function_parameter : bool) =>
             match function_parameter with
             | false => fail MerrUndefinedRealloc
             | true =>
                 get_allocation alloc_id >>=
                   (fun (alloc : allocation) =>
                      if MorelloAddr.eqb alloc.(base) addr then
                        allocate_region tid (Symbol.PrefOther "realloc") align size >>=
                          (fun (new_ptr : pointer_value) =>
                             let size_to_copy :=
                               let size_n := num_of_int size in
                               IV (Z.min (CheriMemory.size alloc) size_n) in
                             memcpy new_ptr ptr size_to_copy ;;
                           kill (Loc_other "realloc") true ptr ;;
                           ret new_ptr)
                      else
                        fail
                          (MerrWIP "realloc: invalid pointer"))
             end)
    | PV _ _ =>
        fail (MerrWIP "realloc: invalid pointer")
    end.

  Definition copy_alloc_id
    (ival : integer_value) (ptrval : pointer_value)
    : memM pointer_value
    :=
    intfromptr Loc_unknown Ctype.void (Ctype.Unsigned Ctype.Intptr_t) ptrval ;;
    ptrfromint Loc_unknown (Ctype.Unsigned Ctype.Intptr_t) Ctype.void ival.

  Definition concurRead_ival: Ctype.integerType -> Symbol.sym -> serr (integer_value)
    := fun _ _ => raise "TODO: concurRead_ival".

  Definition integer_ival (z:Z): integer_value := IV z.

  Definition int_bin
    (vf : Z -> Z -> Z)
    (v1 v2 : integer_value) : integer_value :=
    let n1 := num_of_int v1 in
    let n2 := num_of_int v2 in
    IV (vf n1 n2).

  Definition op_ival
    (iop : integer_operator)
    (v1 v2 : integer_value) : integer_value
    :=
    match iop with
    | IntAdd => int_bin Z.add v1 v2
    | IntSub => int_bin Z.sub v1 v2
    | IntMul => int_bin Z.mul v1 v2
    | IntDiv => int_bin (fun n1 n2 =>
                          if Z.eqb n2 0
                          then 0
                          else Z_integerDiv_t n1 n2) v1 v2
    | IntRem_t => int_bin Z_integerRem_t v1 v2
    | IntRem_f => int_bin Z_integerRem_f v1 v2
    | IntExp => int_bin Z.pow v1 v2
    end.

  Definition sizeof_ival (ty : Ctype.ctype): serr integer_value
    :=
    sz <- sizeof DEFAULT_FUEL None ty ;;
    ret (IV sz).

  Definition alignof_ival (ty: Ctype.ctype): serr integer_value
    :=
    a <- alignof DEFAULT_FUEL None ty ;;
    ret (IV a).

  Definition bitwise_complement_ival
    (ty : Ctype.integerType)
    (v : integer_value) : integer_value
    :=
    IV (Z.sub (Z.opp (num_of_int v)) 1).

  Definition bitwise_and_ival (ty : Ctype.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.land.

  Definition bitwise_or_ival (ty : Ctype.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.lor.

  Definition bitwise_xor_ival (ty : Ctype.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.lxor.

  Definition case_integer_value
    {A : Set}
    (v : integer_value)
    (f : Z -> A)
    (_ : unit -> A) : A :=
    f (num_of_int v).

  Definition is_specified_ival (ival : integer_value) : bool := true.

  Definition eq_ival (_: option mem_state) (n1 n2: integer_value) :=
    Some (Z.eqb (num_of_int n1) (num_of_int n2)).

  Definition lt_ival (_: option mem_state) (n1 n2: integer_value) :=
    Some (Z.ltb (num_of_int n1) (num_of_int n2)).

  Definition le_ival (_: option mem_state) (n1 n2: integer_value) :=
    Some (Z.leb (num_of_int n1) (num_of_int n2)).

  Definition eval_integer_value (n_value : integer_value)
    : option Z := Some (num_of_int n_value).

  Definition zero_fval : float := PrimFloat.zero.

  Definition one_fval : float := PrimFloat.one.

  Definition str_fval (str : string) : serr floating_value :=
    raise "str_fval not implmented".

  Definition op_fval
    (fop : floating_operator)
    (fval1 fval2 : float) : float
    :=
    match fop with
    | FloatAdd => PrimFloat.add fval1 fval2
    | FloatSub => PrimFloat.sub fval1 fval2
    | FloatMul => PrimFloat.mul fval1 fval2
    | FloatDiv => PrimFloat.div fval1 fval2
    end.

  Definition eq_fval := PrimFloat.eqb.
  Definition lt_fval := PrimFloat.ltb.
  Definition le_fval := PrimFloat.leb.

  Definition fvfromint (iv:integer_value): serr (floating_value)
    := raise "fvfromint not implemented".

  Definition ivfromfloat
    (ity: Ctype.integerType)
    (fval: floating_value): serr integer_value
    :=
    match ity with
    | Ctype.Bool =>
        ret (IV (if eq_fval fval zero_fval then 0 else 1))
    | _ =>
        nbytes <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        let nbits := Z.mul 8 nbytes in
        is_signed <- option2serr "no is_signed_ity" (is_signed_ity DEFAULT_FUEL ity) ;;
        let _:bool := is_signed in (* hack to hint type checker *)
        let '(min, max) :=
          if is_signed then
            (Z.opp (Z.pow 2 (Z.sub nbits 1)), Z.sub (Z.pow 2 (Z.sub nbits 1)) 1)
          else
            (0, (Z.sub (Z.pow 2 nbits) 1)) in
        let wrapI (n_value : Z) : Z :=
          let dlt := Z.succ (Z.sub max min) in
          let r_value := Z_integerRem_f n_value dlt in
          if Z.leb r_value max then
            r_value
          else
            Z.sub r_value dlt in
        (* TODO ret (IV (wrapI (Z.of_int64 (Stdlib.Int64.of_float fval)))) *)
        raise "ivfromfloat no implemented"
    end.

  Definition unspecified_mval (ty: Ctype.ctype): mem_value := MVunspecified ty.

  Definition integer_value_mval
    (ity: Ctype.integerType) (ival: integer_value)
    : mem_value := MVinteger ity ival.

  Definition floating_value_mval
    (fty: Ctype.floatingType) (fval: floating_value)
    : mem_value := MVfloating fty fval.

  Definition pointer_mval
    (ref_ty: Ctype.ctype) (ptrval: pointer_value)
    : mem_value := MVpointer ref_ty ptrval.

  Definition array_mval (mvals : list mem_value) : mem_value :=
    MVarray mvals.

  Definition struct_mval
    (tag_sym: Symbol.sym)
    (xs: list(Symbol.identifier * Ctype.ctype * mem_value)): mem_value :=
    MVstruct tag_sym xs.

  Definition union_mval
    (tag_sym : Symbol.sym)
    (memb_ident : Symbol.identifier) (mval : mem_value)
    : mem_value := MVunion tag_sym memb_ident mval.

  Definition case_mem_value
    {A: Set}
    (mval : mem_value)
    (f_unspec : Ctype.ctype -> A)
    (f_concur : Ctype.integerType -> Symbol.sym -> A)
    (f_ival : Ctype.integerType -> integer_value -> A)
    (f_fval : Ctype.floatingType -> floating_value -> A)
    (f_ptr : Ctype.ctype -> pointer_value -> A)
    (f_array : list mem_value -> A)
    (f_struct : Symbol.sym -> list (Symbol.identifier * Ctype.ctype * mem_value) -> A)
    (f_union : Symbol.sym -> Symbol.identifier -> mem_value -> A) : A
    :=
    match mval with
    | MVunspecified ty => f_unspec ty
    | MVinteger ity ival => f_ival ity ival
    | MVfloating fty fval => f_fval fty fval
    | MVpointer ref_ty ptrval => f_ptr ref_ty ptrval
    | MVarray mvals => f_array mvals
    | MVstruct tag_sym xs => f_struct tag_sym xs
    | MVunion tag_sym memb_ident mval' => f_union tag_sym memb_ident mval'
    end.

  Definition sequencePoint: memM unit :=
    ret tt.

  Definition cap_of_mem_value
    (funptrmap : ZMap.t (digest * string * C.t))
    (mv : mem_value)
    : option  (ZMap.t (digest * string * C.t) * C.t)
    :=
    match mv with
    | MVinteger _ (IC _ c_value) => Some (funptrmap, c_value)
    | MVpointer _ (PV _ (PVconcrete c_value)) => Some (funptrmap, c_value)
    | MVpointer _ (PV _ (PVfunction fp)) =>
        Some (resolve_function_pointer funptrmap fp)
    | _ => None
    end.

  Definition update_cap_in_mem_value
    (cap_val : mem_value) (c_value : C.t) : mem_value :=
    match cap_val with
    | MVinteger ty (IC is_signed _) => MVinteger ty (IC is_signed c_value)
    | MVpointer ty (PV prov (PVconcrete _)) =>
      MVpointer ty (PV prov (PVconcrete c_value))
    | MVpointer ty (PV prov (PVfunction fp)) =>
      MVpointer ty (PV prov (PVfunction (FP_invalid c_value)))
    | other => other
    end.

  Definition bool_bits_of_bytes (bytes_value : list ascii): list bool
      := []. (* TODO *)
                                                                 (*
    :=
    let fix get_slice_int' (function_parameter : Z * Z * Z)
      : list bool :=
      let '(n_value, m_value, o_value) := function_parameter in
      if Z.leb n_value 0 then
        nil
      else
        let bit :=
          negb
            (Z.eqb
               (extract_num m_value
                  (Z.sub (Z.add n_value o_value) 1) 1) 0) in
        cons bit (get_slice_int' ((Z.sub n_value 1), m_value, o_value)) in
    let bit_list_of_char (c_value : ascii) : list bool :=
      get_slice_int'
        (8, (Z.of_nat (nat_of_ascii c_value)), 0) in
    List.concat (List.map bit_list_of_char bytes_value).
                                                                  *)

  Definition load_string (loc : location_ocaml) (c_value : C.t): memM string
    := raise (InternalErr "TODO").
    (*
    let fix loop {B : Set} (acc : string) (offset : Z)
      : Eff.eff string Mem_cheri.mem_error B mem_state :=
      Eff.op_gtgt (cap_check loc c_value offset ReadIntent 1)
        (let addr :=
           Z.add (C.cap_get_value c_value)
             offset in
         Eff.op_gtgteq Eff.get
           (fun (st : mem_state) =>
              let bs := fetch_bytes st.(mem_state.bytemap) addr 1 in
              let '_ :=
                (* ❌ Assert instruction is not handled. *)
                assert unit (equiv_decb (List.length bs) 1) in
              match (List.hd bs).(AbsByte.t.value) with
              | None => fail (MerrReadUninit loc)
              | Some c_value =>
                  if equiv_decb c_value "000" % char then
                    ret acc
                  else
                    let s_value := String.append acc (Stdlib.String.make 1 c_value)
                    in
                    loop s_value (Z.succ offset)
              end)) in
    loop "" 0.
    *)

  Definition store_string (loc : location_ocaml) (s_value : string) (n_value : Z) (c_value : C.t) : memM Z
    := raise (InternalErr "TODO").
(*    let n' := Z.to_int n_value in
    if equiv_decb n' 0 then
      ret 0
    else
      let cs := List.of_seq (Stdlib.String.to_seq s_value) in
      let cs := L.take (Z.sub n' 1) cs in
      let pre_bs :=
        List.map
          (fun (c_value : ascii) =>
            {| AbsByte.t.prov := Prov_none; AbsByte.t.copy_offset := None;
              AbsByte.t.value := Some c_value |}) cs in
      let pre_bs :=
        List.append pre_bs
          [
            {| AbsByte.t.prov := Prov_none; AbsByte.t.copy_offset := None;
              AbsByte.t.value := Some "000" % char |}
          ] in
      let '_ :=
        (* ❌ Assert instruction is not handled. *)
        assert unit
          (Z.ltb
            (Z.of_int (List.length pre_bs)) n_value) in
      let addr := C.cap_get_value c_value in
      let bs :=
        mapi
          (fun (i_value : int) =>
            fun (b_value : AbsByte.t) =>
              ((Z.add addr (Z.of_int i_value)), b_value))
          pre_bs in
      Eff.op_gtgt
        (Eff.op_gtgt
          (cap_check loc c_value 0 WriteIntent
            (List.length bs))
          (Eff.update
            (fun (st : mem_state) =>
              mem_state.with_bytemap
                (List.fold_left
                  (fun (acc : ZMap.t AbsByte.t) =>
                    fun (function_parameter : Z * AbsByte.t) =>
                      let '(addr, b_value) := function_parameter in
                      ZMap.add addr b_value acc)
                  st.(mem_state.bytemap) bs) st)))
        (ret (List.length bs)).
 *)

  Definition call_intrinsic
    (loc : location_ocaml) (name : string) (args : list mem_value)
    : memM (option mem_value)
    :=
    if String.eqb name "strfcap" then
      buf_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
      maxsize_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
      format_val <- option2memM "missing argument"  (List.nth_error args 2%nat) ;;
      cap_val <- option2memM "missing argument"  (List.nth_error args 3%nat) ;;
      get >>=
        (fun (st : mem_state) =>
           match cap_of_mem_value st.(funptrmap) cap_val with
           | None =>
               fail
                 (MerrOther
                    (String.append
                       "CHERI.call_intrinsic: non-cap 1st argument in: '"
                       (String.append name "'")))
           | Some (funptrmap, c_value) =>
               (update
                  (fun (st : mem_state) => mem_state_with_funptrmap funptrmap st))
               ;;
               match (buf_val, maxsize_val, format_val) with
               |
                 (MVpointer _ (PV _ (PVconcrete buf_cap)),
                   MVinteger _ (IV maxsize_n),
                   MVpointer _ (PV _ (PVconcrete format_cap))) =>
                   load_string loc format_cap >>=
                     (fun (format : string) =>
                        match C.strfcap format c_value with
                        | None =>
                            ret
                              (Some
                                 (MVinteger
                                    (Ctype.Signed Ctype.Long)
                                    (IV (-1))))
                        | Some res =>
                            let res_size := String.length res in
                            let res_size_n := Z.of_nat res_size in
                            if Z.geb res_size_n maxsize_n then
                              ret
                                (Some
                                   (MVinteger
                                      (Ctype.Signed
                                         Ctype.Long)
                                      (IV (-1))))
                            else
                              store_string loc res maxsize_n buf_cap ;;
                              (ret
                                 (Some
                                    (MVinteger
                                       (Ctype.Signed
                                          Ctype.Long) (IV res_size_n))))
                        end)
               | (_, _, _) =>
                   fail
                     (MerrOther
                        (String.append "CHERI.call_intrinsic: wrong types in: '"
                           (String.append name "'")))
               end
           end)
    else
      if String.eqb name "cheri_bounds_set" then
        cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
        upper_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
        get >>=
          (fun (st : mem_state) =>
             match cap_of_mem_value st.(funptrmap) cap_val with
             | None =>
                 fail
                   (MerrOther
                      (String.append
                         "CHERI.call_intrinsic: non-cap 1st argument in: '"
                         (String.append name "'")))
             | Some (funptrmap, c_value) =>
                 update (fun (st : mem_state) => mem_state_with_funptrmap funptrmap st)
                 ;;
                 match upper_val with
                 | MVinteger Ctype.Size_t (IV n_value) =>
                     let x' := C.cap_get_value c_value in
                     let c_value := C.cap_narrow_bounds c_value (x', (Z.add x' n_value))
                     in ret (Some (update_cap_in_mem_value cap_val c_value))
                 | _ =>
                     fail
                       (MerrOther
                          (String.append
                             "CHERI.call_intrinsic: 2nd argument's type is not size_t in: '"
                             (String.append name "'")))
                 end
             end)
      else
        if String.eqb name "cheri_perms_and" then
          cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
          mask_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
          get >>=
            (fun (st : mem_state) =>
               match cap_of_mem_value st.(funptrmap) cap_val with
               | None =>
                   fail
                     (MerrOther
                        (String.append
                           "CHERI.call_intrinsic: non-cap 1st argument in: '"
                           (String.append name "'")))
               | Some (funptrmap, c_value) =>
                   (update
                      (fun (st : mem_state) =>
                         mem_state_with_funptrmap funptrmap st))
                   ;;
                   match mask_val with
                   | MVinteger (Ctype.Size_t as ity) (IV n_value)
                     =>
                       iss <- option2memM "is_signed_ity failed" (is_signed_ity DEFAULT_FUEL ity) ;;
                       sz <- serr2memM (sizeof DEFAULT_FUEL None (Ctype.Ctype nil(Ctype.Basic (Ctype.Integer ity)))) ;;
                       bytes_value <- serr2memM (bytes_of_Z iss (Z.to_nat sz) n_value) ;;
                       let bits := bool_bits_of_bytes bytes_value in
                       match MorelloPermission.of_list bits with
                       | None =>
                           fail
                             (MerrOther
                                (String.append
                                   "CHERI.call_intrinsic: error decoding permission bits: '"
                                   (String.append name "'")))
                       | Some pmask =>
                           let c_value := C.cap_narrow_perms c_value pmask
                           in ret (Some (update_cap_in_mem_value cap_val c_value))
                       end
                   | _ =>
                       fail
                         (MerrOther
                            (String.append
                               "CHERI.call_intrinsic: 2nd argument's type is not size_t in: '"
                               (String.append name "'")))
                   end
               end)
        else
          if String.eqb name "cheri_offset_get" then
            cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
            get >>=
              (fun (st : mem_state) =>
                 match cap_of_mem_value st.(funptrmap) cap_val with
                 | None =>
                     fail
                       (MerrOther
                          (String.append
                             "CHERI.call_intrinsic: non-cap 1st argument in: '"
                             (String.append name "'")))
                 | Some (_, c_value) =>
                     let v_value := C.cap_get_offset c_value in
                     ret (Some (MVinteger Ctype.Size_t (IV v_value)))
                 end)
          else
            if String.eqb name "cheri_address_get" then
              cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
              get >>=
                (fun (st : mem_state) =>
                   match cap_of_mem_value st.(funptrmap) cap_val with
                   | None =>
                       fail
                         (MerrOther
                            (String.append
                               "CHERI.call_intrinsic: non-cap 1st argument in: '"
                               (String.append name "'")))
                   | Some (_, c_value) =>
                       let v_value := C.cap_get_value c_value in
                       ret (Some (MVinteger Ctype.Vaddr_t (IV v_value)))
                   end)
            else
              if String.eqb name "cheri_base_get" then
                cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                get >>=
                  (fun (st : mem_state) =>
                     match cap_of_mem_value st.(funptrmap) cap_val with
                     | None =>
                         fail
                           (MerrOther
                              (String.append
                                 "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                 (String.append name "'")))
                     | Some (_, c_value) =>
                         let v_value := fst (C.cap_get_bounds c_value)
                         in ret (Some (MVinteger Ctype.Vaddr_t (IV v_value)))
                     end)
              else
                if String.eqb name "cheri_length_get" then
                  cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                  get >>=
                    (fun (st : mem_state) =>
                       match cap_of_mem_value st.(funptrmap) cap_val
                       with
                       | None =>
                           fail
                             (MerrOther
                                (String.append
                                   "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                   (String.append name "'")))
                       | Some (_, c_value) =>
                           let '(base, limit) := C.cap_get_bounds c_value in
                           let v_value := Z.sub limit base in
                           ret (Some (MVinteger Ctype.Size_t (IV v_value)))
                       end)
                else
                  if String.eqb name "cheri_tag_get" then
                    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                    get >>=
                      (fun (st : mem_state) =>
                         match cap_of_mem_value st.(funptrmap) cap_val
                         with
                         | None =>
                             fail
                               (MerrOther
                                  (String.append
                                     "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                     (String.append name "'")))
                         | Some (_, c_value) =>
                             let v_value := if C.cap_is_valid c_value then 1 else 0
                             in  ret (Some (MVinteger Ctype.Bool (IV v_value)))
                         end)
                  else
                    if String.eqb name "cheri_tag_clear" then
                      cap_val <- option2memM "missing argument"  (List.nth_error args 0) ;;
                      get >>=
                        (fun (st : mem_state) =>
                           match
                             cap_of_mem_value st.(funptrmap) cap_val
                           with
                           | None =>
                               fail
                                 (MerrOther
                                    (String.append
                                       "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                       (String.append name "'")))
                           | Some (funptrmap, c_value) =>
                               update (fun st => mem_state_with_funptrmap funptrmap st)
                               ;;
                               let c_value := C.cap_invalidate c_value in
                               ret (Some (update_cap_in_mem_value cap_val c_value))
                           end)
                    else
                      if String.eqb name "cheri_is_equal_exact" then
                        cap_val0 <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                        cap_val1 <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
                        get >>=
                          (fun (st : mem_state) =>
                             match
                               (cap_of_mem_value st.(funptrmap) cap_val0),
                               (cap_of_mem_value st.(funptrmap) cap_val1) with
                             | None, _ =>
                                 fail
                                   (MerrOther
                                      (String.append
                                         "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                         (String.append name "'")))
                             | _, None =>
                                 fail
                                   (MerrOther
                                      (String.append
                                         "CHERI.call_intrinsic: non-cap 2nd argument in: '"
                                         (String.append name "'")))
                             | Some (_, c0), Some (_, c1) =>
                                 let v_value :=
                                   if C.eqb c0 c1 then
                                     1
                                   else
                                     0 in
                                 ret
                                   (Some
                                      (MVinteger Ctype.Bool
                                         (IV v_value)))
                             end)
                      else
                        if String.eqb name "cheri_representable_length" then
                          match List.nth_error args 0%nat with
                          | None =>
                              raise (InternalErr "missing argument")
                          | Some (MVinteger Ctype.Size_t (IV n_value)) =>
                              let l_value := C.representable_length n_value in
                              ret
                                (Some
                                   (MVinteger Ctype.Size_t
                                      (IV l_value)))
                          | Some _ =>
                              fail
                                (MerrOther
                                   (String.append
                                      "CHERI.call_intrinsic: 1st argument's type is not size_t in: '"
                                      (String.append name "'")))
                          end
                        else
                          if
                            String.eqb name "cheri_representable_alignment_mask"
                          then
                            match List.nth_error args 0%nat with
                            | None =>
                                raise (InternalErr "missing argument")
                            | Some (MVinteger Ctype.Size_t (IV n_value))
                              =>
                                let l_value := C.representable_alignment_mask n_value in
                                ret
                                  (Some
                                     (MVinteger Ctype.Size_t
                                        (IV l_value)))
                            | Some _ =>
                                fail
                                  (MerrOther
                                     (String.append
                                        "CHERI.call_intrinsic: 1st argument's type is not size_t in: '"
                                        (String.append name "'")))
                            end
                          else
                            fail
                              (MerrOther
                                 (String.append
                                    "CHERI.call_intrinsic: unknown intrinsic: '"
                                    (String.append name "'"))).

  Definition get_intrinsic_type_spec (name : string)
    : option intrinsics_signature
    :=
    if String.eqb name "strfcap" then
      Some
        ((ExactRet
            Ctype.signed_long),
          [
            ExactArg
              (Ctype.Ctype nil
                 (Ctype.Pointer
                    {|
                      Ctype.const := false;
                      Ctype.restrict := true;
                      Ctype.volatile := false
                    |}
                    Ctype.signed_char));
            ExactArg
              Ctype.size_t;
            ExactArg
              (Ctype.Ctype nil
                 (Ctype.Pointer
                    {| Ctype.const := true;
                      Ctype.restrict := true;
                      Ctype.volatile := false
                    |}
                    Ctype.signed_char));
            PolymorphicArg
              [
                TyPred
                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                TyPred
                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                TyIsPointer
              ]
        ])
    else
      if String.eqb name "cheri_bounds_set" then
        Some
          ((CopyRet 0),
            [
              PolymorphicArg
                [
                  TyPred
                    (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                  TyPred
                    (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                  TyIsPointer
                ];
              ExactArg
                Ctype.size_t
          ])
      else
        if String.eqb name "cheri_perms_and" then
          Some
            ((CopyRet 0),
              [
                PolymorphicArg
                  [
                    TyPred
                      (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                    TyPred
                      (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                    TyIsPointer
                  ];
                ExactArg
                  Ctype.size_t
            ])
        else
          if String.eqb name "cheri_address_get" then
            Some
              ((ExactRet
                  (Ctype.vaddr_t tt)),
                [
                  PolymorphicArg
                    [
                      TyPred
                        (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                      TyPred
                        (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                      TyIsPointer
                    ]
              ])
          else
            if String.eqb name "cheri_base_get" then
              Some
                ((ExactRet
                    (Ctype.vaddr_t tt)),
                  [
                    PolymorphicArg
                      [
                        TyPred
                          (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                        TyPred
                          (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                        TyIsPointer
                      ]
                ])
            else
              if String.eqb name "cheri_length_get" then
                Some
                  ((ExactRet
                      Ctype.size_t),
                    [
                      PolymorphicArg
                        [
                          TyPred
                            (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                          TyPred
                            (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                          TyIsPointer
                        ]
                  ])
              else
                if String.eqb name "cheri_tag_get" then
                  Some
                    ((ExactRet
                        (Ctype.Ctype nil
                           (Ctype.Basic
                              (Ctype.Integer Ctype.Bool)))),
                      [
                        PolymorphicArg
                          [
                            TyPred
                              (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                            TyPred
                              (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                            TyIsPointer
                          ]
                    ])
                else
                  if String.eqb name "cheri_tag_clear" then
                    Some
                      ((CopyRet 0),
                        [
                          PolymorphicArg
                            [
                              TyPred
                                (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                              TyPred
                                (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                              TyIsPointer
                            ]
                      ])
                  else
                    if String.eqb name "cheri_is_equal_exact" then
                      Some
                        ((ExactRet
                            (Ctype.Ctype nil
                               (Ctype.Basic
                                  (Ctype.Integer
                                     Ctype.Bool)))),
                          [
                            PolymorphicArg
                              [
                                TyPred
                                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                                TyPred
                                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                                TyIsPointer
                              ];
                            PolymorphicArg
                              [
                                TyPred
                                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                                TyPred
                                  (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                                TyIsPointer
                              ]
                        ])
                    else
                      if String.eqb name "cheri_representable_length" then
                        Some ((ExactRet Ctype.size_t), [ExactArg Ctype.size_t])
                      else
                        if
                          String.eqb name "cheri_representable_alignment_mask"
                        then
                          Some ((ExactRet Ctype.size_t), [ExactArg Ctype.size_t])
                        else
                          if String.eqb name "cheri_offset_get" then
                            Some
                              ((ExactRet
                                  Ctype.size_t),
                                [
                                  PolymorphicArg
                                    [
                                      TyPred
                                        (Ctype.ctypeEqual DEFAULT_FUEL Ctype.intptr_t);
                                      TyPred
                                        (Ctype.ctypeEqual DEFAULT_FUEL Ctype.uintptr_t);
                                      TyIsPointer
                                    ]
                              ])
                          else
                            None.


End CheriMemory.
