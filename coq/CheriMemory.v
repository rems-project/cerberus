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

From ExtLib.Structures Require Import Monad Monads MonadExc MonadState.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

Require Import Capabilities Addr Memory_model Mem_common ErrorWithState Undefined Morello ErrorWithState Location Symbol Implementation Tags Utils Switches.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

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

  Definition name := "CHERI memory model".

  Definition symbolic_storage_instance_id : Set := Z.
  Definition storage_instance_id : Set := Z.

  (* Following types need to be defined *)
  Definition derivecap_op: Set := unit. (* Mem_common.derivecap_op *)
  Definition integer_operator: Set := unit. (* Mem_common.integer_operator *)
  Definition floating_operator: Set := unit. (* Mem_common.floating_operator *)
  Definition intrinsics_signature: Set := unit. (* intrinsics_signature *)
  Definition Digest_t: Set := unit. (* OCaml Stdlib.Digest_t *)

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
                    (Digest_t * string * C.t);
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

  Definition initial_address := (HexString.to_Z "0xFFFFFFFF").

  Definition DEFAULT_FUEL:nat := 1000%nat. (* TODO maybe needs to be abstracted *)

  Definition initial_mem_state : mem_state :=
    {|
      next_alloc_id := Z0;
      next_iota := Z0;
      last_address := initial_address;
      allocations := ZMap.empty allocation;
      iota_map := ZMap.empty (storage_instance_id + storage_instance_id * storage_instance_id);
      funptrmap := ZMap.empty (Digest_t * string * C.t);
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

  Definition serr2memM {A: Type} (msg:string) (e:serr A): (memM A)
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
            ret ((List.map
                    (fun (function_parameter :
                           Symbol.identifier *
                             (Annot.attributes *
                                Ctype.qualifiers *
                                Ctype.ctype)) =>
                       let '(ident, (_, _, ty)) := function_parameter in
                       (ident, ty, 0)) membrs), 0)
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

  Definition repr
    (funptrmap: ZMap.t(Digest_t * string * C.t))
    (captags : ZMap.t bool)
    (addr : Z)
    (mval : mem_value)
    : (ZMap.t (Digest_t * string * C.t)) *
        (ZMap.t bool) *
        (list AbsByte).
  Proof. Admitted. (* TODO: *)

  Definition allocate_object
    (tid:thread_id)
    (pref:Symbol.prefix)
    (int_val:integer_value)
    (ty:Ctype.ctype)
    (init_opt:option mem_value)
    : memM pointer_value
    :=
    let align_n := num_of_int int_val in
    size_n <- serr2memM "sizeof failed" (sizeof DEFAULT_FUEL None ty) ;;

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
                | Symbol.PrefStringLiteral _ _ =>
                    (true,IsReadOnly_string_literal)
                | _ =>
                    (false,IsWritable)
                end
              in
              let alloc := {| prefix:= pref; base:= addr; size:= size_n'; ty:= Some ty; is_readonly:= readonly_status; taint:= Unexposed |} in
              (* TODO: factorize this with do_store inside CHERI.store *)
              update (fun st =>
                        let '(funptrmap, captags, pre_bs) := repr st.(funptrmap) st.(captags) addr mval in
                        let bs := mapi (fun i b => (Z.add addr (Z.of_nat i), b)) pre_bs in
                        {|
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
                        |})
              ;; ret ro
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

  Fixpoint abst 
    (loc : location_ocaml)
    (find_overlaping : Z.t -> overlap_ind)
    (funptrmap : ZMap.t (Digest_t * string * C.t))
    (tag_query_f : Z.t -> option bool)
    (addr : Z)
    (function_parameter : Ctype.ctype)
    : list AbsByte -> taint_ind * mem_value_with_err * list AbsByte
    :=
    let '(Ctype.Ctype _ ty) as cty := function_parameter in
    fun (bs : list AbsByte) =>
      let self := abst loc find_overlaping funptrmap tag_query_f in
      let '_ :=
        if
          lt (List.length bs) (sizeof None cty)
        then
          raise (InternalErr "abst, |bs| < sizeof(ty)")
        else
          tt in
      let merge_taint
            (x_value : (* `NoTaint *) unit) (y_value : (* `NoTaint *) unit)
        : (* `NoTaint *) unit :=
        match (x_value, y_value) with
        | (NoTaint, NoTaint) => NoTaint
        | ((NoTaint, NewTaint xs) | (NewTaint xs, NoTaint)) => NewTaint xs
        | (NewTaint xs, NewTaint ys) => NewTaint (List.app xs ys)
        end in
      match ty with
      |
        (Ctype.Void | Ctype.Array _ None |
          Ctype.Function _ _ _ |
          Ctype.FunctionNoParams _) =>
          raise (InternalErr "abst on function!")
      |
        (Ctype.Basic
           (Ctype.Integer
              ((Ctype.Signed Ctype.Intptr_t) as ity))
        |
          Ctype.Basic
            (Ctype.Integer
               ((Ctype.Unsigned Ctype.Intptr_t) as ity)))
        =>
          let '(bs1, bs2) := split_at (sizeof None cty) bs in
          let '(prov, _, bs1') := split_bytes bs1 in
          ((provs_of_bytes bs1),
            match extract_unspec bs1' with
            | Some cs =>
                match tag_query_f addr with
                | None =>
                    let '_ :=
                      Debug_ocaml.warn nil
                        (fun (function_parameter : unit) =>
                           let '_ := function_parameter in
                           String.append "Unspecified tag value for address 0x"
                             (Z.format "%x" addr)) in
                    MVEunspecified cty
                | Some tag =>
                    match C.decode cs tag with
                    | None =>
                        let '_ :=
                          Debug_ocaml.warn nil
                            (fun (function_parameter : unit) =>
                               let '_ := function_parameter in
                               "Error decoding [u]intptr_t cap") in
                        MVErr
                          (MerrCHERI loc
                             CheriErrDecodingCap)
                    | Some c_value =>
                        if AilTypesAux.is_signed_ity ity then
                          let n_value := C.cap_get_value c_value
                          in
                          let c_value :=
                            C.cap_set_value c_value
                              (wrap_cap_value n_value) in
                          MVEinteger ity (IC true c_value)
                        else
                          MVEinteger ity (IC false c_value)
                    end
                end
            | None => MVEunspecified cty
            end, bs2)
      | Ctype.Basic (Ctype.Integer ity) =>
          let '(bs1, bs2) := split_at (sizeof None cty) bs in
          let '(prov, _, bs1') := split_bytes bs1 in
          ((provs_of_bytes bs1),
            match extract_unspec bs1' with
            | Some cs =>
                MVEinteger ity
                  (IV
                     (int_of_bytes
                        (AilTypesAux.is_signed_ity ity) cs))
            | None => MVEunspecified cty
            end, bs2)
      | Ctype.Basic (Ctype.Floating fty) =>
          let '(bs1, bs2) := split_at (sizeof None cty) bs in
          let '(_, _, bs1') := split_bytes bs1 in
          (NoTaint,
            match extract_unspec bs1' with
            | Some cs =>
                MVEfloating fty
                  (Stdlib.Int64.float_of_bits
                     (Z.to_int64 (int_of_bytes true cs)))
            | None => MVEunspecified cty
            end, bs2)
      | Ctype.Array elem_ty (Some n_value) =>
          let fix aux
                (n_value : int)
                (function_parameter :
                  ((* `NoTaint *) unit + (* `NewTaint *) list storage_instance_id) *
                    list mem_value_with_err)
            : list AbsByte ->
              ((* `NoTaint *) unit + (* `NewTaint *) list storage_instance_id) *
                mem_value_with_err * list AbsByte :=
            let '(taint_acc, mval_acc) := function_parameter in
            fun (cs : list AbsByte) =>
              if le n_value 0 then
                (taint_acc, (MVEarray (List.rev mval_acc)), cs)
              else
                let el_addr :=
                  Z.add addr
                    (Z.of_int
                       (Z.mul (Z.sub n_value 1) (sizeof None elem_ty))) in
                let '(taint, mval, cs') := self el_addr elem_ty cs in
                aux (Z.sub n_value 1)
                  ((merge_taint taint taint_acc), (cons mval mval_acc)) cs' in
          aux (Z.to_int n_value) (NoTaint, nil) bs
      | Ctype.Pointer _ ref_ty =>
          let '(bs1, bs2) := split_at (sizeof None cty) bs in
          let '_ :=
            Debug_ocaml.print_debug 1 nil
              (fun (function_parameter : unit) =>
                 let '_ := function_parameter in
                 "TODO: Concrete, assuming pointer repr is unsigned??") in
          let '(prov, prov_status, bs1') := split_bytes bs1 in
          (NoTaint,
            match extract_unspec bs1' with
            | Some cs =>
                match tag_query_f addr with
                | None =>
                    let '_ :=
                      Debug_ocaml.warn nil
                        (fun (function_parameter : unit) =>
                           let '_ := function_parameter in
                           String.append "Unspecified tag value for address 0x"
                             (Z.format "%x" addr)) in
                    MVEunspecified cty
                | Some tag =>
                    match C.decode cs tag with
                    | None =>
                        let '_ :=
                          Debug_ocaml.warn nil
                            (fun (function_parameter : unit) =>
                               let '_ := function_parameter in
                               "Error decoding pointer cap") in
                        MVErr
                          (MerrCHERI loc
                             CheriErrDecodingCap)
                    | Some n_value =>
                        match ref_ty with
                        |
                          Ctype.Ctype _
                            (Ctype.Function _ _ _) =>
                            match tag_query_f addr with
                            | None =>
                                let '_ :=
                                  Debug_ocaml.warn nil
                                    (fun (function_parameter : unit) =>
                                       let '_ := function_parameter in
                                       String.append "Unspecified tag value for address 0x"
                                         (Z.format "%x" addr)) in
                                MVEunspecified cty
                            | Some tag =>
                                match C.decode cs tag with
                                | None =>
                                    let '_ :=
                                      Debug_ocaml.warn nil
                                        (fun (function_parameter : unit) =>
                                           let '_ := function_parameter in
                                           "Error decoding function pointer cap") in
                                    MVErr
                                      (MerrCHERI loc
                                         CheriErrDecodingCap)
                                | Some c_value =>
                                    let n_value :=
                                      Z.sub
                                        (C.cap_get_value c_value)
                                        (Z.of_int initial_address) in
                                    match Zmap.find_opt n_value funptrmap
                                    with
                                    | Some (file_dig, name, c') =>
                                        if C.eq c_value c' then
                                          MVEpointer ref_ty
                                            (PV prov
                                               (PVfunction
                                                  (FP_valid
                                                     (Symbol.Symbol file_dig
                                                        (Z.to_int n_value)
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
                                  | DoubleAlloc (alloc_id1, alloc_id2) =>
                                      Prov_some alloc_id1
                                  end
                              | ValidPtrProv => prov
                              end in
                            MVEpointer ref_ty (PV prov (PVconcrete n_value))
                        end
                    end
                end
            | None =>
                MVEunspecified
                  (Ctype.Ctype nil
                     (Ctype.Pointer
                        Ctype.no_qualifiers ref_ty))
            end, bs2)
      | Ctype.Atomic atom_ty =>
          let '_ :=
            Debug_ocaml.print_debug 1 nil
              (fun (function_parameter : unit) =>
                 let '_ := function_parameter in
                 "TODO: Concrete, is it ok to have the repr of atomic types be the same as their non-atomic version??")
          in
          self addr atom_ty bs
      | Ctype.Struct tag_sym =>
          let '(bs1, bs2) := split_at (sizeof None cty) bs in
          let '(taint, rev_xs, _, bs') :=
            List.fold_left
              (fun (function_parameter :
                   ((* `NoTaint *) unit + (* `NewTaint *) list storage_instance_id) *
                     list
                       (Symbol.identifier *
                          Ctype.ctype * mem_value_with_err) *
                     int * list AbsByte) =>
                 let '(taint_acc, acc_xs, previous_offset, acc_bs) :=
                   function_parameter in
                 fun (function_parameter :
                     Symbol.identifier *
                       Ctype.ctype * int) =>
                   let '(memb_ident, memb_ty, memb_offset) := function_parameter in
                   let pad := Z.sub memb_offset previous_offset in
                   let memb_addr :=
                     Z.add addr (Z.of_int memb_offset) in
                   let '(taint, mval, acc_bs') :=
                     self memb_addr memb_ty (L.drop pad acc_bs) in
                   ((merge_taint taint taint_acc),
                     (cons (memb_ident, memb_ty, mval) acc_xs),
                     (Z.add memb_offset (sizeof None memb_ty)), acc_bs'))
              (NoTaint, nil, 0, bs1)
              (fst (offsetsof (Mem_cheri.Tags.tagDefs tt) tag_sym))
          in
          (taint, (MVEstruct tag_sym (List.rev rev_xs)), bs2)
      | Ctype.Union tag_sym =>
          raise (InternalErr "TODO: abst, Union (as value)")
      end.

  (*
  Definition load
    (loc: location_ocaml) (ty: Ctype.ctype) (p:pointer_value): memM (footprint * mem_value) :=
    let '(prov, ptrval_) := break_PV p in
    _
  .
   *)



End CheriMemory.
