Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
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

Require Import Capabilities.
Require Import Addr.
Require Import Memory_model.
Require Import Mem_common.
Require Import ErrorWithState.
Require Import Undefined.
Require Import Morello.
Require Import ErrorWithState.
Require Import Location.
Require Import Symbol.
Require Import Implementation.
Require Import Tags.

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

  Definition initial_address := MorelloAddr.of_Z (HexString.to_Z "0xFFFFFFFF").

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

  (* unfortunate consturctor names mirroring ones from OCaml Nondeterminism monad *)
  Inductive MemMonadError :=
  | Other: mem_error -> MemMonadError
  | Undef0: location_ocaml -> (list undefined_behaviour) -> MemMonadError.

  Definition memM := errS mem_state MemMonadError.
  #[local] Instance memM_monad: Monad memM.
  Proof.
    typeclasses eauto.
  Qed.

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

  Inductive footprint_ind :=
    (* base address, size *)
    | FP: MorelloAddr.t * Z -> footprint_ind.

  Definition footprint := footprint_ind.

  Definition check_overlap a b :=
    match a,b with
    |  (FP (b1, sz1)), (FP (b2, sz2)) =>
         let b1 := MorelloAddr.to_Z b1 in
         let b2 := MorelloAddr.to_Z b2 in
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
        let n := MorelloAddr.to_Z (C.cap_get_value c) in
        if is_signed then unwrap_cap_value n else n
    end.

  (** Invalidate capability tags for memory region starting from
      [addr] with [size].

      All tags which were [true] will be flipped to [false].  For
      addresses which did not have tags set, they will remain
      unspecified.

      Implementation is split into 2 functions: one implementing recursion
      and the other is top level entry point.
   *)
  Function clear_tags_loop (a0:Z) (align:{x:Z|0 < x}) (a : Z) (captags : ZMap.t bool) {wf (Zwf a0) a} : ZMap.t bool
    :=
    let upd (a : Z.t) (ct : ZMap.t bool): ZMap.t bool :=
      match ZMap.find a ct with
      | Some true => ZMap.add a false ct
      | _ => ct
      end in
    if Z.geb a a0 then
      clear_tags_loop a0 align (Z.sub a (proj1_sig align)) (upd a captags)
    else
      captags.
  Proof.
    -
      intros a0 align a captags0 teq.
      destruct align as [align AC].
      unfold Zwf.
      split.
      + lia.
      + apply Z.geb_le in teq.
        apply Z.lt_sub_pos.
        simpl.
        lia.
    -
      apply Zwf_well_founded.
  Qed.
  Definition clear_caps
    (addr:MorelloAddr.t)
    (size:Z)
    (captags:ZMap.t bool): ZMap.t bool
    :=
    let align := IMP.get.(alignof_pointer) in
    let align_pos := IMP.get.(alignof_pointer_positive) in
    let lower_a (x_value : Z) : Z := Z.mul (Z.quot x_value align) align in
    let addr := MorelloAddr.to_Z addr in
    let a0 := lower_a addr in
    let a1 := lower_a (Z.pred (Z.add addr size)) in
    clear_tags_loop a0 (exist _ align align_pos) a1 captags.

  Definition allocator (size:Z) (align:Z) : memM (storage_instance_id * MorelloAddr.t) :=
    get >>= fun st =>
        let alloc_id := st.(next_alloc_id) in
        (
          let z := Z.sub (MorelloAddr.to_Z st.(last_address)) size in
          let (q,m) := Z.quotrem z align in
          let z' := Z.sub z (Z.abs m) in
          if Z.leb z' 0 then
            fail (MerrOther "CHERI.allocator: failed (out of memory)")
          else
            ret z'
        )
          >>= fun addr =>
            let addr := MorelloAddr.of_Z addr in
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


  (* c.f.
   List.fold_left
     : forall A B : Type, (A -> B -> A) -> list B -> A -> A

   TODO: move somewhere else. Perhaps Util.v
   *)
  Fixpoint monadic_fold_left
    {A B : Type}
    {m : Type -> Type}
    {M : Monad m}
    (f : A -> B -> m A) (l : list B) (a : A)
    : m A
    := match l with
       | List.nil => ret a
       | List.cons b l =>
           a' <- f a b ;;
           monadic_fold_left f l a'
       end.

  Definition alignof (fuel: nat) (maybe_tagDefs : option (SymMap.t Ctype.tag_definition))
    : Ctype.ctype -> option Z
    :=
    let tagDefs :=
      match maybe_tagDefs with
      | Some x => x
      | None => Tags.tagDefs tt
      end in
    let fix alignof_ (fuel: nat) ty  :=
      match fuel with
      | O => None
      | S fuel =>
          match ty with
          | Ctype.Ctype _ Ctype.Void => None
          | Ctype.Ctype _ (Ctype.Basic (Ctype.Integer ity)) =>
              Some (IMP.get.(alignof_ity) ity)
          | Ctype.Ctype _ (Ctype.Basic (Ctype.Floating fty)) =>
              Some (IMP.get.(alignof_fty) fty)
          | Ctype.Ctype _ (Ctype.Array elem_ty _) =>
              alignof_ fuel elem_ty
          |
            (Ctype.Ctype _ (Ctype.Function _ _ _) |
              Ctype.Ctype _ (Ctype.FunctionNoParams _)) =>
              None
          | Ctype.Ctype _ (Ctype.Pointer _ _) =>
              Some (IMP.get.(alignof_pointer))
          | Ctype.Ctype _ (Ctype.Atomic atom_ty) =>
              alignof_ fuel  atom_ty
          | Ctype.Ctype _ (Ctype.Struct tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (Ctype.UnionDef _) =>
                  None
              | Some (Ctype.StructDef membrs flexible_opt) =>
                  init <-
                    match flexible_opt with
                    | None => Some 0
                    | Some (Ctype.FlexibleArrayMember _ _ _ elem_ty) =>
                        alignof_ fuel (Ctype.Ctype nil (Ctype.Array elem_ty None))
                    end ;;
                  monadic_fold_left
                    (fun acc '(_, (_, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       Some (Z.max al acc)
                    )
                    membrs
                    init
              | None => None
              end
          | Ctype.Ctype _ (Ctype.Union tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (Ctype.StructDef _ _) =>
                  None
              | Some (Ctype.UnionDef membrs) =>
                  monadic_fold_left
                    (fun acc '(_, (_, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       Some (Z.max al acc)
                    )
                    membrs
                    0
              | None => None
              end
          end
      end
    in alignof_ fuel.

  Fixpoint offsetsof
    (tagDefs : SymMap.t Ctype.tag_definition)
    (tag_sym : Symbol.sym)
    : option (list (Symbol.identifier * Ctype.ctype * Z) * Z)
    :=
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
               size <- sizeof (Some tagDefs) ty ;;
               align <- alignof (Some tagDefs) ty ;;
               let x_value := Z.modulo last_offset align in
               let pad :=
                 if Z.eqb x_value 0 then
                   0
                 else
                   Z.sub align x_value in
               Some ((cons (membr, ty, (Z.add last_offset pad)) xs),
                   (Z.add (Z.add last_offset pad) size))
            )
            membrs
            (nil, 0) ;;
        Some ((List.rev xs), maxoffset)
    | Some (Ctype.UnionDef membrs) =>
        Some ((List.map
                 (fun (function_parameter :
                      Symbol.identifier *
                        (Annot.attributes *
                           Ctype.qualifiers *
                           Ctype.ctype)) =>
                    let '(ident, (_, _, ty)) := function_parameter in
                    (ident, ty, 0)) membrs), 0)
    | None => None
    end

  with sizeof (maybe_tagDefs : option (SymMap.t Ctype.tag_definition))
    : Ctype.ctype -> option Z
       :=
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
               Ctype.FunctionNoParams _) => None
           | Ctype.Basic (Ctype.Integer ity) =>
               IMP.get.(sizeof_ity) ity
           | Ctype.Basic (Ctype.Floating fty) =>
               IMP.get.(sizeof_fty) fty
           | Ctype.Array elem_ty (Some n_value) =>
               sz <- (sizeof (Some tagDefs) elem_ty) ;;
               Some (Z.mul n_value sz)
           | Ctype.Pointer _ _ =>
               Some (IMP.get.(sizeof_pointer))
           | Ctype.Atomic atom_ty =>
               sizeof (Some tagDefs) atom_ty
           | Ctype.Struct tag_sym =>
               '(_, max_offset) <- offsetsof tagDefs tag_sym ;;
               align <- alignof (Some tagDefs) cty ;;
               let x_value := Z.modulo max_offset align in
               Some (if Z.eqb x_value 0 then
                       max_offset
                     else
                       Z.add max_offset (Z.sub align x_value))
           | Ctype.Union tag_sym =>
               match SymMap.find tag_sym (Tags.tagDefs tt) with
               | Some (Ctype.StructDef _ _) => None
               | Some (Ctype.UnionDef membrs) =>
                   '(max_size, max_align) <-
                     monadic_fold_left
                       (fun '(acc_size, acc_align) '(_, (_, _, ty)) =>
                          sz <- sizeof (Some tagDefs) ty ;;
                          al <- alignof (Some tagDefs) ty ;;
                          Some ((Z.max acc_size sz),(Z.max acc_align al))
                       )
                       membrs (0, 0) ;;
                   let x_value := Z.modulo max_size max_align in
                   Some (if Z.eqb x_value 0 then
                           max_size
                         else
                           Z.add max_size (Z.sub max_align x_value))
               | None => None
               end
           end


  Definition allocate_object (tid:thread_id) (pref:Symbol.prefix) (int_val:integer_value) (ty:Ctype.ctype) (init_opt:option mem_value) : memM pointer_value  :=
    let align_n := num_of_int int_val in
    let sz := sizeof ty in
    let size_n := Z.of_int sz in

    let mask := C.representable_alignment_mask size_n in
    let size_n' := C.representable_length size_n in
    let align_n' := Z.max align_n (Z.add (Z.succ (Z.zero)) (C.vaddr_bitwise_complement mask)) in

    allocator size_n' align_n' >>= fun `(alloc_id, addr) =>
        begin match init_opt with
          | None =>
              let alloc := {| prefix := pref; base:= addr; size:= size_n'; ty:= Some ty; is_readonly:= IsWritable; taint:= Unexposed|} in
              update (fun st =>
              {|
                next_alloc_id    := st.(next_alloc_id);
                next_iota        := st.(next_iota);
                last_address     := st.(last_address) ;
                allocations      := ZMap.add alloc_id alloc st.allocations;
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
                | Symbol.PrefStringLiteral _ =>
                    (true,IsReadOnly_string_literal)
                | _ =>
                    (false,IsWritable)
                end
              in
              let alloc := {| prefix:= pref; base:= addr; size:= size_n'; ty:= Some ty; is_readonly:= readonly_status; taint:= Unexposed |} in
              (* TODO: factorize this with do_store inside CHERI.store *)
              update (fun st =>
                        let (funptrmap, captags, pre_bs) := repr st.funptrmap st.captags addr mval in
                        let bs := List.mapi (fun i b => (Z.add addr (Z.of_int i), b)) pre_bs in
                        {|
                          next_alloc_id    := st.(next_alloc_id);
                          next_iota        := st.(next_iota);
                          last_address     := st.(last_address) ;
                          allocations      := ZMap.add alloc_id alloc st.allocations;
                          iota_map         := st.(iota_map);
                          funptrmap        := funptrmap;
                          varargs          := st.(varargs);
                          next_varargs_id  := st.(next_varargs_id);
                          bytemap          := List.fold_left (fun acc `(addr, b) =>
                                                                ZMap.add addr b acc
                                                ) st.bytemap bs;
                          captags          := captags;
                          dead_allocations := st.(dead_allocations);
                          dynamic_addrs    := st.(dynamic_addrs);
                          last_used        := st.(last_used);
                        |})
              ;; ret ro
          end >>= (fun ro =>
                     let c := C.alloc_cap addr size_n' in
                     if C.cap_bounds_representable_exactly c (addr, Z.add addr size_n')
                     then
                       let c :=
                         if ro then
                           let p := C.cap_get_perms c in
                           let p := C.P.perm_clear_store p in
                           let p := C.P.perm_clear_store_cap p in
                           let p := C.P.perm_clear_store_local_cap p in
                           C.cap_narrow_perms c p
                         else c
                       in
                       ret (PV (Prov_some alloc_id, PVconcrete c))
                     else failwith "Error settting exeact bounds for allocated region")

End CheriMemory.
