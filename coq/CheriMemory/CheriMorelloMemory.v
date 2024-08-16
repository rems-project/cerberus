Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.Floats.PrimFloat.
From Coq.Strings Require Import String Ascii HexString.
Require Import Lia.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads MonadExc MonadState Traversable.
From ExtLib.Data.Monads Require Import EitherMonad OptionMonad.

From Coq.Lists Require Import List. (* after exltlib *)

From CheriCaps.Morello Require Import Capabilities.
From CheriCaps.Common Require Import Capabilities.

From Common Require Import SimpleError Utils ZMap AMap.
From Morello Require Import CapabilitiesGS MorelloCapsGS.

Require Import Memory_model CoqMem_common ErrorWithState CoqUndefined ErrorWithState CoqLocation CoqSymbol CoqImplementation CoqTags CoqSwitches CerbSwitches CoqAilTypesAux.

Local Open Scope string_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Require Import AltBinNotations.
Import ListNotations.
Import MonadNotation.

(* these are generic functions defined in odd places *)
Local Notation opt_def := Values.opt_def.
Local Notation is_some := CapFns.is_some.

Definition AddressValue_with_offset_safe (v:AddressValue.t) (o:Z): option AddressValue.t
  :=
  AddressValue.of_Z_safe (AddressValue.to_Z v + o).

Definition wrapI min_v max_v n :=
  let dlt := Z.succ (max_v - min_v) in
  let r := Z_integerRem_f n dlt in
  if r <=? max_v then r
  else r - dlt.

Definition extract_unspec {A : Set} (xs : list (option A))
  : option (list A) :=
  List.fold_left
    (fun (acc_opt : option (list A)) =>
     fun (c_opt : option A) =>
       match (acc_opt, c_opt) with
       | (None, _) => None
       | (_, None) => None
       | (Some acc, Some c_value) => Some (cons c_value acc)
       end) (List.rev xs) (Some []) .

Module Type CheriMemoryImpl
  (MC:Mem_common(AddressValue)(Bounds))
  (C:CAPABILITY_GS
       (AddressValue)
       (Flags)
       (ObjType)
       (SealType)
       (Bounds)
       (Permissions)
  )
  (IMP: Implementation)
  (TD: TagDefs)
  (SW: CerbSwitchesDefs)
<: Memory(AddressValue)(Bounds)(MC).

  Import MC.

  Definition name := "cheri-coq".

  Import MC.
  Include AilTypesAux(IMP).

  Definition storage_instance_id : Set := Z.
  Definition symbolic_storage_instance_id : Set := Z.
  Definition floating_value : Set := float. (* 64 bit *)

  Inductive function_pointer : Set :=
  | FP_valid : CoqSymbol.sym -> function_pointer
  | FP_invalid : C.t -> function_pointer.

  Inductive pointer_value_indt : Set :=
  | PVfunction : function_pointer -> pointer_value_indt
  | PVconcrete : C.t -> pointer_value_indt.

  Inductive integer_value_indt : Set :=
  | IV : Z -> integer_value_indt
  | IC : bool -> C.t -> integer_value_indt.

  Unset Elimination Schemes.
  (* This prevent default elimination principle from being generated for
     this type, as it is inadequate *)
  Inductive mem_value_with_err :=
  | MVEunspecified : CoqCtype.ctype -> mem_value_with_err
  | MVEinteger :
    CoqIntegerType.integerType -> integer_value_indt ->
    mem_value_with_err
  | MVEfloating :
    CoqCtype.floatingType -> floating_value ->
    mem_value_with_err
  | MVEpointer :
    CoqCtype.ctype -> pointer_value_indt -> mem_value_with_err
  | MVErr : mem_error -> mem_value_with_err
  | MVEarray : list mem_value_with_err -> mem_value_with_err
  | MVEstruct :
    CoqSymbol.sym ->
    list  (CoqSymbol.identifier *  CoqCtype.ctype * mem_value_with_err) ->
    mem_value_with_err
  | MVEunion :
    CoqSymbol.sym ->
    CoqSymbol.identifier -> mem_value_with_err ->
    mem_value_with_err.
  Set Elimination Schemes.

  (* Custom induction principle for mem_value_with_err *)
  Theorem mem_value_with_err_ind
    : forall P : mem_value_with_err -> Prop,
      (* base cases *)
      (forall c : CoqCtype.ctype, P (MVEunspecified c)) ->
      (forall (i : CoqIntegerType.integerType) (i0 : integer_value_indt), P (MVEinteger i i0)) ->
      (forall (f : CoqCtype.floatingType) (f0 : floating_value), P (MVEfloating f f0)) ->
      (forall (c : CoqCtype.ctype) (p : pointer_value_indt), P (MVEpointer c p)) ->
      (forall (e: mem_error), P (MVErr e)) ->
      (* recursive cases *)
      (forall l : list mem_value_with_err, List.Forall P l -> P (MVEarray l)) ->
      (forall (s : sym) (l : list (identifier * CoqCtype.ctype * mem_value_with_err)),
          List.Forall (fun '(_,_,b) => P b) l ->
          P (MVEstruct s l)) ->
      (forall (s : sym) (i : identifier) (m : mem_value_with_err), P m -> P (MVEunion s i m)) ->

      forall m : mem_value_with_err, P m.
  Proof.
    intros P H_unspecified H_integer H_floating H_pointer H_err H_array H_struct H_union.
    fix IH 1.
    destruct m.
    - apply H_unspecified.
    - apply H_integer.
    - apply H_floating.
    - apply H_pointer.
    - apply H_err.
    -
      apply H_array.
      induction l.
      constructor.
      constructor.
      apply IH.
      apply IHl.
    -
      apply H_struct.
      induction l.
      constructor.
      constructor.
      destruct a.
      destruct p.
      apply IH.
      apply IHl.
    - apply H_union.
      apply IH.
  Qed.

  Unset Elimination Schemes.
  (* This prevent default elimination principle from being generated for
     this type, as it is inadequate *)
  Inductive mem_value_indt :=
  | MVunspecified : CoqCtype.ctype -> mem_value_indt
  | MVinteger :
    CoqIntegerType.integerType -> integer_value_indt -> mem_value_indt
  | MVfloating :
    CoqCtype.floatingType -> floating_value -> mem_value_indt
  | MVpointer :
    CoqCtype.ctype -> pointer_value_indt -> mem_value_indt
  | MVarray : list mem_value_indt -> mem_value_indt
  | MVstruct :
    CoqSymbol.sym ->
    list (CoqSymbol.identifier * CoqCtype.ctype * mem_value_indt) -> mem_value_indt
  | MVunion :
    CoqSymbol.sym ->
    CoqSymbol.identifier -> mem_value_indt -> mem_value_indt.
  Set Elimination Schemes.

  (* Custom induction principle for mem_value_indt *)
  Theorem mem_value_indt_ind
    : forall P : mem_value_indt -> Prop,
      (* base cases *)
      (forall c : CoqCtype.ctype, P (MVunspecified c)) ->
      (forall (i : CoqIntegerType.integerType) (i0 : integer_value_indt), P (MVinteger i i0)) ->
      (forall (f : CoqCtype.floatingType) (f0 : floating_value), P (MVfloating f f0)) ->
      (forall (c : CoqCtype.ctype) (p : pointer_value_indt), P (MVpointer c p)) ->
      (* recursive cases *)
      (forall l : list mem_value_indt, List.Forall P l -> P (MVarray l)) ->
      (forall (s : sym) (l : list (identifier * CoqCtype.ctype * mem_value_indt)),
          List.Forall (fun '(_,_,b) => P b) l ->
          P (MVstruct s l)) ->
      (forall (s : sym) (i : identifier) (m : mem_value_indt), P m -> P (MVunion s i m)) ->

      forall m : mem_value_indt, P m.
  Proof.
    intros P H_unspecified H_integer H_floating H_pointer H_array H_struct H_union.
    fix IH 1.
    destruct m.
    - apply H_unspecified.
    - apply H_integer.
    - apply H_floating.
    - apply H_pointer.
    -
      apply H_array.
      induction l.
      constructor.
      constructor.
      apply IH.
      apply IHl.
    -
      apply H_struct.
      induction l.
      constructor.
      constructor.
      destruct a.
      destruct p.
      apply IH.
      apply IHl.
    - apply H_union.
      apply IH.
  Qed.

  Inductive access_intention : Set :=
  | ReadIntent : access_intention
  | WriteIntent : access_intention
  | CallIntent : access_intention.

  Inductive readonly_status : Set :=
  | IsWritable : readonly_status
  | IsReadOnly : readonly_kind -> readonly_status.

  (* Unfortunate names of two consturctors are mirroring ones from
     OCaml `Nondeterminism` monad. Third one is used where `failwith` was
     or `assert false` was used in OCaml. *)
  Inductive memMError :=
  | Other: mem_error -> memMError
  | Undef0: location_ocaml -> (list undefined_behaviour) -> memMError
  | InternalErr: string -> memMError.

  Record allocation :=
    {
      prefix : CoqSymbol.prefix;
      base : AddressValue.t;
      size : nat;
      ty : option CoqCtype.ctype;
      is_readonly : readonly_status;
      is_dynamic : bool ;
      is_dead : bool ; (* only used in cornucopia *)
    }.


  Definition pointer_value := pointer_value_indt.
  Definition integer_value := integer_value_indt.
  Definition mem_value := mem_value_indt.


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
    Build_allocation prefix r.(base) r.(size) r.(ty) r.(is_readonly) r.(is_dynamic) r.(is_dead).

  Definition allocation_with_dead (r : allocation) :=
    Build_allocation r.(prefix) r.(base) r.(size) r.(ty) r.(is_readonly) r.(is_dynamic) true.

  Definition allocation_with_is_readonly (r : allocation) ro :=
    Build_allocation r.(prefix) r.(base) r.(size) r.(ty) ro r.(is_dynamic) r.(is_dead).

  Record mem_state_r :=
    {
      next_alloc_id : storage_instance_id;
      last_address : AddressValue.t;
      allocations : ZMap.M.t allocation;
      funptrmap : ZMap.M.t
                    (digest * string * C.t);
      varargs : ZMap.M.t
                  (Z * list (CoqCtype.ctype * pointer_value));
      next_varargs_id : Z;
      bytemap : AMap.M.t (option ascii);
      capmeta : AMap.M.t (bool* CapGhostState);
    }.

  (*
     Copy of the state (for copy-and-pase) in absence of "with" notation

              {|
                next_alloc_id    := st.(next_alloc_id);
                last_address     := st.(last_address) ;
                allocations      := st.(allocations);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                capmeta          := st.(capmeta);
              |}
   *)

  Definition mem_state := mem_state_r.

  Definition mem_state_with_last_address last_address (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) last_address r.(allocations) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_bytemap bytemap (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) r.(funptrmap) r.(varargs) r.(next_varargs_id) bytemap r.(capmeta).

  Definition mem_state_with_allocations allocations (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) allocations r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_next_alloc_id next_alloc_id (r : mem_state) :=
    Build_mem_state_r next_alloc_id r.(last_address) r.(allocations) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_capmeta capmeta (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) capmeta.

  Definition mem_state_with_funptrmap funptrmap (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) funptrmap r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_varargs_next_varargs_id varargs next_varargs_id (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) r.(funptrmap) varargs next_varargs_id r.(bytemap) r.(capmeta).

  Definition mem_state_with_bytemap_capmeta bytemap capmeta (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) r.(funptrmap) r.(varargs) r.(next_varargs_id) bytemap capmeta.

  Definition mem_state_with_funptrmap_bytemap_capmeta funptrmap bytemap capmeta (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(last_address) r.(allocations) funptrmap r.(varargs) r.(next_varargs_id) bytemap capmeta.

  Definition initial_address := AddressValue.of_Z (HexString.to_Z "0xFFFFFFFFFFFF").

  Definition DEFAULT_FUEL:nat := 1000%nat. (* TODO maybe needs to be abstracted *)
  Definition MAX_STRFCAP_FORMAT_LEN := 4096%nat.

  Definition initial_mem_state : mem_state :=
    {|
      next_alloc_id := Z0;
      last_address := initial_address;
      allocations := ZMap.M.empty allocation;
      funptrmap := ZMap.M.empty (digest * string * C.t);
      varargs := ZMap.M.empty (Z * list (CoqCtype.ctype * pointer_value));
      next_varargs_id := Z0;
      bytemap := AMap.M.empty _;
      capmeta := AMap.M.empty _;
    |}.

  Definition memM := errS mem_state memMError.
  #[local] Instance memM_monad: Monad memM.
  Proof.
    typeclasses eauto.
  Defined.

  Definition mprint_msg (msg : string) : memM unit :=
    ret (print_msg msg).

  Definition serr2InternalErr {A: Type} (e:serr A): (memM A)
    := match e with
       | inr v => ret v
       | inl msg => raise (InternalErr msg)
       end.

  Definition option2memM {A: Type} (msg:string) (o:option A): (memM A)
    := match o with
       | Some v => ret v
       | None => raise (InternalErr msg)
       end.

  Definition fail {A:Type} loc err : memM A :=
    match undefinedFromMem_error err with
    | Some ub =>
        raise (Undef0 loc [ub])
    | None =>
        raise (Other err)
    end.

  Definition fail_noloc {A:Type} err : memM A :=
    fail (Loc_other "cherimem") err.

  Inductive merr :=
  | OK: merr
  | FAIL: location_ocaml -> mem_error -> merr.

  Definition merr2memM {A: Type} (v:A) (e:merr): (memM A)
    := match e with
       | OK => ret v
       | FAIL loc me => fail loc me
       end.

  Inductive footprint_kind :=
  | Write | Read.

  Inductive footprint_indt :=
  (* base address, size *)
  | FP: footprint_kind -> AddressValue.t -> nat -> footprint_indt.

  Definition footprint := footprint_indt.

  Definition cap_to_Z c := AddressValue.to_Z (C.cap_get_value c).

  Definition overlapping a b :=
    match a,b with
    | FP k1 b1 sz1, FP k2 b2 sz2 =>
        match k1, k2 with
        | Read, Read => false
        | _, _ =>
            let zb1 := AddressValue.to_Z b1 in
            let zb2 := AddressValue.to_Z b2 in
            negb
              ((zb1 + Z.of_nat sz1 <=? zb2)
               || (zb2 + Z.of_nat sz2 <=? zb1)
               || (sz1 =? 0)%nat
               || (sz2 =? 0)%nat
              )
        end
    end.

  Definition unwrap_cap_value n :=
    let ptraddr_bits := (Z.of_nat C.sizeof_ptraddr) * 8 in
    let min_v := Z.opp (Z.pow 2 (ptraddr_bits - 1)) in
    let max_v := (Z.pow 2 (ptraddr_bits - 1)) - 1 in
    if (n <=? min_v) && (n <=? max_v)
    then n
    else wrapI min_v max_v n.

  Definition num_of_int x :=
    match x with
    | IV n => n
    | IC is_signed c =>
        let n := (cap_to_Z c) in
        if is_signed then unwrap_cap_value n else n
    end.

  (* Aligns given addres down according to alignment *)
  Definition align_down (addr alignment:Z)
    := addr - (addr mod alignment).


  (* Crear new cap meta for region where all tags are unspecified *)
  Definition init_ghost_tags
    (addr: AddressValue.t)
    (size: nat)
    (capmeta: AMap.M.t (bool*CapGhostState)): AMap.M.t (bool*CapGhostState)
    :=
    match size with
    | O => capmeta
    | S size' =>
        let alignment := Z.of_nat (IMP.get.(alignof_pointer)) in
        let a0 := align_down (AddressValue.to_Z addr) alignment in
        let a1 := align_down (AddressValue.to_Z addr + (Z.of_nat size')) alignment in
        let n := Z.to_nat ((a1-a0)/alignment) in
        let v := (false, {| tag_unspecified := true; bounds_unspecified := false |}) in
        AMap.map_range_init (AddressValue.of_Z a0) (S n) alignment v capmeta
    end.

  (** "Ghost" capability existing tags for memory region starting from [addr]
      with [size].

      All "true" tags associated with addresses in this region will be
      marked as unspecified.

      All "false" tags will be left intact.
   *)
  Definition capmeta_ghost_tags
    (addr: AddressValue.t)
    (size: nat)
    (capmeta: AMap.M.t (bool*CapGhostState)): AMap.M.t (bool*CapGhostState)
    :=
    match size with
    | O => capmeta
    | S size' =>
        let alignment := Z.of_nat (IMP.get.(alignof_pointer)) in
        let a0 := align_down (AddressValue.to_Z addr) alignment in
        let a1 := align_down (AddressValue.to_Z addr + (Z.of_nat size')) alignment in
        AMap.M.mapi
          (fun (a:AddressValue.t) '(t, gs) =>
             let az := AddressValue.to_Z a in
             if negb gs.(tag_unspecified) && t && (az >=? a0) && (az <=? a1)
             then
               (true, {| tag_unspecified := true; bounds_unspecified := gs.(bounds_unspecified) |})
             else
               (t, gs)
          ) capmeta
    end.

  Definition allocator
    (size: nat)
    (align: Z)
    (is_dynamic: bool)
    (pref: CoqSymbol.prefix)
    (ty: option CoqCtype.ctype)
    (ro_status: readonly_status)
    : memM (storage_instance_id * AddressValue.t)
    :=
    st <- get ;;
    let alloc_id := st.(next_alloc_id) in

    let z := AddressValue.to_Z st.(last_address) - Z.of_nat size in
    if z <? 0 then
      fail_noloc (MerrOther "allocator: failed (out of memory)") (* before alignment *)
    else
      let r := z mod align in
      if r >? z then
        fail_noloc (MerrOther "allocator: failed (out of memory)") (* afer alignment *)
      else
        let addr := z - r in
        put (
            let alloc :=
              {|
                prefix := pref;
                base:= (AddressValue.of_Z addr);
                size:= size;
                ty:= ty;
                is_dynamic := is_dynamic;
                is_dead := false;
                is_readonly:= ro_status;
              |}
            in
            {|
              next_alloc_id    := Z.succ st.(next_alloc_id);
              last_address     := AddressValue.of_Z addr;
              allocations      := ZMap.M.add alloc_id alloc st.(allocations);
              funptrmap        := st.(funptrmap);
              varargs          := st.(varargs);
              next_varargs_id  := st.(next_varargs_id);
              bytemap          := st.(bytemap);
              capmeta          := (init_ghost_tags (AddressValue.of_Z addr) size st.(capmeta));
            |})
        ;;
        (* mprint_msg ("Alloc: " ++ String.hex_str addr ++ " (" ++ String.dec_str size ++ ")" ) ;; *)
        ret (alloc_id, (AddressValue.of_Z addr)).

  Definition alignof
    (fuel: nat)
    (maybe_tagDefs : option (SymMap.t CoqCtype.tag_definition))
    (ty: CoqCtype.ctype): serr nat
    :=
    let tagDefs :=
      match maybe_tagDefs with
      | Some x => x
      | None => TD.tagDefs tt
      end in
    let fix alignof_ (fuel: nat) ty  :=
      match fuel with
      | O => raise "alignof out of fuel"
      | S fuel =>
          match ty with
          | CoqCtype.Ctype _ CoqCtype.Void => raise "no alignment for void"
          | CoqCtype.Ctype _ (CoqCtype.Basic (CoqCtype.Integer ity)) =>
              ret (IMP.get.(alignof_ity) ity)
          | CoqCtype.Ctype _ (CoqCtype.Basic (CoqCtype.Floating fty)) =>
              ret (IMP.get.(alignof_fty) fty)
          | CoqCtype.Ctype _ (CoqCtype.Array elem_ty _) =>
              alignof_ fuel elem_ty
          |
            (CoqCtype.Ctype _ (CoqCtype.Function _ _ _) |
              CoqCtype.Ctype _ (CoqCtype.FunctionNoParams _)) =>
              raise "no alighment for function types"
          | CoqCtype.Ctype _ (CoqCtype.Pointer _ _) =>
              ret (IMP.get.(alignof_pointer))
          | CoqCtype.Ctype _ (CoqCtype.Atomic atom_ty) =>
              alignof_ fuel  atom_ty
          | CoqCtype.Ctype _ (CoqCtype.Struct tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (CoqCtype.UnionDef _) =>
                  raise "no alignment for struct with union tag"
              | Some (CoqCtype.StructDef membrs flexible_opt) =>
                  init <-
                    match flexible_opt with
                    | None => ret 0%nat
                    | Some (CoqCtype.FlexibleArrayMember _ _ _ elem_ty) =>
                        alignof_ fuel (CoqCtype.Ctype [] (CoqCtype.Array elem_ty None))
                    end ;;
                  monadic_fold_left
                    (fun acc '(_, (_, _, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       ret (Nat.max al acc)
                    )
                    membrs
                    init
              | None => raise "could not find struct tag to compute alignment"
              end
          | CoqCtype.Ctype _ (CoqCtype.Union tag_sym) =>
              match SymMap.find tag_sym tagDefs with
              | Some (CoqCtype.StructDef _ _) =>
                  raise "no alignment for union with struct tag"
              | Some (CoqCtype.UnionDef membrs) =>
                  monadic_fold_left
                    (fun acc '(_, (_, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       ret (Nat.max al acc)
                    )
                    membrs
                    0%nat
              | None => raise "could not find union tag to compute alignment"
              end
          end
      end
    in alignof_ fuel ty.

  Fixpoint offsetsof_struct
    (fuel: nat)
    (tagDefs : SymMap.t CoqCtype.tag_definition)
    (tag_sym : CoqSymbol.sym)
    :=
    match fuel with
    | O => raise "offsetof out of fuel"
    | S fuel =>
        match SymMap.find tag_sym tagDefs with
        | Some (CoqCtype.StructDef members flexible_opt) =>
            sassert (Nat.ltb 0 (List.length members)) "Empty struct encountered" ;;
            let members :=
              match flexible_opt with
              | None => members
              | Some (CoqCtype.FlexibleArrayMember attrs ident qs ty) =>
                  members ++ [ (ident, (attrs, None, qs, ty)) ]
              end
            in
            '(xs, maxoffset) <-
              monadic_fold_left
                (fun '(xs, last_offset) '(membr, (_, _, _, ty))  =>
                   size  <- sizeof fuel (Some tagDefs) ty ;;
                   align <- alignof fuel (Some tagDefs) ty ;;
                   let x_value := Nat.modulo last_offset align in
                   let pad :=
                     if Nat.eqb x_value O
                     then O
                     else (align - x_value)%nat in
                   ret ((membr, ty, (last_offset + pad)%nat)::xs, (last_offset+pad+size)%nat)
                ) members ([], O) ;;
            ret (List.rev xs, maxoffset)
        | _ => raise "struct tagdefs mismatch"
        end
    end
  with sizeof
         (fuel: nat)
         (maybe_tagDefs : option (SymMap.t CoqCtype.tag_definition))
    : CoqCtype.ctype -> serr nat
       :=
         match fuel with
         | O => fun _ => raise "sizeof out of fuel"
         | S fuel =>
             let tagDefs :=
               match maybe_tagDefs with
               | Some x => x
               | None => TD.tagDefs tt
               end in
             fun (function_parameter : CoqCtype.ctype) =>
               let '(CoqCtype.Ctype _ ty) as cty := function_parameter in
               match ty with
               | (CoqCtype.Void | CoqCtype.Array _ None |
                   CoqCtype.Function _ _ _ |
                   CoqCtype.FunctionNoParams _) =>
                   raise "no sizeof for function types"
               | CoqCtype.Basic (CoqCtype.Integer ity) =>
                   option2serr "sizeof_ity not defined in Implementation" (IMP.get.(sizeof_ity) ity)
               | CoqCtype.Basic (CoqCtype.Floating fty) =>
                   option2serr "sizeof_fty not defined in Implementation" (IMP.get.(sizeof_fty) fty)
               | CoqCtype.Array elem_ty (Some asize) =>
                   sassert (Nat.ltb 0 asize) "Zero array size encountered" ;;
                   sz <- sizeof fuel (Some tagDefs) elem_ty ;;
                   ret (asize * sz)%nat
               | CoqCtype.Pointer _ _ =>
                   ret (IMP.get.(sizeof_pointer))
               | CoqCtype.Atomic atom_ty =>
                   sizeof fuel (Some tagDefs) atom_ty
               | CoqCtype.Struct tag_sym =>
                   '(_, max_offset) <- offsetsof_struct fuel tagDefs tag_sym ;;
                   align <- alignof fuel (Some tagDefs) cty ;;
                   let x_value := Nat.modulo max_offset align in
                   ret (if Nat.eqb x_value 0%nat
                        then max_offset
                        else (max_offset + (align - x_value))%nat)
               | CoqCtype.Union tag_sym =>
                   match SymMap.find tag_sym tagDefs with
                   | Some (CoqCtype.StructDef _ _) =>
                       raise "no alignment for struct with union tag"
                   | Some (CoqCtype.UnionDef members) =>
                       sassert (Nat.ltb 0 (List.length members)) "Empty union encountered" ;;
                       '(max_size, max_align) <-
                         monadic_fold_left
                           (fun '(acc_size, acc_align) '(_, (_, _, ty)) =>
                              sz <- sizeof fuel (Some tagDefs) ty ;;
                              al <- alignof fuel (Some tagDefs) ty ;;
                              ret (Nat.max acc_size sz, Nat.max acc_align al)
                           )
                           members (0%nat, 0%nat) ;;
                       let x_value := Nat.modulo max_size max_align in
                       ret (if Nat.eqb x_value 0%nat
                            then max_size
                            else (max_size + (max_align - x_value)))%nat
                   | None => raise "could not find union tag to compute sizeof"
                   end
               end
         end.

  Definition offsetof_union
    (members: list
                (identifier * (CoqAnnot.attributes * option CoqCtype.alignment * CoqCtype.qualifiers * CoqCtype.ctype)))
    : serr (list (CoqSymbol.identifier * CoqCtype.ctype * nat) * nat)
    :=
    ret ((List.map (fun '(ident, (_, _, _, ty)) => (ident, ty, O)) members), O).

  Definition offsetsof
    (fuel: nat)
    (tagDefs : SymMap.t CoqCtype.tag_definition)
    (tag_sym : CoqSymbol.sym)
    : serr (list (CoqSymbol.identifier * CoqCtype.ctype * nat) * nat)
    :=
    match SymMap.find tag_sym tagDefs with
    | Some (CoqCtype.StructDef members flexible_opt) =>
        offsetsof_struct fuel tagDefs tag_sym
    | Some (CoqCtype.UnionDef members) =>
        offsetof_union members
    | None => raise "could not find tag"
    end.

  Definition resolve_function_pointer
    (funptrmap : ZMap.M.t (digest * string * C.t))
    (fp : function_pointer)
    : ZMap.M.t (digest * string * C.t) * C.t
    :=
    match fp with
    | FP_valid (CoqSymbol.Symbol file_dig n opt_name) =>
        match ZMap.M.find n funptrmap with
        | Some (_, _, c) => (funptrmap, c)
        | None =>
            let c := C.alloc_fun (AddressValue.of_Z (AddressValue.to_Z initial_address+ n)) in
            (match opt_name with
             | CoqSymbol.SD_Id name =>
                 ZMap.M.add n (file_dig, name, c) funptrmap
             | _ => funptrmap
             end, c)
        end
    | FP_invalid c => (funptrmap, c)
    end.

  Definition is_pointer_algined (addr : AddressValue.t) : bool :=
    let align := IMP.get.(alignof_pointer) in
    (AddressValue.to_Z addr) mod (Z.of_nat align) =? 0.

  Fixpoint typeof (mval : mem_value)
    : serr CoqCtype.ctype :=
    ct <-
      match mval with
      | MVunspecified (CoqCtype.Ctype _ ty) => ret ty
      | MVinteger ity _ =>
          ret (CoqCtype.Basic (CoqCtype.Integer ity))
      | MVfloating fty _ =>
          ret (CoqCtype.Basic (CoqCtype.Floating fty))
      | MVpointer ref_ty _ =>
          ret (CoqCtype.Pointer CoqCtype.no_qualifiers ref_ty)
      | MVarray [] =>
          raise "ill-formed value"
      | MVarray ((mval::_) as mvals) =>
          mt <- typeof mval ;;
          ret (CoqCtype.Array mt (Some (List.length mvals)))
      | MVstruct tag_sym _ => ret (CoqCtype.Struct tag_sym)
      | MVunion tag_sym _ _ => ret (CoqCtype.Union tag_sym)
      end ;;
    ret (CoqCtype.Ctype [] ct).


  (** Update [capmeta] dictionary for capability [c] stored at [addr]. *)
  Definition update_capmeta
    (c: C.t)
    (addr: AddressValue.t)
    (capmeta : AMap.M.t (bool*CapGhostState))
    : AMap.M.t (bool*CapGhostState)
    :=
    AMap.M.add addr (C.cap_is_valid c, C.get_ghost_state c) capmeta.

  Fixpoint repr
    (fuel: nat)
    (addr : AddressValue.t)
    (mval : mem_value)
    (s: mem_state)
    : serr (mem_state * AddressValue.t)
    :=
    match fuel with
    | O => raise "out of fuel in repr"
    | S fuel =>
        match mval with
        | MVunspecified ty =>
            sz <- sizeof DEFAULT_FUEL None ty ;;
            sassert ((AddressValue.to_Z addr + (Z.of_nat sz)) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
            let bs := List.repeat None sz in
            ret (mem_state_with_bytemap_capmeta
                   (AMap.map_add_list_at s.(bytemap) bs addr)
                   (capmeta_ghost_tags addr sz (capmeta s))
                   s
                ,
                AddressValue.with_offset addr (Z.of_nat sz))
        | MVinteger ity (IV ivalue) =>
            iss <- option2serr "Could not get int signedness of a type in repr" (is_signed_ity DEFAULT_FUEL ity) ;;
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype [] (CoqCtype.Basic (CoqCtype.Integer ity))) ;;
            bs' <- bytes_of_Z iss sz ivalue ;;
            let bs := List.map (Some) bs' in
            sassert (AddressValue.to_Z addr + (Z.of_nat (length bs)) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;

            ret (mem_state_with_bytemap_capmeta
                   (AMap.map_add_list_at s.(bytemap) bs addr)
                   (capmeta_ghost_tags addr (List.length bs) (capmeta s))
                   s
                ,
                AddressValue.with_offset addr (Z.of_nat sz))
        | MVinteger ity (IC _ c)
          =>
            match ity with
            | CoqIntegerType.Signed CoqIntegerType.Intptr_t
            | CoqIntegerType.Unsigned CoqIntegerType.Intptr_t
              =>
                '(cb, ct) <- option2serr "int encoding error" (C.encode true c) ;;
                let sz := length cb in
                sassert (is_pointer_algined addr) "unaligned pointer to cap" ;;
                sassert (AddressValue.to_Z addr + (Z.of_nat sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;

                let cm := update_capmeta c addr (capmeta s) in
                let bs := List.map (Some) cb in
                ret (mem_state_with_bytemap_capmeta
                       (AMap.map_add_list_at s.(bytemap) bs addr)
                       cm
                       s
                    ,
                    AddressValue.with_offset addr (Z.of_nat sz))
            | _ =>
                raise "invalid integer value (capability for non-(u)intptr_t"
            end
        | MVfloating fty fval =>
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype [] (CoqCtype.Basic (CoqCtype.Floating fty))) ;;
            sassert (AddressValue.to_Z addr + (Z.of_nat sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
            bs' <- bytes_of_Z true sz (bits_of_float fval) ;;
            let bs := List.map (Some) bs' in
            ret (mem_state_with_bytemap_capmeta
                   (AMap.map_add_list_at s.(bytemap) bs addr)
                   (capmeta_ghost_tags addr sz (capmeta s))
                   s
                ,
                AddressValue.with_offset addr (Z.of_nat sz))
        | MVpointer ref_ty ptrval_ =>
            match ptrval_ with
            | PVfunction
                ((FP_valid (CoqSymbol.Symbol file_dig n_value opt_name)) as
                  fp) =>
                let '(fm, c_value) := resolve_function_pointer (funptrmap s) fp in
                '(cb, ct) <- option2serr "valid function pointer encoding error" (C.encode true c_value) ;;
                sassert (is_pointer_algined addr) "unaligned pointer to cap" ;;
                let sz := length cb in
                sassert (AddressValue.to_Z addr + (Z.of_nat sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
                let cm := update_capmeta c_value addr (capmeta s) in
                let bs := List.map (Some) cb in
                ret (mem_state_with_funptrmap_bytemap_capmeta
                       fm
                       (AMap.map_add_list_at s.(bytemap) bs addr)
                       cm
                       s
                    ,
                    AddressValue.with_offset addr (Z.of_nat sz))
            | (PVfunction (FP_invalid c) | PVconcrete c) =>
                '(cb, ct) <- option2serr "pointer encoding error" (C.encode true c) ;;
                sassert (is_pointer_algined addr) "unaligned pointer to cap" ;;
                let sz := length cb in
                sassert (AddressValue.to_Z addr + (Z.of_nat sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
                let cm := update_capmeta c addr (capmeta s) in
                let bs := List.map (Some) cb in
                ret (mem_state_with_bytemap_capmeta
                       (AMap.map_add_list_at s.(bytemap) bs addr)
                       cm
                       s
                    ,
                    AddressValue.with_offset addr (Z.of_nat sz))
            end
        | MVarray mvals =>
            monadic_fold_left
              (fun '(s', addr') (mval': mem_value) => repr fuel addr' mval' s')
              mvals (s, addr)
        | MVunion tag_sym memb_ident mval =>
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype [] (CoqCtype.Union tag_sym)) ;;
            sassert (AddressValue.to_Z addr + (Z.of_nat sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
            '(s', pad_addr) <- repr fuel addr mval s ;;
            let pad_size := Nat.sub sz (Z.to_nat (AddressValue.to_Z pad_addr - AddressValue.to_Z addr)) in
            let pad_bs := List.repeat None pad_size in
            let s'' := mem_state_with_bytemap
                         (AMap.map_add_list_at s'.(bytemap) pad_bs pad_addr)
                         s' in
            ret (s'', AddressValue.with_offset pad_addr (Z.of_nat pad_size))
        | MVstruct tag_sym xs =>
            szn <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype [] (CoqCtype.Struct tag_sym)) ;;
            let sz := Z.of_nat szn in
            sassert ((AddressValue.to_Z addr + sz) <=? AddressValue.ADDR_LIMIT) "The object does not fit in the address space" ;;
            let padding_byte := None in
            '(offs, final_off) <- offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym ;;
            let final_pad_size := sz - (Z.of_nat final_off) in

            '(s', final_pad_addr) <-
              monadic_fold_left2
                (fun '(s0, addr0) '(ident, ty, off) '(_, _, mval) =>
                   (*  off - offset of this field from the start of struct, *after* padding *)
                   let value_a := AddressValue.with_offset addr (Z.of_nat off) in
                   let pad_size := AddressValue.to_Z value_a - AddressValue.to_Z addr0 in
                   (* write padding *)
                   (* TODO: What if padding/offsets big enough to fit a capability? should we ghost/clear tags? *)
                   let pad_bs := List.repeat padding_byte (Z.to_nat pad_size) in
                   let s1 := mem_state_with_bytemap
                               (AMap.map_add_list_at s0.(bytemap) pad_bs addr0)
                               s0 in
                   (* write the value *)
                   '(s2, end_addr) <- repr fuel value_a mval s1 ;;
                   szn <- sizeof DEFAULT_FUEL None ty ;;
                   ret (s2, AddressValue.with_offset value_a (Z.of_nat szn)))

                (s, addr) offs xs ;;

            let final_pad_bs := List.repeat padding_byte (Z.to_nat final_pad_size) in
            let s'' := mem_state_with_bytemap
                         (AMap.map_add_list_at s'.(bytemap) final_pad_bs final_pad_addr)
                         s' in
            ret (s'', AddressValue.with_offset final_pad_addr final_pad_size)
        end
    end.

  Definition allocate_region
    (tid : MC.thread_id)
    (pref : CoqSymbol.prefix)
    (align_int : integer_value)
    (size_int : integer_value)
    : memM pointer_value
    :=
    let size_n := num_of_int size_int in
    if size_n <? 0
    then raise (InternalErr "negative size passed to allocate_region")
    else
      let align_n := num_of_int align_int in
      if align_n <=? 0
      then raise (InternalErr "non-positive aligment passed to allocate_region")
      else
        let mask := C.representable_alignment_mask size_n in
        let size_n' := C.representable_length size_n in
        let align_n' :=
          Z.max align_n (Z.succ (AddressValue.to_Z (AddressValue.bitwise_complement (AddressValue.of_Z mask)))) in

        '(alloc_id, addr) <- allocator (Z.to_nat size_n') align_n' true CoqSymbol.PrefMalloc None IsWritable ;;
        let c_value := C.alloc_cap addr (AddressValue.of_Z size_n') in
        ret (PVconcrete c_value).

  Definition allocate_object
    (tid: MC.thread_id)
    (pref: CoqSymbol.prefix)
    (int_val: integer_value)
    (ty: CoqCtype.ctype)
    (init_opt: option mem_value)
    : memM pointer_value
    :=
    let align_n := num_of_int int_val in
    if align_n <=? 0
      then raise (InternalErr "non-positive aligment passed to allocate_object")
    else
      size_n <- serr2InternalErr (sizeof DEFAULT_FUEL None ty) ;;
      let size_z := Z.of_nat size_n in
      let mask := C.representable_alignment_mask size_z in
      let size_z' := C.representable_length size_z in
      let size_n' := Z.to_nat size_z' in
      let align_n' := Z.max align_n (1 + (AddressValue.to_Z (AddressValue.bitwise_complement (AddressValue.of_Z mask)))) in

      (*
    (if (negb ((size_n =? size_n') && (align_n =? align_n')))
    then
      mprint_msg
          ("allocate_object CHERI size/alignment adusted. WAS: " ++
            ", size= " ++ String.dec_str size_n ++
              ", align= " ++ String.dec_str align_n ++
                "BECOME: " ++
                  ", size= " ++ String.dec_str size_n' ++
                    ", align= " ++ String.dec_str align_n')
    else ret tt) ;;
       *)

      (match init_opt with
       | None =>
           '(alloc_id, addr) <- allocator size_n' align_n' false pref (Some ty) IsWritable ;;
           ret (alloc_id, addr, false)
       | Some mval =>  (* here we allocate an object with initiliazer *)
           let (ro,readonly_status) :=
             match pref with
             | CoqSymbol.PrefStringLiteral _ _ => (true, IsReadOnly ReadonlyStringLiteral)
             | CoqSymbol.PrefTemporaryLifetime _ _ =>
                 (true, IsReadOnly ReadonlyTemporaryLifetime)
             | _ =>
                 (true, IsReadOnly ReadonlyConstQualified)
                   (* | _ => (false,IsWritable) *)
             end
           in
           '(alloc_id, addr) <- allocator size_n' align_n' false pref (Some ty) readonly_status ;;
           (* We should be careful not to introduce a state change here
              in case of error which happens after the [allocator]
              invocation, as [allocator] modifies state. In the current
              implementation, this is not happening, as errors are handled
              as [InternalErr] which supposedly should terminate program
              evaluation.  *)
           s <- get ;;
           '(s',_) <- serr2InternalErr (repr DEFAULT_FUEL addr mval s) ;;
           put s' ;;
           ret (alloc_id, addr, ro)
       end)
        >>=
        fun '(alloc_id, addr, ro)  =>
          let c := C.alloc_cap addr (AddressValue.of_Z size_z') in
          let c :=
            if ro then
              let p := C.cap_get_perms c in
              let p := Permissions.perm_clear_store p in
              let p := Permissions.perm_clear_store_cap p in
              let p := Permissions.perm_clear_store_local_cap p in
              C.cap_narrow_perms c p
            else c
          in
          ret (PVconcrete c).


  Definition cap_is_null  (c : C.t) : bool :=
    cap_to_Z c =? 0.

  (* Find first live allocation with given starting addrress. We need
     to check for liveness here, instead of later as multiple dead
     allocations may correspond to given address.
   *)
  Definition find_live_allocation (addr:AddressValue.t) : memM (option (storage_instance_id*allocation)) :=
    st <- get ;;
        ret
          (ZMap.M.fold (fun alloc_id alloc acc =>
                        match acc with
                        | None =>
                            if AddressValue.eqb alloc.(base) addr && negb alloc.(is_dead)
                            then Some (alloc_id,alloc)
                            else None
                        | Some _ => acc
                        end
             ) st.(allocations) None).

  (* private *)
  Definition is_dynamic_addr (addr:AddressValue.t) : memM bool :=
    find_live_allocation addr >>= fun x =>
        match x with
        | None => ret false
        | Some (_,alloc) =>
            ret alloc.(is_dynamic)
        end.

  (*

    Check if given cap is matches exactly a cap retruned by one of
    previous dynamic allocations.

    1. The allocation must be dynamic
    2. Bounds must exactly span allocation
    3. Address must be equal to the beginning of allocation
    4. Permissions must be the same as returned by allocator

    TODO: assumes that [C.cap_get_value c = fst (C.cap_get_bounds c) ]
   *)
  Definition cap_match_dyn_allocation c alloc : bool :=
    let gs := C.get_ghost_state c in
    (* We check here only [tag_unspecified] because setting [bounds_unspecified]
       always concides with setting [tag_unspecified] as well *)
    (negb gs.(tag_unspecified)) &&
      (Permissions.eqb (C.cap_get_perms c) Permissions.perm_alloc
       && alloc.(is_dynamic)
       && AddressValue.eqb alloc.(base) (C.cap_get_value c)
       && (let zbounds := Bounds.to_Zs (C.cap_get_bounds c) in
           let csize := (snd zbounds) - (fst zbounds) in
           (Z.of_nat alloc.(size)) =? csize)).

  Definition remove_allocation (alloc_id : Z) : memM unit :=
    update (fun st =>
              {|
                next_alloc_id    := st.(next_alloc_id);
                last_address     := st.(last_address) ;
                allocations      := ZMap.M.remove alloc_id st.(allocations);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                capmeta          := st.(capmeta);
              |}).

  Definition get_allocation_opt (alloc_id : Z) : memM (option allocation) :=
    st <- get ;; ret (ZMap.M.find alloc_id st.(allocations)).

  Definition get_allocation (alloc_id : Z) : memM allocation :=
    st <- get ;;
    match ZMap.M.find alloc_id st.(allocations) with
    | Some v => ret v
    | None =>
        fail_noloc (MerrOutsideLifetime
                      (String.append "get_allocation, alloc_id="
                         (of_Z alloc_id)))
    end.

  Definition is_dead_allocation (alloc_id : storage_instance_id) : memM bool :=
    st <- get ;;
    match ZMap.M.find alloc_id st.(allocations) with
    | Some a => ret a.(is_dead)
    | None => ret true
    end.

  (** Convert an arbitrary integer value to unsinged cap value *)
  Definition wrap_cap_value (n_value : Z) : Z :=
    if (n_value <=? (AddressValue.to_Z C.min_ptraddr)) && (n_value <=? (AddressValue.to_Z C.max_ptraddr))
    then n_value
    else  wrapI (AddressValue.to_Z C.min_ptraddr) (AddressValue.to_Z C.max_ptraddr) n_value.

  Fixpoint abst
    (fuel: nat)
    (find_allocation : C.t -> option (storage_instance_id * allocation))
    (funptrmap : ZMap.M.t (digest * string * C.t))
    (tag_query_f : AddressValue.t -> (bool* CapGhostState))
    (addr : AddressValue.t)
    (cty : CoqCtype.ctype)
    (bs : list (option ascii))
    : serr (mem_value_with_err * list (option ascii))
    :=
    match fuel with
    | O => raise "abst out of fuel"
    | S fuel =>
        let '(CoqCtype.Ctype _ ty) := cty in
        let self f := abst f find_allocation funptrmap tag_query_f in
        sz <- sizeof DEFAULT_FUEL None cty ;;
        sassert (negb (Nat.ltb (List.length bs) sz)) "abst, |bs| < sizeof(ty)" ;;
        match ty with
        | (CoqCtype.Void | CoqCtype.Array _ None |
            CoqCtype.Function _ _ _ |
            CoqCtype.FunctionNoParams _) =>
            raise "abst on function!"
        | (CoqCtype.Basic (CoqCtype.Integer ((CoqIntegerType.Signed CoqIntegerType.Intptr_t) as ity))
          | CoqCtype.Basic (CoqCtype.Integer ((CoqIntegerType.Unsigned CoqIntegerType.Intptr_t) as ity)))
          =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at sz bs in
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            let _:bool := iss in (* hack to hint type checker *)
            match extract_unspec bs1 with
            | Some cs =>
                ret (
                    let (tag,gs) := tag_query_f addr in
                    match C.decode cs tag with
                    | None => MVErr (MerrCHERI CheriErrDecodingCap)
                    | Some c_value =>
                        let c_value := C.set_ghost_state c_value gs in
                        if iss then
                          let n_value := C.cap_get_value c_value in
                          let c_value := C.cap_set_value c_value (AddressValue.of_Z (wrap_cap_value (AddressValue.to_Z n_value))) in
                          MVEinteger ity (IC true c_value)
                        else
                          MVEinteger ity (IC false c_value)
                    end
                      , bs2)
            | None => ret (MVEunspecified cty, bs)
            end
        | CoqCtype.Basic (CoqCtype.Floating fty) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at sz bs in
            match extract_unspec bs1 with
            | Some cs =>
                zb <- Z_of_bytes true cs ;;
                ret (MVEfloating fty (float_of_bits zb), bs2)
            | None => ret (MVEunspecified cty, bs2)
            end
        | CoqCtype.Basic (CoqCtype.Integer ity) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at sz bs in
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            match extract_unspec bs1 with
            | Some cs =>
                zb <- Z_of_bytes iss cs ;;
                ret (MVEinteger ity (IV zb), bs2)
            | None =>
                ret (MVEunspecified cty, bs2)
            end
        | CoqCtype.Array elem_ty (Some n_value) =>
            let fix aux (n_value : nat) mval_acc (cs : list (option ascii))
              : serr (mem_value_with_err * list (option ascii))
              :=
              match n_value with
              | O => ret ((MVEarray (List.rev mval_acc)), cs)
              | S n_value =>
                  sz <- sizeof DEFAULT_FUEL None elem_ty ;;
                  let el_addr := AddressValue.with_offset addr (Z.of_nat (n_value * sz)%nat) in
                  '(mval, cs') <- self fuel el_addr elem_ty cs ;;
                  aux n_value (mval::mval_acc) cs'
              end
            in
            aux n_value [] bs
        | CoqCtype.Pointer _ ref_ty =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at sz bs in
            match extract_unspec bs1 with
            | Some cs =>
                let (tag,gs) := tag_query_f addr in
                match C.decode cs tag with
                | None => ret (MVErr (MerrCHERI CheriErrDecodingCap), bs2)
                | Some c_value =>
                    let c_value := C.set_ghost_state c_value gs in
                    match ref_ty with
                    | CoqCtype.Ctype _ (CoqCtype.Function _ _ _) =>
                        let n_value := cap_to_Z c_value - (AddressValue.to_Z initial_address) in
                        match ZMap.M.find n_value funptrmap with
                        | Some (file_dig, name, c') =>
                            if C.eqb c_value c' then
                              ret (MVEpointer ref_ty
                                              (PVfunction
                                                    (FP_valid
                                                       (CoqSymbol.Symbol file_dig
                                                          n_value
                                                          (CoqSymbol.SD_Id name)))), bs2)
                            else
                              ret (MVEpointer ref_ty
                                              (PVfunction (FP_invalid c_value)), bs2)
                        | None =>
                            ret (MVEpointer ref_ty
                                            (PVfunction (FP_invalid c_value)), bs2)
                        end
                    | _ =>
                        ret (MVEpointer ref_ty (PVconcrete c_value), bs2)
                    end
                end
            | None =>
                ret (MVEunspecified (CoqCtype.Ctype [] (CoqCtype.Pointer CoqCtype.no_qualifiers ref_ty)), bs2)
            end
        | CoqCtype.Atomic atom_ty =>
            self fuel addr atom_ty bs
        | CoqCtype.Struct tag_sym =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            '(offsets,_) <- offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym ;;
            let '(bs1, bs2) := split_at sz bs in
            '(rev_xs, _, bs') <-
              monadic_fold_left
                (fun '(acc_xs, previous_offset, acc_bs) '(memb_ident, memb_ty, memb_offset) =>
                   let pad := (memb_offset - previous_offset)%nat in
                   let memb_addr := AddressValue.with_offset addr (Z.of_nat memb_offset) in
                   '(mval, acc_bs') <-
                     self fuel memb_addr memb_ty (List.skipn pad acc_bs) ;;
                   sz <- sizeof DEFAULT_FUEL None memb_ty ;;
                   ret ((memb_ident, memb_ty, mval)::acc_xs,
                       (memb_offset + sz)%nat, acc_bs'))
                offsets
                ([], O, bs1)
            ;;
            ret (MVEstruct tag_sym (List.rev rev_xs), bs2)
        | CoqCtype.Union tag_sym =>
            raise "TODO: abst, Union (as value)"
        end
    end.

  Definition fetch_bytes
    (bytemap : AMap.M.t (option ascii))
    (base_addr : AddressValue.t)
    (n_bytes : nat)
    :
    list (option ascii)
    :=
    List.map
      (fun (addr : AddressValue.t) =>
         match AMap.M.find addr bytemap with
         | Some b_value => b_value
         | None => None
         end)
      (list_init n_bytes
         (fun (i : nat) => AddressValue.with_offset base_addr (Z.of_nat i))).

  Fixpoint mem_value_strip_err
    (loc : location_ocaml)
    (x_value : mem_value_with_err)
    : memM mem_value
    :=
    match x_value with
    | MVEunspecified x_value => ret (MVunspecified x_value)
    | MVEinteger x_value y_value => ret (MVinteger x_value y_value)
    | MVEfloating x_value y_value => ret (MVfloating x_value y_value)
    | MVEpointer x_value y_value => ret (MVpointer x_value y_value)
    | MVEarray l_value =>
        mapT (mem_value_strip_err loc) l_value >>=
          (fun (x_value : list mem_value) => ret (MVarray x_value))
    | MVEstruct x_value y_value =>
        mapT
          (fun '(x_value, y_value, z_value) =>
             (mem_value_strip_err loc z_value) >>=
               (fun (z' : mem_value) => ret (x_value, y_value, z')))
          y_value
          >>=
          (fun y' =>ret (MVstruct x_value y'))
    | MVEunion x_value y_value z_value =>
        mem_value_strip_err loc z_value >>=
          (fun (z' : mem_value) => ret (MVunion x_value y_value z'))
    | MVErr err => fail loc err
    end.

  (** Find the first live allocation which fully contains the bounds of the given capability. *)
  Definition find_cap_allocation_st st c : option (storage_instance_id * allocation)
    :=
    let (cbase,climit) := Bounds.to_Zs (C.cap_get_bounds c) in
    let csize := climit - cbase in

    ZMap.map_find_first
      (fun alloc_id alloc =>
         let abase := AddressValue.to_Z alloc.(base) in
         let asize := Z.of_nat alloc.(size) in
         let alimit := abase + asize in

         (negb alloc.(is_dead))
         && ((abase <=? cbase) && (cbase <? alimit))
      ) st.(allocations).

  (** Find the first live allocation which fully contains the bounds of the given capability. *)
  Definition find_cap_allocation c : memM (option (storage_instance_id * allocation))
    :=  st <- get ;; ret (find_cap_allocation_st st c).

  (* Check whether this cap base address is within allocation *)
  Definition cap_bounds_within_alloc_bool (c:C.t) a : bool
    :=
    let alloc_base := AddressValue.to_Z a.(base) in
    let alloc_limit := alloc_base + Z.of_nat a.(size) in
    let ptr_base := fst (Bounds.to_Zs (C.cap_get_bounds c)) in
    (alloc_base <=? ptr_base) && (ptr_base <? alloc_limit).

  Definition fetch_and_decode_cap bytemap (addr:AddressValue.t) tag : serr C.t :=
    let bs := fetch_bytes bytemap addr IMP.get.(sizeof_pointer) in
    cs <- option2serr "cap contains unspecified bytes" (extract_unspec bs) ;;
    option2serr "error decoding cap" (C.decode cs tag).

  (* If pointer stored at [addr] with meta information [meta] has it's
     base within given [base] and [limit] region, revoke it by returning
     new meta.
   *)
  Definition maybe_revoke_pointer
    allocation
    (st: mem_state)
    (addr: AddressValue.t)
    (meta: (bool*CapGhostState))
    :
    memM (bool* CapGhostState)
    :=
    (* mprint_msg ("maybe_revoke_pointer "  ++ String.hex_str addr) ;; *)
    let '(tag, gs) := meta in
    if negb tag then ret meta (* the pointer is already untagged *)
    else
      c <- serr2InternalErr (fetch_and_decode_cap st.(bytemap) addr tag) ;;
      if cap_bounds_within_alloc_bool c allocation
      then
        ret (false, {| tag_unspecified := false; bounds_unspecified := gs.(bounds_unspecified) |})
      else ret meta. (* outside allocation. leave unchanged *)

  (* revoke (clear tag) any pointer in the memory pointing within the
     bounds of given dynamic allocation.

     [alloc] parameter should be a dynamic allocation
   *)
  Definition revoke_pointers allocation : memM unit
    :=
    (* mprint_msg ("revoke_pointers " ++ (String.hex_str base) ++ " - "  ++ (String.hex_str limit)) ;; *)
    st <- get ;;
    newmeta <- AMap.map_mmapi (maybe_revoke_pointer allocation st) st.(capmeta) ;;
    update (mem_state_with_capmeta newmeta) ;;
    ret tt.

  Definition kill
    (loc : location_ocaml)
    (is_dyn : bool)
    (ptr : pointer_value)
    : memM unit
    :=
    (* Checks if capability matches allocation *)
    let check_cap_alloc_match c alloc :=
      if is_dyn && negb (cap_match_dyn_allocation c alloc)
      then
        (* the capability corresponding to dynamic allocation was changed *)
        fail loc (MerrUndefinedFree Free_non_matching)
      else ret tt
    in

    (* Attempt to re-use some memory if we removing the last
       allocation. this will not not allways recover all memory, as we
       do not know how much alignment have been added. The alighment
       part will not get recovered.

       Unfortunately this naive implementation won't work for `malloc`
       call followed by `free` because some intermediate values will
       be allocated during the call.
     *)
    let try_memory_reuse alloc :=
      st <- get ;;
      (* mprint_msg ("Kill: "  ++ AddressValue.to_string alloc.(base) ++ " (" ++ String.dec_str alloc.(size) ++ ")" ) ;; *)
      if
        (negb (AddressValue.eqb st.(last_address) initial_address)) &&
          AddressValue.eqb st.(last_address) alloc.(base)
      then
        (* mprint_msg ("Reuse!");; *)
        update (mem_state_with_last_address
                  (AddressValue.with_offset alloc.(base) (Z.of_nat alloc.(size))))
      else
        ret tt
    in

    (* update allocations in memory state and run revocation if necessary *)
    let update_allocations alloc alloc_id :=
      (if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation INSTANT)
       then
         (* instant revocation. Revoke and remove allocation id.
           both static and dynamic *)
         revoke_pointers alloc ;; remove_allocation alloc_id
       else if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA) && is_dyn
            then
              (* delayed revocation. Mark allocation as 'dead'.
                NB: Cornucopia revokes only dynamic allocations.*)
              st <- get ;;
              let newallocs := ZMap.map_update_element alloc_id (allocation_with_dead alloc) st.(allocations) in
              update (mem_state_with_allocations newallocs)
            else
              (* no revocation. remove allocation *)
              remove_allocation alloc_id
      )
      (* ;;  try_memory_reuse alloc *)
    in

    (* check if [is_dyn] parameter matches [allocation.(is_dynamic)] *)
    let check_dyn_match alloc_dyn :=
      match is_dyn, alloc_dyn with
      | true, false =>
          (* an attempt to kill a static allocation as dynamic. e.g. call free on
             the address of local variable *)
          fail loc (MerrUndefinedFree Free_non_matching)
      | false, true =>
          (* This should not happen *)
          raise (InternalErr "An attempt to kill dymanic allocation as static")
      | _ , _ =>
          ret tt
      end
    in

    match ptr with
    | PVconcrete c =>
        if cap_is_null c
           && CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_forbid_nullptr_free
        then fail loc MerrFreeNullPtr
        else
          find_live_allocation (C.cap_get_value c) >>=
            fun x =>
              match x with
              | None =>
                  (* Unfortunately we could not distinguish here
                     between the cases where allocation could not be
                     found because of the starting address does not
                     match (`Free_non_matching`) or it was previously
                     killed (`Free_dead_allocation`).
                   *)
                  fail loc
                    (if is_dyn
                     then MerrUndefinedFree Free_non_matching
                     else MerrOther "attempted to kill with a pointer not matching any live allocation")
              | Some (alloc_id,alloc) =>
                  check_dyn_match alloc.(is_dynamic) ;;
                  check_cap_alloc_match c alloc ;;
                  update_allocations alloc alloc_id
              end
    | PVfunction _ =>
        fail loc (MerrOther "attempted to kill with a function pointer")
    end.


  (** Checks if memory region starting from [addr] and
      of size [sz] fits withing interval \[b1,b2) *)
  Definition cap_bounds_check (bounds : Bounds.t)
    : Z -> Z -> bool
    :=
    let '(base, limit) := Bounds.to_Zs bounds in
    fun (addr : Z) (sz : Z) =>
      (base <=? addr) && ((addr + sz) <=? limit).

  Definition cap_check
    (loc : location_ocaml)
    (c : C.t)
    (offset : nat)
    (intent : access_intention)
    (size_n : nat)
    : memM unit :=
    (* We check here only [tag_unspecified] because setting [bounds_unspecified]
       always concides with setting [tag_unspecified] as well *)
    if (C.get_ghost_state c).(tag_unspecified) then
      fail loc (MerrCHERI CheriUndefinedTag)
    else
      if C.cap_is_valid c then
        let addr := cap_to_Z c + (Z.of_nat offset) in
        let pcheck :=
          match intent with
          | ReadIntent =>
              Permissions.has_load_perm
          | WriteIntent =>
              Permissions.has_store_perm
          | CallIntent =>
              Permissions.has_execute_perm
          end in
        if pcheck (C.cap_get_perms c) then
          let sz := Z.of_nat size_n in
          let limit := addr + sz in
          if C.cap_bounds_check c (Bounds.of_Zs (addr, sz))
          then ret tt
          else
            fail loc
              (MerrCHERI (CheriBoundsErr (C.cap_get_bounds c, AddressValue.of_Z addr, (Z.to_nat sz))))
        else
          fail loc (MerrCHERI CheriMerrInsufficientPermissions)
      else
        fail loc
          (MerrCHERI CheriMerrInvalidCap).

  Definition is_within_bound
    (alloc_id : Z.t)
    (lvalue_ty : CoqCtype.ctype)
    (addr : Z) : memM bool
    :=
    szn <- serr2InternalErr (sizeof DEFAULT_FUEL None lvalue_ty) ;;
    let sz := Z.of_nat szn in
    get_allocation alloc_id >>=
      (fun (alloc : allocation) =>
         ret
           ((AddressValue.to_Z alloc.(base) <=? addr)
            && (addr + sz <=?
                  AddressValue.to_Z alloc.(base) + Z.of_nat alloc.(size)))).

  Definition is_atomic_member_access
    (alloc_id : Z.t)
    (lvalue_ty : CoqCtype.ctype)
    (addr : Z.t)
    : memM bool
    :=
    szn <- serr2InternalErr (sizeof DEFAULT_FUEL None lvalue_ty) ;;
    let sz := Z.of_nat szn in
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
             e <- serr2InternalErr (CoqCtype.ctypeEqual DEFAULT_FUEL lvalue_ty ty) ;;
             ret
               (negb
                  ((addr =? (AddressValue.to_Z alloc.(base))) && (Nat.eqb szn alloc.(size) && e)))
         | _, _ => ret false
         end).

  Definition load
    (loc: location_ocaml)
    (ty: CoqCtype.ctype)
    (ptrval_: pointer_value)
    :
    memM (footprint * mem_value)
    :=
    let do_load
          (alloc_id_opt : option storage_instance_id)
          (addr : AddressValue.t)
          (sz : nat)
      : memM (footprint * mem_value)
      :=
      st <- get ;;
      let bs := fetch_bytes st.(bytemap) addr sz in
      let tag_query (a_value : AddressValue.t) : bool* CapGhostState :=
        if is_pointer_algined a_value then
          match AMap.M.find a_value st.(capmeta) with
          | Some x => x
          | None =>
              (* this should not happen *)
              (false,
                {| tag_unspecified := true;
                  bounds_unspecified := false |})
          end
        else
          (* An attempt to load a capability from not properly
                  aligned address. OCaml handles this with [failwith]
                  but here we just return default value. But the
                  question what error to raise is moot since this is
                  an internal error which should never happen, and
                  hopefully we will prove so. *)
          (false,
            {| tag_unspecified := true;
              bounds_unspecified := false |})
      in
      '(mval, bs') <-
        serr2InternalErr (abst DEFAULT_FUEL (find_cap_allocation_st st) st.(funptrmap) tag_query addr ty bs)
      ;;
      mval <- mem_value_strip_err loc mval ;;
      szn <- serr2InternalErr (sizeof DEFAULT_FUEL None ty) ;;
      let fp := FP Read addr szn in
      match bs' with
      | [] =>
          if CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_strict_reads
          then
            match mval with
            | MVunspecified _ =>
                fail loc MerrReadUninit
            | _ => ret (fp, mval)
            end
          else
            ret (fp, mval)
      | _ =>
          fail loc (MerrWIP "load, bs' <> []")
      end
    in
    let do_load_cap
          (alloc_id_opt : option storage_instance_id)
          (c : C.t)
          (sz : nat)
      : memM (footprint * mem_value)
      :=
      cap_check loc c 0 ReadIntent sz ;;
      do_load alloc_id_opt (C.cap_get_value c) sz
    in
    let load_concrete (alloc_id:storage_instance_id) (c:C.t) : memM (footprint * mem_value) :=
      if cap_is_null c then
        fail loc (MerrAccess LoadAccess NullPtr)
      else
        dead <- is_dead_allocation alloc_id;;
        (if dead
         then fail loc (MerrAccess LoadAccess DeadPtr)
         else ret tt)
        ;;
        inbounds <- is_within_bound alloc_id ty (cap_to_Z c) ;;
        if inbounds then
          atomic <- is_atomic_member_access alloc_id ty  (cap_to_Z c) ;;
          if atomic
          then fail loc (MerrAccess LoadAccess AtomicMemberof)
          else
            (sz <- serr2InternalErr (sizeof DEFAULT_FUEL None ty) ;;
             do_load_cap (Some alloc_id) c sz)
        else
          fail loc (MerrAccess LoadAccess OutOfBoundPtr)
    in
    match ptrval_ with
    | PVfunction _ =>
        fail loc (MerrAccess LoadAccess FunctionPtr)
    | PVconcrete c =>
        olp <- find_cap_allocation c ;;
        match olp with
        | None => fail loc (MerrAccess LoadAccess OutOfBoundPtr)
        | Some (alloc_id,_) => load_concrete alloc_id c
        end
    end.

  Definition store
    (loc : location_ocaml)
    (cty : CoqCtype.ctype)
    (is_locking : bool)
    (ptrval_ : pointer_value)
    (mval : mem_value)
    : memM  footprint
    :=
    cond <- serr2InternalErr (
               mt <- typeof mval ;;
               CoqCtype.ctypeEqual DEFAULT_FUEL (CoqCtype.unatomic cty)
                 (CoqCtype.unatomic mt))
    ;;
    if negb cond
    then fail loc (MerrOther "store with an ill-typed memory value")
    else
      let select_ro_kind p :=
        match p with
        | CoqSymbol.PrefTemporaryLifetime _ _ => ReadonlyTemporaryLifetime
        | CoqSymbol.PrefStringLiteral _ _ => ReadonlyStringLiteral
        | _ => ReadonlyConstQualified
        end
      in
      let do_store_cap
            (alloc_id_opt : option storage_instance_id)
            (c_value : C.t)
        : memM footprint
        :=
        szn <- serr2InternalErr (sizeof DEFAULT_FUEL None cty) ;;
        let sz := Z.of_nat szn in
        cap_check loc c_value 0 WriteIntent szn ;;
        let addr := C.cap_get_value c_value in

        s <- get ;;
        '(s',_) <- serr2InternalErr (repr DEFAULT_FUEL addr mval s) ;;
        put s' ;;
        ret (FP Write addr szn)
      in

      let store_concrete alloc_id c :=
        if cap_is_null c then
          fail loc (MerrAccess StoreAccess NullPtr)
        else
          inbounds <- is_within_bound alloc_id cty (cap_to_Z c) ;;
          if inbounds then
            (alloc <- get_allocation alloc_id ;;
             match alloc.(is_readonly) with
             | IsReadOnly ro_kind =>
                 fail loc (MerrWriteOnReadOnly ro_kind)
             | IsWritable =>
                 atomic <- is_atomic_member_access alloc_id cty (cap_to_Z c) ;;
                 if atomic
                 then fail loc (MerrAccess LoadAccess AtomicMemberof)
                 else
                   (fp <- do_store_cap (Some alloc_id) c ;;
                    if is_locking then
                      update
                        (fun (st : mem_state) =>
                           mem_state_with_allocations
                             (ZMap.map_update alloc_id
                                (fun (oa:option allocation) =>
                                   a <- oa ;;
                                   ret (allocation_with_is_readonly a (IsReadOnly (select_ro_kind a.(prefix))))
                                ) st.(allocations))
                             st)
                      ;;
                      ret fp
                    else
                      ret fp)
             end)
          else  fail loc (MerrAccess StoreAccess OutOfBoundPtr)
      in

      match ptrval_ with
      | PVfunction _ =>
          fail loc
            (MerrAccess
               StoreAccess
               FunctionPtr)
      | PVconcrete c =>
          olp <- find_cap_allocation c ;;
          match olp with
          | None => fail loc (MerrAccess StoreAccess OutOfBoundPtr)
          | Some (alloc_id,_) => store_concrete alloc_id c
          end
      end.

  Definition null_ptrval (_:CoqCtype.ctype) : pointer_value
    :=
    PVconcrete (C.cap_c0 tt).

  Definition fun_ptrval (sym : CoqSymbol.sym)
    : serr pointer_value :=
    ret (PVfunction (FP_valid sym)).

  Definition concrete_ptrval : Z -> AddressValue.t -> serr pointer_value :=
    fun _ _ =>
      raise
        "concrete_ptrval: integer to pointer cast is not supported".
  (*
  Definition case_ptrval
    {A: Set}
    (pv : pointer_value)
    (fnull : unit -> A)
    (ffun : option CoqSymbol.sym -> A)
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
    : option CoqSymbol.sym
    :=
    let '(_, ptrval) := break_PV ptr in
    match ptrval with
    | PVfunction (FP_valid sym) => Some sym
    | PVfunction (FP_invalid c_value)
    | PVconcrete c_value =>
        let n_value :=
          Z.sub (C.cap_get_value c_value) initial_address in
        match ZMap.M.find n_value st.(funptrmap) with
        | Some (file_dig, name, _) =>
            Some
              (CoqSymbol.Symbol file_dig n_value
                 (CoqSymbol.SD_Id name))
        | None => None
        end
    end.
   *)

  Definition case_funsym_opt (st:mem_state) (ptrval:pointer_value_indt): option CoqSymbol.sym
    :=
    match ptrval with
    | PVfunction (FP_valid sym) => Some sym
    | PVfunction (FP_invalid c)
    | PVconcrete c =>
        let n := cap_to_Z c - (AddressValue.to_Z initial_address) in
        match ZMap.M.find n st.(funptrmap) with
        | Some (file_dig, name, _) =>
            Some (CoqSymbol.Symbol file_dig n (SD_Id name))
        | None =>
            None
        end
    end.

  Definition eq_ptrval
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM bool
    :=
    match ptrval_1, ptrval_2 with
    | PVfunction (FP_valid sym1), PVfunction (FP_valid sym2) =>
        ret (CoqSymbol.symbolEquality sym1 sym2)
    | PVfunction (FP_invalid c1), PVfunction (FP_invalid c2) =>
        ret (AddressValue.eqb (C.cap_get_value c1) (C.cap_get_value c2))
    | PVfunction (FP_valid sym), PVfunction (FP_invalid c_value)
    | PVfunction (FP_invalid c_value), PVfunction (FP_valid sym) =>
        st <- get ;;
        let n_value :=
          cap_to_Z c_value - (AddressValue.to_Z initial_address)
        in
        match ZMap.M.find n_value st.(funptrmap) with
        | Some (file_dig, name, _) =>
            let sym2 := CoqSymbol.Symbol file_dig n_value (CoqSymbol.SD_Id name) in
            ret (CoqSymbol.symbolEquality sym sym2)
        | None =>
            raise (InternalErr
                     "eq_ptrval ==> FP_valid failed to resolve function symbol")
        end
    | PVfunction _, _
    | _, PVfunction _ =>
        ret false
    | PVconcrete c1, PVconcrete c2 =>
        ret (AddressValue.eqb (C.cap_get_value c1) (C.cap_get_value c2))
    end.

  Definition ne_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    eq_ptrval loc ptr1 ptr2 >>= (fun (x : bool) => ret (negb x)).

  Definition compare_ptrval
    (label: string)
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM comparison
    :=
    match ptrval_1, ptrval_2 with
    | PVconcrete c1, PVconcrete c2 =>
        if cap_is_null c1 || cap_is_null c2 then
          fail loc (MerrWIP ("one of pointers is NULL in " ++ label))
        else
          oa1 <- find_cap_allocation c1 ;;
          oa2 <- find_cap_allocation c2 ;;
          match oa1, oa2 with
          | Some (alloc_id1, _), Some (alloc_id2, _)
            =>
              if alloc_id1 =? alloc_id2 then
                ret (C.value_compare c1 c2)
              else
                fail loc MerrPtrComparison
          | _, _ => fail loc MerrPtrComparison
          end
    | _, _ => fail loc (MerrWIP ("incompatible pointers in " ++ label))
    end.

  Definition lt_ptrval
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM bool
    :=
    cp <- compare_ptrval "lt_ptrval" loc ptrval_1 ptrval_2 ;;
    ret (match cp with
         | Lt => true
         | _ => false
         end).

  Definition gt_ptrval
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM bool
    :=
    cp <- compare_ptrval "gt_ptrval" loc ptrval_1 ptrval_2 ;;
    ret (match cp with
         | Gt => true
         | _ => false
         end).

  Definition le_ptrval
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM bool
    :=
    cp <- compare_ptrval "le_ptrval" loc ptrval_1 ptrval_2 ;;
    ret (match cp with
         | Lt => true
         | Eq => true
         | _ => false
         end).

  Definition ge_ptrval
    (loc : location_ocaml)
    (ptrval_1 ptrval_2 : pointer_value) : memM bool
    :=
    cp <- compare_ptrval "gt_ptrval" loc ptrval_1 ptrval_2 ;;
    ret (match cp with
         | Gt => true
         | Eq => true
         | _ => false
         end).

  Definition diff_ptrval
    (loc: location_ocaml)
    (diff_ty : CoqCtype.ctype)
    (ptrval1 ptrval2 : pointer_value)
    : memM integer_value
    :=
    let precond (alloc: allocation) (addr1 addr2: Z): bool
      :=
      let asize := Z.of_nat alloc.(size) in
      (AddressValue.to_Z alloc.(base) <=? addr1) &&   (addr1 <=? (AddressValue.to_Z alloc.(base) + asize)) &&
        (AddressValue.to_Z alloc.(base) <=? addr2) && (addr2 <=? (AddressValue.to_Z alloc.(base) + asize))
    in

    let valid_postcond  (addr1 addr2: Z) : memM integer_value :=
      let diff_ty' :=
        match diff_ty with
        | CoqCtype.Ctype _ (CoqCtype.Array elem_ty _) => elem_ty
        | _ => diff_ty
        end in
      sz <- serr2InternalErr (sizeof DEFAULT_FUEL None diff_ty') ;;
      ret (IV (Z.div (addr1 - addr2) (Z.of_nat sz)))
    in

    let error_postcond := fail loc MerrPtrdiff
    in

    match ptrval1, ptrval2 with
    | PVconcrete c1, PVconcrete c2 =>
        oa1 <- find_cap_allocation c1 ;;
        oa2 <- find_cap_allocation c2 ;;
        match oa1, oa2 with
        | Some (alloc_id1, alloc1), Some (alloc_id2, alloc2)
          =>
            if alloc_id1 =? alloc_id2 then
              if precond alloc1 (cap_to_Z c1) (cap_to_Z c2)
              then valid_postcond (cap_to_Z c1) (cap_to_Z c2)
              else error_postcond
            else
              error_postcond
        | _, _ => error_postcond
        end
    | _, _ => error_postcond
    end.

  Definition update_prefix
    (x : CoqSymbol.prefix * mem_value)
    : memM unit
    :=
    let '(pref, mval) := x in
    match mval with
    | MVpointer _ (PVconcrete c) =>
        oa <- find_cap_allocation c ;;
        match oa with
        | Some (alloc_id,alloc) =>
            let upd_alloc (x : option allocation) : option allocation :=
              match x with
              | Some alloc => Some (allocation_with_prefix pref alloc)
              | None => None
              end
            in
            update
              (fun (st : mem_state) =>
                 mem_state_with_allocations (ZMap.map_update alloc_id upd_alloc st.(allocations)) st)
        | None =>
            ret tt
        end
    | _ =>
        ret tt
    end.

  (*
  Local Open Scope string_scope.
  Fixpoint prefix_of_pointer_aux addr alloc x :=
    match x with
    | None
    | Some (CoqCtype.Ctype _ CoqCtype.Void)
    | Some (CoqCtype.Ctype _ (CoqCtype.Function _ _ _))
    | Some (CoqCtype.Ctype _ (CoqCtype.FunctionNoParams _)) =>
        ret None
    | Some (CoqCtype.Ctype _ (CoqCtype.Basic _))
    | Some (CoqCtype.Ctype _ (CoqCtype.Union _))
    | Some (CoqCtype.Ctype _ (CoqCtype.Pointer _ _)) =>
        let offset := Z.sub addr alloc.(base) in
        ret (Some (CoqSymbol.string_of_prefix alloc.(prefix) ++ " + " ++ String.dec_str offset))
    | Some (CoqCtype.Ctype _ (CoqCtype.Struct tag_sym)) => (* TODO: nested structs *)
        let offset := Z.sub addr alloc.(base) in
        '(offs, _) <- serr2InternalErr (offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym) ;;
        let fix find y :=
          match y with
          | [] => None
          | (CoqSymbol.Identifier _ memb, _, off) :: offs =>
              if offset =? off
              then Some (CoqSymbol.string_of_prefix alloc.(prefix) ++ "." ++ memb)
              else find offs
          end
        in
        ret (find offs)
    | Some (CoqCtype.Ctype _ (CoqCtype.Array ty _)) =>
        let offset := Z.sub addr alloc.(base) in
        if offset <? alloc.(size) then
          sz <- serr2InternalErr (sizeof DEFAULT_FUEL None ty) ;;
          let n := Z.div offset sz in
          ret (Some (CoqSymbol.string_of_prefix alloc.(prefix) ++ "[" ++ String.dec_str n ++ "]"))
        else
          ret None
    | Some (CoqCtype.Ctype _ (CoqCtype.Atomic ty)) =>
        prefix_of_pointer_aux addr alloc (Some ty)
    end.

  Definition prefix_of_pointer (ptr:pointer_value): memM (option string)
    :=
    let '(prov, pv) := break_PV ptr in
    match prov with
    | Prov_some alloc_id =>
        get_allocation alloc_id >>= fun alloc =>
            match pv with
            | PVconcrete addr =>
                if C.cap_get_value addr = alloc.(base)
                then ret (Some (CoqSymbol.string_of_prefix alloc.(prefix)))
                else prefix_of_pointer_aux (C.cap_get_value addr) alloc alloc.(ty)
            | _ =>
                ret None
            end
    | _ =>
        ret None
    end.
  Local Close Scope string_scope.
   *)

  Definition isWellAligned_ptrval
    (ref_ty:  CoqCtype.ctype) (ptrval : pointer_value)
    : memM bool
    :=
    match CoqCtype.unatomic_ ref_ty with
    | (CoqCtype.Void | CoqCtype.Function _ _ _) =>
        fail_noloc
          (MerrOther
             "called isWellAligned_ptrval on void or a function type")
    | _ =>
        match ptrval with
        | PVfunction _ =>
            fail_noloc
              (MerrOther
                 "called isWellAligned_ptrval on function pointer")
        | PVconcrete addr =>
            sz <- serr2InternalErr (alignof DEFAULT_FUEL None ref_ty) ;;
            ret ((cap_to_Z addr) mod (Z.of_nat sz) =? 0)
        end
    end.

  (* References:
       §6.5.3.3, footnote 102 in C11
       §6.5.3.2, footnote 106 in C17
   *)
  Definition validForDeref_ptrval
    (ref_ty: CoqCtype.ctype) (ptrval: pointer_value)
    : memM bool
    :=
    let do_test (alloc_id : storage_instance_id): memM bool
      :=
      is_dead_allocation alloc_id >>=
        (fun (x : bool) =>
           match x with
           | true => ret false
           | false => isWellAligned_ptrval ref_ty ptrval
           end)
    in
    match ptrval with
    | PVfunction _ => ret false
    | PVconcrete c_value =>
        if cap_is_null c_value
        then ret false
        else
          find_cap_allocation c_value >>= fun x =>
              match x with
              | None => ret false
              | Some _ => isWellAligned_ptrval ref_ty ptrval
              end
    end.

  Definition ptrfromint
    (loc : location_ocaml)
    (int_ty : CoqIntegerType.integerType)
    (ref_ty : CoqCtype.ctype)
    (int_v : integer_value) : memM pointer_value
    :=
    match int_ty, int_v with
    | CoqIntegerType.Unsigned CoqIntegerType.Intptr_t, IC _ c
    | CoqIntegerType.Signed CoqIntegerType.Intptr_t, IC _ c
      =>
        ret (PVconcrete c)
    |CoqIntegerType.Unsigned CoqIntegerType.Intptr_t, IV _
    | CoqIntegerType.Signed CoqIntegerType.Intptr_t, IV _ =>
        raise (InternalErr "ptrfromint: invalid encoding for (u)intptr_t")
    | _, IV n =>
        if n =? 0
        then ret (null_ptrval ref_ty)
        else
          let addr :=
            (* wrapI *)
            let dlt := Z.succ (AddressValue.to_Z C.max_ptraddr - (AddressValue.to_Z C.min_ptraddr)) in
            let r := Z_integerRem_f n dlt in
            if r <=? (AddressValue.to_Z C.max_ptraddr)
            then r
            else r - dlt
          in
          let c := C.cap_set_value (C.cap_c0 tt) (AddressValue.of_Z addr) in
          ret (PVconcrete c)
    | _, IC _ _ =>
        raise (InternalErr
                 "invalid integer value (capability for non-(u)intptr_t")
    end.

  Definition internal_intcast
    (loc : location_ocaml)
    (ity2 : CoqIntegerType.integerType)
    (ival : integer_value)
    : serr (sum mem_error integer_value)
    :=
    zbytes <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity2) ;;
    let nbytes := Z.of_nat zbytes in
    let '(min_ity2, max_ity2) :=
      let nbits := Z.mul 8 nbytes in
      let is_signed := is_signed_ity DEFAULT_FUEL ity2 in
      if is_signed then
        (Z.opp (Z.pow 2 (nbits - 1)),
          Z.pow 2 (nbits - 1) - 1)
      else
        (0, Z.pow 2 nbits - 1) in
    let conv_int_to_ity2 (n_value : Z) : Z :=
      match ity2 with
      | CoqIntegerType.Bool =>
          if n_value =? 0
          then 0
          else 1
      | _ =>
          if (n_value <=? min_ity2) && (n_value <=? max_ity2)
          then n_value
          else wrapI min_ity2 max_ity2 n_value
      end in
    match ival, ity2 with
    | IC false _, CoqIntegerType.Unsigned CoqIntegerType.Intptr_t
    | IC true _, CoqIntegerType.Signed CoqIntegerType.Intptr_t =>
        ret (inr ival)
    | IC (false as is_signed) cap, CoqIntegerType.Signed CoqIntegerType.Intptr_t
    | IC (true as is_signed) cap,  CoqIntegerType.Unsigned CoqIntegerType.Intptr_t =>
        ret (inr  (IC (negb is_signed) cap))
    | IC false cap, _ =>
        let n_value := (cap_to_Z cap) in
        ret (inr (IV (conv_int_to_ity2 n_value)))
    | IC true cap, _ =>
        let n_value := (cap_to_Z cap) in
        ret (inr (IV (conv_int_to_ity2 (unwrap_cap_value n_value))))
    | IV n_value, CoqIntegerType.Unsigned CoqIntegerType.Intptr_t
    | IV n_value, CoqIntegerType.Signed CoqIntegerType.Intptr_t =>
        if n_value =? 0 then
          ret (inr (IC false (C.cap_c0 tt)))
        else
          let n_value := wrap_cap_value n_value in
          let c_value := C.cap_c0 tt in
          ret (inr (IC false (C.cap_set_value c_value (AddressValue.of_Z n_value))))
    | IV n_value, _ =>
        ret (inr (IV (conv_int_to_ity2 n_value)))
    end.

  Definition max_ival (ity: CoqIntegerType.integerType)
    : serr integer_value
    :=
    let signed_max (n_value : Z) : Z :=
      (Z.pow 2 (Z.mul 8 n_value - 1)) - 1 in
    let unsigned_max (n_value : Z) : Z :=
      (Z.pow 2 (Z.mul 8 n_value)) - 1 in
    match ity with
    | CoqIntegerType.Signed CoqIntegerType.Intptr_t =>
        ret (IV (signed_max (Z.of_nat C.sizeof_ptraddr)))
    | CoqIntegerType.Unsigned CoqIntegerType.Intptr_t =>
        ret (IV (unsigned_max (Z.of_nat C.sizeof_ptraddr)))
    | _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        let z_value := Z.of_nat n_value in
        match ity with
        | CoqIntegerType.Char =>
            if IMP.get.(CoqImplementation.is_signed_ity) CoqIntegerType.Char
            then ret (IV (signed_max z_value))
            else ret (IV (unsigned_max z_value))
        | CoqIntegerType.Bool => ret (IV (unsigned_max z_value))
        | CoqIntegerType.Size_t
        | CoqIntegerType.Wchar_t
        | CoqIntegerType.Unsigned _ => ret (IV (unsigned_max z_value))
        | CoqIntegerType.Ptrdiff_t
        | CoqIntegerType.Wint_t
        | CoqIntegerType.Signed _ => ret (IV (signed_max z_value))
        | CoqIntegerType.Ptraddr_t => ret (IV (unsigned_max z_value))
        | CoqIntegerType.Enum _ => ret (IV (signed_max 4))
        end
    end.

  Definition min_ival (ity: CoqIntegerType.integerType)
    : serr integer_value
    :=
    let signed_min (n_value: Z) : Z :=
      Z.opp (Z.pow 2 (Z.mul 8 n_value - 1)) in
    match ity with
    | CoqIntegerType.Char =>
        if IMP.get.(CoqImplementation.is_signed_ity) CoqIntegerType.Char
        then ret (IV (signed_min 1))
        else ret (IV 0)
    | CoqIntegerType.Bool
    | CoqIntegerType.Size_t
    | CoqIntegerType.Wchar_t
    | CoqIntegerType.Wint_t
    | CoqIntegerType.Unsigned _ => ret (IV 0)
    | CoqIntegerType.Signed CoqIntegerType.Intptr_t =>
        ret (IV (signed_min (Z.of_nat C.sizeof_ptraddr)))
    | CoqIntegerType.Ptrdiff_t
    | CoqIntegerType.Signed _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        ret (IV (signed_min (Z.of_nat n_value)))
    | CoqIntegerType.Ptraddr_t => ret (IV 0)
    | CoqIntegerType.Enum _ => ret (IV (signed_min 4))
    end.

  Definition intfromptr
    (loc : location_ocaml)
    (_ : CoqCtype.ctype)
    (ity: CoqIntegerType.integerType)
    (ptrval: pointer_value)
    : memM integer_value
    :=
    let wrap_intcast (ity2 : CoqIntegerType.integerType) (ival : integer_value)
      : memM integer_value
      :=
      icr <- serr2InternalErr (internal_intcast loc ity2 ival) ;;
      match icr with
      | inl err => fail loc err
      | inr ival => ret ival
      end in
    match ptrval with
    |
      PVfunction
        (FP_valid ((CoqSymbol.Symbol _ n_value _) as fp)) =>
        st <- get ;;
        match ity with
        |
          (CoqIntegerType.Signed CoqIntegerType.Intptr_t |
            CoqIntegerType.Unsigned CoqIntegerType.Intptr_t) =>
            match ZMap.M.find n_value st.(funptrmap) with
            | Some (file_dig, name, c_value) =>
                wrap_intcast ity (IC false c_value)
            | None =>
                raise (InternalErr "intfromptr: Unknown function")
            end
        | _ =>
            ret (IV (AddressValue.to_Z initial_address + n_value))
        end
    | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
        if cap_is_null c_value then
          match ity with
          | CoqIntegerType.Signed CoqIntegerType.Intptr_t =>
              ret (IC true (C.cap_c0 tt))
          | CoqIntegerType.Unsigned CoqIntegerType.Intptr_t =>
              ret (IC false (C.cap_c0 tt))
          | _ => ret (IV 0)
          end
        else
          match ity with
          |
            (CoqIntegerType.Signed CoqIntegerType.Intptr_t |
              CoqIntegerType.Unsigned CoqIntegerType.Intptr_t) =>
              wrap_intcast ity (IC false c_value)
          | _ =>
              maxival <- serr2InternalErr (max_ival ity) ;;
              minival <- serr2InternalErr (min_ival ity) ;;
              let ity_max := num_of_int maxival in
              let ity_min := num_of_int minival in
              let addr := (cap_to_Z c_value) in
              if (addr <? ity_min) || (ity_max <? addr)
              then fail loc MerrIntFromPtr
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
    | IC is_signed c, IV n =>
        ret (IC is_signed
               (C.cap_set_value
                  (if C.cap_ptraddr_representable c (AddressValue.of_Z n)
                   then
                     (if C.cap_is_sealed c
                      then C.set_ghost_state c
                                             {|
                                               tag_unspecified := true ;
                                               bounds_unspecified := (C.get_ghost_state c).(bounds_unspecified)
                                             |}
                      else c)
                   else C.set_ghost_state
                          c
                          {|
                            tag_unspecified := true ;
                            bounds_unspecified := true
                          |})
                  (AddressValue.of_Z n))
          )

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

  Definition array_shift_ptrval: pointer_value -> CoqCtype.ctype -> integer_value ->
                                 serr pointer_value
    := fun _ _ _ => raise "pure array_shift_ptrval not used in CHERI".

  Definition member_shift_ptrval: pointer_value -> CoqSymbol.sym ->
                                  CoqSymbol.identifier -> serr pointer_value
    := fun _ _ _ => raise "members_shift_ptrval (pure) is not supported in CHERI".

  Definition eff_array_shift_ptrval
    (loc : location_ocaml)
    (ptrval : pointer_value)
    (ty : CoqCtype.ctype)
    (ival_int : integer_value)
    : memM pointer_value
    :=
    let ival := num_of_int ival_int in
    szn <- serr2InternalErr (sizeof DEFAULT_FUEL None ty) ;;
    let sz := Z.of_nat szn in
    let offset := Z.mul sz ival
    in
    (* Check if [shifted_addr] fits within allocation and return it *)
    let shift_concrete c_value shifted_addr alloc_id  :=
      get_allocation alloc_id >>=
        (fun (alloc : allocation) =>
           if (AddressValue.leb alloc.(base) shifted_addr)
              && (AddressValue.to_Z shifted_addr + sz <=?
                    (AddressValue.to_Z alloc.(base) + (Z.of_nat alloc.(size)) + sz))
           then
             let c_value := C.cap_set_value c_value shifted_addr in
             ret (PVconcrete c_value)
           else
             fail loc MerrArrayShift
        )
    in
    match ptrval with
    | PVfunction _ =>
        raise (InternalErr "eff_array_shift_ptrval, PVfunction")
    | PVconcrete c_value =>
        let shifted_addr := AddressValue.with_offset (C.cap_get_value c_value) offset in
        oa <- find_cap_allocation c_value ;;
        match oa with
        | None => fail loc (MerrAccess LoadAccess OutOfBoundPtr)
        | Some (alloc_id,_) => shift_concrete c_value shifted_addr alloc_id
        end
    end.

  Definition offsetof_ival
    (tagDefs: SymMap.t CoqCtype.tag_definition)
    (tag_sym : CoqSymbol.sym)
    (memb_ident : CoqSymbol.identifier) : serr integer_value
    :=
    '(xs, _) <- offsetsof DEFAULT_FUEL tagDefs tag_sym ;;
    let pred x : bool :=
      let '(ident, _, _) := x in
      ident_equal ident memb_ident in
    match List.find pred xs with
    | Some (_, _, offset) => ret (IV (Z.of_nat offset))
    | None =>
        raise "offsetof_ival: invalid memb_ident"
    end.

  Definition eff_member_shift_ptrval
    (loc : location_ocaml)
    (ptrval: pointer_value)
    (tag_sym: CoqSymbol.sym)
    (memb_ident: CoqSymbol.identifier):  memM pointer_value
    :=
    ioff <- serr2InternalErr (offsetof_ival (TD.tagDefs tt) tag_sym memb_ident) ;;
    offset <-
      match ioff with
      | IV offset => ret (offset)
      | IC _ c_value =>
          raise (InternalErr
                   "member_shift_ptrval invalid offset value type")
      end ;;
    match ptrval with
    | PVfunction _ =>
        raise (InternalErr "member_shift_ptrval, PVfunction")
    | PVconcrete c_value =>
        if cap_is_null c_value then
          if 0 =? offset
          then ret (PVconcrete (C.cap_c0 tt)) (* null_ptrval may be better, but need to derive type first *)
          else raise (InternalErr "member_shift_ptrval, shifting NULL")
        else
          let addr := (cap_to_Z c_value) in
          let c_value := C.cap_set_value c_value (AddressValue.of_Z (addr + offset)) in
          ret (PVconcrete c_value)
    end.

  (* Helper function *)
  Fixpoint capmeta_copy_tags
    (dst src: AddressValue.t)
    (n: nat)
    (step: nat)
    (cm: AMap.M.t (bool * CapGhostState))
    : AMap.M.t (bool * CapGhostState)
    :=
    match n with
    | O => cm
    | S n =>
        let cm' := capmeta_copy_tags dst src n step cm in
        let src' := AddressValue.with_offset src (Z.of_nat (n*step)) in
        let dst' := AddressValue.with_offset dst (Z.of_nat (n*step)) in
        match AMap.M.find src' cm with
        | None =>
            (* This is the case where a pointer-aligned address does
               not have any meta information associated with
               it. Normally, it should not happen, but instead of
               enforcing this via an additional clause in the memory
               invariant, we just propagate this situation further. *)
            AMap.M.remove dst' cm'
        | Some meta => AMap.M.add dst' meta cm'
        end
    end.

  (* Helpe function *)
  Definition cap_addr_of_pointer_value (ptr: pointer_value) : serr AddressValue.t :=
    match ptr with
    | PVconcrete c => ret (C.cap_get_value c)
    | _ => raise "memcpy: invalid pointer value"
    end.

  Definition ghost_tags
    (addr: AddressValue.t)
    (size: nat) : memM unit
    :=
    update
      (fun (st : mem_state) =>
         mem_state_with_capmeta
           (capmeta_ghost_tags
              addr
              size
              st.(capmeta))
           st).

  (** Copy caps meta-information between `memcpy` source and
      destinations, only for positions where both source and
      desination addresses align and capability fully fits.
   *)
  Definition memcpy_copy_tags
    (loc: location_ocaml)
    (dst_a src_a: AddressValue.t)
    (sz: nat)
    : memM unit :=
    let pointer_alignof_n := IMP.get.(alignof_pointer) in
    let pointer_alignof := Z.of_nat pointer_alignof_n in

    (* Calculate alignments *)
    let dst_align := (AddressValue.to_Z dst_a) mod pointer_alignof in
    let src_align := (AddressValue.to_Z src_a) mod pointer_alignof in

    if dst_align =? src_align then
      (* Calculate the offset to the next aligned address *)
      let off := if dst_align =? 0 then 0 else pointer_alignof - dst_align in
      let zsz := Z.of_nat sz in

      if off >=? zsz then
        ret tt
      else
        (* Calculate the number of fully aligned regions *)
        let n := (zsz - off) / pointer_alignof in

        (* Update memory state with aligned regions *)
        update
          (fun (st : mem_state) =>
             mem_state_with_capmeta
               (capmeta_copy_tags
                  (AddressValue.with_offset dst_a off)
                  (AddressValue.with_offset src_a off)
                  (Z.to_nat n)
                  pointer_alignof_n
                  st.(capmeta))
               st)
    else
      (* Source and destination regions are misaligned, no tags will be copied *)
      ret tt.

  (* Helper function *)
  Fixpoint bytemap_copy_data
    (dst src: AddressValue.t)
    (n: nat)
    (bm: AMap.M.t (option ascii))
    : AMap.M.t (option ascii)
    :=
    match n with
    | O => bm
    | S n =>
        let bm' := bytemap_copy_data dst src n bm in
        match AMap.M.find (AddressValue.with_offset src (Z.of_nat n)) bm with
        | None => AMap.M.remove (AddressValue.with_offset dst (Z.of_nat n)) bm'
        | Some b => AMap.M.add (AddressValue.with_offset dst (Z.of_nat n)) b bm'
        end
    end.

  (** Helper function checks if regions of size [sz] fit within
      [allocation1] starting from [c1] and [allocation2] starting from
      [c2]. Additionally, it checks that they do not overlap.
  *)
  Definition memcpy_alloc_bounds_check loc c1 c2 (alloc1 alloc2:allocation) (sz:Z)
    : memM unit :=
    let ptr1_base := cap_to_Z c1 in
    let ptr1_limit := ptr1_base + sz in
    let alloc1_base := AddressValue.to_Z alloc1.(base) in
    let alloc1_limit := alloc1_base + Z.of_nat alloc1.(size) in

    let ptr2_base := cap_to_Z c2 in
    let ptr2_limit := ptr2_base + sz in
    let alloc2_base := AddressValue.to_Z alloc2.(base) in
    let alloc2_limit := alloc2_base + Z.of_nat alloc2.(size) in

    if (ptr1_base <? alloc1_base) || (ptr1_limit >? alloc1_limit) ||
         (ptr2_base <? alloc2_base) || (ptr2_limit >? alloc2_limit)
    then fail loc (MerrUndefinedMemcpy Memcpy_out_of_bound)
    else
      (* Checking for overlap. This should only be required if
         allocation IDs are the same, but since live allocations do
         not overlap, we perform a more general check for
         simplicity.
       *)
      if Z.abs (ptr1_base-ptr2_base) >=? sz
      then ret tt
      else fail loc (MerrUndefinedMemcpy Memcpy_overlap).

  (** Check if arguments to memcpy are sane:

     0. Size should be non-negative (corresponds to `size_t` which is unsigned )
     1. Both pointers should point to C objects
        (null pointers and pointers to functions is not allowed)
     2. Corresponding allocations must be live
     3. Copied regions must be within objects' bounds
     4. Source and destination must not overlap

     NOTE: We allow to copy parts of static objects.
           This may be not compatible with optimizations
           performed by some compilers. Copying parts
           of objects allocated on heap is non-controversial.
   *)
  Definition memcpy_args_check loc ptrval1 ptrval2 (size:Z):
    memM unit :=
    if size <? 0
    then raise (InternalErr "negative size passed to memcpy")
    else
      match ptrval1, ptrval2 with
      | PVconcrete c1, PVconcrete c2 =>
          if cap_is_null c1 || cap_is_null c2
          then fail loc (MerrUndefinedMemcpy Memcpy_non_object)
          else
            oa1 <- find_cap_allocation c1 ;;
            oa2 <- find_cap_allocation c2 ;;
            match oa1, oa2 with
            | Some (_,alloc1), Some (_,alloc2) =>
                memcpy_alloc_bounds_check loc c1 c2 alloc1 alloc2 size
            | _, _ =>
                (* One of allocations does not exists or dead.
                   We return [Memcpy_non_object] which is more
                   general than [Memcpy_dead_object]
                 *)
                fail loc (MerrUndefinedMemcpy Memcpy_non_object)
            end
      (* memcpy accepts only pointers to C objects *)
      | _, _ =>  fail loc (MerrUndefinedMemcpy Memcpy_non_object)
      end.

  (** Copy byte content of memory in given region. No sanity checks
      perfomed as it is supposed to be guarded by [memcpy_args_check].
   *)
  Definition memcpy_copy_data
    (loc: location_ocaml)
    (dst_a src_a: AddressValue.t)
    (size: nat): memM unit :=
    update (fun (st : mem_state) =>
              mem_state_with_bytemap
                (bytemap_copy_data
                   dst_a
                   src_a
                   size
                   st.(bytemap))
                st).

  Definition memcpy
    (loc: location_ocaml)
    (dst_p src_p: pointer_value)
    (size_int: integer_value)
    : memM pointer_value
    :=
    let size_z := num_of_int size_int in
    memcpy_args_check loc dst_p src_p size_z ;;

    dst_a <- serr2InternalErr (cap_addr_of_pointer_value dst_p) ;;
    src_a <- serr2InternalErr (cap_addr_of_pointer_value src_p) ;;

    let size := Z.to_nat size_z in

    ghost_tags dst_a size ;;
    memcpy_copy_data loc dst_a src_a size ;;
    memcpy_copy_tags loc dst_a src_a size ;;
    ret dst_p.

  Definition memcmp
    (ptrval1 ptrval2 : pointer_value)
    (size_int : integer_value)
    : memM integer_value
    :=
    let size_n := num_of_int size_int in
    if size_n <? 0
    then raise (InternalErr "negative size passed to memcmp")
    else
      let fix get_bytes
            (ptrval : pointer_value)
            (acc : list Z)
            (size : nat)
        : memM (list Z) :=
        match size with
        | O => ret (List.rev acc)
        | S size =>
            let loc := Loc_other "memcmp" in
            load loc CoqCtype.unsigned_char ptrval >>=
              (fun (x : footprint * mem_value) =>
                 match x with
                 | (_, MVinteger _ (IV byte_n)) =>
                     eff_array_shift_ptrval loc ptrval
                       CoqCtype.unsigned_char (IV 1) >>=
                       (fun (ptr' : pointer_value) =>
                          get_bytes ptr' (byte_n::acc) size)
                 | _ =>
                     raise (InternalErr "memcmp load unexpected result")
                 end)
        end in
      get_bytes ptrval1 [] (Z.to_nat size_n) >>=
        (fun (bytes1: list Z) =>
           get_bytes ptrval2 [] (Z.to_nat size_n) >>=
             (fun (bytes2: list Z) =>
                ret (IV
                       (List.fold_left
                          (fun (acc : Z) '(n1, n2) =>
                             if acc =? 0 then
                               match Z.compare n1 n2 with
                               | Eq => 0
                               | Gt => 1
                               | Lt => -1
                               end
                             else
                               acc)
                          (List.combine bytes1 bytes2) 0)))).

  Definition cornucopiaRevoke (_:unit) : memM unit
    :=
    st <- get ;;
    monadic_fold_left
      (fun _ '(allloc_id, alloc) =>
         if alloc.(is_dead) && alloc.(is_dynamic)
         then
           (revoke_pointers alloc ;;
            remove_allocation allloc_id)
         else ret tt
      )
      (ZMap.M.elements st.(allocations)) tt.

  Definition realloc
    (loc : location_ocaml)
    (tid : thread_id) (align : integer_value) (ptr : pointer_value)
    (size_v : integer_value) : memM pointer_value
    :=
    (if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
     then cornucopiaRevoke tt
     else ret tt) ;;
    match ptr with
    | PVconcrete c =>
        if cap_is_null c  then
          allocate_region tid (CoqSymbol.PrefOther "realloc") align size_v
        else
          find_live_allocation (C.cap_get_value c) >>=
            fun x =>
              match x with
              | None => fail loc (MerrUndefinedRealloc Free_non_matching)
              | Some (alloc_id,alloc) =>
                  if negb (cap_match_dyn_allocation c alloc)
                  then fail loc (MerrUndefinedRealloc Free_non_matching)
                  else
                    allocate_region tid (CoqSymbol.PrefOther "realloc") align size_v >>=
                      (fun (new_ptr : pointer_value) =>
                         let size_to_copy :=
                           let size_z := num_of_int size_v in
                           IV (Z.min (Z.of_nat alloc.(size)) size_z) in
                         memcpy loc new_ptr ptr size_to_copy ;;
                         kill (Loc_other "realloc") true ptr ;;
                         ret new_ptr)
              end
    | _ =>
        fail loc (MerrWIP "realloc: invalid pointer")
    end.

  Definition va_start (args:  list (CoqCtype.ctype * pointer_value)) : memM integer_value :=
    st <- get ;;
    let id := st.(next_varargs_id) in
    update (fun st => mem_state_with_varargs_next_varargs_id (ZMap.M.add id (0, args) st.(varargs)) (Z.succ st.(next_varargs_id)) st) ;;
    ret (IV id).

  Definition va_copy (va : integer_value) : memM integer_value :=
    match va with
    | IV id =>
        st <- get ;;
        match ZMap.M.find id st.(varargs) with
        | Some args =>
            let id := st.(next_varargs_id) in
            update
              (fun st =>
                 mem_state_with_varargs_next_varargs_id
                   (ZMap.M.add id args st.(varargs))
                   (Z.succ st.(next_varargs_id))
                   st) ;;
            ret (IV id)
        | None =>
            fail_noloc (MerrWIP "va_copy: not initiliased")
        end
    | _ => fail_noloc (MerrWIP "va_copy: invalid va_list")
    end.

  Definition va_arg (va: integer_value) (ty: CoqCtype.ctype): memM pointer_value :=
    match va with
    | IV id =>
        st <- get ;;
        match ZMap.M.find id st.(varargs) with
        | Some (i_value, args) =>
            match Lists.List.nth_error args (Z.to_nat i_value) with
            | Some (_, ptr) =>
                update
                  (fun st =>
                     mem_state_with_varargs_next_varargs_id
                       (ZMap.M.add id (i_value + 1, args) st.(varargs))
                       st.(next_varargs_id) (* unchanged *)
                            st) ;;
                ret ptr
            | None =>
                fail_noloc
                  (MerrWIP
                     "va_arg: invalid number of arguments")
            end
        | None =>
            fail_noloc (MerrWIP "va_arg: not initiliased")
        end
    | _ => fail_noloc (MerrWIP "va_arg: invalid va_list")
    end.

  Definition va_end (va : integer_value): memM unit :=
    match va with
    | IV id =>
        st <- get ;;
        match ZMap.M.find id st.(varargs) with
        | Some _ =>
            update
              (fun (st : mem_state) =>
                 mem_state_with_varargs_next_varargs_id
                   (ZMap.M.remove id st.(varargs))
                   st.(next_varargs_id) (* unchanged *)
                        st)
        | None =>
            fail_noloc (MerrWIP "va_end: not initiliased")
        end
    | _ => fail_noloc (MerrWIP "va_end: invalid va_list")
    end.

  Definition va_list (va_idx:Z) : memM (list (CoqCtype.ctype * pointer_value)) :=
    st <- get ;;
    match ZMap.M.find va_idx st.(varargs) with
    | Some (n_value, args) => ret args
    | None => fail_noloc (MerrWIP "va_list")
    end.

  Definition copy_alloc_id
    (ival : integer_value) (ptrval : pointer_value)
    : memM pointer_value
    :=
    intfromptr Loc_unknown CoqCtype.void (CoqIntegerType.Unsigned CoqIntegerType.Intptr_t) ptrval ;;
    ptrfromint Loc_unknown (CoqIntegerType.Unsigned CoqIntegerType.Intptr_t) CoqCtype.void ival.

  Definition concurRead_ival: CoqIntegerType.integerType -> CoqSymbol.sym -> serr (integer_value)
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
                          if n2 =? 0
                          then 0
                          else Z_integerDiv_t n1 n2) v1 v2
    | IntRem_t => int_bin Z_integerRem_t v1 v2
    | IntRem_f => int_bin Z_integerRem_f v1 v2
    | IntExp => int_bin Z.pow v1 v2
    end.

  Definition sizeof_ival (ty : CoqCtype.ctype): serr integer_value
    :=
    sz <- sizeof DEFAULT_FUEL None ty ;;
    ret (IV (Z.of_nat sz)).

  Definition alignof_ival (ty: CoqCtype.ctype): serr integer_value
    :=
    a <- alignof DEFAULT_FUEL None ty ;;
    ret (IV (Z.of_nat a)).

  Definition bitwise_complement_ival
    (ty : CoqIntegerType.integerType)
    (v : integer_value) : integer_value
    :=
    IV (Z.opp (num_of_int v) -1).

  Definition bitwise_and_ival (ty : CoqIntegerType.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.land.

  Definition bitwise_or_ival (ty : CoqIntegerType.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.lor.

  Definition bitwise_xor_ival (ty : CoqIntegerType.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.lxor.

  (* Definition case_integer_value
    {A : Set}
    (v : integer_value)
    (f : Z -> A)
    (_ : unit -> A) : A :=
    f (num_of_int v).
   *)

  Definition is_specified_ival (ival : integer_value) : bool := true.

  Definition eq_ival (n1 n2: integer_value) :=
    Some (num_of_int n1 =? num_of_int n2).

  Definition lt_ival (n1 n2: integer_value) :=
    Some (num_of_int n1 <? num_of_int n2).

  Definition le_ival (n1 n2: integer_value) :=
    Some (num_of_int n1 <=? num_of_int n2).

  Definition zero_fval : float := PrimFloat.zero.

  Definition one_fval : float := PrimFloat.one.

  (* Not implmeneted but we need a placeholder to compile libc during build *)
  Definition str_fval (str : string) : serr floating_value :=
    ret PrimFloat.zero.
  (* raise "str_fval not implmented". *)

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
    (ity: CoqIntegerType.integerType)
    (fval: floating_value): serr integer_value
    :=
    match ity with
    | CoqIntegerType.Bool =>
        ret (IV (if eq_fval fval zero_fval then 0 else 1))
    | _ =>
        nbytes <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        let zbytes := Z.of_nat nbytes in
        let nbits := Z.mul 8 zbytes in
        is_signed <- option2serr "no is_signed_ity" (is_signed_ity DEFAULT_FUEL ity) ;;
        let _:bool := is_signed in (* hack to hint type checker *)
        let '(min, max) :=
          if is_signed then
            (Z.opp (Z.pow 2 (nbits - 1)), (Z.pow 2 (nbits - 1)) - 1)
          else
            (0, Z.pow 2 nbits - 1) in
        let wrapI (n_value : Z) : Z :=
          let dlt := Z.succ (max - min) in
          let r_value := Z_integerRem_f n_value dlt in
          if r_value <=? max then
            r_value
          else
            r_value - dlt in
        (* TODO ret (IV (wrapI (Z.of_int64 (Stdlib.Int64.of_float fval)))) *)
        raise "ivfromfloat no implemented"
    end.

  Definition unspecified_mval (ty: CoqCtype.ctype): mem_value := MVunspecified ty.

  Definition integer_value_mval
    (ity: CoqIntegerType.integerType) (ival: integer_value)
    : mem_value := MVinteger ity ival.

  Definition floating_value_mval
    (fty: CoqCtype.floatingType) (fval: floating_value)
    : mem_value := MVfloating fty fval.

  Definition pointer_mval
    (ref_ty: CoqCtype.ctype) (ptrval: pointer_value)
    : mem_value := MVpointer ref_ty ptrval.

  Definition array_mval (mvals : list mem_value) : mem_value :=
    MVarray mvals.

  Definition struct_mval
    (tag_sym: CoqSymbol.sym)
    (xs: list(CoqSymbol.identifier * CoqCtype.ctype * mem_value)): mem_value :=
    MVstruct tag_sym xs.

  Definition union_mval
    (tag_sym : CoqSymbol.sym)
    (memb_ident : CoqSymbol.identifier) (mval : mem_value)
    : mem_value := MVunion tag_sym memb_ident mval.

  (* Definition case_mem_value
    {A: Set}
    (mval : mem_value)
    (f_unspec : CoqCtype.ctype -> A)
    (f_concur : CoqIntegerType.integerType -> CoqSymbol.sym -> A)
    (f_ival : CoqIntegerType.integerType -> integer_value -> A)
    (f_fval : CoqCtype.floatingType -> floating_value -> A)
    (f_ptr : CoqCtype.ctype -> pointer_value -> A)
    (f_array : list mem_value -> A)
    (f_struct : CoqSymbol.sym -> list (CoqSymbol.identifier * CoqCtype.ctype * mem_value) -> A)
    (f_union : CoqSymbol.sym -> CoqSymbol.identifier -> mem_value -> A) : A
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
   *)

  Definition sequencePoint: memM unit :=
    ret tt.

  Definition cap_of_mem_value
    (funptrmap : ZMap.M.t (digest * string * C.t))
    (mv : mem_value)
    : option  (ZMap.M.t (digest * string * C.t) * C.t)
    :=
    match mv with
    | MVinteger _ (IC _ c_value) => Some (funptrmap, c_value)
    | MVpointer _ (PVconcrete c_value) => Some (funptrmap, c_value)
    | MVpointer _ (PVfunction fp) =>
        Some (resolve_function_pointer funptrmap fp)
    | _ => None
    end.

  Definition update_cap_in_mem_value
    (cap_val : mem_value) (c_value : C.t) : mem_value :=
    match cap_val with
    | MVinteger ty (IC is_signed _) => MVinteger ty (IC is_signed c_value)
    | MVpointer ty (PVconcrete _) =>
        MVpointer ty (PVconcrete c_value)
    | MVpointer ty (PVfunction fp) =>
        MVpointer ty (PVfunction (FP_invalid c_value))
    | other => other
    end.

  Definition load_string (loc: location_ocaml) (c: C.t) (max_len: nat) : memM string
    :=
    let fix loop max_len (acc: string) (offset: nat) : memM string :=
      match max_len with
      | O => raise (InternalErr "string too long")
      | S max_len =>
          cap_check loc c offset ReadIntent 1%nat ;;
          let addr := AddressValue.with_offset (C.cap_get_value c) (Z.of_nat offset) in
          st <- get;;
          let bs := fetch_bytes st.(bytemap) addr 1 in
          ohd <- option2memM "fetch of 1 byte failed" (List.hd_error bs) ;;
          match ohd with
          | None => fail loc MerrReadUninit
          | Some c_value =>
              if Ascii.eqb c_value zero
              then ret acc
              else
                let s_value := String.append acc (String c_value "")
                in loop max_len s_value (S offset)
          end
      end
    in
    loop max_len "" O.

  Definition store_string (loc : location_ocaml) (s_value : string) (n : nat) (c_value : C.t) : memM nat
    :=
    match n with
    | O => ret O
    | S n =>
        let cs := list_ascii_of_string s_value in
        let cs := List.firstn n cs in
        let pre_bs := List.map (Some) cs in
        let pre_bs := List.app pre_bs [Some "000" % char] in
        let addr := C.cap_get_value c_value in
        let bs :=
          mapi
            (fun (i_value : nat) (b_value : (option ascii)) =>
               (AddressValue.with_offset addr (Z.of_nat i_value), b_value))
            pre_bs in
        cap_check loc c_value 0 WriteIntent (List.length bs) ;;
        update
          (fun (st : mem_state) =>
             mem_state_with_bytemap
               (List.fold_left
                  (fun acc '(addr, b_value) => AMap.M.add addr b_value acc)
                  bs st.(bytemap)) st)
        ;;
        ret (List.length bs)
    end.

  Definition intrinsic_revoke
    (loc : location_ocaml)
    : memM (option mem_value)
    :=
    if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
    then (cornucopiaRevoke tt ;; ret None)
    else fail loc (MerrOther "'cheri_revoke' called without 'cornucopia' switch").

  Definition intrinsic_strfcap
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    buf_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    maxsize_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
    format_val <- option2memM "missing argument"  (List.nth_error args 2%nat) ;;
    cap_val <- option2memM "missing argument"  (List.nth_error args 3%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (funptrmap, c_value) =>
        (update
           (fun (st : mem_state) => mem_state_with_funptrmap funptrmap st))
        ;;
        match (buf_val, maxsize_val, format_val) with
        |
          (MVpointer _ (PVconcrete buf_cap),
            MVinteger _ (IV maxsize_n),
            MVpointer _ (PVconcrete format_cap)) =>
            load_string loc format_cap MAX_STRFCAP_FORMAT_LEN >>=
              (fun (format : string) =>
                 match C.strfcap format c_value with
                 | None =>
                     ret
                       (Some
                          (MVinteger
                             (CoqIntegerType.Signed CoqIntegerType.Long)
                             (IV (-1))))
                 | Some res =>
                     let res_size := String.length res in
                     let res_size_n := Z.of_nat res_size in
                     if Z.geb res_size_n maxsize_n then
                       ret
                         (Some
                            (MVinteger
                               (CoqIntegerType.Signed
                                  CoqIntegerType.Long)
                               (IV (-1))))
                     else
                       store_string loc res (Z.to_nat maxsize_n) buf_cap ;;
                       (ret
                          (Some
                             (MVinteger
                                (CoqIntegerType.Signed
                                   CoqIntegerType.Long) (IV res_size_n))))
                 end)
        | (_, _, _) =>
            fail loc
              (MerrOther
                 (String.append "call_intrinsic: wrong types in: '"
                    (String.append name "'")))
        end
    end.

  Definition intrinsic_bounds_set
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    upper_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (funptrmap, c_value) =>
        update (fun (st : mem_state) => mem_state_with_funptrmap funptrmap st)
        ;;
        match upper_val with
        | MVinteger CoqIntegerType.Size_t (IV n_value) =>
            let x' := (cap_to_Z c_value) in
            let c_value := C.cap_narrow_bounds c_value (Bounds.of_Zs (x', x' + n_value))
            in ret (Some (update_cap_in_mem_value cap_val c_value))
        | _ =>
            fail loc
              (MerrOther
                 (String.append
                    "call_intrinsic: 2nd argument's type is not size_t in: '"
                    (String.append name "'")))
        end
    end.

  Definition intrinsic_perms_and
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    mask_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (funptrmap, c_value) =>
        (update
           (fun (st : mem_state) =>
              mem_state_with_funptrmap funptrmap st))
        ;;
        match mask_val with
        | MVinteger (CoqIntegerType.Size_t as ity) (IV n_value)
          =>
            iss <- option2memM "is_signed_ity failed" (is_signed_ity DEFAULT_FUEL ity) ;;
            sz <- serr2InternalErr (sizeof DEFAULT_FUEL None (CoqCtype.Ctype [](CoqCtype.Basic (CoqCtype.Integer ity)))) ;;
            bytes_value <- serr2InternalErr (bytes_of_Z iss sz n_value) ;;
            let bits := bool_bits_of_bytes bytes_value in
            match Permissions.of_list bits with
            | None =>
                fail loc
                  (MerrOther
                     (String.append
                        "call_intrinsic: error decoding permission bits: '"
                        (String.append name "'")))
            | Some pmask =>
                let c_value := C.cap_narrow_perms c_value pmask
                in ret (Some (update_cap_in_mem_value cap_val c_value))
            end
        | _ =>
            fail loc
              (MerrOther
                 (String.append
                    "call_intrinsic: 2nd argument's type is not size_t in: '"
                    (String.append name "'")))
        end
    end.

  Definition intrinsic_offset_get
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (_, c_value) =>
        if (C.get_ghost_state c_value).(bounds_unspecified)
        then ret (Some (MVunspecified CoqCtype.size_t))
        else
          let v_value := C.cap_get_offset c_value in
          ret (Some (MVinteger CoqIntegerType.Size_t (IV v_value)))
    end.

  Definition intrinsic_address_get
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (_, c_value) =>
        let v_value := (cap_to_Z c_value) in
        ret (Some (MVinteger CoqIntegerType.Ptraddr_t (IV v_value)))
    end.

  Definition intrinsic_base_get
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (_, c_value) =>
        if (C.get_ghost_state c_value).(bounds_unspecified)
        then ret (Some (MVunspecified (CoqCtype.ptraddr_t tt)))
        else
          let v_value := fst (Bounds.to_Zs (C.cap_get_bounds c_value))
          in ret (Some (MVinteger CoqIntegerType.Ptraddr_t (IV v_value)))
    end.

  Definition intrinsic_length_get
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val
    with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (_, c_value) =>
        if (C.get_ghost_state c_value).(bounds_unspecified)
        then ret (Some (MVunspecified CoqCtype.size_t))
        else
          let '(base, limit) := Bounds.to_Zs (C.cap_get_bounds c_value) in
          (* length, as computed from the internal
                                representation of bounds, could exceed
                                the width of the return type. To avoid
                                that we cap it here *)
          max_size_t <- serr2InternalErr (max_ival CoqIntegerType.Size_t) ;;
          let length := Z.min (limit - base) (num_of_int max_size_t) in
          ret (Some (MVinteger CoqIntegerType.Size_t (IV length)))
    end.

  Definition intrinsic_tag_get
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    st <- get ;;
    match cap_of_mem_value st.(funptrmap) cap_val
    with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (_, c) =>
        if (C.get_ghost_state c).(tag_unspecified) then
          ret (Some (MVunspecified
                       (CoqCtype.Ctype []
                          (CoqCtype.Basic
                             (CoqCtype.Integer
                                CoqIntegerType.Bool)))))
        else
          let b_value := if C.cap_is_valid c then 1 else 0
          in ret (Some (MVinteger CoqIntegerType.Bool (IV b_value)))
    end.

  Definition intrinsic_tag_clear
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val <- option2memM "missing argument"  (List.nth_error args 0) ;;
    st <- get ;;
    match
      cap_of_mem_value st.(funptrmap) cap_val
    with
    | None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | Some (funptrmap, c_value) =>
        update (fun st => mem_state_with_funptrmap funptrmap st)
        ;;
        let c_value := C.cap_invalidate c_value in
        ret (Some (update_cap_in_mem_value cap_val c_value))
    end.

  Definition intrinsic_is_equal_exact
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    cap_val0 <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
    cap_val1 <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
    st <- get ;;
    match
      (cap_of_mem_value st.(funptrmap) cap_val0),
      (cap_of_mem_value st.(funptrmap) cap_val1) with
    | None, _ =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 1st argument in: '"
                (String.append name "'")))
    | _, None =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: non-cap 2nd argument in: '"
                (String.append name "'")))
    | Some (_, c0), Some (_, c1) =>
        let gs0 := C.get_ghost_state c0 in
        let gs1 := C.get_ghost_state c1 in
        if gs0.(tag_unspecified) || gs1.(tag_unspecified)
           || gs0.(bounds_unspecified) || gs1.(bounds_unspecified)
        then
          ret (Some (MVunspecified
                       (CoqCtype.Ctype []
                          (CoqCtype.Basic
                             (CoqCtype.Integer
                                CoqIntegerType.Bool)))))
        else
          let v_value := if C.eqb c0 c1 then 1 else 0 in
          ret
            (Some
               (MVinteger CoqIntegerType.Bool
                  (IV v_value)))
    end.

  Definition intrinsic_representable_length
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    match List.nth_error args 0%nat with
    | None =>
        raise (InternalErr "missing argument")
    | Some (MVinteger CoqIntegerType.Size_t (IV n_value)) =>
        let l_value := C.representable_length n_value in
        ret
          (Some
             (MVinteger CoqIntegerType.Size_t
                (IV l_value)))
    | Some _ =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: 1st argument's type is not size_t in: '"
                (String.append name "'")))
    end.

  Definition intrinsic_representable_alignment_mask
    (loc : location_ocaml) (args : list mem_value)
    : memM (option mem_value)
    :=
    match List.nth_error args 0%nat with
    | None =>
        raise (InternalErr "missing argument")
    | Some (MVinteger CoqIntegerType.Size_t (IV n_value))
      =>
        let l_value := C.representable_alignment_mask n_value in
        ret
          (Some
             (MVinteger CoqIntegerType.Size_t
                (IV l_value)))
    | Some _ =>
        fail loc
          (MerrOther
             (String.append
                "call_intrinsic: 1st argument's type is not size_t in: '"
                (String.append name "'")))
    end.

  Definition call_intrinsic
    (loc : location_ocaml) (name : string) (args : list mem_value)
    : memM (option mem_value)
    :=
    if String.eqb name "cheri_revoke"
    then intrinsic_revoke loc
    else if String.eqb name "strfcap"
         then intrinsic_strfcap loc args
         else if String.eqb name "cheri_bounds_set"
              then intrinsic_bounds_set loc args
              else if String.eqb name "cheri_perms_and"
                   then intrinsic_perms_and loc args
                   else if String.eqb name "cheri_offset_get"
                        then intrinsic_offset_get loc args
                        else if String.eqb name "cheri_address_get"
                             then intrinsic_address_get loc args
                             else if String.eqb name "cheri_base_get"
                                  then intrinsic_base_get loc args
                                  else if String.eqb name "cheri_length_get"
                                       then intrinsic_length_get loc args
                                       else if String.eqb name "cheri_tag_get"
                                            then intrinsic_tag_get loc args
                                            else if String.eqb name "cheri_tag_clear"
                                                 then intrinsic_tag_clear loc args
                                                 else if String.eqb name "cheri_is_equal_exact"
                                                      then intrinsic_is_equal_exact loc args
                                                      else if String.eqb name "cheri_representable_length"
                                                           then intrinsic_representable_length loc args
                                                           else if String.eqb name "cheri_representable_alignment_mask"
                                                                then intrinsic_representable_alignment_mask loc args
                                                                else
                                                                  fail loc
                                                                    (MerrOther
                                                                       (String.append
                                                                          "call_intrinsic: unknown intrinsic: '"
                                                                          (String.append name "'"))).

  Definition get_intrinsic_type_spec (name : string)
    : option intrinsics_signature
    :=
    if String.eqb name "cheri_revoke" then
      if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
      then Some ((ExactRet CoqCtype.void), [])
      else None
    else if String.eqb name "strfcap" then
           Some
             ((ExactRet
                 CoqCtype.signed_long),
               [
                 ExactArg
                   (CoqCtype.Ctype []
                      (CoqCtype.Pointer
                         {|
                           CoqCtype.const := false;
                           CoqCtype.restrict := true;
                           CoqCtype.volatile := false
                         |}
                         CoqCtype.signed_char));
                 ExactArg
                   CoqCtype.size_t;
                 ExactArg
                   (CoqCtype.Ctype []
                      (CoqCtype.Pointer
                         {| CoqCtype.const := true;
                           CoqCtype.restrict := true;
                           CoqCtype.volatile := false
                         |}
                         CoqCtype.signed_char));
                 PolymorphicArg
                   [
                     TyPred
                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                     TyPred
                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
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
                         (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                       TyPred
                         (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                       TyIsPointer
                     ];
                   ExactArg
                     CoqCtype.size_t
               ])
           else
             if String.eqb name "cheri_perms_and" then
               Some
                 ((CopyRet 0),
                   [
                     PolymorphicArg
                       [
                         TyPred
                           (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                         TyPred
                           (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                         TyIsPointer
                       ];
                     ExactArg
                       CoqCtype.size_t
                 ])
             else
               if String.eqb name "cheri_address_get" then
                 Some
                   ((ExactRet
                       (CoqCtype.ptraddr_t tt)),
                     [
                       PolymorphicArg
                         [
                           TyPred
                             (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                           TyPred
                             (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                           TyIsPointer
                         ]
                   ])
               else
                 if String.eqb name "cheri_base_get" then
                   Some
                     ((ExactRet
                         (CoqCtype.ptraddr_t tt)),
                       [
                         PolymorphicArg
                           [
                             TyPred
                               (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                             TyPred
                               (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                             TyIsPointer
                           ]
                     ])
                 else
                   if String.eqb name "cheri_length_get" then
                     Some
                       ((ExactRet
                           CoqCtype.size_t),
                         [
                           PolymorphicArg
                             [
                               TyPred
                                 (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                               TyPred
                                 (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                               TyIsPointer
                             ]
                       ])
                   else
                     if String.eqb name "cheri_tag_get" then
                       Some
                         ((ExactRet
                             (CoqCtype.Ctype []
                                (CoqCtype.Basic
                                   (CoqCtype.Integer CoqIntegerType.Bool)))),
                           [
                             PolymorphicArg
                               [
                                 TyPred
                                   (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                                 TyPred
                                   (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
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
                                     (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                                   TyPred
                                     (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                                   TyIsPointer
                                 ]
                           ])
                       else
                         if String.eqb name "cheri_is_equal_exact" then
                           Some
                             ((ExactRet
                                 (CoqCtype.Ctype []
                                    (CoqCtype.Basic
                                       (CoqCtype.Integer
                                          CoqIntegerType.Bool)))),
                               [
                                 PolymorphicArg
                                   [
                                     TyPred
                                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                                     TyPred
                                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                                     TyIsPointer
                                   ];
                                 PolymorphicArg
                                   [
                                     TyPred
                                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                                     TyPred
                                       (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                                     TyIsPointer
                                   ]
                             ])
                         else
                           if String.eqb name "cheri_representable_length" then
                             Some ((ExactRet CoqCtype.size_t), [ExactArg CoqCtype.size_t])
                           else
                             if
                               String.eqb name "cheri_representable_alignment_mask"
                             then
                               Some ((ExactRet CoqCtype.size_t), [ExactArg CoqCtype.size_t])
                             else
                               if String.eqb name "cheri_offset_get" then
                                 Some
                                   ((ExactRet
                                       CoqCtype.size_t),
                                     [
                                       PolymorphicArg
                                         [
                                           TyPred
                                             (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.intptr_t);
                                           TyPred
                                             (CoqCtype.ctypeEqual DEFAULT_FUEL CoqCtype.uintptr_t);
                                           TyIsPointer
                                         ]
                                   ])
                               else
                                 None.


End CheriMemoryImpl.

Module MemCommonExe:Mem_common(AddressValue)(Bounds).
  Include Mem_common(AddressValue)(Bounds).
End MemCommonExe.

Module CheriMemoryExe
  (MC:Mem_common(AddressValue)(Bounds))
  (C:CAPABILITY_GS
       (AddressValue)
       (Flags)
       (ObjType)
       (SealType)
       (Bounds)
       (Permissions)
  )
  (IMP: Implementation)
  (TD: TagDefs)
  (SW: CerbSwitchesDefs)
<: CheriMemoryImpl(MC)(C)(IMP)(TD)(SW).

  Include CheriMemoryImpl(MC)(C)(IMP)(TD)(SW).

End CheriMemoryExe.
