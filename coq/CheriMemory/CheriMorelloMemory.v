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

From Common Require Import SimpleError Utils ZMap.
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

Module Type CheriMemoryTypes
  (MC:Mem_common(AddressValue)(Bounds))
  (C:CAPABILITY_GS
       (AddressValue)
       (Flags)
       (ObjType)
       (SealType)
       (Bounds)
       (Permissions)
  )
  (IMP: Implementation).

  Import MC.
  Include AilTypesAux(IMP).

  Definition storage_instance_id : Set := Z.
  Definition symbolic_storage_instance_id : Set := Z.
  Definition floating_value : Set := float. (* 64 bit *)

  Inductive provenance : Set :=
  | Prov_disabled : provenance
  | Prov_none : provenance
  | Prov_some : storage_instance_id -> provenance
  | Prov_symbolic : symbolic_storage_instance_id -> provenance
  | Prov_device : provenance.

  Inductive function_pointer : Set :=
  | FP_valid : CoqSymbol.sym -> function_pointer
  | FP_invalid : C.t -> function_pointer.

  Inductive pointer_value_base : Set :=
  | PVfunction : function_pointer -> pointer_value_base
  | PVconcrete : C.t -> pointer_value_base.

  Inductive pointer_value_ind : Set :=
  | PV : provenance -> pointer_value_base -> pointer_value_ind.

  Inductive integer_value_ind : Set :=
  | IV : Z -> integer_value_ind
  | IC : bool -> C.t -> integer_value_ind.

  Inductive mem_value_with_err :=
  | MVEunspecified : CoqCtype.ctype -> mem_value_with_err
  | MVEinteger :
    CoqCtype.integerType -> integer_value_ind ->
    mem_value_with_err
  | MVEfloating :
    CoqCtype.floatingType -> floating_value ->
    mem_value_with_err
  | MVEpointer :
    CoqCtype.ctype -> pointer_value_ind -> mem_value_with_err
  | MVEarray : list mem_value_with_err -> mem_value_with_err
  | MVEstruct :
    CoqSymbol.sym ->
    list  (CoqSymbol.identifier *  CoqCtype.ctype * mem_value_with_err) ->
    mem_value_with_err
  | MVEunion :
    CoqSymbol.sym ->
    CoqSymbol.identifier -> mem_value_with_err ->
    mem_value_with_err
  | MVErr : mem_error -> mem_value_with_err.

  Inductive mem_value_ind :=
  | MVunspecified : CoqCtype.ctype -> mem_value_ind
  | MVinteger :
    CoqCtype.integerType -> integer_value_ind -> mem_value_ind
  | MVfloating :
    CoqCtype.floatingType -> floating_value -> mem_value_ind
  | MVpointer :
    CoqCtype.ctype -> pointer_value_ind -> mem_value_ind
  | MVarray : list mem_value_ind -> mem_value_ind
  | MVstruct :
    CoqSymbol.sym ->
    list (CoqSymbol.identifier * CoqCtype.ctype * mem_value_ind) -> mem_value_ind
  | MVunion :
    CoqSymbol.sym ->
    CoqSymbol.identifier -> mem_value_ind -> mem_value_ind.

  Inductive access_intention : Set :=
  | ReadIntent : access_intention
  | WriteIntent : access_intention
  | CallIntent : access_intention.

  Inductive readonly_status : Set :=
  | IsWritable : readonly_status
  | IsReadOnly : readonly_kind -> readonly_status.

  Inductive allocation_taint :=
  | Exposed
  | Unexposed.

  (* Unfortunate names of two consturctors are mirroring ones from
     OCaml `Nondeterminism` monad. Third one is used where `failwith` was
     or `assert false` was used in OCaml. *)
  Inductive memMError :=
  | Other: mem_error -> memMError
  | Undef0: location_ocaml -> (list undefined_behaviour) -> memMError
  | InternalErr: string -> memMError.

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
      prefix : CoqSymbol.prefix;
      base : AddressValue.t;
      size : Z;
      ty : option CoqCtype.ctype;
      is_readonly : readonly_status;
      is_dynamic : bool ;
      is_dead : bool ;
      taint : allocation_taint
    }.

  Record AbsByte :=
    {
      prov : provenance;
      copy_offset : option nat;
      value : option ascii
    }.

End CheriMemoryTypes.


(* OCaml Z.sign *)
Definition sign (x:Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos _ => 1
  | Zneg _ => (-1)
  end.

(* See [Z.ediv_rem] in OCaml ZArith *)
Definition quomod (a b: Z) : (Z*Z) :=
  let (q,r) := Z.quotrem a b in
  if Z.geb (sign r) 0 then (q,r) else
    if Z.geb (sign b) 0 then (Z.pred q, Z.add r b)
    else (Z.succ q, Z.sub r b).


Definition wrapI min_v max_v n :=
  let dlt := Z.succ (Z.sub max_v min_v) in
  let r := Z_integerRem_f n dlt in
  if Z.leb r max_v then r
  else Z.sub r dlt.


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
  (MT: CheriMemoryTypes(MC)(C)(IMP))
  (TD: TagDefs)
  (SW: CerbSwitchesDefs)
<: Memory(AddressValue)(Bounds)(MC).

  Import MC.
  Import MT.

  Definition name := "cheri-coq".

  Definition pointer_value := pointer_value_ind.
  Definition integer_value := integer_value_ind.
  Definition floating_value : Set := MT.floating_value.
  Definition symbolic_storage_instance_id : Set := MT.symbolic_storage_instance_id.
  Definition storage_instance_id : Set := MT.storage_instance_id.
  Definition mem_value := mem_value_ind.


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
    Build_allocation prefix r.(base) r.(size) r.(ty) r.(is_readonly) r.(is_dynamic) r.(is_dead) r.(taint).

  Definition allocation_with_dead (r : allocation) :=
    Build_allocation r.(prefix) r.(base) r.(size) r.(ty) r.(is_readonly) r.(is_dynamic) true r.(taint).

  Definition absbyte_v prov copy_offset value : AbsByte
    :=
    {| prov := prov; copy_offset := copy_offset; value := value |}.


  Record mem_state_r :=
    {
      next_alloc_id : storage_instance_id;
      next_iota : symbolic_storage_instance_id;
      last_address : AddressValue.t;
      allocations : ZMap.t allocation;
      iota_map : ZMap.t
                   ((* `Single *) storage_instance_id +
                      (* `Double *) storage_instance_id * storage_instance_id);
      funptrmap : ZMap.t
                    (digest * string * C.t);
      varargs : ZMap.t
                  (Z * list (CoqCtype.ctype * pointer_value));
      next_varargs_id : Z;
      bytemap : ZMap.t AbsByte;
      capmeta : ZMap.t (bool* CapGhostState);
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
                capmeta          := st.(capmeta);
              |}
   *)

  Definition mem_state := mem_state_r.

  Definition mem_state_with_bytemap bytemap (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) bytemap r.(capmeta).

  Definition mem_state_with_allocations allocations (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) allocations r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_iota_map iota_map (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) iota_map r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_next_iota next_iota (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) next_iota r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_capmeta capmeta (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) r.(varargs) r.(next_varargs_id) r.(bytemap) capmeta.

  Definition mem_state_with_funptrmap funptrmap (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) funptrmap r.(varargs) r.(next_varargs_id) r.(bytemap) r.(capmeta).

  Definition mem_state_with_varargs_next_varargs_id varargs next_varargs_id (r : mem_state) :=
    Build_mem_state_r r.(next_alloc_id) r.(next_iota) r.(last_address) r.(allocations) r.(iota_map) r.(funptrmap) varargs next_varargs_id r.(bytemap) r.(capmeta).


  Definition initial_address := AddressValue.of_Z (HexString.to_Z "0xFFFFFFFF").

  Definition DEFAULT_FUEL:nat := 1000%nat. (* TODO maybe needs to be abstracted *)
  Definition MAX_STRFCAP_FORMAT_LEN := 4096%nat.

  Definition initial_mem_state : mem_state :=
    {|
      next_alloc_id := Z0;
      next_iota := Z0;
      last_address := initial_address;
      allocations := ZMap.empty allocation;
      iota_map := ZMap.empty (storage_instance_id + storage_instance_id * storage_instance_id);
      funptrmap := ZMap.empty (digest * string * C.t);
      varargs := ZMap.empty (Z * list (CoqCtype.ctype * pointer_value));
      next_varargs_id := Z0;
      bytemap := ZMap.empty AbsByte;
      capmeta := ZMap.empty _;
    |}.

  Definition memM := errS mem_state memMError.
  #[local] Instance memM_monad: Monad memM.
  Proof.
    typeclasses eauto.
  Defined.

  Definition mprint_msg (msg : string) : memM unit :=
    ret (print_msg msg).

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

  Inductive footprint_ind :=
  (* base address, size *)
  | FP: footprint_kind -> AddressValue.t -> Z -> footprint_ind.

  Definition footprint := footprint_ind.

  Definition cap_to_Z c := AddressValue.to_Z (C.cap_get_value c).

  Definition overlapping a b :=
    match a,b with
    | FP k1 b1 sz1, FP k2 b2 sz2 =>
        match k1, k2 with
        | Read, Read => false
        | _, _ => negb
                    (orb
                       (Z.leb (Z.add (AddressValue.to_Z b1) sz1) (AddressValue.to_Z b2))
                       (Z.leb (Z.add (AddressValue.to_Z b2) sz2) (AddressValue.to_Z b1)))
        end
    end.

  Definition unwrap_cap_value n :=
    let ptraddr_bits := (Z.of_nat C.sizeof_ptraddr) * 8 in
    let min_v := Z.opp (Z.pow 2 (ptraddr_bits - 1)) in
    let max_v := Z.sub (Z.pow 2 (ptraddr_bits - 1)) 1 in
    if Z.leb n min_v && Z.leb n max_v
    then n
    else wrapI min_v max_v n.

  Definition num_of_int x :=
    match x with
    | IV n => n
    | IC is_signed c =>
        let n := (cap_to_Z c) in
        if is_signed then unwrap_cap_value n else n
    end.

  (* Creare new cap meta for region where all tags are unspecified *)
  Program Definition init_ghost_tags
    (addr: AddressValue.t)
    (size: Z)
    (capmeta: ZMap.t (bool*CapGhostState)): ZMap.t (bool*CapGhostState)
    :=
    let align := IMP.get.(alignof_pointer) in
    let lower_a x :=
      let (q,_) := quomod x align in
      Z.mul q align in
    let a0 := lower_a (AddressValue.to_Z addr) in
    let a1 := lower_a (Z.pred (Z.add (AddressValue.to_Z addr) size)) in
    let v := (false, {| tag_unspecified := true; bounds_unspecified := false |}) in
    let n := Z.to_nat (Z.div a1 a0) in
    zmap_range_init a0 n align v capmeta.

  (** "Ghost" capability existing tags for memory region starting from [addr]
      with [size].

      All "true" tags associated with addresses in this region will be
      marked as unspecified.

      All "false" tags will be left intact.
   *)
  Definition ghost_tags
    (addr: AddressValue.t)
    (size: Z)
    (capmeta: ZMap.t (bool*CapGhostState)): ZMap.t (bool*CapGhostState)
    :=
    let align := IMP.get.(alignof_pointer) in
    let lower_a x :=
      let (q,_) := quomod x align in
      Z.mul q align in
    let a0 := lower_a (AddressValue.to_Z addr) in
    let a1 := lower_a (Z.pred (Z.add (AddressValue.to_Z addr) size)) in
    ZMap.mapi
      (fun (a:Z) '(t, gs) =>
         if negb gs.(tag_unspecified) && t && Z.geb a a0 && Z.leb a a1
         then
           (true, {| tag_unspecified := true; bounds_unspecified := gs.(bounds_unspecified) |})
         else (t, gs)
      ) capmeta.

  Definition allocator (size:Z) (align:Z) : memM (storage_instance_id * AddressValue.t) :=
    get >>= fun st =>
        let alloc_id := st.(next_alloc_id) in
        (
          let z := Z.sub (AddressValue.to_Z st.(last_address)) size in
          let (q,m) := quomod z align in
          let z' := Z.sub z (if Z.ltb q 0 then Z.opp m else m) in
          if Z.leb z' 0 then
            fail_noloc (MerrOther "CHERI.allocator: failed (out of memory)")
          else
            ret z'
        )
          >>= fun addr =>
            put
              {|
                next_alloc_id    := Z.succ alloc_id;
                next_iota        := st.(next_iota);
                last_address     := AddressValue.of_Z addr;
                allocations      := st.(allocations);
                iota_map         := st.(iota_map);
                funptrmap        := st.(funptrmap);
                varargs          := st.(varargs);
                next_varargs_id  := st.(next_varargs_id);
                bytemap          := st.(bytemap);
                (* tags in newly allocated region are unspecified *)
                capmeta          := init_ghost_tags (AddressValue.of_Z addr) size st.(capmeta);
              |}
            ;;
            ret (alloc_id, (AddressValue.of_Z addr)).


  Definition alignof
    (fuel: nat)
    (maybe_tagDefs : option (SymMap.t CoqCtype.tag_definition))
    (ty: CoqCtype.ctype): serr Z
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
                    | None => ret 0
                    | Some (CoqCtype.FlexibleArrayMember _ _ _ elem_ty) =>
                        alignof_ fuel (CoqCtype.Ctype nil (CoqCtype.Array elem_ty None))
                    end ;;
                  monadic_fold_left
                    (fun acc '(_, (_, _, _, ty)) =>
                       al <- alignof_ fuel ty ;;
                       ret (Z.max al acc)
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
                       ret (Z.max al acc)
                    )
                    membrs
                    0
              | None => raise "could not find union tag to compute alignment"
              end
          end
      end
    in alignof_ fuel ty.

  Fixpoint offsetsof
    (fuel: nat)
    (tagDefs : SymMap.t CoqCtype.tag_definition)
    (tag_sym : CoqSymbol.sym)
    : serr (list (CoqSymbol.identifier * CoqCtype.ctype * Z) * Z)
    :=
    match fuel with
    | O => raise "offsetof out of fuel"
    | S fuel =>
        match SymMap.find tag_sym tagDefs with
        | Some (CoqCtype.StructDef membrs_ flexible_opt) =>
            let membrs :=
              match flexible_opt with
              | None => membrs_
              | Some (CoqCtype.FlexibleArrayMember attrs ident qs ty) =>
                  List.app membrs_ [ (ident, (attrs, None, qs, ty)) ]
              end in
            '(xs, maxoffset) <-
              monadic_fold_left
                (fun '(xs, last_offset) '(membr, (_, _, _, ty))  =>
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
        | Some (CoqCtype.UnionDef membrs) =>
            ret ((List.map (fun '(ident, (_, _, _, ty)) => (ident, ty, 0)) membrs), 0)
        | None => raise "could not find tag"
        end
    end
  with sizeof
         (fuel: nat)
         (maybe_tagDefs : option (SymMap.t CoqCtype.tag_definition))
    : CoqCtype.ctype -> serr Z
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
               |
                 (CoqCtype.Void | CoqCtype.Array _ None |
                   CoqCtype.Function _ _ _ |
                   CoqCtype.FunctionNoParams _) =>
                   raise "no sizeof for function types"
               | CoqCtype.Basic (CoqCtype.Integer ity) =>
                   option2serr "sizeof_ity not defined in Implementation" (IMP.get.(sizeof_ity) ity)
               | CoqCtype.Basic (CoqCtype.Floating fty) =>
                   option2serr "sizeof_fty not defined in Implementation" (IMP.get.(sizeof_fty) fty)
               | CoqCtype.Array elem_ty (Some n_value) =>
                   sz <- (sizeof fuel (Some tagDefs) elem_ty) ;;
                   ret (Z.mul n_value sz)
               | CoqCtype.Pointer _ _ =>
                   ret (IMP.get.(sizeof_pointer))
               | CoqCtype.Atomic atom_ty =>
                   sizeof fuel (Some tagDefs) atom_ty
               | CoqCtype.Struct tag_sym =>
                   '(_, max_offset) <- offsetsof fuel tagDefs tag_sym ;;
                   align <- alignof fuel (Some tagDefs) cty ;;
                   let x_value := Z.modulo max_offset align in
                   ret (if Z.eqb x_value 0 then
                          max_offset
                        else
                          Z.add max_offset (Z.sub align x_value))
               | CoqCtype.Union tag_sym =>
                   match SymMap.find tag_sym tagDefs with
                   | Some (CoqCtype.StructDef _ _) =>
                       raise "no alignment for struct with union tag"
                   | Some (CoqCtype.UnionDef membrs) =>
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

  Definition resolve_function_pointer
    (funptrmap : ZMap.t (digest * string * C.t))
    (fp : function_pointer)
    : ZMap.t (digest * string * C.t) * C.t
    :=
    match fp with
    | FP_valid (CoqSymbol.Symbol file_dig n opt_name) =>
        match ZMap.find n funptrmap with
        | Some (_, _, c) => (funptrmap, c)
        | None =>
            let c := C.alloc_fun (AddressValue.of_Z (Z.add (AddressValue.to_Z initial_address) n)) in
            (match opt_name with
             | CoqSymbol.SD_Id name =>
                 ZMap.add n (file_dig, name, c) funptrmap
             | _ => funptrmap
             end, c)
        end
    | FP_invalid c => (funptrmap, c)
    end.

  Definition default_prov (_:unit) :=
    if CoqSwitches.is_PNVI (SW.get_switches tt)
    then Prov_none
    else Prov_disabled.

  Fixpoint repr
    (fuel: nat)
    (funptrmap: ZMap.t (digest * string * C.t))
    (capmeta : ZMap.t (bool*CapGhostState))
    (addr : Z)
    (mval : mem_value)
    : serr ((ZMap.t (digest * string * C.t))
            * (ZMap.t (bool*CapGhostState))
            * (list AbsByte))
    :=
    match fuel with
    | O => raise "out of fuel in repr"
    | S fuel =>
        match mval with
        | MVunspecified ty =>
            sz <- sizeof DEFAULT_FUEL None ty ;;
            ret (funptrmap, (ghost_tags (AddressValue.of_Z addr) sz capmeta),
                (list_init (Z.to_nat sz) (fun _ => absbyte_v (default_prov tt) None None)))
        | MVinteger ity (IV n_value) =>
            iss <- option2serr "Could not get int signedness of a type in repr" (is_signed_ity DEFAULT_FUEL ity) ;;
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype nil (CoqCtype.Basic (CoqCtype.Integer ity))) ;;
            bs' <- bytes_of_Z iss (Z.to_nat sz) n_value ;;
            let bs := List.map (fun (x : ascii) => absbyte_v (default_prov tt) None (Some x)) bs' in
            ret (funptrmap, (ghost_tags (AddressValue.of_Z addr) (Z.of_nat (List.length bs)) capmeta), bs)
        | MVinteger ity (IC _ c_value) =>
            '(cb, ct) <- option2serr "int encoding error" (C.encode true c_value) ;;
            let capmeta := ZMap.add addr
                             (C.cap_is_valid c_value, C.get_ghost_state c_value)
                             capmeta
            in
            ret (funptrmap, capmeta,
                (mapi
                   (fun (i_value : nat) (b_value : ascii) =>
                      absbyte_v (default_prov tt) None (Some b_value)) cb))
        | MVfloating fty fval =>
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype nil (CoqCtype.Basic (CoqCtype.Floating fty))) ;;
            bs' <- bytes_of_Z true (Z.to_nat sz) (bits_of_float fval) ;;
            let bs := List.map (fun (x : ascii) => absbyte_v (default_prov tt) None (Some x)) bs'
            in
            ret (funptrmap, (ghost_tags (AddressValue.of_Z addr) (Z.of_nat (List.length bs)) capmeta), bs)
        | MVpointer ref_ty (PV prov ptrval_) =>
            match ptrval_ with
            | PVfunction
                ((FP_valid (CoqSymbol.Symbol file_dig n_value opt_name)) as
                  fp) =>
                let '(funptrmap, c_value) := resolve_function_pointer funptrmap fp in
                '(cb, ct) <- option2serr "valid function pointer encoding error" (C.encode true c_value) ;;
                let capmeta := ZMap.add addr
                                 (C.cap_is_valid c_value, C.get_ghost_state c_value)
                                 capmeta
                in
                ret (funptrmap, capmeta,
                    (mapi
                       (fun (i_value : nat) (b_value : ascii) =>
                          absbyte_v prov (Some i_value) (Some b_value)) cb))
            | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
                '(cb, ct) <- option2serr "pointer encoding error" (C.encode true c_value) ;;
                let capmeta := ZMap.add addr
                                 (C.cap_is_valid c_value, C.get_ghost_state c_value)
                                 capmeta
                in
                ret (funptrmap, capmeta,
                    (mapi
                       (fun (i_value : nat) (b_value : ascii) =>
                          absbyte_v prov (Some i_value) (Some b_value)) cb))
            end
        | MVarray mvals =>
            '(funptrmap, capmeta, _, bs_s) <-
              monadic_fold_left
                (fun '(funptrmap, captmeta, addr, bs) (mval : mem_value) =>
                   '(funptrmap, capmeta, bs') <- repr fuel funptrmap capmeta addr mval ;;
                   let addr := Z.add addr (Z.of_nat (List.length bs')) in
                   ret (funptrmap, capmeta, addr, (cons bs' bs)))
                mvals (funptrmap, capmeta, addr, nil) ;;
            ret (funptrmap, capmeta, (List.concat (List.rev bs_s)))
        | MVstruct tag_sym xs =>
            let padding_byte _ : AbsByte := absbyte_v (default_prov tt) None None in
            '(offs, last_off) <- offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym ;;
            sz <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype nil (CoqCtype.Struct tag_sym)) ;;
            let final_pad := Z.sub sz last_off in
            '(funptrmap, capmeta, _, bs) <-
              monadic_fold_left2
                (fun (f: ZMap.t (digest * string * C.t) * ZMap.t (bool*CapGhostState) * Z * list AbsByte) =>
                   let '(funptrmap, capmeta, last_off, acc) := f in
                   fun (f : CoqSymbol.identifier *  CoqCtype.ctype * Z) =>
                     let '(ident, ty, off) := f in
                     fun (function_parameter :
                           CoqSymbol.identifier *
                             CoqCtype.ctype * mem_value) =>
                       let '(_, _, mval) := function_parameter in
                       let pad := Z.sub off last_off in
                       '(funptrmap, capmeta, bs) <-
                         repr fuel funptrmap capmeta (Z.add addr off) mval ;;
                       sz <- sizeof DEFAULT_FUEL None ty ;;
                       ret (funptrmap, capmeta, (Z.add off sz),
                           (List.app acc
                              (List.app (list_init (Z.to_nat pad) padding_byte) bs))))
                (funptrmap, capmeta, 0, nil) offs xs ;;
            ret (funptrmap, capmeta,
                (List.app bs (list_init (Z.to_nat final_pad) padding_byte)))
        | MVunion tag_sym memb_ident mval =>
            size <- sizeof DEFAULT_FUEL None (CoqCtype.Ctype nil (CoqCtype.Union tag_sym)) ;;
            '(funptrmap', capmeta', bs) <- repr fuel funptrmap capmeta addr mval ;;
            ret (funptrmap', capmeta',
                (List.app bs
                   (list_init (Nat.sub (Z.to_nat size) (List.length bs))
                      (fun _ => absbyte_v (default_prov tt) None None))))
        end
    end.


  Definition allocate_object
    (tid:MC.thread_id)
    (pref:CoqSymbol.prefix)
    (int_val:integer_value)
    (ty:CoqCtype.ctype)
    (init_opt:option mem_value)
    : memM pointer_value
    :=
    let align_n := num_of_int int_val in
    size_n <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;

    let mask := C.representable_alignment_mask size_n in
    let size_n' := C.representable_length size_n in
    let align_n' := Z.max align_n (Z.add (Z.succ (0)) (AddressValue.to_Z (AddressValue.bitwise_complement (AddressValue.of_Z mask)))) in

    (*
    (if (negb ((Z.eqb size_n size_n') && (Z.eqb align_n align_n')))
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

    allocator size_n' align_n' >>=
      (fun '(alloc_id, addr) =>
         (*
         mprint_msg
           ("allocate_object addr="  ++ String.hex_str (AddressValue.to_Z addr) ++
              ", size=" ++ String.dec_str size_n' ++
              ", align=" ++ String.dec_str align_n' ++
              ", alloc_id=" ++ String.dec_str alloc_id
           ) ;;
          *)
         (match init_opt with
          | None =>
              let alloc := {| prefix := pref; base:= addr; size:= size_n'; ty:= Some ty; is_dynamic := false; is_dead := false; is_readonly:= IsWritable; taint:= Unexposed|} in
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
                          capmeta          := st.(capmeta);
                        |}) ;; ret false
          | Some mval =>  (* here we allocate an object with initiliazer *)
              let (ro,readonly_status) :=
                match pref with
                | CoqSymbol.PrefStringLiteral _ _ => (true,IsReadOnly ReadonlyStringLiteral)
                | _ => (false,IsWritable)
                end
              in
              let alloc := {| prefix:= pref; base:= addr; size:= size_n'; ty:= Some ty; is_dynamic := false; is_dead := false; is_readonly:= readonly_status; taint:= Unexposed |} in

              st <- get ;;
              '(funptrmap, capmeta, pre_bs) <- serr2memM (repr DEFAULT_FUEL st.(funptrmap) st.(capmeta) (AddressValue.to_Z addr) mval) ;;
              let bs := mapi (fun i b => (Z.add (AddressValue.to_Z addr) (Z.of_nat i), b)) pre_bs in
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
                  capmeta          := capmeta;
                |}
              ;;
              ret ro
          end)
           >>=
           fun ro =>
             let c := C.alloc_cap addr (AddressValue.of_Z size_n') in
             (* Check here *)
             let c :=
               if ro then
                 let p := C.cap_get_perms c in
                 let p := Permissions.perm_clear_store p in
                 let p := Permissions.perm_clear_store_cap p in
                 let p := Permissions.perm_clear_store_local_cap p in
                 C.cap_narrow_perms c p
               else c
             in
             let prov := if CoqSwitches.is_PNVI (SW.get_switches tt)
                         then Prov_some alloc_id
                         else Prov_disabled
             in
             ret (PV prov (PVconcrete c))
      ).

  Definition allocate_region
    (tid : MC.thread_id)
    (pref : CoqSymbol.prefix)
    (align_int : integer_value)
    (size_int : integer_value)
    : memM pointer_value
    :=
    let align_n := num_of_int align_int in
    let size_n := num_of_int size_int in
    let mask := C.representable_alignment_mask size_n in
    let size_n' := C.representable_length size_n in
    let align_n' :=
      Z.max align_n (Z.succ (AddressValue.to_Z (AddressValue.bitwise_complement (AddressValue.of_Z mask)))) in

    allocator size_n' align_n' >>=
      fun '(alloc_id, addr) =>
        let alloc :=
          {| prefix := CoqSymbol.PrefMalloc;
            base := addr;
            size := size_n';
            ty := None;
            is_dynamic := true ;
            is_dead := false ;
            is_readonly := IsWritable;
            taint := Unexposed |}
        in
        let c_value := C.alloc_cap addr (AddressValue.of_Z size_n') in
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
               capmeta          := st.(capmeta);
             |})
        ;;
        let prov := if CoqSwitches.is_PNVI (SW.get_switches tt)
                    then Prov_some alloc_id
                    else Prov_disabled
        in
        ret (PV prov (PVconcrete c_value)
          ).

  Definition cap_is_null  (c : C.t) : bool :=
    Z.eqb (cap_to_Z c) 0.

  (* find first live allocation with given starting addrress *)
  Definition find_live_allocation (addr:AddressValue.t) : memM (option (Z*allocation)) :=
    get >>= fun st =>
        ret
          (ZMap.fold (fun alloc_id alloc acc =>
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

    0. The allocation must be live (ensured by [find_live_allocation]
    1. The allocation must be dynamic
    2. Bounds must exactly span allocation
    3. Address must be equal to the beginning of allocation
    4. Permissions must be the same as returned by allocator

    TODO: assumes that [C.cap_get_value c = fst (C.cap_get_bounds c) ]
   *)
  Definition cap_match_dyn_allocation c alloc : bool :=
    let gs := C.get_ghost_state c in
    (negb (gs.(tag_unspecified) || gs.(tag_unspecified))) &&
      (Permissions.eqb (C.cap_get_perms c) Permissions.perm_alloc
       && alloc.(is_dynamic)
       && AddressValue.eqb alloc.(base) (C.cap_get_value c)
       && (let zbounds := Bounds.to_Zs (C.cap_get_bounds c) in
           let csize := (snd zbounds) - (fst zbounds) in
           Z.eqb alloc.(size) csize)).

  Definition remove_allocation (alloc_id : Z) : memM unit :=
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
                capmeta          := st.(capmeta);
              |}).

  Definition get_allocation (alloc_id : Z) : memM allocation :=
    get >>=
      fun st =>
        match ZMap.find alloc_id st.(allocations) with
        | Some v => ret v
        | None =>
            fail_noloc (MerrOutsideLifetime
                          (String.append "CHERI.get_allocation, alloc_id="
                             (of_Z alloc_id)))
        end.

  Definition is_dead_allocation (alloc_id : storage_instance_id) : memM bool :=
    get_allocation alloc_id >>= fun alloc => ret alloc.(is_dead).

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
                               | FAIL _ _ =>
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
                    capmeta          := st.(capmeta);
                  |}) ;; ret alloc_id.

  Definition is_pointer_algined (a : Z) : bool :=
    let v := IMP.get.(alignof_pointer) in
    let (_,m) := quomod a v in
    Z.eqb m 0.

  (* Convinience function to be used in breaking let to avoid match *)
  Definition break_PV (p:pointer_value) :=
    match p with
    | PV prov ptrval => (prov,ptrval)
    end.

  Inductive overlap_ind :=
  | NoAlloc: overlap_ind
  | SingleAlloc: storage_instance_id -> overlap_ind
  | DoubleAlloc: storage_instance_id -> storage_instance_id -> overlap_ind.

  Inductive prov_ptr_valid_ind :=
  | NotValidPtrProv
  | ValidPtrProv.

  Definition string_of_prov_ptr_valid_ind p :=
    match p with
    | NotValidPtrProv => "NotValidPtrProv"
    | ValidPtrProv => "ValidPtrProv"
    end.

  Inductive prov_valid_ind :=
  | VALID: provenance -> prov_valid_ind
  | INVALID: prov_valid_ind.

  Definition string_of_prov_valid_ind p :=
    match p with
    | VALID _ => "VALID _"
    | INVALID => "INVALID"
    end.

  Inductive bytes_ind :=
  | PtrBytes: Z -> bytes_ind
  | OtherBytes: bytes_ind.

  Definition split_bytes (bs : list AbsByte)
    : serr (provenance * prov_ptr_valid_ind * list (option ascii))
    :=
    match bs with
    | [] => raise "CHERI.AbsByte.split_bytes: called on an empty list"
    | bs =>
        '(_prov, rev_values, offset_status) <-
          monadic_fold_left
            (fun '(prov_acc, val_acc, offset_acc) b_value =>

               let acond :=
                 match prov_acc, b_value.(prov) with
                 | VALID (Prov_some alloc_id1), Prov_some alloc_id2 =>
                     Z.eqb alloc_id1 alloc_id2
                 | _, _ => false
                 end in

               let icond :=
                 match prov_acc, b_value.(prov) with
                 | VALID (Prov_symbolic iota1), Prov_symbolic iota2 =>
                     Z.eqb iota1 iota2
                 | _, _ => false
                 end in

               prov_acc' <-
                 match (prov_acc, b_value.(prov)), acond, icond with
                 | (VALID (Prov_some alloc_id1), Prov_some alloc_id2), false, _
                   => ret INVALID
                 | (VALID (Prov_symbolic iota1), Prov_symbolic iota2), _, false
                   => ret INVALID
                 | (VALID (Prov_symbolic iota1), Prov_some alloc_id'), _, _
                   => raise "TODO(iota) split_bytes 1"
                 | (VALID (Prov_some alloc_id), Prov_symbolic iota), _, _ =>
                     raise "TODO(iota) split_bytes 2"
                 | (VALID Prov_none, (Prov_some _) as new_prov), _, _ =>
                     ret (VALID new_prov)
                 | (VALID Prov_disabled, Prov_some _), _, _ =>
                     ret INVALID
                 | (VALID Prov_disabled, Prov_symbolic _), _, _ =>
                     ret INVALID
                 | (VALID Prov_none, (Prov_symbolic _) as new_prov), _, _ =>
                     ret (VALID new_prov)
                 | (prev_acc, _), _, _ => ret prev_acc
                 end ;;

               let offset_acc' :=
                 let ncond :=
                   match offset_acc, b_value.(copy_offset) with
                   | PtrBytes n1, Some n2 => Z.eqb n1 (Z.of_nat n2)
                   | _, _ => false
                   end in

                 match offset_acc, b_value.(copy_offset),ncond with
                 | PtrBytes n1, Some n2, true => PtrBytes (Z.add n1 1)
                 | _, _, _ => OtherBytes
                 end in

               ret (prov_acc', (cons b_value.(value) val_acc), offset_acc'))
            (List.rev bs) ((VALID (default_prov tt)), nil, (PtrBytes 0)) ;;

        let pvalid := match _prov with
                      | INVALID => Prov_disabled
                      | VALID z_value => z_value
                      end in

        let pptrvalid := match offset_status with
                         | OtherBytes => NotValidPtrProv
                         | _ => ValidPtrProv
                         end in

        ret (pvalid,pptrvalid,rev_values)
    end.

  Definition provs_of_bytes (bs : list AbsByte) : taint_ind :=
    let xs :=
      List.fold_left
        (fun (acc : list storage_instance_id) =>
         fun (b_value : AbsByte) =>
           match b_value.(prov) with
           | Prov_disabled
           | Prov_none
           | Prov_symbolic _
           | Prov_device
             => acc
           | Prov_some alloc_id => cons alloc_id acc
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
    if Z.leb n_value (AddressValue.to_Z C.min_ptraddr) && Z.leb n_value (AddressValue.to_Z C.max_ptraddr)
    then n_value
    else  wrapI (AddressValue.to_Z C.min_ptraddr) (AddressValue.to_Z C.max_ptraddr) n_value.

  Fixpoint abst
    (fuel: nat)
    (find_overlapping : Z -> overlap_ind)
    (funptrmap : ZMap.t (digest * string * C.t))
    (tag_query_f : Z -> (bool* CapGhostState))
    (addr : Z)
    (cty : CoqCtype.ctype)
    (bs : list AbsByte)
    : serr (taint_ind * mem_value_with_err * list AbsByte)
    :=
    match fuel with
    | O => raise "abst out of fuel"
    | S fuel =>
        let '(CoqCtype.Ctype _ ty) := cty in
        let self f := abst f find_overlapping funptrmap tag_query_f in
        sz <- sizeof DEFAULT_FUEL None cty ;;
        sassert (negb (Nat.ltb (List.length bs) (Z.to_nat sz))) "abst, |bs| < sizeof(ty)" ;;
        let merge_taint (x_value : taint_ind) (y_value : taint_ind) : taint_ind :=
          match (x_value, y_value) with
          | (NoTaint, NoTaint) => NoTaint
          | ((NoTaint, NewTaint xs) | (NewTaint xs, NoTaint)) => NewTaint xs
          | (NewTaint xs, NewTaint ys) => NewTaint (List.app xs ys)
          end in
        match ty with
        | (CoqCtype.Void | CoqCtype.Array _ None |
            CoqCtype.Function _ _ _ |
            CoqCtype.FunctionNoParams _) =>
            raise "abst on function!"
        | (CoqCtype.Basic (CoqCtype.Integer ((CoqCtype.Signed CoqCtype.Intptr_t) as ity))
          | CoqCtype.Basic (CoqCtype.Integer ((CoqCtype.Unsigned CoqCtype.Intptr_t) as ity)))
          =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, _, bs1') <- split_bytes bs1 ;;
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            let _:bool := iss in (* hack to hint type checker *)
            match extract_unspec bs1' with
            | Some cs =>
                ret (provs_of_bytes bs1,
                    let (tag,gs) := tag_query_f addr in
                    match C.decode (List.rev cs) tag with
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
            | None => ret (provs_of_bytes bs1, MVEunspecified cty, bs)
            end
        | CoqCtype.Basic (CoqCtype.Floating fty) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(_, _, bs1') <- split_bytes bs1 ;;
            match extract_unspec bs1' with
            | Some cs =>
                zb <- Z_of_bytes true cs ;;
                ret (NoTaint,MVEfloating fty (float_of_bits zb),bs2)
            | None => ret (NoTaint, MVEunspecified cty, bs2)
            end
        | CoqCtype.Basic (CoqCtype.Integer ity) =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, _, bs1') <- split_bytes bs1 ;;
            iss <- option2serr "Could not get signedness of a type"  (is_signed_ity DEFAULT_FUEL ity) ;;
            match extract_unspec bs1' with
            | Some cs =>
                zb <- Z_of_bytes iss cs ;;
                ret (provs_of_bytes bs1, MVEinteger ity (IV zb), bs2)
            | None =>
                ret (provs_of_bytes bs1, MVEunspecified cty, bs2)
            end
        | CoqCtype.Array elem_ty (Some n_value) =>
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
        | CoqCtype.Pointer _ ref_ty =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            let '(bs1, bs2) := split_at (Z.to_nat sz) bs in
            '(prov, prov_status, bs1') <- split_bytes bs1 ;;
            (* sprint_msg ("BS1 prov_status=" ++ (string_of_prov_ptr_valid_ind prov_status)) ;; *)
            match extract_unspec bs1' with
            | Some cs =>
                let (tag,gs) := tag_query_f addr in
                match C.decode (List.rev cs) tag with
                | None => ret (NoTaint, MVErr (MerrCHERI CheriErrDecodingCap), bs2)
                | Some c_value =>
                    let c_value := C.set_ghost_state c_value gs in
                    match ref_ty with
                    | CoqCtype.Ctype _ (CoqCtype.Function _ _ _) =>
                        let n_value := Z.sub (cap_to_Z c_value) (AddressValue.to_Z initial_address) in
                        match ZMap.find n_value funptrmap with
                        | Some (file_dig, name, c') =>
                            if C.eqb c_value c' then
                              ret (NoTaint, MVEpointer ref_ty
                                              (PV prov
                                                 (PVfunction
                                                    (FP_valid
                                                       (CoqSymbol.Symbol file_dig
                                                          n_value
                                                          (CoqSymbol.SD_Id name))))), bs2)
                            else
                              ret (NoTaint, MVEpointer ref_ty
                                              (PV prov (PVfunction (FP_invalid c_value))), bs2)
                        | None =>
                            ret (NoTaint, MVEpointer ref_ty
                                            (PV prov (PVfunction (FP_invalid c_value))), bs2)
                        end
                    | _ =>
                        let prov :=
                          match prov_status with
                          | NotValidPtrProv =>
                              match
                                find_overlapping
                                  (cap_to_Z c_value) with
                              | NoAlloc => (default_prov tt)
                              | SingleAlloc alloc_id => Prov_some alloc_id
                              | DoubleAlloc alloc_id1 alloc_id2 =>
                                  Prov_some alloc_id1
                              end
                          | ValidPtrProv => prov
                          end in
                        (* sprint_msg (C.to_string n_value) ;; *)
                        ret (NoTaint, MVEpointer ref_ty (PV prov (PVconcrete c_value)), bs2)
                    end
                end
            | None =>
                ret (NoTaint,
                    MVEunspecified (CoqCtype.Ctype nil (CoqCtype.Pointer CoqCtype.no_qualifiers ref_ty)), bs2)
            end
        | CoqCtype.Atomic atom_ty =>
            self fuel addr atom_ty bs
        | CoqCtype.Struct tag_sym =>
            sz <- sizeof DEFAULT_FUEL None cty ;;
            '(offsets,_) <- offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym ;;
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
        | CoqCtype.Union tag_sym =>
            raise "TODO: abst, Union (as value)"
        end
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
         | None => absbyte_v (default_prov tt) None None
         end)
      (list_init (Z.to_nat n_bytes)
         (fun (i : nat) =>
            let offset := Z.of_nat i in
            Z.add base_addr offset)).

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

  Definition find_overlapping_st st addr : overlap_ind
    :=
    let (require_exposed, allow_one_past) :=
      match CoqSwitches.has_switch_pred (SW.get_switches tt)
              (fun x => match x with SW_PNVI _ => true | _ => false end)
      with
      | Some (CoqSwitches.SW_PNVI variant) =>
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
                   if alloc.(is_dead)
                   then None
                   else if Z.leb (AddressValue.to_Z alloc.(base)) addr && Z.ltb addr (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size))
                        then
                          (* PNVI-ae, PNVI-ae-udi *)
                          if require_exposed && (negb (allocation_taint_eqb alloc.(taint) Exposed))
                          then None
                          else Some alloc_id
                        else if allow_one_past then
                               (* PNVI-ae-udi *)
                               if Z.eqb addr (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size))
                                  && negb (require_exposed && (negb (allocation_taint_eqb alloc.(taint) Exposed)))
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

  Definition find_overlapping addr : memM overlap_ind
    :=  get >>= fun st => ret (find_overlapping_st st addr).

  (* If pointer stored at [addr] with meta information [meta] has it's
     base within given [base] and [limit] region, revoke it by returning
     new meta.
   *)
  Definition maybe_revoke_pointer
    (alloc_base alloc_limit: Z)
    (st: mem_state)
    (addr: Z)
    (meta: (bool*CapGhostState))
    :
    memM (bool* CapGhostState)
    :=
    (* mprint_msg ("maybe_revoke_pointer "  ++ String.hex_str addr) ;; *)
    if negb (fst meta)
    then ret meta (* the pointer is already untagged *)
    else
      let bs := fetch_bytes st.(bytemap) addr IMP.get.(sizeof_pointer) in
      '(_, mval, _) <-
        serr2memM (abst DEFAULT_FUEL (fun _ => NoAlloc) st.(funptrmap) (fun _ => meta) addr
                                                             (CoqCtype.mk_ctype_pointer CoqCtype.no_qualifiers CoqCtype.void) bs)
      ;;
      match mval with
      | MVEpointer _ (PV _ (PVconcrete c)) =>
          let '(t, gs) := meta  in
          let ptr_base := fst (Bounds.to_Zs (C.cap_get_bounds c)) in
          if Z.leb alloc_base ptr_base && Z.ltb ptr_base alloc_limit
          then ret (false, {| tag_unspecified := false; bounds_unspecified := gs.(bounds_unspecified) |})
          else ret meta (* outside allocation. leave unchanged *)
      | MVEunspecified _ => raise (InternalErr "unexpected unspec.")
      | _ => raise (InternalErr "unexpected abst return value. Expecting concrete pointer.")
      end.

  (* revoke (clear tag) any pointer in the memory pointing within the
     bounds of given dynamic allocation.
   *)
  Definition revoke_pointers alloc : memM unit
    :=
    if alloc.(is_dynamic)
    then
      let base := AddressValue.to_Z alloc.(base) in
      let limit := base + alloc.(size) in
      (* mprint_msg ("revoke_pointers " ++ (String.hex_str base) ++ " - "  ++ (String.hex_str limit)) ;; *)
      get >>=
        (fun st =>
           zmap_mmapi
             (maybe_revoke_pointer base limit st)
             st.(capmeta)
        )
        >>=
        (fun newmeta => update (fun st => mem_state_with_capmeta newmeta st))
      ;; ret tt
    else
      ret tt. (* allocation is not dynamic *)

  Definition kill
    (loc : location_ocaml)
    (is_dyn : bool)
    (ptr : pointer_value)
    : memM unit
    :=

    let precond c alloc alloc_id :=
      if is_dyn && negb (cap_match_dyn_allocation c alloc)
      then fail loc (MerrUndefinedFree Free_non_matching)
      else
        if is_dyn && CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation INSTANT)
        then revoke_pointers alloc ;; remove_allocation alloc_id
        else ret tt
    in

    let update_allocations alloc alloc_id all_allocs :=
      if is_dyn && CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
      then zmap_update_element alloc_id (allocation_with_dead alloc) all_allocs
      else ZMap.remove alloc_id all_allocs
    in

    match ptr with
    | PV _ (PVfunction _) =>
        fail loc (MerrOther "attempted to kill with a function pointer")
    | PV Prov_none (PVconcrete c) =>
        fail loc (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV Prov_disabled (PVconcrete c) =>
        if cap_is_null c
           && CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_forbid_nullptr_free
        then fail loc MerrFreeNullPtr
        else
          find_live_allocation (C.cap_get_value c) >>=
            fun x =>
              match x with
              | None => fail loc
                          (if is_dyn
                           then (MerrUndefinedFree Free_non_matching)
                           else (MerrOther "attempted to kill with a pointer not matching any live allocation"))
              | Some (alloc_id,alloc) =>
                  precond c alloc alloc_id ;;
                  update
                    (fun st =>
                       {|
                         next_alloc_id    := st.(next_alloc_id);
                         next_iota        := st.(next_iota);
                         last_address     := st.(last_address) ;
                         allocations      := update_allocations alloc
                                               alloc_id
                                               st.(allocations);
                         iota_map         := st.(iota_map);
                         funptrmap        := st.(funptrmap);
                         varargs          := st.(varargs);
                         next_varargs_id  := st.(next_varargs_id);
                         bytemap          := st.(bytemap);
                         capmeta          := st.(capmeta);
                       |})
              end
    | PV Prov_device (PVconcrete _) => ret tt
    | PV (Prov_symbolic iota) (PVconcrete c) =>
        if cap_is_null c && CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_forbid_nullptr_free
        then fail loc MerrFreeNullPtr
        else
          let precondition z :=
            get_allocation z >>=
              fun alloc =>
                ret
                  (if alloc.(is_dead)
                   then (FAIL loc (MerrUndefinedFree Free_dead_allocation))
                   else if AddressValue.eqb (C.cap_get_value c) alloc.(base)
                        then OK
                        else FAIL loc (MerrUndefinedFree Free_out_of_bound))
          in
          resolve_iota precondition iota >>=
            (fun alloc_id =>
               get_allocation alloc_id >>=
                 (fun alloc =>
                    precond c alloc alloc_id ;;
                    update (fun st =>
                              {|
                                next_alloc_id    := st.(next_alloc_id);
                                next_iota        := st.(next_iota);
                                last_address     := st.(last_address) ;
                                allocations      := update_allocations alloc
                                                      alloc_id
                                                      st.(allocations) ;
                                iota_map         := st.(iota_map);
                                funptrmap        := st.(funptrmap);
                                varargs          := st.(varargs);
                                next_varargs_id  := st.(next_varargs_id);
                                bytemap          := st.(bytemap);
                                capmeta          := st.(capmeta);
                              |})
            ))
    | PV (Prov_some alloc_id) (PVconcrete c) =>
        if cap_is_null c
           && CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_forbid_nullptr_free
        then fail loc MerrFreeNullPtr
        else
          get_allocation alloc_id >>= fun alloc =>
              if alloc.(is_dead) then
                if is_dyn
                then fail loc (MerrUndefinedFree Free_dead_allocation)
                else raise (InternalErr "Concrete: FREE was called on a dead allocation")
              else
                if is_dyn && negb (cap_match_dyn_allocation c alloc)
                then fail loc (MerrUndefinedFree Free_non_matching)
                else
                  precond c alloc alloc_id ;;
                  update
                    (fun st =>
                       {|
                         next_alloc_id    := st.(next_alloc_id);
                         next_iota        := st.(next_iota);
                         last_address     := st.(last_address) ;
                         allocations      := update_allocations alloc
                                               alloc_id
                                               st.(allocations);
                         iota_map         := st.(iota_map);
                         funptrmap        := st.(funptrmap);
                         varargs          := st.(varargs);
                         next_varargs_id  := st.(next_varargs_id);
                         bytemap          := st.(bytemap);
                         capmeta          := st.(capmeta);
                       |})
    end.


  (** Checks if memory region starting from [addr] and
      of size [sz] fits withing interval \[b1,b2) *)
  Definition cap_bounds_check (bounds : Bounds.t)
    : Z -> Z -> bool
    :=
    let '(base, limit) := Bounds.to_Zs bounds in
    fun (addr : Z) (sz : Z) =>
      Z.leb base addr && Z.leb (Z.add addr sz) limit.

  Definition cap_check
    (loc : location_ocaml)
    (c : C.t)
    (offset : Z)
    (intent : access_intention)
    (sz : Z)
    : memM unit :=
    if (C.get_ghost_state c).(tag_unspecified) then
      fail loc (MerrCHERI CheriUndefinedTag)
    else
      if C.cap_is_valid c then
        let addr :=
          Z.add (cap_to_Z c) offset in
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
          let limit := Z.add addr sz in
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
                                          is_dynamic := alloc.(is_dynamic);
                                          is_dead := alloc.(is_dead);
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
                                                 is_dynamic := alloc.(is_dynamic);
                                                 is_dead := alloc.(is_dead);
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
    (lvalue_ty : CoqCtype.ctype)
    (addr : Z) : memM bool
    :=
    sz <- serr2memM (sizeof DEFAULT_FUEL None lvalue_ty) ;;
    get_allocation alloc_id >>=
      (fun (alloc : allocation) =>
         ret
           (Z.leb (AddressValue.to_Z alloc.(base)) addr
            && Z.leb
                 (Z.add addr sz)
                 (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size)))).

  Definition device_ranges : list (AddressValue.t * AddressValue.t) :=
    [ (AddressValue.of_Z 0x40000000, AddressValue.of_Z 0x40000004)
      ; (AddressValue.of_Z 0xABC, AddressValue.of_Z 0XAC0) ].

  Definition is_within_device (ty : CoqCtype.ctype) (addr : Z) : memM bool
    :=
    sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
    ret
      (List.existsb
         (fun '(min, max) =>
              Z.leb (AddressValue.to_Z min) addr
              && Z.leb (Z.add addr sz) (AddressValue.to_Z max))
         device_ranges).

  Definition is_atomic_member_access
    (alloc_id : Z.t)
    (lvalue_ty : CoqCtype.ctype)
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
             e <- serr2memM (CoqCtype.ctypeEqual DEFAULT_FUEL lvalue_ty ty) ;;
             ret
               (negb
                  (Z.eqb addr (AddressValue.to_Z alloc.(base)) && (Z.eqb sz alloc.(size) && e)))
         | _, _ => ret false
         end).

  Definition load
    (loc: location_ocaml)
    (ty: CoqCtype.ctype)
    (p: pointer_value)
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
           let tag_query (a_value : Z) : bool* CapGhostState :=
             if is_pointer_algined a_value then
               match ZMap.find a_value st.(capmeta) with
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
           '(taint, mval, bs') <-
             serr2memM (abst DEFAULT_FUEL (find_overlapping_st st) st.(funptrmap) tag_query addr ty bs)
           ;;
           mem_value_strip_err loc mval >>=
             (fun (mval : mem_value) =>
                (if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_PNVI AE)
                    || CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_PNVI AE_UDI)
                 then expose_allocations taint
                 else ret tt) ;;
                sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
                let fp := FP Read (AddressValue.of_Z addr) sz in
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
                end))
    in
    let do_load_cap
          (alloc_id_opt : option storage_instance_id)
          (c : C.t)
          (sz : Z)
      : memM (footprint * mem_value)
      :=
      cap_check loc c 0 ReadIntent sz ;;
      do_load alloc_id_opt (cap_to_Z c) sz
    in
    let load_concrete (alloc_id:storage_instance_id) (c:C.t) : memM (footprint * mem_value) :=
      if cap_is_null c then
        fail loc (MerrAccess LoadAccess NullPtr)
      else
        (is_dead_allocation alloc_id) >>=
          (fun x =>
             match x with
             | true => fail loc (MerrAccess LoadAccess DeadPtr)
             | false => ret tt
             end)
        ;;
        is_within_bound alloc_id ty
          (cap_to_Z c) >>=
          (fun (function_parameter : bool) =>
             match function_parameter with
             | false =>
                 fail loc (MerrAccess LoadAccess OutOfBoundPtr)
             | true =>
                 is_atomic_member_access alloc_id ty
                   (cap_to_Z c) >>=
                   (fun (function_parameter : bool) =>
                      match function_parameter with
                      | true =>
                          fail loc (MerrAccess LoadAccess AtomicMemberof)
                      | false =>
                          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
                          do_load_cap (Some alloc_id) c sz
                      end)
             end)
    in
    match prov, ptrval_ with
    | _, PVfunction _ =>
        fail loc (MerrAccess LoadAccess FunctionPtr)
    | Prov_none, PVconcrete c =>
        fail loc (MerrAccess LoadAccess OutOfBoundPtr)
    | Prov_disabled, PVconcrete c =>
        find_overlapping (cap_to_Z c) >>= fun x =>
            match x with
            | NoAlloc => fail loc (MerrAccess LoadAccess OutOfBoundPtr)
            | DoubleAlloc _ _ => fail loc (MerrInternal "DoubleAlloc without PNVI")
            | SingleAlloc alloc_id => load_concrete alloc_id c
            end
    | Prov_device, PVconcrete c =>
        if cap_is_null c then
          fail loc (MerrAccess LoadAccess NullPtr)
        else
          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
          is_within_device ty (cap_to_Z c) >>=
            (fun (function_parameter : bool) =>
               match function_parameter with
               | false =>
                   fail loc (MerrAccess LoadAccess OutOfBoundPtr)
               | true =>
                   do_load_cap None c sz
               end)
    | Prov_symbolic iota, PVconcrete addr =>
        if cap_is_null addr then
          fail loc
            (MerrAccess
               LoadAccess
               NullPtr)
        else
          let precondition (z_value : storage_instance_id) : memM merr
            :=
            is_dead_allocation z_value >>=
              (fun (function_parameter : bool) =>
                 if function_parameter
                 then ret (FAIL loc (MerrAccess LoadAccess DeadPtr))
                 else
                   is_within_bound z_value ty (cap_to_Z addr) >>=
                     (fun (function_parameter : bool) =>
                        match function_parameter with
                        | false =>
                            ret (FAIL loc (MerrAccess LoadAccess OutOfBoundPtr))
                        | true =>
                            is_atomic_member_access z_value ty
                              (cap_to_Z addr) >>=
                              (fun (function_parameter : bool) =>
                                 match function_parameter with
                                 | true =>
                                     ret (FAIL loc (MerrAccess LoadAccess AtomicMemberof))
                                 | false => ret OK
                                 end)
                        end))
          in
          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
          resolve_iota precondition iota >>=
            (fun (alloc_id : storage_instance_id) =>
               do_load_cap (Some alloc_id) addr sz)
    | Prov_some alloc_id, PVconcrete c =>
        load_concrete alloc_id c
    end.

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
      | MVarray ((cons mval _) as mvals) =>
          mt <- typeof mval ;;
          ret (CoqCtype.Array mt (Some (Z.of_nat (List.length mvals))))
      | MVstruct tag_sym _ => ret (CoqCtype.Struct tag_sym)
      | MVunion tag_sym _ _ => ret (CoqCtype.Union tag_sym)
      end ;;
    ret (CoqCtype.Ctype [] ct).

  Definition store
    (loc : location_ocaml)
    (cty : CoqCtype.ctype)
    (is_locking : bool)
    (ptr : pointer_value)
    (mval : mem_value)
    : memM  footprint
    :=
    let '(prov,ptrval_) := break_PV ptr in
    cond <- serr2memM (
                mt <- typeof mval ;;
                CoqCtype.ctypeEqual DEFAULT_FUEL (CoqCtype.unatomic cty)
                  (CoqCtype.unatomic mt))
    ;;
    if negb cond 
    then fail loc (MerrOther "store with an ill-typed memory value")
    else
      let do_store_cap
            (alloc_id_opt : option storage_instance_id)
            (c_value : C.t)
        : memM footprint
        :=
        nsz <- serr2memM (sizeof DEFAULT_FUEL None cty) ;;
        cap_check loc c_value 0 WriteIntent nsz ;;
        let addr := (cap_to_Z c_value) in
        
        st <- get ;;
        '(funptrmap, capmeta, pre_bs) <-
          serr2memM (repr DEFAULT_FUEL st.(funptrmap) st.(capmeta) addr mval)
        ;;
        let bs :=
          mapi (fun (i_value: nat) (b_value: AbsByte)
                => ((Z.add addr (Z.of_nat i_value)), b_value)) pre_bs
        in
        let bytemap : ZMap.t AbsByte := (List.fold_left
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
            capmeta          := capmeta;
          |}
        ;;
        ret (FP Write (AddressValue.of_Z addr) nsz)
      in
      let store_concrete alloc_id c :=
        if cap_is_null c  then
          fail loc (MerrAccess StoreAccess NullPtr)
        else
          is_within_bound alloc_id cty (cap_to_Z c)
            >>=
            (fun (x : bool) =>
               match x with
               | false =>
                   fail loc (MerrAccess StoreAccess OutOfBoundPtr)
               | true
                 =>
                   get_allocation alloc_id >>=
                     (fun (alloc : allocation) =>
                        match alloc.(is_readonly) with
                        | IsReadOnly ro_kind =>
                            fail loc (MerrWriteOnReadOnly ro_kind)
                        | IsWritable =>
                            is_atomic_member_access alloc_id cty
                              (cap_to_Z c) >>=
                              (fun (x : bool) =>
                                 match x with
                                 | true =>
                                     fail loc
                                       (MerrAccess LoadAccess AtomicMemberof)
                                 | false =>
                                     do_store_cap (Some alloc_id) c >>=
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
                                                                 prefix      := a.(prefix)     ;
                                                                 base        := a.(base)       ;
                                                                 size        := a.(size)       ;
                                                                 ty          := a.(ty)         ;
                                                                 is_dynamic  := a.(is_dynamic) ;
                                                                 is_dead     := a.(is_dead)    ;
                                                                 is_readonly := IsReadOnly ReadonlyConstQualified;
                                                                 taint       := a.(taint)      ;
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
      in

      match prov, ptrval_ with
      | _, PVfunction _ =>
          fail loc
            (MerrAccess
               StoreAccess
               FunctionPtr)
      | Prov_none, PVconcrete c =>
          fail loc (MerrAccess StoreAccess OutOfBoundPtr)
      | Prov_disabled, PVconcrete c =>
          find_overlapping (cap_to_Z c) >>= fun x =>
              match x with
              | NoAlloc => fail loc (MerrAccess StoreAccess OutOfBoundPtr)
              | DoubleAlloc _ _ => fail loc (MerrInternal "DoubleAlloc without PNVI")
              | SingleAlloc alloc_id => store_concrete alloc_id c
              end
      | Prov_device, PVconcrete c =>
          if cap_is_null c then
            fail loc
              (MerrAccess
                 StoreAccess
                 NullPtr)
          else
            is_within_device cty (cap_to_Z c) >>=
              (fun (x : bool) =>
                 if x
                 then do_store_cap None c
                 else fail loc (MerrAccess StoreAccess OutOfBoundPtr))
      | Prov_symbolic iota, PVconcrete c =>
          if cap_is_null c then
            fail loc
              (MerrAccess
                 StoreAccess
                 NullPtr)
          else
            let precondition (z_value : Z) : memM merr
              :=
              is_within_bound z_value cty (cap_to_Z c) >>=
                (fun (x : bool) =>
                   match x with
                   | false =>
                       ret (FAIL loc (MerrAccess StoreAccess OutOfBoundPtr))
                   | true =>
                       get_allocation z_value >>=
                         (fun (alloc : allocation) =>
                            match alloc.(is_readonly) with
                            | IsReadOnly ro_kind =>
                                ret
                                  (FAIL loc
                                     (MerrWriteOnReadOnly
                                        ro_kind))
                            | IsWritable =>
                                is_atomic_member_access z_value cty
                                (cap_to_Z c)
                                  >>=
                                  (fun (x : bool) =>
                                     if x
                                     then ret
                                            (FAIL loc (MerrAccess
                                                           LoadAccess
                                                           AtomicMemberof))
                                     else ret OK)
                            end)
                   end)
            in
            resolve_iota precondition iota >>=
              (fun (alloc_id : storage_instance_id) =>
                 do_store_cap (Some alloc_id) c >>=
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
                                              prefix      := a.(prefix)     ;
                                              base        := a.(base)       ;
                                              size        := a.(size)       ;
                                              ty          := a.(ty)         ;
                                              is_dynamic  := a.(is_dynamic) ;
                                              is_dead     := a.(is_dead)    ;
                                              is_readonly := IsReadOnly ReadonlyConstQualified;
                                              taint       := a.(taint)      ;
                                            |}
                                      | None => None
                                      end) st.(allocations))
                                st)
                       else
                         ret tt)
                      ;;
                      ret fp))
      | Prov_some alloc_id, PVconcrete c
        => store_concrete alloc_id c
(*
      | Prov_some alloc_id, PVconcrete addr
        =>
          if cap_is_null addr then
            fail loc (MerrAccess StoreAccess NullPtr)
          else
            is_within_bound alloc_id cty (AddressValue.to_Z (C.cap_get_value addr))
              >>=
              (fun (x : bool) =>
                 match x with
                 | false =>
                     fail loc (MerrAccess StoreAccess OutOfBoundPtr)
                 | true
                   =>
                     get_allocation alloc_id >>=
                       (fun (alloc : allocation) =>
                          match alloc.(is_readonly) with
                          | IsReadOnly ro_kind =>
                              fail loc (MerrWriteOnReadOnly ro_kind)
                          | IsWritable =>
                              is_atomic_member_access alloc_id cty
                                (AddressValue.to_Z (C.cap_get_value addr)) >>=
                                (fun (x : bool) =>
                                   match x with
                                   | true =>
                                       fail loc
                                         (MerrAccess LoadAccess AtomicMemberof)
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
                                                                   is_readonly := IsReadOnly ReadonlyConstQualified;
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
*)
      end.

  Definition null_ptrval (_:CoqCtype.ctype) : pointer_value
    :=
    PV (default_prov tt) (PVconcrete (C.cap_c0 tt)).

  Definition fun_ptrval (sym : CoqSymbol.sym)
    : serr pointer_value :=
    ret (PV (default_prov tt) (PVfunction (FP_valid sym))).

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
        match ZMap.find n_value st.(funptrmap) with
        | Some (file_dig, name, _) =>
            Some
              (CoqSymbol.Symbol file_dig n_value
                 (CoqSymbol.SD_Id name))
        | None => None
        end
    end.
 *)

  Definition case_funsym_opt (st:mem_state) (pv:pointer_value_ind): option CoqSymbol.sym
    :=
    let '(_, ptrval) := break_PV pv in
    match ptrval with
    | PVfunction (FP_valid sym) => Some sym
    | PVfunction (FP_invalid c)
    | PVconcrete c =>
        let n := (Z.sub (cap_to_Z c) (AddressValue.to_Z initial_address)) in
        match ZMap.find n st.(funptrmap) with
        | Some (file_dig, name, _) =>
            Some (CoqSymbol.Symbol file_dig n (SD_Id name))
        | None =>
            None
        end
    end.

  Definition eq_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVfunction (FP_valid sym1), PVfunction (FP_valid sym2) =>
        ret (CoqSymbol.symbolEquality sym1 sym2)
    | PVfunction (FP_invalid c1), PVfunction (FP_invalid c2) =>
        ret (AddressValue.eqb (C.cap_get_value c1) (C.cap_get_value c2))
    | PVfunction (FP_valid sym), PVfunction (FP_invalid c_value)
    | PVfunction (FP_invalid c_value), PVfunction (FP_valid sym) =>
        get >>=
          (fun (st : mem_state) =>
             let n_value :=
               Z.sub (cap_to_Z c_value) (AddressValue.to_Z initial_address)
             in
             match ZMap.find n_value st.(funptrmap) with
             | Some (file_dig, name, _) =>
                 let sym2 := CoqSymbol.Symbol file_dig n_value (CoqSymbol.SD_Id name) in
                 ret (CoqSymbol.symbolEquality sym sym2)
             | None =>
                 raise (InternalErr
                          "CHERI.eq_ptrval ==> FP_valid failed to resolve function symbol")
             end)
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

  Definition lt_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if cap_is_null addr1 || cap_is_null addr2 then
          fail loc (MerrWIP "lt_ptrval ==> one null pointer")
        else if CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_strict_pointer_relationals then
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
               | _, _, _ => fail loc MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Lt => true
                    | _ => false
                    end)
    | _, _ => fail loc (MerrWIP "lt_ptrval")
    end.


  Definition is_strict_pointer_arith (_:unit) :=
    CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_pointer_arith STRICT)
    || negb (CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_pointer_arith PERMISSIVE)).

  Definition gt_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if cap_is_null addr1 || cap_is_null addr2 then
          fail loc (MerrWIP "gt_ptrval ==> one null pointer")
        else if CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_strict_pointer_relationals then
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
               | _, _, _ => fail loc MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Gt => true
                    | _ => false
                    end)
    | _, _ => fail loc (MerrWIP "gt_ptrval")
    end.

  Definition le_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if cap_is_null addr1 || cap_is_null addr2
        then fail loc (MerrWIP "le_ptrval ==> one null pointer")
        else
          if CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_strict_pointer_relationals then
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
               | _, _, _ => fail loc MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Lt => true
                    | Eq => true
                    | _ => false
                    end)
    | _, _ => fail loc (MerrWIP "le_ptrval")
    end.

  Definition ge_ptrval
    (loc : location_ocaml)
    (ptr1 ptr2 : pointer_value) : memM bool
    :=
    let '(prov1, ptrval_1) := break_PV ptr1 in
    let '(prov2, ptrval_2) := break_PV ptr2 in
    match ptrval_1, ptrval_2 with
    | PVconcrete addr1, PVconcrete addr2 =>
        if cap_is_null addr1 || cap_is_null addr2 then
          fail loc (MerrWIP "ge_ptrval ==> one null pointer")
        else if CoqSwitches.has_switch (SW.get_switches tt) CoqSwitches.SW_strict_pointer_relationals then
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
               | _, _, _ => fail loc MerrPtrComparison
               end
             else
               ret (match C.value_compare addr1 addr2 with
                    | Gt => true
                    | Eq => true
                    | _ => false
                    end)
    | _, _ => fail loc (MerrWIP "ge_ptrval")
    end.

  Definition diff_ptrval
    (loc : location_ocaml)
    (diff_ty : CoqCtype.ctype) (ptrval1 ptrval2 : pointer_value)
    : memM integer_value
    :=
    let precond (alloc: allocation) (addr1 addr2: Z): bool
      :=
      Z.leb (AddressValue.to_Z alloc.(base)) addr1 &&
        Z.leb addr1 (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size)) &&
        Z.leb (AddressValue.to_Z alloc.(base)) addr2 &&
        Z.leb addr2 (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size))
    in
    let valid_postcond  (addr1 addr2: Z) : memM integer_value :=
      let diff_ty' :=
        match diff_ty with
        | CoqCtype.Ctype _ (CoqCtype.Array elem_ty _) => elem_ty
        | _ => diff_ty
        end in
      sz <- serr2memM (sizeof DEFAULT_FUEL None diff_ty') ;;
      ret (IV (Z.div (Z.sub addr1 addr2) sz))
    in
    let error_postcond := fail loc MerrPtrdiff
    in

    if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_pointer_arith PERMISSIVE)
    then
      match ptrval1, ptrval2 with
      | PV _ (PVconcrete addr1), PV _ (PVconcrete addr2) =>
          valid_postcond (cap_to_Z addr1) (cap_to_Z addr2)
      | _, _=> error_postcond
      end
    else
      match ptrval1, ptrval2 with
      | PV (Prov_some alloc_id1) (PVconcrete addr1),
        PV (Prov_some alloc_id2) (PVconcrete addr2) =>
          if Z.eqb alloc_id1 alloc_id2 then
            get_allocation alloc_id1 >>=
              (fun (alloc : allocation) =>
                 if precond alloc (cap_to_Z addr1) (cap_to_Z addr2)
                 then
                   valid_postcond (cap_to_Z addr1) (cap_to_Z addr2)
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
                              (cap_to_Z addr1)
                              (cap_to_Z addr2)
                          then
                            valid_postcond
                              (cap_to_Z addr1)
                              (cap_to_Z addr2)
                          else
                            error_postcond)
                   else
                     error_postcond
               | inr (alloc_id1, alloc_id2) =>
                   if Z.eqb alloc_id1 alloc_id' || Z.eqb alloc_id2 alloc_id'
                   then
                     get_allocation alloc_id' >>=
                       (fun (alloc : allocation) =>
                          if precond alloc
                               (cap_to_Z addr1)
                               (cap_to_Z addr2)
                          then
                            (update
                               (fun (st : mem_state) =>
                                  mem_state_with_iota_map
                                    (ZMap.add iota (inl alloc_id')
                                       st.(iota_map)) st))
                            ;;
                            (valid_postcond
                               (cap_to_Z addr1)
                               (cap_to_Z addr2))
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
                          (cap_to_Z addr1)
                          (cap_to_Z addr2)
                    | DoubleAlloc alloc_id1 alloc_id2 =>
                        match C.value_compare addr1 addr2 with
                        | Eq =>
                            valid_postcond
                              (cap_to_Z addr1)
                              (cap_to_Z addr2)
                        | _ =>
                            fail loc
                              (MerrOther
                                 "in `diff_ptrval` invariant of PNVI-ae-udi failed: ambiguous iotas with addr1 <> addr2")
                        end
                    end))
      | _,_ => error_postcond
      end.

  Definition update_prefix
    (x : CoqSymbol.prefix * mem_value)
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

  Local Open Scope string_scope.


  (*
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
        '(offs, _) <- serr2memM (offsetsof DEFAULT_FUEL (TD.tagDefs tt) tag_sym) ;;
        let fix find y :=
          match y with
          | [] => None
          | (CoqSymbol.Identifier _ memb, _, off) :: offs =>
              if Z.eqb offset off
              then Some (CoqSymbol.string_of_prefix alloc.(prefix) ++ "." ++ memb)
              else find offs
          end
        in
        ret (find offs)
    | Some (CoqCtype.Ctype _ (CoqCtype.Array ty _)) =>
        let offset := Z.sub addr alloc.(base) in
        if Z.ltb offset alloc.(size) then
          sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
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
        | PV _ (PVfunction _) =>
            fail_noloc
              (MerrOther
                 "called isWellAligned_ptrval on function pointer")
        | PV _ (PVconcrete addr) =>
            sz <- serr2memM (alignof DEFAULT_FUEL None ref_ty) ;;
            ret (Z.eqb (Z.modulo (cap_to_Z addr) sz) 0)
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
    | PV _ (PVfunction _) => ret false
    | (PV Prov_device (PVconcrete c_value)) as ptrval =>
        if cap_is_null c_value
        then ret false
        else isWellAligned_ptrval ref_ty ptrval
    | PV (Prov_symbolic iota) (PVconcrete c_value) =>
        if cap_is_null c_value
        then ret false
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
    | PV Prov_none (PVconcrete c_value) =>
        ret false
    | PV Prov_disabled (PVconcrete c_value) =>
        if cap_is_null c_value
        then ret false
        else
          find_overlapping (cap_to_Z c_value) >>= fun x =>
              match x with
              | NoAlloc => fail Loc_unknown (MerrAccess LoadAccess OutOfBoundPtr)
              | DoubleAlloc _ _ => fail Loc_unknown (MerrInternal "DoubleAlloc without PNVI")
              | SingleAlloc alloc_id => isWellAligned_ptrval ref_ty ptrval
              end
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
    (int_ty : CoqCtype.integerType)
    (ref_ty : CoqCtype.ctype)
    (int_v : integer_value) : memM pointer_value
    :=
    match int_ty, int_v with
    | CoqCtype.Unsigned CoqCtype.Intptr_t, IC _ c_value
    | CoqCtype.Signed CoqCtype.Intptr_t, IC _ c_value
      =>
        let addr := (cap_to_Z c_value) in
        find_overlapping addr >>=
          (fun x =>
             match x with
             | NoAlloc => ret (default_prov tt)
             | SingleAlloc alloc_id => ret (Prov_some alloc_id)
             | DoubleAlloc alloc_id1 alloc_id2 =>
                 add_iota (alloc_id1,alloc_id2) >>=
                   (fun (iota : symbolic_storage_instance_id) =>
                      ret (Prov_symbolic iota))
             end >>=
               (fun (prov : provenance) => ret (PV prov (PVconcrete c_value))))
    | CoqCtype.Unsigned CoqCtype.Intptr_t, IV _
    | CoqCtype.Signed CoqCtype.Intptr_t, IV _ =>
        raise (InternalErr "ptrfromint: invalid encoding for [u]intptr_t")
    | _, IV n_value =>
        if Z.eqb n_value 0
        then ret (PV (default_prov tt) (PVconcrete (C.cap_c0 tt)))
        else
          let addr :=
            let dlt := Z.succ (Z.sub (AddressValue.to_Z C.max_ptraddr) (AddressValue.to_Z C.min_ptraddr)) in
            let r_value := Z_integerRem_f n_value dlt in
            if  Z.leb r_value (AddressValue.to_Z C.max_ptraddr)
            then r_value
            else Z.sub r_value dlt
          in
          find_overlapping addr >>=
            (fun x =>
               match x with
               | NoAlloc => ret (default_prov tt)
               | SingleAlloc alloc_id => ret (Prov_some alloc_id)
               | DoubleAlloc alloc_id1 alloc_id2 =>
                   add_iota (alloc_id1, alloc_id2) >>=
                     (fun (iota : symbolic_storage_instance_id) =>
                        ret (Prov_symbolic iota))
               end >>=
                 (fun (prov : provenance) =>
                    let c_value := C.cap_set_value (C.cap_c0 tt) (AddressValue.of_Z addr) in
                    ret (PV prov (PVconcrete c_value))))
    | _, IC _ _ =>
        raise (InternalErr
                 "invalid integer value (capability for non- [u]intptr_t")
    end.

  Definition internal_intcast
    (loc : location_ocaml)
    (ity2 : CoqCtype.integerType)
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
      | CoqCtype.Bool =>
          if Z.eqb n_value 0 then
            0
          else
            1
      | _ =>
          if Z.leb n_value min_ity2 && Z.leb n_value max_ity2
          then n_value
          else wrapI min_ity2 max_ity2 n_value
      end in
    match ival, ity2 with
    | IC false _, CoqCtype.Unsigned CoqCtype.Intptr_t
    | IC true _, CoqCtype.Signed CoqCtype.Intptr_t =>
        ret (inr ival)
    | IC (false as is_signed) cap, CoqCtype.Signed CoqCtype.Intptr_t
    | IC (true as is_signed) cap,  CoqCtype.Unsigned CoqCtype.Intptr_t =>
        ret (inr  (IC (negb is_signed) cap))
    | IC false cap, _ =>
        let n_value := (cap_to_Z cap) in
        ret (inr (IV (conv_int_to_ity2 n_value)))
    | IC true cap, _ =>
        let n_value := (cap_to_Z cap) in
        ret (inr (IV (conv_int_to_ity2 (unwrap_cap_value n_value))))
    | IV n_value, CoqCtype.Unsigned CoqCtype.Intptr_t
    | IV n_value, CoqCtype.Signed CoqCtype.Intptr_t =>
        if Z.eqb n_value 0 then
          ret (inr (IC false (C.cap_c0 tt)))
        else
          let n_value := wrap_cap_value n_value in
          let c_value := C.cap_c0 tt in
          ret (inr (IC false (C.cap_set_value c_value (AddressValue.of_Z n_value))))
    | IV n_value, _ =>
        ret (inr (IV (conv_int_to_ity2 n_value)))
    end.

  Definition max_ival (ity: CoqCtype.integerType)
    : serr integer_value
    :=
    let signed_max (n_value : Z) : Z :=
      Z.sub (Z.pow 2 (Z.sub (Z.mul 8 n_value) 1)) 1 in
    let unsigned_max (n_value : Z) : Z :=
      Z.sub (Z.pow 2 (Z.mul 8 n_value)) 1 in
    match ity with
    | CoqCtype.Signed CoqCtype.Intptr_t =>
        ret (IV (signed_max (Z.of_nat C.sizeof_ptraddr)))
    | CoqCtype.Unsigned CoqCtype.Intptr_t =>
        ret (IV (unsigned_max (Z.of_nat C.sizeof_ptraddr)))
    | _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        match ity with
        | CoqCtype.Char =>
            if IMP.get.(CoqImplementation.is_signed_ity) CoqCtype.Char
            then ret (IV (signed_max n_value))
            else ret (IV (unsigned_max n_value))
        | CoqCtype.Bool => ret (IV (unsigned_max n_value))
        | CoqCtype.Size_t
        | CoqCtype.Wchar_t
        | CoqCtype.Unsigned _ => ret (IV (unsigned_max n_value))
        | CoqCtype.Ptrdiff_t
        | CoqCtype.Wint_t
        | CoqCtype.Signed _ => ret (IV (signed_max n_value))
        | CoqCtype.Ptraddr_t => ret (IV (unsigned_max n_value))
        | CoqCtype.Enum _ => ret (IV (signed_max 4))
        end
    end.

  Definition min_ival (ity: CoqCtype.integerType)
    : serr integer_value
    :=
    let signed_min (n_value: Z) : Z :=
      Z.opp (Z.pow 2 (Z.sub (Z.mul 8 n_value) 1)) in
    match ity with
    | CoqCtype.Char =>
        if IMP.get.(CoqImplementation.is_signed_ity) CoqCtype.Char
        then ret (IV (signed_min 1))
        else ret (IV 0)
    | CoqCtype.Bool
    | CoqCtype.Size_t
    | CoqCtype.Wchar_t
    | CoqCtype.Wint_t
    | CoqCtype.Unsigned _ => ret (IV 0)
    | CoqCtype.Signed CoqCtype.Intptr_t =>
        ret (IV (signed_min (Z.of_nat C.sizeof_ptraddr)))
    | CoqCtype.Ptrdiff_t
    | CoqCtype.Signed _ =>
        n_value <- option2serr "no sizeof_ity!" (IMP.get.(sizeof_ity) ity) ;;
        ret (IV (signed_min n_value))
    | CoqCtype.Ptraddr_t => ret (IV 0)
    | CoqCtype.Enum _ => ret (IV (signed_min 4))
    end.

  Definition intfromptr
    (loc : location_ocaml)
    (_ : CoqCtype.ctype)
    (ity: CoqCtype.integerType)
    (ptr: pointer_value)
    : memM integer_value
    :=
    let '(prov,ptrval_) := break_PV ptr in
    let wrap_intcast (ity2 : CoqCtype.integerType) (ival : integer_value)
      : memM integer_value
      :=
      icr <- serr2memM (internal_intcast loc ity2 ival) ;;
      match icr with
      | inl err => fail loc err
      | inr ival => ret ival
      end in
    match ptrval_ with
    |
      PVfunction
        (FP_valid ((CoqSymbol.Symbol _ n_value _) as fp)) =>
        get >>=
          (fun (st : mem_state) =>
             match ity with
             |
               (CoqCtype.Signed CoqCtype.Intptr_t |
                 CoqCtype.Unsigned CoqCtype.Intptr_t) =>
                 match ZMap.find n_value st.(funptrmap) with
                 | Some (file_dig, name, c_value) =>
                     wrap_intcast ity (IC false c_value)
                 | None =>
                     raise (InternalErr "intfromptr: Unknown function")
                 end
             | _ =>
                 ret (IV (Z.add (AddressValue.to_Z initial_address) n_value))
             end)
    | (PVfunction (FP_invalid c_value) | PVconcrete c_value) =>
        if cap_is_null c_value then
          match ity with
          | CoqCtype.Signed CoqCtype.Intptr_t =>
              ret (IC true (C.cap_c0 tt))
          | CoqCtype.Unsigned CoqCtype.Intptr_t =>
              ret (IC false (C.cap_c0 tt))
          | _ => ret (IV 0)
          end
        else
          (if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_PNVI AE) ||
                CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_PNVI AE_UDI)
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
            (CoqCtype.Signed CoqCtype.Intptr_t |
              CoqCtype.Unsigned CoqCtype.Intptr_t) =>
              wrap_intcast ity (IC false c_value)
          | _ =>
              maxival <- serr2memM (max_ival ity) ;;
              minival <- serr2memM (min_ival ity) ;;
              let ity_max := num_of_int maxival in
              let ity_min := num_of_int minival in
              let addr := (cap_to_Z c_value) in
              if Z.ltb addr ity_min || Z.ltb ity_max addr
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

  Inductive collapse_ind :=
  | NoCollapse: collapse_ind
  | Collapse: Z -> collapse_ind.

  Definition eff_array_shift_ptrval
    (loc : location_ocaml)
    (ptrval : pointer_value)
    (ty : CoqCtype.ctype)
    (ival_int : integer_value)
    : memM pointer_value
    :=
    let ival := num_of_int ival_int in
    sz <- serr2memM (sizeof DEFAULT_FUEL None ty) ;;
    let offset := Z.mul sz ival
    in
    let shift_concrete c_value shifted_addr alloc_id :=
      get_allocation alloc_id >>=
        (fun (alloc : allocation) =>
           if Z.leb (AddressValue.to_Z alloc.(base)) shifted_addr
              && Z.leb (Z.add shifted_addr sz)
                   (Z.add (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size)) sz)
           then
             let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
             ret (PV (Prov_some alloc_id) (PVconcrete c_value))
           else
             fail loc MerrArrayShift
        )
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
            Z.add (cap_to_Z c_value)
              offset in
          let precond (z_value : Z.t) : memM bool :=
            if is_strict_pointer_arith tt
            then
              get_allocation z_value >>=
                (fun (alloc : allocation) =>
                   ret (Z.leb (AddressValue.to_Z alloc.(base)) shifted_addr
                        && Z.leb
                             (Z.add shifted_addr sz)
                             (Z.add (Z.add (AddressValue.to_Z alloc.(base)) alloc.(size)) sz)))
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
                                        if CoqSwitches.has_switch (SW.get_switches tt) (SW_pointer_arith PERMISSIVE)
                                        then ret NoCollapse
                                        else
                                          fail loc
                                            (MerrOther
                                               "(PNVI-ae-uid) ambiguous non-zero array shift")
                                    | false => ret (Collapse alloc_id1)
                                    end)
                           | false =>
                               precond alloc_id2 >>=
                                 (fun (function_parameter : bool) =>
                                    match function_parameter with
                                    | true => ret (Collapse alloc_id2)
                                    | false => fail loc MerrArrayShift
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
                     let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
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
                                   | false => fail loc MerrArrayShift
                                   end)
                          end)
                     ;;
                     let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
                     ret (PV prov (PVconcrete c_value))
               | inl alloc_id =>
                   precond alloc_id >>=
                     (fun (function_parameter : bool) =>
                        match function_parameter with
                        | true =>
                            let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
                            ret (PV prov (PVconcrete c_value))
                        | false => fail loc MerrArrayShift
                        end)
               end)
    | PV (Prov_some alloc_id) (PVconcrete c_value) =>
        let shifted_addr := Z.add (cap_to_Z c_value) offset in
        if is_strict_pointer_arith tt
        then
          shift_concrete c_value shifted_addr alloc_id
        else
          let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
          ret (PV (Prov_some alloc_id) (PVconcrete c_value))
    | PV Prov_none (PVconcrete c_value) =>
        let shifted_addr := Z.add (AddressValue.to_Z (C.cap_get_value c_value)) offset in
        if is_strict_pointer_arith tt
        then fail loc (MerrOther "out-of-bound pointer arithmetic (Prov_none)")
        else
          let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
          ret (PV Prov_none (PVconcrete c_value))
    | PV Prov_disabled (PVconcrete c_value) =>
        let shifted_addr := Z.add (cap_to_Z c_value) offset in
        if is_strict_pointer_arith tt
        then
          find_overlapping (cap_to_Z c_value) >>= fun x =>
              match x with
              | NoAlloc => fail loc (MerrAccess LoadAccess OutOfBoundPtr)
              | DoubleAlloc _ _ => fail loc (MerrInternal "DoubleAlloc without PNVI")
              | SingleAlloc alloc_id => shift_concrete c_value shifted_addr  alloc_id
              end
        else
          let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
          ret (PV Prov_disabled (PVconcrete c_value))
    | PV Prov_device (PVconcrete c_value) =>
        let shifted_addr := Z.add (cap_to_Z c_value) offset in
        let c_value := C.cap_set_value c_value (AddressValue.of_Z shifted_addr) in
        ret (PV Prov_device (PVconcrete c_value))
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
    | Some (_, _, offset) => ret (IV offset)
    | None =>
        raise "CHERI.offsetof_ival: invalid memb_ident"
    end.

  Definition eff_member_shift_ptrval
    (loc : location_ocaml)
    (ptr : pointer_value)
    (tag_sym: CoqSymbol.sym)
    (memb_ident: CoqSymbol.identifier):  memM pointer_value
    :=
    let '(prov,ptrval_) := break_PV ptr in
    ioff <- serr2memM (offsetof_ival (TD.tagDefs tt) tag_sym memb_ident) ;;
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
          let addr := (cap_to_Z c_value) in
          let c_value := C.cap_set_value c_value (AddressValue.of_Z (Z.add addr offset)) in
          ret (PV prov (PVconcrete c_value))
    end.

  Definition memcpy
    (ptrval1 ptrval2: pointer_value)
    (size_int: integer_value)
    : memM pointer_value
    :=
    let cap_addr_of_pointer_value (ptr: pointer_value) : serr Z :=
      match ptr with
      | PV _ (PVconcrete c_value)
      | PV _ (PVfunction (FP_invalid c_value)) =>
          ret (cap_to_Z c_value)
      | _ => raise "memcpy: invalid pointer value"
      end in
    let size_n := num_of_int size_int in
    let loc := Loc_other "memcpy" in
    let fix copy_data (index: nat): memM pointer_value :=
      match index with
      | O => ret ptrval1
      | S index =>
          let i_value := Z.of_nat index in
          ptrval1' <- eff_array_shift_ptrval loc ptrval1 CoqCtype.unsigned_char (IV i_value) ;;
          ptrval2' <- eff_array_shift_ptrval loc ptrval2 CoqCtype.unsigned_char (IV i_value) ;;
          '(_, mval) <- load loc CoqCtype.unsigned_char ptrval2' ;;
          store loc CoqCtype.unsigned_char false ptrval1' mval ;;
          copy_data index
      end
    in
    let pointer_sizeof := IMP.get.(sizeof_pointer) in
    let npointer_sizeof := Z.to_nat pointer_sizeof in
    let fix copy_tags (index: nat): memM pointer_value :=
      let copy_tag (dst_p : pointer_value) (src_p : pointer_value)
        : memM unit :=
        dst_a <- serr2memM (cap_addr_of_pointer_value dst_p) ;;
        src_a <- serr2memM (cap_addr_of_pointer_value src_p) ;;
        update
          (fun (st : mem_state) =>
             match ZMap.find src_a st.(capmeta) with
             | None => st
             | Some t_value =>
                 if negb (is_pointer_algined dst_a)
                 then st
                 else mem_state_with_capmeta (ZMap.add dst_a t_value st.(capmeta)) st
             end)
      in
      match index with
      | O => ret ptrval1
      | S index =>
          let i_value := IV (Z.of_nat index) in
          ptrval1' <- eff_array_shift_ptrval loc ptrval1 CoqCtype.unsigned_char i_value ;;
          ptrval2' <- eff_array_shift_ptrval loc ptrval2 CoqCtype.unsigned_char i_value ;;
          copy_tag ptrval1' ptrval2' ;;
          copy_tags index
      end
    in
    copy_data (Z.to_nat size_n) ;;
    let (q,_) := quomod size_n pointer_sizeof in
    let size_n_bottom_aligned := Z.mul q pointer_sizeof in
    copy_tags (Z.to_nat size_n_bottom_aligned).

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
          load loc CoqCtype.unsigned_char ptrval >>=
            (fun (x : footprint * mem_value) =>
               match x with
               | (_, MVinteger _ (IV byte_n)) =>
                   eff_array_shift_ptrval loc ptrval
                     CoqCtype.unsigned_char (IV 1) >>=
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
      (ZMap.elements st.(allocations)) tt.

  Definition realloc
    (loc : location_ocaml)
    (tid : thread_id) (align : integer_value) (ptr : pointer_value)
    (size : integer_value) : memM pointer_value
    :=
    (if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
    then cornucopiaRevoke tt
    else ret tt) ;;
    match ptr with
    | PV Prov_none (PVconcrete c) =>
        if cap_is_null c  then
          allocate_region tid (CoqSymbol.PrefOther "realloc") align size
        else
          fail loc (MerrWIP "realloc no provenance")
    | PV Prov_disabled (PVconcrete c) =>
        if cap_is_null c  then
          allocate_region tid (CoqSymbol.PrefOther "realloc") align size
        else
          find_live_allocation (C.cap_get_value c) >>=
            fun x =>
              match x with
              | None => fail loc (MerrUndefinedFree Free_non_matching)
              | Some (alloc_id,alloc) =>
                  if negb (cap_match_dyn_allocation c alloc)
                  then fail loc (MerrUndefinedFree Free_non_matching)
                  else
                    allocate_region tid (CoqSymbol.PrefOther "realloc") align size >>=
                      (fun (new_ptr : pointer_value) =>
                         let size_to_copy :=
                           let size_n := num_of_int size in
                           IV (Z.min (MT.size alloc) size_n) in
                         memcpy new_ptr ptr size_to_copy ;;
                         kill (Loc_other "realloc") true ptr ;;
                         ret new_ptr)
              end
    | PV (Prov_some alloc_id) (PVconcrete c) =>
        if cap_is_null c then
          allocate_region tid (CoqSymbol.PrefOther "realloc") align size
        else
          get_allocation alloc_id >>=
            fun (alloc : allocation) =>
              if negb (cap_match_dyn_allocation c alloc)
              then fail loc (MerrUndefinedRealloc Free_non_matching)
              else
                if alloc.(is_dead)
                then fail loc (MerrUndefinedRealloc Free_dead_allocation)
                else
                  if AddressValue.eqb alloc.(base) (C.cap_get_value c)
                  then
                    allocate_region tid (CoqSymbol.PrefOther "realloc") align size >>=
                    (fun (new_ptr : pointer_value) =>
                       let size_to_copy :=
                         let size_n := num_of_int size in
                         IV (Z.min (MT.size alloc) size_n) in
                       memcpy new_ptr ptr size_to_copy ;;
                       kill (Loc_other "realloc") true ptr ;;
                       ret new_ptr)
                  else
                    fail loc (MerrUndefinedRealloc Free_out_of_bound)
    | PV _ _ =>
        fail loc (MerrWIP "realloc: invalid pointer")
    end.

  Definition va_start (args:  list (CoqCtype.ctype * pointer_value)) : memM integer_value :=
    get >>= fun st =>
        let id := st.(next_varargs_id) in
        update (fun st => mem_state_with_varargs_next_varargs_id (ZMap.add id (0, args) st.(varargs)) (Z.succ st.(next_varargs_id)) st) ;;
        ret (IV id).

  Definition va_copy (va : integer_value) : memM integer_value :=
    match va with
    | IV id =>
        get >>=
          fun st =>
            match ZMap.find id st.(varargs) with
            | Some args =>
                let id := st.(next_varargs_id) in
                update
                  (fun st =>
                     mem_state_with_varargs_next_varargs_id
                       (ZMap.add id args st.(varargs))
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
        get >>=
          fun st =>
            match ZMap.find id st.(varargs) with
            | Some (i_value, args) =>
                match Lists.List.nth_error args (Z.to_nat i_value) with
                | Some (_, ptr) =>
                    update
                      (fun st =>
                         mem_state_with_varargs_next_varargs_id
                           (ZMap.add id ((Z.add i_value 1), args) st.(varargs))
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
        get >>=
          fun st =>
            match ZMap.find id st.(varargs) with
            | Some _ =>
                update
                  (fun (st : mem_state) =>
                     mem_state_with_varargs_next_varargs_id
                       (ZMap.remove id st.(varargs))
                       st.(next_varargs_id) (* unchanged *)
                            st)
            | None =>
                fail_noloc (MerrWIP "va_end: not initiliased")
            end
    | _ => fail_noloc (MerrWIP "va_end: invalid va_list")
    end.

  Definition va_list (va_idx:Z) : memM (list (CoqCtype.ctype * pointer_value)) :=
    get >>=
      fun st=>
        match ZMap.find va_idx st.(varargs) with
        | Some (n_value, args) => ret args
        | None => fail_noloc (MerrWIP "va_list")
        end.

  Definition copy_alloc_id
    (ival : integer_value) (ptrval : pointer_value)
    : memM pointer_value
    :=
    intfromptr Loc_unknown CoqCtype.void (CoqCtype.Unsigned CoqCtype.Intptr_t) ptrval ;;
    ptrfromint Loc_unknown (CoqCtype.Unsigned CoqCtype.Intptr_t) CoqCtype.void ival.

  Definition concurRead_ival: CoqCtype.integerType -> CoqSymbol.sym -> serr (integer_value)
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

  Definition sizeof_ival (ty : CoqCtype.ctype): serr integer_value
    :=
    sz <- sizeof DEFAULT_FUEL None ty ;;
    ret (IV sz).

  Definition alignof_ival (ty: CoqCtype.ctype): serr integer_value
    :=
    a <- alignof DEFAULT_FUEL None ty ;;
    ret (IV a).

  Definition bitwise_complement_ival
    (ty : CoqCtype.integerType)
    (v : integer_value) : integer_value
    :=
    IV (Z.sub (Z.opp (num_of_int v)) 1).

  Definition bitwise_and_ival (ty : CoqCtype.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.land.

  Definition bitwise_or_ival (ty : CoqCtype.integerType)
    : integer_value -> integer_value -> integer_value :=
    int_bin Z.lor.

  Definition bitwise_xor_ival (ty : CoqCtype.integerType)
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
    Some (Z.eqb (num_of_int n1) (num_of_int n2)).

  Definition lt_ival (n1 n2: integer_value) :=
    Some (Z.ltb (num_of_int n1) (num_of_int n2)).

  Definition le_ival (n1 n2: integer_value) :=
    Some (Z.leb (num_of_int n1) (num_of_int n2)).

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
    (ity: CoqCtype.integerType)
    (fval: floating_value): serr integer_value
    :=
    match ity with
    | CoqCtype.Bool =>
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

  Definition unspecified_mval (ty: CoqCtype.ctype): mem_value := MVunspecified ty.

  Definition integer_value_mval
    (ity: CoqCtype.integerType) (ival: integer_value)
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
    (f_concur : CoqCtype.integerType -> CoqSymbol.sym -> A)
    (f_ival : CoqCtype.integerType -> integer_value -> A)
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

  Definition load_string (loc: location_ocaml) (c_value: C.t) (max_len: nat) : memM string
    :=
    let fix loop max_len (acc: string) (offset: Z) : memM string :=
      match max_len with
      | O => raise (InternalErr "string too long")
      | S max_len =>
          cap_check loc c_value offset ReadIntent 1 ;;
          let addr := Z.add (cap_to_Z c_value) offset
          in
          get >>=
            (fun st =>
               let bs := fetch_bytes st.(bytemap) addr 1 in
               ohd <- option2memM "fetch of 1 byte failed" (List.hd_error bs) ;;
               match ohd.(value) with
               | None => fail loc MerrReadUninit
               | Some c_value =>
                   if Ascii.eqb c_value zero
                   then ret acc
                   else
                     let s_value := String.append acc (String c_value "")
                     in loop max_len s_value (Z.succ offset)
               end)
      end
    in
    loop max_len "" 0.

  Definition store_string (loc : location_ocaml) (s_value : string) (n : nat) (c_value : C.t) : memM nat
    :=
    match n with
    | O => ret O
    | S n =>
        let cs := list_ascii_of_string s_value in
        let cs := List.firstn n cs in
        let pre_bs :=
          List.map
            (fun (c_value : ascii) =>
               {| prov := (default_prov tt); copy_offset := None;
                                     value := Some c_value |}) cs in
        let pre_bs :=
          List.app pre_bs
            [
              {| prov := (default_prov tt); copy_offset := None;
                                    value := Some "000" % char |}
            ] in
        let addr := (cap_to_Z c_value) in
        let bs :=
          mapi
            (fun (i_value : nat) (b_value : AbsByte) =>
               ((Z.add addr (Z.of_nat i_value)), b_value))
            pre_bs in
        cap_check loc c_value 0 WriteIntent (Z.of_nat (List.length bs)) ;;
        update
          (fun (st : mem_state) =>
             mem_state_with_bytemap
               (List.fold_left
                  (fun acc '(addr, b_value) => ZMap.add addr b_value acc)
                  bs st.(bytemap)) st)
        ;;
        ret (List.length bs)
    end.

  Definition call_intrinsic
    (loc : location_ocaml) (name : string) (args : list mem_value)
    : memM (option mem_value)
    :=
    if String.eqb name "cheri_revoke" then
      if CoqSwitches.has_switch (SW.get_switches tt) (CoqSwitches.SW_revocation CORNUCOPIA)
      then (cornucopiaRevoke tt ;; ret None)
      else fail loc (MerrOther "'cheri_revoke' called without 'cornucopia' switch")
    else if String.eqb name "strfcap" then
      buf_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
      maxsize_val <- option2memM "missing argument"  (List.nth_error args 1%nat) ;;
      format_val <- option2memM "missing argument"  (List.nth_error args 2%nat) ;;
      cap_val <- option2memM "missing argument"  (List.nth_error args 3%nat) ;;
      get >>=
        (fun (st : mem_state) =>
           match cap_of_mem_value st.(funptrmap) cap_val with
           | None =>
               fail loc
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
                   load_string loc format_cap MAX_STRFCAP_FORMAT_LEN >>=
                     (fun (format : string) =>
                        match C.strfcap format c_value with
                        | None =>
                            ret
                              (Some
                                 (MVinteger
                                    (CoqCtype.Signed CoqCtype.Long)
                                    (IV (-1))))
                        | Some res =>
                            let res_size := String.length res in
                            let res_size_n := Z.of_nat res_size in
                            if Z.geb res_size_n maxsize_n then
                              ret
                                (Some
                                   (MVinteger
                                      (CoqCtype.Signed
                                         CoqCtype.Long)
                                      (IV (-1))))
                            else
                              store_string loc res (Z.to_nat maxsize_n) buf_cap ;;
                              (ret
                                 (Some
                                    (MVinteger
                                       (CoqCtype.Signed
                                          CoqCtype.Long) (IV res_size_n))))
                        end)
               | (_, _, _) =>
                   fail loc
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
                 fail loc
                   (MerrOther
                      (String.append
                         "CHERI.call_intrinsic: non-cap 1st argument in: '"
                         (String.append name "'")))
             | Some (funptrmap, c_value) =>
                 update (fun (st : mem_state) => mem_state_with_funptrmap funptrmap st)
                 ;;
                 match upper_val with
                 | MVinteger CoqCtype.Size_t (IV n_value) =>
                     let x' := (cap_to_Z c_value) in
                     let c_value := C.cap_narrow_bounds c_value (Bounds.of_Zs (x', (Z.add x' n_value)))
                     in ret (Some (update_cap_in_mem_value cap_val c_value))
                 | _ =>
                     fail loc
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
                   fail loc
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
                   | MVinteger (CoqCtype.Size_t as ity) (IV n_value)
                     =>
                       iss <- option2memM "is_signed_ity failed" (is_signed_ity DEFAULT_FUEL ity) ;;
                       sz <- serr2memM (sizeof DEFAULT_FUEL None (CoqCtype.Ctype nil(CoqCtype.Basic (CoqCtype.Integer ity)))) ;;
                       bytes_value <- serr2memM (bytes_of_Z iss (Z.to_nat sz) n_value) ;;
                       let bits := bool_bits_of_bytes bytes_value in
                       match Permissions.of_list bits with
                       | None =>
                           fail loc
                             (MerrOther
                                (String.append
                                   "CHERI.call_intrinsic: error decoding permission bits: '"
                                   (String.append name "'")))
                       | Some pmask =>
                           let c_value := C.cap_narrow_perms c_value pmask
                           in ret (Some (update_cap_in_mem_value cap_val c_value))
                       end
                   | _ =>
                       fail loc
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
                     fail loc
                       (MerrOther
                          (String.append
                             "CHERI.call_intrinsic: non-cap 1st argument in: '"
                             (String.append name "'")))
                 | Some (_, c_value) =>
                     if (C.get_ghost_state c_value).(bounds_unspecified)
                     then ret (Some (MVunspecified CoqCtype.size_t))
                     else
                       let v_value := C.cap_get_offset c_value in
                       ret (Some (MVinteger CoqCtype.Size_t (IV v_value)))
                 end)
          else
            if String.eqb name "cheri_address_get" then
              cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
              get >>=
                (fun (st : mem_state) =>
                   match cap_of_mem_value st.(funptrmap) cap_val with
                   | None =>
                       fail loc
                         (MerrOther
                            (String.append
                               "CHERI.call_intrinsic: non-cap 1st argument in: '"
                               (String.append name "'")))
                   | Some (_, c_value) =>
                       let v_value := (cap_to_Z c_value) in
                       ret (Some (MVinteger CoqCtype.Ptraddr_t (IV v_value)))
                   end)
            else
              if String.eqb name "cheri_base_get" then
                cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                get >>=
                  (fun (st : mem_state) =>
                     match cap_of_mem_value st.(funptrmap) cap_val with
                     | None =>
                         fail loc
                           (MerrOther
                              (String.append
                                 "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                 (String.append name "'")))
                     | Some (_, c_value) =>
                         if (C.get_ghost_state c_value).(bounds_unspecified)
                         then ret (Some (MVunspecified (CoqCtype.ptraddr_t tt)))
                         else
                           let v_value := fst (Bounds.to_Zs (C.cap_get_bounds c_value))
                           in ret (Some (MVinteger CoqCtype.Ptraddr_t (IV v_value)))
                     end)
              else
                if String.eqb name "cheri_length_get" then
                  cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                  get >>=
                    (fun (st : mem_state) =>
                       match cap_of_mem_value st.(funptrmap) cap_val
                       with
                       | None =>
                           fail loc
                             (MerrOther
                                (String.append
                                   "CHERI.call_intrinsic: non-cap 1st argument in: '"
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
                             max_size_t <- serr2memM (max_ival CoqCtype.Size_t) ;;
                             let length := Z.min (Z.sub limit base) (num_of_int max_size_t) in
                             ret (Some (MVinteger CoqCtype.Size_t (IV length)))
                       end)
                else
                  if String.eqb name "cheri_tag_get" then
                    cap_val <- option2memM "missing argument"  (List.nth_error args 0%nat) ;;
                    get >>=
                      (fun (st : mem_state) =>
                         match cap_of_mem_value st.(funptrmap) cap_val
                         with
                         | None =>
                             fail loc
                               (MerrOther
                                  (String.append
                                     "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                     (String.append name "'")))
                         | Some (_, c) =>
                             if (C.get_ghost_state c).(tag_unspecified) then
                               ret (Some (MVunspecified
                                            (CoqCtype.Ctype nil
                                               (CoqCtype.Basic
                                                  (CoqCtype.Integer
                                                     CoqCtype.Bool)))))
                             else
                               let b_value := if C.cap_is_valid c then 1 else 0
                               in ret (Some (MVinteger CoqCtype.Bool (IV b_value)))
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
                               fail loc
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
                                 fail loc
                                   (MerrOther
                                      (String.append
                                         "CHERI.call_intrinsic: non-cap 1st argument in: '"
                                         (String.append name "'")))
                             | _, None =>
                                 fail loc
                                   (MerrOther
                                      (String.append
                                         "CHERI.call_intrinsic: non-cap 2nd argument in: '"
                                         (String.append name "'")))
                             | Some (_, c0), Some (_, c1) =>
                                 let gs0 := C.get_ghost_state c0 in
                                 let gs1 := C.get_ghost_state c1 in
                                 if gs0.(tag_unspecified) || gs1.(tag_unspecified)
                                    || gs0.(bounds_unspecified) || gs1.(bounds_unspecified)
                                 then
                                   ret (Some (MVunspecified
                                                (CoqCtype.Ctype nil
                                                   (CoqCtype.Basic
                                                      (CoqCtype.Integer
                                                         CoqCtype.Bool)))))
                                 else
                                   let v_value := if C.eqb c0 c1 then 1 else 0 in
                                   ret
                                     (Some
                                        (MVinteger CoqCtype.Bool
                                           (IV v_value)))
                             end)
                      else
                        if String.eqb name "cheri_representable_length" then
                          match List.nth_error args 0%nat with
                          | None =>
                              raise (InternalErr "missing argument")
                          | Some (MVinteger CoqCtype.Size_t (IV n_value)) =>
                              let l_value := C.representable_length n_value in
                              ret
                                (Some
                                   (MVinteger CoqCtype.Size_t
                                      (IV l_value)))
                          | Some _ =>
                              fail loc
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
                            | Some (MVinteger CoqCtype.Size_t (IV n_value))
                              =>
                                let l_value := C.representable_alignment_mask n_value in
                                ret
                                  (Some
                                     (MVinteger CoqCtype.Size_t
                                        (IV l_value)))
                            | Some _ =>
                                fail loc
                                  (MerrOther
                                     (String.append
                                        "CHERI.call_intrinsic: 1st argument's type is not size_t in: '"
                                        (String.append name "'")))
                            end
                          else
                            fail loc
                              (MerrOther
                                 (String.append
                                    "CHERI.call_intrinsic: unknown intrinsic: '"
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
              (CoqCtype.Ctype nil
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
              (CoqCtype.Ctype nil
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
                        (CoqCtype.Ctype nil
                           (CoqCtype.Basic
                              (CoqCtype.Integer CoqCtype.Bool)))),
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
                            (CoqCtype.Ctype nil
                               (CoqCtype.Basic
                                  (CoqCtype.Integer
                                     CoqCtype.Bool)))),
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

Module CheriMemoryTypesExe: CheriMemoryTypes(MemCommonExe)(Capability_GS)(MorelloImpl).
  Include CheriMemoryTypes(MemCommonExe)(Capability_GS)(MorelloImpl).
End CheriMemoryTypesExe.

(* TODO: see if we can instantiate it in OCaml *)
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
  (MT: CheriMemoryTypes(MC)(C)(IMP))
  (TD: TagDefs)
  (SW: CerbSwitchesDefs)
<: CheriMemoryImpl(MC)(C)(IMP)(MT)(TD)(SW).

  Include CheriMemoryImpl(MC)(C)(IMP)(MT)(TD)(SW).

End CheriMemoryExe.
