Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Require Import Addr.
Require Import Undefined.
Require Import Location.

Module Mem_common (A:VADDR).

  Definition thread_id := Z. (* Mem_common.thread_id *)

  Inductive overlap_status : Set :=
  | Disjoint : overlap_status
  | ExactOverlap : overlap_status
  | PartialOverlap : overlap_status.

    Inductive access_kind : Set :=
  | LoadAccess : access_kind
  | StoreAccess : access_kind.

  Inductive access_error : Set :=
  | NullPtr : access_error
  | FunctionPtr : access_error
  | DeadPtr : access_error
  | OutOfBoundPtr : access_error
  | NoProvPtr : access_error
  | AtomicMemberof : access_error.

  Inductive free_error : Set :=
  | Free_static_allocation : free_error
  | Free_dead_allocation : free_error
  | Free_out_of_bound : free_error.

  Inductive vip_kind : Set :=
  | VIP_null : vip_kind
  | VIP_empty : vip_kind
  | VIP_killed : vip_kind
  | VIP_out_of_bound : vip_kind
  | VIP_funptr : vip_kind.

  Inductive vip_error : Set :=
  | VIP_free_invalid_pointer : location_ocaml -> vip_error
  | VIP_relop_killed : vip_error
  | VIP_relop_out_of_bound : vip_error
  | VIP_relop_invalid : vip_error
  | VIP_diffptr_out_of_bound : vip_error
  | VIP_ptrcast_empty : vip_error
  | VIP_intcast : vip_kind -> vip_error
  | VIP_intcast_not_in_range : vip_error
  | VIP_array_shift : vip_kind -> vip_error
  | VIP_copy_alloc_id : vip_kind -> vip_error
  | VIP_copy_alloc_id_invalid : vip_error.

  Inductive mem_cheri_error : Set :=
  | CheriErrDecodingCap : mem_cheri_error
  | CheriMerrInvalidCap : mem_cheri_error
  | CheriMerrUnsufficientPermissions : mem_cheri_error
  | CheriBoundsErr : (* bounds,address,length *)
    (A.t * A.t) * A.t * nat ->
    mem_cheri_error.

  Inductive mem_error : Set :=
  | MerrOutsideLifetime : string -> mem_error
  | MerrInternal : string -> mem_error
  | MerrOther : string -> mem_error
  | MerrPtrdiff : mem_error
  | MerrAccess : location_ocaml -> access_kind -> access_error -> mem_error
  | MerrWriteOnReadOnly : bool -> location_ocaml -> mem_error
  | MerrReadUninit : location_ocaml -> mem_error
  | MerrUndefinedFree : location_ocaml -> free_error -> mem_error
  | MerrUndefinedRealloc : mem_error
  | MerrIntFromPtr : location_ocaml -> mem_error
  | MerrPtrFromInt : mem_error
  | MerrPtrComparison : mem_error
  | MerrArrayShift : location_ocaml -> mem_error
  | MerrFreeNullPtr : location_ocaml -> mem_error
  | MerrWIP : string -> mem_error
  | MerrVIP : vip_error -> mem_error
  | MerrCHERI : location_ocaml -> mem_cheri_error -> mem_error.

  Inductive mem_constraint (a : Set) : Set :=
  | MC_empty : mem_constraint a
  | MC_eq : a -> a -> mem_constraint a
  | MC_le : a -> a -> mem_constraint a
  | MC_lt : a -> a -> mem_constraint a
  | MC_in_device : a -> mem_constraint a
  | MC_or : mem_constraint a -> mem_constraint a -> mem_constraint a
  | MC_conj : list (mem_constraint a) -> mem_constraint a
  | MC_not : mem_constraint a -> mem_constraint a.

  (*


Definition stringFromAccess_error (function_parameter : access_error)
  : string :=
  match function_parameter with
  | NullPtr => "NullPtr"
  | FunctionPtr => "FunctionPtr"
  | DeadPtr => "DeadPtr"
  | OutOfBoundPtr => "OutOfBoundPtr"
  | NoProvPtr => "NoProvPtr"
  | AtomicMemberof => "AtomicMemberof"
  end.
   *)


  (*
Definition stringFromFree_error (function_parameter : free_error) : string :=
  match function_parameter with
  | Free_static_allocation => "Free_static_allocation"
  | Free_dead_allocation => "Free_dead_allocation"
  | Free_out_of_bound => "Free_out_of_bound"
  end.
   *)


  (*
Definition instance_Show_Show_Mem_common_mem_cheri_error_dict
  : Lem_pervasives.show_class mem_cheri_error :=
  {|
    Lem_show.show_class.show_method :=
      fun (function_parameter : mem_cheri_error) =>
        match function_parameter with
        | CheriErrDecodingCap => "CheriErrDecodingCap"
        | CheriMerrInvalidCap => "CheriMerrInvalidCap"
        | CheriMerrUnsufficientPermissions => "CheriMerrUnsufficientPermissions"
        | CheriBoundsErr _ => "CheriBoundsErr"
        end |}.
   *)

  (*
Definition instance_Show_Show_Mem_common_mem_error_dict
  : Lem_pervasives.show_class mem_error :=
  {|
    Lem_show.show_class.show_method :=
      fun (function_parameter : mem_error) =>
        match function_parameter with
        | MerrOutsideLifetime str =>
          String.append "MerrOutsideLifetime \""" (String.append str "\""")
        | MerrInternal str =>
          String.append "MerrInternal \""" (String.append str "\""")
        | MerrOther str =>
          String.append "MerrOther \""" (String.append str "\""")
        | MerrWIP str => String.append "Memory WIP: " str
        | MerrPtrdiff => "MerrPtrdiff"
        | MerrAccess loc LoadAccess err =>
          String.append "MerrAccess Load ["
            (String.append (Location_ocaml.location_to_string None loc)
              (String.append "] " (stringFromAccess_error err)))
        | MerrWriteOnReadOnly _ loc =>
          String.append "MerrWriteOnReadOnly ["
            (String.append (Location_ocaml.location_to_string None loc) "]")
        | MerrReadUninit loc =>
          String.append "MerrReadUninit ["
            (String.append (Location_ocaml.location_to_string None loc) "]")
        | MerrAccess loc StoreAccess err =>
          String.append "MerrAccess Store ["
            (String.append (Location_ocaml.location_to_string None loc)
              (String.append "] " (stringFromAccess_error err)))
        | MerrUndefinedFree loc err =>
          String.append "MerrUndefinedFree ["
            (String.append (Location_ocaml.location_to_string None loc)
              (String.append "] " (stringFromFree_error err)))
        | MerrUndefinedRealloc => "MerrUndefinedRealloc"
        | MerrIntFromPtr loc =>
          String.append "MerrIntFromPtr ["
            (String.append (Location_ocaml.location_to_string None loc) "]")
        | MerrPtrFromInt => "MerrPtrFromInt"
        | MerrPtrComparison => "MerrPtrComparison"
        | MerrArrayShift loc =>
          String.append "MerrArrayShift ["
            (String.append (Location_ocaml.location_to_string None loc) "]")
        | MerrFreeNullPtr loc =>
          String.append "MerrFreeNullPtr ["
            (String.append (Location_ocaml.location_to_string None loc) "]")
        | MerrVIP err =>
          let show_kind (function_parameter : vip_kind) : string :=
            match function_parameter with
            | VIP_null => "null"
            | VIP_empty => "empty"
            | VIP_killed => "killed"
            | VIP_out_of_bound => "out_of_bound"
            | VIP_funptr => "funptr"
            end in
          match err with
          | VIP_free_invalid_pointer loc =>
            String.append "MerrVIP free_invalid_pointer ["
              (String.append (Location_ocaml.location_to_string None loc) "]")
          | VIP_relop_killed => "MerrVIP relop_killed"
          | VIP_relop_out_of_bound => "MerrVIP relop_out_of_bound"
          | VIP_relop_invalid => "MerrVIP relop_out_of_invalid"
          | VIP_diffptr_out_of_bound => "MerrVIP diffptr_out_of_bound"
          | VIP_ptrcast_empty => "MerrVIP ptrcast_empty"
          | VIP_intcast kind =>
            String.append "MerrVIP intcast, " (show_kind kind)
          | VIP_intcast_not_in_range => "MerrVIP intcast_not_in_range"
          | VIP_array_shift kind =>
            String.append "MerrVIP array_shift, " (show_kind kind)
          | VIP_copy_alloc_id kind =>
            String.append "MerrVIP copy_alloc_id, " (show_kind kind)
          | VIP_copy_alloc_id_invalid => "MerrVIP copy_alloc_id_invalid"
          end
        | MerrCHERI loc k_value =>
          String.append "MerrCHERI "
            (String.append
              ((fun (function_parameter : mem_cheri_error) =>
                match function_parameter with
                | CheriErrDecodingCap => "CheriErrDecodingCap"
                | CheriMerrInvalidCap => "CheriMerrInvalidCap"
                | CheriMerrUnsufficientPermissions =>
                  "CheriMerrUnsufficientPermissions"
                | CheriBoundsErr _ => "CheriBoundsErr"
                end) k_value)
              (String.append " ["
                (String.append (Location_ocaml.location_to_string None loc) "]")))
        end |}.
   *)

  Definition undefinedFromMem_error (function_parameter : mem_error)
    : option undefined_behaviour :=
    match function_parameter with
    | MerrOutsideLifetime _ => Some UB009_outside_lifetime
    | MerrPtrdiff =>
        Some UB048_disjoint_array_pointers_subtraction
    | MerrAccess _ _ NullPtr =>
        Some UB019_lvalue_not_an_object
    | MerrAccess _ _ DeadPtr =>
        Some UB010_pointer_to_dead_object
    | MerrIntFromPtr _ =>
        Some
          UB024_out_of_range_pointer_to_integer_conversion
    | MerrPtrFromInt =>
        Some UB_CERB001_integer_to_dead_pointer
    | MerrPtrComparison =>
        Some
          UB053_distinct_aggregate_union_pointer_comparison
    | MerrArrayShift _ => Some UB046_array_pointer_outside
    | MerrFreeNullPtr _ => None
    | MerrAccess _ LoadAccess OutOfBoundPtr =>
        Some UB_CERB002a_out_of_bound_load
    | MerrAccess _ StoreAccess OutOfBoundPtr =>
        Some UB_CERB002b_out_of_bound_store
    | MerrAccess _ _ AtomicMemberof =>
        Some UB042_access_atomic_structUnion_member
    | MerrUndefinedFree loc Free_static_allocation =>
        Some UB179a_static_allocation
    | MerrUndefinedFree loc Free_dead_allocation =>
        Some UB179b_dead_allocation
    | MerrUndefinedFree loc Free_out_of_bound => None
    | MerrUndefinedRealloc =>
        Some UB179a_static_allocation
    | MerrWriteOnReadOnly true _ =>
        Some UB033_modifying_string_literal
    | MerrWriteOnReadOnly false _ =>
        Some UB064_modifying_const
    | MerrReadUninit _ => None
    | MerrCHERI _ err =>
        match err with
        | CheriMerrInvalidCap => Some UB_CHERI_InvalidCap
        | CheriErrDecodingCap =>
            Some UB012_lvalue_read_trap_representation
        | CheriMerrUnsufficientPermissions =>
            Some UB_CHERI_UnsufficientPermissions
        | CheriBoundsErr _ => Some UB_CHERI_BoundsViolation
        end
  | _ => None
  end.

(*
Inductive integer_operator : Set :=
| IntAdd : integer_operator
| IntSub : integer_operator
| IntMul : integer_operator
| IntDiv : integer_operator
| IntRem_t : integer_operator
| IntRem_f : integer_operator
| IntExp : integer_operator.

Inductive floating_operator : Set :=
| FloatAdd : floating_operator
| FloatSub : floating_operator
| FloatMul : floating_operator
| FloatDiv : floating_operator.

Inductive derivecap_op : Set :=
| DCunary : Cerb_frontend.AilSyntax.unaryOperator -> derivecap_op
| DCbinary : Cerb_frontend.AilSyntax.binaryOperator -> derivecap_op.

Inductive pure_memop : Set :=
| DeriveCap : derivecap_op -> bool -> pure_memop
| CapAssignValue : pure_memop
| Ptr_tIntValue : pure_memop.

Inductive generic_memop (sym : Set) : Set :=
| PtrEq : generic_memop sym
| PtrNe : generic_memop sym
| PtrLt : generic_memop sym
| PtrGt : generic_memop sym
| PtrLe : generic_memop sym
| PtrGe : generic_memop sym
| Ptrdiff : generic_memop sym
| IntFromPtr : generic_memop sym
| PtrFromInt : generic_memop sym
| PtrValidForDeref : generic_memop sym
| PtrWellAligned : generic_memop sym
| PtrArrayShift : generic_memop sym
| PtrMemberShift : sym -> Cerb_frontend.Symbol.identifier -> generic_memop sym
| Memcpy : generic_memop sym
| Memcmp : generic_memop sym
| Realloc : generic_memop sym
| Va_start : generic_memop sym
| Va_copy : generic_memop sym
| Va_arg : generic_memop sym
| Va_end : generic_memop sym
| Copy_alloc_id : generic_memop sym
| CHERI_intrinsic :
  string -> Cerb_frontend.Ctype.ctype * list Cerb_frontend.Ctype.ctype ->
  generic_memop sym.

Arguments PtrEq {_}.
Arguments PtrNe {_}.
Arguments PtrLt {_}.
Arguments PtrGt {_}.
Arguments PtrLe {_}.
Arguments PtrGe {_}.
Arguments Ptrdiff {_}.
Arguments IntFromPtr {_}.
Arguments PtrFromInt {_}.
Arguments PtrValidForDeref {_}.
Arguments PtrWellAligned {_}.
Arguments PtrArrayShift {_}.
Arguments PtrMemberShift {_}.
Arguments Memcpy {_}.
Arguments Memcmp {_}.
Arguments Realloc {_}.
Arguments Va_start {_}.
Arguments Va_copy {_}.
Arguments Va_arg {_}.
Arguments Va_end {_}.
Arguments Copy_alloc_id {_}.
Arguments CHERI_intrinsic {_}.

Definition memop : Set := generic_memop Cerb_frontend.Symbol.sym.

Definition instance_Show_Show_Mem_common_generic_memop_dict {a : Set}
  (dict_Show_Show_a : Lem_pervasives.show_class a)
  : Lem_pervasives.show_class (generic_memop a) :=
  {|
    Lem_show.show_class.show_method :=
      fun (function_parameter : generic_memop a) =>
        match function_parameter with
        | PtrEq => "ptreq"
        | PtrNe => "ptrne"
        | PtrLt => "ptrlt"
        | PtrGt => "ptrgt"
        | PtrLe => "ptrle"
        | PtrGe => "ptrge"
        | Ptrdiff => "ptrdiff"
        | IntFromPtr => "intfromptr"
        | PtrFromInt => "ptrfromint"
        | PtrValidForDeref => "ptrvalidforderef"
        | PtrWellAligned => "ptrwellaligned"
        | Memcpy => "memcpy"
        | Memcmp => "memcmp"
        | Realloc => "realloc"
        | PtrArrayShift => "ptrarrayshift"
        | PtrMemberShift tag_sym membr_ident =>
          String.append "ptrmembershift["
            (String.append
              (dict_Show_Show_a.(Lem_show.show_class.show_method) tag_sym)
              (String.append ", "
                (String.append
                  (let 'Cerb_frontend.Symbol.Identifier _ str := membr_ident in
                  str) "]")))
        | Va_start => "va_start"
        | Va_copy => "va_copy"
        | Va_arg => "va_arg"
        | Va_end => "va_end"
        | Copy_alloc_id => "copy_alloc_id"
        | CHERI_intrinsic str _ => String.append "cheri_" str
        end |}.

Definition stringFromInteger_operator (function_parameter : integer_operator)
  : string :=
  match function_parameter with
  | IntAdd => "IntAdd"
  | IntSub => "IntSub"
  | IntMul => "IntMul"
  | IntDiv => "IntDiv"
  | IntRem_t => "IntRem_t"
  | IntRem_f => "IntRem_f"
  | IntExp => "IntExp"
  end.

Definition stringFromFloating_operator (function_parameter : floating_operator)
  : string :=
  match function_parameter with
  | FloatAdd => "FloatAdd"
  | FloatSub => "FloatSub"
  | FloatMul => "FloatMul"
  | FloatDiv => "FloatDiv"
  end.
   *)


(*
Arguments MC_empty {_}.
Arguments MC_eq {_}.
Arguments MC_le {_}.
Arguments MC_lt {_}.
Arguments MC_in_device {_}.
Arguments MC_or {_}.
Arguments MC_conj {_}.
Arguments MC_not {_}.

Definition instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict
  {a : Set}
  : Cerb_frontend.Nondeterminism.constraints_class (mem_constraint a) :=
  {| Cerb_frontend.Nondeterminism.constraints_class.empty_method := MC_empty;
    Cerb_frontend.Nondeterminism.constraints_class.negate_method :=
      fun (cs : mem_constraint a) => MC_not cs;
    Cerb_frontend.Nondeterminism.constraints_class.concat_method :=
      fun (cs1 : mem_constraint a) =>
        fun (cs2 : mem_constraint a) => MC_conj [ cs1; cs2 ] |}.

Inductive type_predicate : Set :=
| TyPred : (Cerb_frontend.Ctype.ctype -> bool) -> type_predicate
| TyIsPointer : type_predicate.

Inductive instrinsics_ret_spec : Set :=
| ExactRet : Cerb_frontend.Ctype.ctype -> instrinsics_ret_spec
| CopyRet : int -> instrinsics_ret_spec.

Inductive intrinsics_arg_spec : Set :=
| ExactArg : Cerb_frontend.Ctype.ctype -> intrinsics_arg_spec
| PolymorphicArg : list type_predicate -> intrinsics_arg_spec
| CopyArg : int -> intrinsics_arg_spec.

Definition intrinsics_signature : Set :=
  instrinsics_ret_spec * list intrinsics_arg_spec.

Definition instance_Show_Show_Mem_common_intrinsics_arg_spec_dict
  : Lem_pervasives.show_class intrinsics_arg_spec :=
  {|
    Lem_show.show_class.show_method :=
      fun (function_parameter : intrinsics_arg_spec) =>
        match function_parameter with
        | ExactArg ty => "ExactArg"
        | PolymorphicArg _ => "PolymorphicArg"
        | CopyArg i_value =>
          String.append "CopyArg("
            (String.append (CoqOfOCaml.Stdlib.string_of_int i_value) ")")
        end |}.

Module memory_flags.
  Record record : Set := Build {
    allow_multi_provenance : bool }.
  Definition with_allow_multi_provenance allow_multi_provenance (r : record) :=
    Build allow_multi_provenance.
End memory_flags.
Definition memory_flags := memory_flags.record.

Inductive memory_flag : Set :=
| Allow_disjoint_alloc_tests : memory_flag.

Fixpoint either_sequence {a b : Set} (xs : list (Either.either a b))
  : Either.either a (list b) :=
  match xs with
  | [] => Either.Right nil
  | cons (Either.Left msg) _ => Either.Left msg
  | cons (Either.Right x_value) xs =>
    match either_sequence xs with
    | Either.Left msg => Either.Left msg
    | Either.Right xs' => Either.Right (cons x_value xs')
    end
  end.

Definition try_usual_arithmetic (function_parameter : Cerb_frontend.Ctype.ctype)
  : Cerb_frontend.Ctype.ctype -> option Cerb_frontend.Ctype.ctype :=
  let 'Cerb_frontend.Ctype.Ctype _ ty1 := function_parameter in
  fun (function_parameter : Cerb_frontend.Ctype.ctype) =>
    let 'Cerb_frontend.Ctype.Ctype _ ty2 := function_parameter in
    match (ty1, ty2) with
    |
      (Cerb_frontend.Ctype.Basic (Cerb_frontend.Ctype.Integer ity1),
        Cerb_frontend.Ctype.Basic (Cerb_frontend.Ctype.Integer ity2)) =>
      Some
        (Cerb_frontend.Ctype.Ctype nil
          (Cerb_frontend.Ctype.Basic
            (Cerb_frontend.Ctype.Integer
              (Cerb_frontend.AilTypesAux.usual_arithmetic_integer
                (Cerb_frontend.Implementation.integerImpl tt) ity1 ity2))))
    | _ => None
    end.

Fixpoint resolve_arg
  (n_value : int) (get_arg : int -> Cerb_frontend.Ctype.ctype * bool)
  (get_spec : int -> intrinsics_arg_spec)
  (function_parameter : Cerb_frontend.Ctype.ctype * bool)
  : intrinsics_arg_spec -> Either.either string Cerb_frontend.Ctype.ctype :=
  let '(arg, is_null_pointer_constant1) := function_parameter in
  fun (spec : intrinsics_arg_spec) =>
    let resolve_arg1 := resolve_arg n_value get_arg get_spec in
    match spec with
    | ExactArg ty =>
      if Cerb_frontend.Ctype.ctypeEqual arg ty then
        Either.Right arg
      else
        match try_usual_arithmetic ty arg with
        | Some usual_ty =>
          if Cerb_frontend.Ctype.ctypeEqual usual_ty ty then
            Either.Right usual_ty
          else
            Either.Left "ExactArg -- common type didn't match"
        | None => Either.Left "ExactArg -- type mismatch"
        end
    | PolymorphicArg tyl =>
      let opt :=
        Stdlib.List.fold_left
          (fun (acc : option Cerb_frontend.Ctype.ctype) =>
            fun (p_value : type_predicate) =>
              match (acc, p_value) with
              | (Some ty, _) => Some ty
              | (None, TyPred pred) =>
                if pred arg then
                  Some arg
                else
                  None
              | (None, TyIsPointer) =>
                if Cerb_frontend.AilTypesAux.is_pointer arg then
                  Some arg
                else
                  if is_null_pointer_constant1 then
                    Some
                      (Cerb_frontend.Ctype.mk_ctype_pointer
                        Cerb_frontend.Ctype.no_qualifiers
                        Cerb_frontend.Ctype.void)
                  else
                    None
              end) None tyl in
      match opt with
      | Some ty => Either.Right ty
      | None => Either.Left "PolymorphicArg -- all preds failed"
      end
    | CopyArg i_value =>
      if CoqOfOCaml.Stdlib.ge i_value n_value then
        Either.Left "CopyArg -- invalid index"
      else
        match get_spec i_value with
        | CopyArg _ => Either.Left "CopyArg -- dual indirection not allowed!"
        | spec' => resolve_arg1 (get_arg i_value) spec'
        end
    end.

Definition derive_intrinsic_signature
  (args : list (Cerb_frontend.Ctype.ctype * bool))
  (function_parameter : instrinsics_ret_spec * list intrinsics_arg_spec)
  : Either.either string
    (Cerb_frontend.Ctype.ctype * list Cerb_frontend.Ctype.ctype) :=
  let '(ret_spec, specs) := function_parameter in
  let n_value := CoqOfOCaml.List.length args in
  if negb (equiv_decb n_value (CoqOfOCaml.List.length specs)) then
    Either.Left "|args| <> |specs|"
  else
    match
      either_sequence
        (Cerb_frontend.Utils.map2
          (resolve_arg n_value
            (fun (idx : Nat_num.nat) =>
              match Lem_list.list_index args idx with
              | Some z_value => z_value
              | None =>
                Debug_ocaml._error
                  "Mem_common.derive_intrinsic_signature: internal error (get)"
              end)
            (fun (idx : Nat_num.nat) =>
              match Lem_list.list_index specs idx with
              | Some z_value => z_value
              | None =>
                Debug_ocaml._error
                  "Mem_common.derive_intrinsic_signature: internal error (get)"
              end)) args specs) with
    | Either.Left msg => Either.Left msg
    | Either.Right tys =>
      Either.Right
        match ret_spec with
        | ExactRet ty => (ty, tys)
        | CopyRet i_value =>
          (match Lem_list.list_index tys i_value with
          | Some z_value => z_value
          | None =>
            Debug_ocaml._error
              "Mem_common.derive_intrinsic_signature: internal error (get)"
          end, tys)
        end
    end.
 *)

End Mem_common.
