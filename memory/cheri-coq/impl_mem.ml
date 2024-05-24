[@@@warning "+8-37"]
open Ctype

(*open Ocaml_implementation*)
open Memory_model
open Mem_common
open CheriMorelloMemory
open CoqImplementation
open Strfcap
open CoqSwitches
open Switches
open ZMap
open AMap

module CerbSwitchesProxy = struct

  let toCoq_switch: Switches.cerb_switch -> CoqSwitches.cerb_switch = function
    | SW_pointer_arith `PERMISSIVE -> CoqSwitches.SW_pointer_arith CoqSwitches.PERMISSIVE
    | SW_pointer_arith `STRICT -> CoqSwitches.SW_pointer_arith CoqSwitches.STRICT
    | SW_strict_reads -> SW_strict_reads
    | SW_forbid_nullptr_free -> SW_forbid_nullptr_free
    | SW_zap_dead_pointers -> SW_zap_dead_pointers
    | SW_strict_pointer_equality -> SW_strict_pointer_equality
    | SW_strict_pointer_relationals -> SW_strict_pointer_relationals
    | SW_PNVI `PLAIN -> SW_PNVI PLAIN
    | SW_PNVI `AE -> SW_PNVI AE
    | SW_PNVI `AE_UDI -> SW_PNVI AE_UDI
    | SW_CHERI -> SW_CHERI
    | SW_inner_arg_temps -> SW_inner_arg_temps
    | SW_permissive_printf -> SW_permissive_printf
    | SW_zero_initialised -> SW_zero_initialised
    | SW_revocation `INSTANT -> SW_revocation INSTANT
    | SW_revocation `CORNUCOPIA -> SW_revocation CORNUCOPIA
    | SW_at_magic_comments -> SW_at_magic_comments

  let toCoq_switches (cs: cerb_switch list): CoqSwitches.cerb_switches_t =
    let open ListSet in
    List.fold_left
      (fun s x -> set_add (=) (toCoq_switch x) s) empty_set cs

  let get_switches _ = toCoq_switches (Switches.get_switches ())
end

module CerbTagDefs = struct

  let toCoq_lexing_position (lp:Lexing.position): CoqLocation.lexing_position =
    {
      pos_fname = lp.pos_fname;
      pos_lnum = Z.of_int lp.pos_lnum;
      pos_bol = Z.of_int lp.pos_bol;
      pos_cnum = Z.of_int lp.pos_cnum;
    }

  let toCoq_location_cursor: Cerb_location.cursor -> CoqLocation.location_cursor = function
    | NoCursor -> NoCursor
    | PointCursor lp -> PointCursor (toCoq_lexing_position lp)
    | RegionCursor (lp1,lp2) -> RegionCursor (toCoq_lexing_position lp1, toCoq_lexing_position lp2)

  let toCoq_location (l:Cerb_location.t): CoqLocation.location_ocaml =
    match l with
    | Loc_unknown -> Loc_unknown
    | Loc_other s -> Loc_other s
    | Loc_point p -> Loc_point (toCoq_lexing_position p)
    | Loc_region (lp1,lp2,lc) -> Loc_region (toCoq_lexing_position lp1, toCoq_lexing_position lp2,toCoq_location_cursor lc)
    | Loc_regions (ps, lc) -> Loc_regions
                                ((List.map (fun (lp1,lp2) -> (toCoq_lexing_position lp1, toCoq_lexing_position lp2)) ps),
                                 toCoq_location_cursor lc)



  let toCoq_Symbol_description: Symbol.symbol_description -> CoqSymbol.symbol_description = function
    | SD_None -> SD_None
    | SD_unnamed_tag l -> SD_unnamed_tag (toCoq_location l)
    | SD_Id s -> SD_Id s
    | SD_CN_Id s -> SD_CN_Id s
    | SD_ObjectAddress s -> SD_ObjectAddress s
    | SD_Return -> SD_Return
    | SD_FunArgValue s -> SD_FunArgValue s
    | SD_FunArg (l,v) -> SD_FunArg (toCoq_location l, Z.of_int v)

  let toCoq_Symbol_sym: Symbol.sym -> CoqSymbol.sym = function
    | Symbol (d,v,desc) -> Symbol (d, Z.of_int v, toCoq_Symbol_description desc)

  let toCoq_Symbol_prefix: Symbol.prefix -> CoqSymbol.prefix = function
    | PrefSource (loc, sl) -> PrefSource (toCoq_location loc, List.map toCoq_Symbol_sym sl)
    | PrefFunArg (l, d, v) -> PrefFunArg (toCoq_location l, d, Z.of_int v)
    | PrefStringLiteral (l,d) -> PrefStringLiteral (toCoq_location l, d)
    | PrefTemporaryLifetime (l,d) -> PrefTemporaryLifetime (toCoq_location l, d)
    | PrefCompoundLiteral (l,d) ->  PrefCompoundLiteral (toCoq_location l, d)
    | PrefMalloc -> PrefMalloc
    | PrefOther s -> PrefOther s

  let toCoq_Symbol_identifier: Symbol.identifier -> CoqSymbol.identifier = function
    | Identifier (l,s) -> Identifier (toCoq_location l, s)


  let toCoq_annot: Annot.bmc_annot -> CoqAnnot.bmc_annot  = function
    | Abmc_id ba -> Z.of_int ba

  let toCoq_attribute (a:Annot.attribute) : CoqAnnot.attribute =
    {
      attr_ns = Option.map (toCoq_Symbol_identifier) a.attr_ns;
      attr_id =  toCoq_Symbol_identifier a.attr_id ;
      attr_args =
        List.map (fun (loc, s, ll) ->
            ((toCoq_location loc,
              s),
             List.map (fun (loc', s) -> (toCoq_location loc', s)) ll)
          ) a.attr_args
    }

  let toCoq_attributes: Annot.attributes -> CoqAnnot.attributes  = function
    | Attrs ats -> List.map toCoq_attribute ats

  let toCoq_qualifiers (q:qualifiers): CoqCtype.qualifiers =
    {
      const    = q.const;
      restrict = q.restrict;
      volatile = q.volatile
    }

  let toCoq_integerBaseType: integerBaseType -> CoqIntegerType.integerBaseType = function
    | Ichar           -> Ichar
    | Short           -> Short
    | Int_            -> Int_
    | Long            -> Long
    | LongLong        -> LongLong
    | IntN_t n        -> IntN_t (Z.of_int n)
    | Int_leastN_t n  -> Int_leastN_t (Z.of_int n)
    | Int_fastN_t n   -> Int_fastN_t (Z.of_int n)
    | Intmax_t        -> Intmax_t
    | Intptr_t        -> Intptr_t

  let toCoq_integerType: integerType -> CoqIntegerType.integerType = function
    | Char          -> Char
    | Bool          -> Bool
    | Signed bt     -> Signed (toCoq_integerBaseType bt)
    | Unsigned bt   -> Unsigned (toCoq_integerBaseType bt)
    | Enum s        -> Enum (toCoq_Symbol_sym s)
    | Wchar_t       -> Wchar_t
    | Wint_t        -> Wint_t
    | Size_t        -> Size_t
    | Ptrdiff_t     -> Ptrdiff_t
    | Ptraddr_t       -> Ptraddr_t

  let toCoq_realFloatingType: realFloatingType -> CoqCtype.realFloatingType = function
    | Float -> Float
    | Double -> Double
    | LongDouble -> LongDouble

  let toCoq_floatingType: floatingType -> CoqCtype.floatingType  = function
    | RealFloating rft -> (toCoq_realFloatingType rft)

  let [@warning "-8"] toCoq_label_annot: Annot.label_annot -> CoqAnnot.label_annot = function
    | LAloop_prebody lid  -> LAloop_prebody (Z.of_int lid)
    | LAloop_body lid     -> LAloop_body (Z.of_int lid)
    | LAloop_continue lid -> LAloop_continue (Z.of_int lid)
    | LAloop_break lid    -> LAloop_break (Z.of_int lid)
    | LAreturn            -> LAreturn
    | LAswitch            -> LAswitch
    | LAcase              -> LAcase
    | LAdefault           -> LAdefault

  let toCoq_cerb_attribute: Annot.cerb_attribute -> CoqAnnot.cerb_attribute = function
    | ACerb_with_address n -> ACerb_with_address n
    | ACerb_hidden -> ACerb_hidden

  let toCoq_value_annot: Annot.value_annot -> CoqAnnot.value_annot = function
    | Ainteger a -> toCoq_integerType a

  let [@warning "-8"] toCoq_annot: Annot.annot -> CoqAnnot.annot = function
    | Astd s       -> Astd s
    | Aloc loc     -> Aloc (toCoq_location loc)
    | Auid s       -> Auid s
    | Amarker n -> Amarker (Z.of_int n)
    | Amarker_object_types n -> Amarker_object_types (Z.of_int n)
    | Abmc ba      -> Abmc (toCoq_annot ba)
    | Aattrs atr   -> Aattrs (toCoq_attributes atr)
    | Atypedef s   -> Atypedef (toCoq_Symbol_sym s)
    | Anot_explode -> Anot_explode
    | Alabel la    -> Alabel (toCoq_label_annot la)
    | Acerb ca -> Acerb (toCoq_cerb_attribute ca)
    | Avalue va -> Avalue (toCoq_value_annot va)
    | Ainlined_label (l,s,la) ->
       Ainlined_label (toCoq_location l, toCoq_Symbol_sym s, toCoq_label_annot la)
    | Astmt -> Astmt
    | Aexpr -> Aexpr

  let toCoq_basicType: basicType -> CoqCtype.basicType = function
    | Integer ity -> Integer (toCoq_integerType ity)
    | Floating fty -> Floating (toCoq_floatingType fty)


  let rec toCoq_ctype: Ctype.ctype -> CoqCtype.ctype  = function
    | Ctype (la, ct) -> Ctype (List.map toCoq_annot la, toCoq_ctype_ ct)
  and toCoq_ctype_: Ctype.ctype_ -> CoqCtype.ctype'  = function
    | Void -> Void
    | Basic bty -> Basic (toCoq_basicType bty)
    | Array (cty, zo) -> CoqCtype.Array (toCoq_ctype cty, zo)
    | Function ((q, cty),l,b) ->
       Function ((toCoq_qualifiers q, toCoq_ctype cty),
                 List.map (fun (q,cty,b) -> ((toCoq_qualifiers q,toCoq_ctype cty), b)) l,
                 b)
    | FunctionNoParams (q, cty) ->  FunctionNoParams (toCoq_qualifiers q, toCoq_ctype cty)
    | Pointer (q, cty) -> Pointer (toCoq_qualifiers q, toCoq_ctype cty)
    | Atomic cty ->  Atomic (toCoq_ctype cty)
    | Struct s -> Struct (toCoq_Symbol_sym s)
    | Union s -> Union (toCoq_Symbol_sym s)

  let toCoq_flexible_array_member: Ctype.flexible_array_member -> CoqCtype.flexible_array_member = function
    | FlexibleArrayMember (attr,sym, q, cty) ->
       FlexibleArrayMember (toCoq_attributes attr,
                            toCoq_Symbol_identifier sym,
                            toCoq_qualifiers q,
                            toCoq_ctype cty)

  let toCoq_alignment: Ctype.alignment -> CoqCtype.alignment = function
    | AlignInteger n -> AlignInteger n
    | AlignType cty -> AlignType (toCoq_ctype cty)

  let toCoq_tag_definition: Ctype.tag_definition -> CoqCtype.tag_definition = function
    | StructDef (l, f)
      -> StructDef (List.map (fun (sym,(attr,align_opt,q,cty)) ->
                        (toCoq_Symbol_identifier sym,
                         (((toCoq_attributes attr, Option.map toCoq_alignment align_opt),
                           toCoq_qualifiers q),
                          toCoq_ctype cty))) l,
                    Option.map toCoq_flexible_array_member f)
    | UnionDef l ->
       UnionDef
         (List.map (fun (s,(attr,align_opt,q,cty)) ->
              (toCoq_Symbol_identifier s,
               ( ((toCoq_attributes attr, Option.map toCoq_alignment align_opt),
                  toCoq_qualifiers q),
                 toCoq_ctype cty))
            ) l)

  (* very inefficient! *)
  let toCoq_SymMap (m:(Symbol.sym, Cerb_location.t * Ctype.tag_definition) Pmap.map) : CoqCtype.tag_definition CoqSymbol.SymMap.t =
    let l = Pmap.bindings_list m in
    let (e:CoqCtype.tag_definition CoqSymbol.SymMap.t) = CoqSymbol.SymMap.empty in
    List.fold_left (fun m (s,(_, d)) -> CoqSymbol.SymMap.add (toCoq_Symbol_sym s) (toCoq_tag_definition d) m) e l

  let tagDefs _ = toCoq_SymMap (Tags.tagDefs ())
end


module MM = CheriMemoryExe(MemCommonExe)(MorelloCapabilityWithStrfcap)(MorelloImpl)(CheriMemoryTypesExe)(CerbTagDefs:CoqTags.TagDefs)(CerbSwitchesProxy)
module C = MorelloCapabilityWithStrfcap

module Z = struct
  include Nat_big_num
  let format = Z.format
end

module L = struct
  include List
  include Lem_list
end


module CHERIMorello : Memory = struct

  let name = MM.name

  type pointer_value = MM.pointer_value
  type integer_value = MM.integer_value
  type floating_value = MM.floating_value
  type mem_value = MM.mem_value

  type mem_iv_constraint = integer_value Mem_common.mem_constraint
  type footprint = MM.footprint
  type mem_state = MM.mem_state

  let initial_mem_state = MM.initial_mem_state
  let overlapping = MM.overlapping

  let cs_module = (module struct
                     type t = mem_iv_constraint
                     let negate x = MC_not x

                     type 'a eff = Eff of (bool -> ('a * bool))
                     let return a = Eff (fun b -> (a, b))
                     let bind (Eff ma) f =
                       Eff (fun b -> let (a, b') = ma b in let Eff mb = f a in mb b')
                     let rec foldlM f a = function
                       | [] ->
                          return a
                       | x::xs ->
                          bind (f a x) (fun fax -> foldlM f fax xs)

                     let runEff (Eff ma) = fst (ma true)

                     let string_of_solver = return []
                     let check_sat =
                       Eff (fun b -> ((if b then `SAT else `UNSAT), b))

                     let with_constraints _ cs (Eff ma) =
                       Cerb_debug.print_debug 1 [] (fun () -> "HELLO: Concrete.with_constraints");
                       let rec eval_cs = function
                         | MC_empty ->
                            true
                         | MC_eq (ival1, ival2) ->
                            Stdlib.Option.value (MM.eq_ival ival1 ival2) ~default:false
                         | MC_le (ival1, ival2) ->
                            Stdlib.Option.value (MM.le_ival ival1 ival2) ~default:false
                         | MC_lt (ival1, ival2) ->
                            Stdlib.Option.value (MM.lt_ival ival1 ival2) ~default:false
                         | MC_in_device _ ->
                            failwith "TODO: Concrete, with_constraints: MC_in_device"
                         | MC_or (cs1, cs2) ->
                            eval_cs cs1 || eval_cs cs2
                         | MC_conj css ->
                            List.for_all (fun z -> eval_cs z) css
                         | MC_not cs ->
                            not (eval_cs cs)
                       in
                       Eff (fun b -> ma (b && eval_cs cs))
                   end : Constraints with type t = mem_iv_constraint)

  type 'a memM =
    ('a, string, Mem_common.mem_error, integer_value Mem_common.mem_constraint, MM.mem_state) Nondeterminism.ndM

  let return = Nondeterminism.nd_return
  let bind = Nondeterminism.nd_bind
  let get = Nondeterminism.nd_get
  let (>>=) = Nondeterminism.nd_bind

  (* TODO: hackish *)
  let fail ?(loc=Cerb_location.other "Cheri") err =
    let open Nondeterminism in
    match undefinedFromMem_error err with
      | Some ub ->
          kill (Undef0 (loc, [ub]))
      | None ->
          kill (Other err)

  let lift_coq_serr: (string, 'a) Datatypes.sum -> 'a = function
    | Coq_inl errs -> failwith errs
    | Coq_inr v -> v

  let fromCoq_lexing_position (lp:CoqLocation.lexing_position): Lexing.position =
    {
      pos_fname = lp.pos_fname;
      pos_lnum = Z.to_int lp.pos_lnum;
      pos_bol = Z.to_int lp.pos_bol;
      pos_cnum = Z.to_int lp.pos_cnum;
    }

  let fromCoq_location_cursor: CoqLocation.location_cursor -> Cerb_location.cursor = function
    | NoCursor -> NoCursor
    | PointCursor lp -> PointCursor (fromCoq_lexing_position lp)
    | RegionCursor (lp1,lp2) -> RegionCursor (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2)

  (* Coq -> OCaml type conversion *)
  let fromCoq_location: CoqLocation.location_ocaml -> Cerb_location.t = function
    | Loc_unknown -> Cerb_location.unknown
    | Loc_other s -> Cerb_location.other s
    | Loc_point p -> Cerb_location.point (fromCoq_lexing_position p)
    | Loc_region (lp1,lp2,lc) -> Cerb_location.region (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2) (fromCoq_location_cursor lc)
    | Loc_regions (ps, lc) -> Cerb_location.regions
                                (List.map (fun (lp1,lp2) -> (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2)) ps)
                                (fromCoq_location_cursor lc)

  let fromCoq_access_kind: MemCommonExe.access_kind -> access_kind = function
    | LoadAccess -> LoadAccess
    | StoreAccess -> StoreAccess

  let fromCoq_access_error: MemCommonExe.access_error -> access_error = function
    | NullPtr        -> NullPtr
    | FunctionPtr    -> FunctionPtr
    | DeadPtr        -> DeadPtr
    | OutOfBoundPtr  -> OutOfBoundPtr
    | NoProvPtr      -> NoProvPtr
    | AtomicMemberof -> AtomicMemberof

  let from_Coq_vip_error (_:MemCommonExe.vip_error) : vip_error =
    failwith "vip_error not supported in cheri-coq memory model"

  let from_Coq_mem_cheri_error: MemCommonExe.mem_cheri_error -> mem_cheri_error = function
    | CheriErrDecodingCap -> CheriErrDecodingCap
    | CheriMerrInvalidCap -> CheriMerrInvalidCap
    | CheriMerrInsufficientPermissions -> CheriMerrInsufficientPermissions
    | CheriBoundsErr (((b, s), a), l) -> CheriBoundsErr ((b, s), a, l)
    | CheriUndefinedTag -> CheriUndefinedTag

  let from_Coq_free_error: MemCommonExe.free_error -> free_error = function
    | Free_non_matching -> Free_non_matching
    | Free_dead_allocation -> Free_dead_allocation
    | Free_out_of_bound -> Free_out_of_bound

  let from_Coq_memcpy_error: MemCommonExe.memcpy_error -> memcpy_error = function
    | Memcpy_overlap -> Memcpy_overlap
    | Memcpy_non_object -> Memcpy_non_object
    | Memcpy_dead_object -> Memcpy_non_object
    | Memcpy_out_of_bound -> Memcpy_non_object

  let fromCoq_readonly_kind: MemCommonExe.readonly_kind -> readonly_kind = function
    | ReadonlyConstQualified -> ReadonlyConstQualified
    | ReadonlyStringLiteral -> ReadonlyStringLiteral
    | ReadonlyTemporaryLifetime -> ReadonlyTemporaryLifetime
  
  let fromCoq_mem_error: MemCommonExe.mem_error -> mem_error = function
    | MerrOutsideLifetime s -> MerrOutsideLifetime s
    | MerrInternal s -> MerrInternal s
    | MerrOther s -> MerrOther s
    | MerrPtrdiff -> MerrPtrdiff
    | MerrAccess (k,e) -> MerrAccess (fromCoq_access_kind k, fromCoq_access_error e)
    | MerrWriteOnReadOnly k -> MerrWriteOnReadOnly (fromCoq_readonly_kind k)
    | MerrReadUninit -> MerrReadUninit
    | MerrUndefinedFree e -> MerrUndefinedFree ( from_Coq_free_error e)
    | MerrUndefinedRealloc e -> MerrUndefinedRealloc (from_Coq_free_error e)
    | MerrUndefinedMemcpy e -> MerrUndefinedMemcpy (from_Coq_memcpy_error e)
    | MerrIntFromPtr -> MerrIntFromPtr
    | MerrPtrFromInt -> MerrPtrFromInt
    | MerrPtrComparison -> MerrPtrComparison
    | MerrArrayShift -> MerrArrayShift
    | MerrFreeNullPtr -> MerrFreeNullPtr
    | MerrWIP s -> MerrWIP s
    | MerrVIP e -> MerrVIP (from_Coq_vip_error e)
    | MerrCHERI e -> MerrCHERI (from_Coq_mem_cheri_error e)

  let fromCoq_undefined_by_omission: CoqUndefined.undefined_by_omission -> Undefined.undefined_by_omission = function
    | UB_OMIT_memcpy_non_object -> UB_OMIT_memcpy_non_object
    | UB_OMIT_memcpy_out_of_bound -> UB_OMIT_memcpy_out_of_bound

  let fromCoq_undefined_behaviour: CoqUndefined.undefined_behaviour -> Undefined.undefined_behaviour = function
    | DUMMY s                                              -> DUMMY s
    | UB_unspecified_lvalue                                -> UB_unspecified_lvalue
    | UB_std_omission om                                   -> UB_std_omission (fromCoq_undefined_by_omission om)
    | UB001                                                -> UB001
    | UB002                                                -> UB002
    | UB003                                                -> UB003
    | UB004a_incorrect_main_return_type                    -> UB004a_incorrect_main_return_type
    | UB004b_incorrect_main_argument1                      -> UB004b_incorrect_main_argument1
    | UB004c_incorrect_main_argument2                      -> UB004c_incorrect_main_argument2
    | UB004d_main_not_function                             -> UB004d_main_not_function
    | UB005_data_race                                      -> UB005_data_race
    | UB006                                                -> UB006
    | UB007                                                -> UB007
    | UB008_multiple_linkage                               -> UB008_multiple_linkage
    | UB009_outside_lifetime                               -> UB009_outside_lifetime
    | UB010_pointer_to_dead_object                         -> UB010_pointer_to_dead_object
    | UB011_use_indeterminate_automatic_object             -> UB011_use_indeterminate_automatic_object
    | UB_modifying_temporary_lifetime                      -> UB_modifying_temporary_lifetime
    | UB012_lvalue_read_trap_representation                -> UB012_lvalue_read_trap_representation
    | UB013_lvalue_side_effect_trap_representation         -> UB013_lvalue_side_effect_trap_representation
    | UB014_unsupported_negative_zero                      -> UB014_unsupported_negative_zero
    | UB015_incompatible_redeclaration                     -> UB015_incompatible_redeclaration
    | UB016                                                -> UB016
    | UB017_out_of_range_floating_integer_conversion       -> UB017_out_of_range_floating_integer_conversion
    | UB018                                                -> UB018
    | UB019_lvalue_not_an_object                           -> UB019_lvalue_not_an_object
    | UB020_nonarray_incomplete_lvalue_conversion          -> UB020_nonarray_incomplete_lvalue_conversion
    | UB021                                                -> UB021
    | UB022_register_array_decay                           -> UB022_register_array_decay
    | UB023                                                -> UB023
    | UB024_out_of_range_pointer_to_integer_conversion     -> UB024_out_of_range_pointer_to_integer_conversion
    | UB025_misaligned_pointer_conversion                  -> UB025_misaligned_pointer_conversion
    | UB026                                                -> UB026
    | UB027                                                -> UB027
    | UB028                                                -> UB028
    | UB029                                                -> UB029
    | UB030                                                -> UB030
    | UB031                                                -> UB031
    | UB032                                                -> UB032
    | UB033_modifying_string_literal                       -> UB033_modifying_string_literal
    | UB034                                                -> UB034
    | UB035_unsequenced_race                               -> UB035_unsequenced_race
    | UB036_exceptional_condition                          -> UB036_exceptional_condition
    | UB037_illtyped_load                                  -> UB037_illtyped_load
    | UB038_number_of_args                                 -> UB038_number_of_args
    | UB039                                                -> UB039
    | UB040                                                -> UB040
    | UB041_function_not_compatible                        -> UB041_function_not_compatible
    | UB042_access_atomic_structUnion_member               -> UB042_access_atomic_structUnion_member
    | UB043_indirection_invalid_value                      -> UB043_indirection_invalid_value
    | UB044                                                -> UB044
    | UB045a_division_by_zero                              -> UB045a_division_by_zero
    | UB045b_modulo_by_zero                                -> UB045b_modulo_by_zero
    | UB045c_quotient_not_representable                    -> UB045c_quotient_not_representable
    | UB046_array_pointer_outside                          -> UB046_array_pointer_outside
    | UB047a_array_pointer_addition_beyond_indirection     -> UB047a_array_pointer_addition_beyond_indirection
    | UB047b_array_pointer_subtraction_beyond_indirection  -> UB047b_array_pointer_subtraction_beyond_indirection
    | UB048_disjoint_array_pointers_subtraction            -> UB048_disjoint_array_pointers_subtraction
    | UB049                                                -> UB049
    | UB050_pointers_subtraction_not_representable         -> UB050_pointers_subtraction_not_representable
    | UB051a_negative_shift                                -> UB051a_negative_shift
    | UB51b_shift_too_large                                -> UB51b_shift_too_large
    | UB052a_negative_left_shift                           -> UB052a_negative_left_shift
    | UB052b_non_representable_left_shift                  -> UB052b_non_representable_left_shift
    | UB053_distinct_aggregate_union_pointer_comparison    -> UB053_distinct_aggregate_union_pointer_comparison
    | UB054a_inexactly_overlapping_assignment              -> UB054a_inexactly_overlapping_assignment
    | UB054b_incompatible_overlapping_assignment           -> UB054b_incompatible_overlapping_assignment
    | UB055_invalid_integer_constant_expression            -> UB055_invalid_integer_constant_expression
    | UB056                                                -> UB056
    | UB057                                                -> UB057
    | UB058                                                -> UB058
    | UB059_incomplete_no_linkage_identifier               -> UB059_incomplete_no_linkage_identifier
    | UB060_block_scope_function_with_storage_class        -> UB060_block_scope_function_with_storage_class
    | UB061_no_named_members                               -> UB061_no_named_members
    | UB062                                                -> UB062
    | UB063                                                -> UB063
    | UB064_modifying_const                                -> UB064_modifying_const
    | UB065                                                -> UB065
    | UB066_qualified_function_specification               -> UB066_qualified_function_specification
    | UB067                                                -> UB067
    | UB068                                                -> UB068
    | UB069                                                -> UB069
    | UB070_inline_not_defined                             -> UB070_inline_not_defined
    | UB071_noreturn                                       -> UB071_noreturn
    | UB072_incompatible_alignment_specifiers              -> UB072_incompatible_alignment_specifiers
    | UB073                                                -> UB073
    | UB074                                                -> UB074
    | UB075                                                -> UB075
    | UB076                                                -> UB076
    | UB077                                                -> UB077
    | UB078_modified_void_parameter                        -> UB078_modified_void_parameter
    | UB079                                                -> UB079
    | UB080                                                -> UB080
    | UB081_scalar_initializer_not_single_expression       -> UB081_scalar_initializer_not_single_expression
    | UB082                                                -> UB082
    | UB083                                                -> UB083
    | UB084                                                -> UB084
    | UB085                                                -> UB085
    | UB086_incomplete_adjusted_parameter                  -> UB086_incomplete_adjusted_parameter
    | UB087                                                -> UB087
    | UB088_reached_end_of_function                        -> UB088_reached_end_of_function
    | UB089_tentative_definition_internal_linkage          -> UB089_tentative_definition_internal_linkage
    | UB090                                                -> UB090
    | UB091                                                -> UB091
    | UB092                                                -> UB092
    | UB093                                                -> UB093
    | UB094                                                -> UB094
    | UB095                                                -> UB095
    | UB096                                                -> UB096
    | UB097                                                -> UB097
    | UB098                                                -> UB098
    | UB099                                                -> UB099
    | UB100                                                -> UB100
    | UB101                                                -> UB101
    | UB102                                                -> UB102
    | UB103                                                -> UB103
    | UB104                                                -> UB104
    | UB105                                                -> UB105
    | UB106                                                -> UB106
    | UB107                                                -> UB107
    | UB108                                                -> UB108
    | UB109                                                -> UB109
    | UB110                                                -> UB110
    | UB111_illtyped_assert                                -> UB111_illtyped_assert
    | UB112                                                -> UB112
    | UB113                                                -> UB113
    | UB114                                                -> UB114
    | UB115                                                -> UB115
    | UB116                                                -> UB116
    | UB117                                                -> UB117
    | UB118                                                -> UB118
    | UB119                                                -> UB119
    | UB120                                                -> UB120
    | UB121                                                -> UB121
    | UB122                                                -> UB122
    | UB123                                                -> UB123
    | UB124                                                -> UB124
    | UB125                                                -> UB125
    | UB126                                                -> UB126
    | UB127                                                -> UB127
    | UB128                                                -> UB128
    | UB129                                                -> UB129
    | UB130                                                -> UB130
    | UB131                                                -> UB131
    | UB132                                                -> UB132
    | UB133                                                -> UB133
    | UB134                                                -> UB134
    | UB135                                                -> UB135
    | UB136                                                -> UB136
    | UB137                                                -> UB137
    | UB138                                                -> UB138
    | UB139                                                -> UB139
    | UB140                                                -> UB140
    | UB141                                                -> UB141
    | UB142                                                -> UB142
    | UB143                                                -> UB143
    | UB144                                                -> UB144
    | UB145                                                -> UB145
    | UB146                                                -> UB146
    | UB147                                                -> UB147
    | UB148                                                -> UB148
    | UB149                                                -> UB149
    | UB150                                                -> UB150
    | UB151                                                -> UB151
    | UB152                                                -> UB152
    | UB153a_insufficient_arguments_for_format             -> UB153a_insufficient_arguments_for_format
    | UB153b_illtyped_argument_for_format                  -> UB153b_illtyped_argument_for_format
    | Invalid_format s                                     -> Invalid_format s
    | UB154                                                -> UB154
    | UB155                                                -> UB155
    | UB156                                                -> UB156
    | UB157                                                -> UB157
    | UB158_invalid_length_modifier                        -> UB158_invalid_length_modifier
    | UB159                                                -> UB159
    | UB160                                                -> UB160
    | UB161                                                -> UB161
    | UB162                                                -> UB162
    | UB163                                                -> UB163
    | UB164                                                -> UB164
    | UB165                                                -> UB165
    | UB166                                                -> UB166
    | UB167                                                -> UB167
    | UB168                                                -> UB168
    | UB169                                                -> UB169
    | UB170                                                -> UB170
    | UB171                                                -> UB171
    | UB172                                                -> UB172
    | UB173                                                -> UB173
    | UB174                                                -> UB174
    | UB175                                                -> UB175
    | UB176                                                -> UB176
    | UB177                                                -> UB177
    | UB178                                                -> UB178
    | UB179a_non_matching_allocation_free                  -> UB179a_non_matching_allocation_free
    | UB179b_dead_allocation_free                          -> UB179b_dead_allocation_free
    | UB179c_non_matching_allocation_realloc               -> UB179c_non_matching_allocation_realloc
    | UB179d_dead_allocation_realloc                       -> UB179d_dead_allocation_realloc
    | UB180                                                -> UB180
    | UB181                                                -> UB181
    | UB182                                                -> UB182
    | UB183                                                -> UB183
    | UB184                                                -> UB184
    | UB185                                                -> UB185
    | UB186                                                -> UB186
    | UB187                                                -> UB187
    | UB188                                                -> UB188
    | UB189                                                -> UB189
    | UB190                                                -> UB190
    | UB191                                                -> UB191
    | UB192                                                -> UB192
    | UB193                                                -> UB193
    | UB194                                                -> UB194
    | UB195                                                -> UB195
    | UB196                                                -> UB196
    | UB197                                                -> UB197
    | UB198                                                -> UB198
    | UB199                                                -> UB199
    | UB200                                                -> UB200
    | UB201                                                -> UB201
    | UB202                                                -> UB202
    | UB203                                                -> UB203
    | UB204_illtyped_Static_assert                         -> UB204_illtyped_Static_assert
    | UB205_atomic_store_memorder                          -> UB205_atomic_store_memorder
    | UB206_atomic_load_memorder                           -> UB206_atomic_load_memorder
    | UB207_atomic_compare_exchange_memorder               -> UB207_atomic_compare_exchange_memorder
    | UB_CERB001_integer_to_dead_pointer                   -> UB_CERB001_integer_to_dead_pointer
    | UB_CERB002a_out_of_bound_load                        -> UB_CERB002a_out_of_bound_load
    | UB_CERB002b_out_of_bound_store                       -> UB_CERB002b_out_of_bound_store
    | UB_CERB002c_out_of_bound_free                        -> UB_CERB002c_out_of_bound_free
    | UB_CERB002d_out_of_bound_realloc                     -> UB_CERB002d_out_of_bound_realloc
    | UB_CERB003_invalid_function_pointer                  -> UB_CERB003_invalid_function_pointer
    | UB_CHERI_InvalidCap                                  -> UB_CHERI_InvalidCap
    | UB_CHERI_InsufficientPermissions                     -> UB_CHERI_InsufficientPermissions
    | UB_CHERI_BoundsViolation                             -> UB_CHERI_BoundsViolation
    | UB_CHERI_UndefinedTag                                -> UB_CHERI_UndefinedTag

  let fromCoq_Symbol_description: CoqSymbol.symbol_description -> Symbol.symbol_description = function
    | SD_None -> SD_None
    | SD_unnamed_tag l -> SD_unnamed_tag (fromCoq_location l)
    | SD_Id s -> SD_Id s
    | SD_CN_Id s -> SD_CN_Id s
    | SD_ObjectAddress s -> SD_ObjectAddress s
    | SD_Return -> SD_Return
    | SD_FunArgValue s -> SD_FunArgValue s
    | SD_FunArg (l,v) -> SD_FunArg (fromCoq_location l, Z.to_int v)

  let fromCoq_Symbol_sym: CoqSymbol.sym -> Symbol.sym = function
    | Symbol (d,v,desc) -> Symbol (d,Z.to_int v, fromCoq_Symbol_description desc)

  let fromCoq_Symbol_prefix: CoqSymbol.prefix -> Symbol.prefix = function
    | PrefSource (loc, sl) -> PrefSource (fromCoq_location loc, List.map fromCoq_Symbol_sym sl)
    | PrefFunArg (l, d, v) -> PrefFunArg (fromCoq_location l, d, Z.to_int v)
    | PrefStringLiteral (l,d) -> PrefStringLiteral (fromCoq_location l, d)
    | PrefTemporaryLifetime (l, d) -> PrefTemporaryLifetime (fromCoq_location l, d)
    | PrefCompoundLiteral (l,d) ->  PrefCompoundLiteral (fromCoq_location l, d)
    | PrefMalloc -> PrefMalloc
    | PrefOther s -> PrefOther s

  let fromCoq_Symbol_identifier: CoqSymbol.identifier -> Symbol.identifier = function
    | Identifier (l,s) -> Identifier (fromCoq_location l, s)

  let fromCoq_integerBaseType: CoqIntegerType.integerBaseType -> integerBaseType = function
    | Ichar           -> Ichar
    | Short           -> Short
    | Int_            -> Int_
    | Long            -> Long
    | LongLong        -> LongLong
    | IntN_t n        -> IntN_t (Z.to_int n)
    | Int_leastN_t n  -> Int_leastN_t (Z.to_int n)
    | Int_fastN_t n   -> Int_fastN_t (Z.to_int n)
    | Intmax_t        -> Intmax_t
    | Intptr_t        -> Intptr_t
      
  let fromCoq_integerType: CoqIntegerType.integerType -> integerType = function
    | Char          -> Char
    | Bool          -> Bool
    | Signed bt     -> Signed (fromCoq_integerBaseType bt)
    | Unsigned bt   -> Unsigned (fromCoq_integerBaseType bt)
    | Enum s        -> Enum (fromCoq_Symbol_sym s)
    | Wchar_t       -> Wchar_t
    | Wint_t        -> Wint_t
    | Size_t        -> Size_t
    | Ptrdiff_t     -> Ptrdiff_t
    | Ptraddr_t       -> Ptraddr_t

  let fromCoq_realFloatingType: CoqCtype.realFloatingType -> realFloatingType = function
    | Float -> Float
    | Double -> Double
    | LongDouble -> LongDouble

  let fromCoq_floatingType (rft:CoqCtype.floatingType): floatingType =
    RealFloating (fromCoq_realFloatingType rft)

  let fromCoq_annot (ba:CoqAnnot.bmc_annot): Annot.bmc_annot =
    Abmc_id (Z.to_int ba)

  let fromCoq_attribute (a:CoqAnnot.attribute) : Annot.attribute =
    {
      attr_ns = Option.map (fromCoq_Symbol_identifier) a.attr_ns;
      attr_id =  fromCoq_Symbol_identifier a.attr_id ;
      attr_args =
        List.map (fun ((loc, s), ll) ->
            (fromCoq_location loc,
             s,
             List.map (fun (loc', s) -> (fromCoq_location loc', s)) ll)
          ) a.attr_args
    }

  let fromCoq_attributes (ats:CoqAnnot.attributes): Annot.attributes =
    Attrs (List.map fromCoq_attribute ats)

  let fromCoq_label_annot: CoqAnnot.label_annot -> Annot.label_annot = function
  | LAloop_prebody lid  -> LAloop_prebody (Z.to_int lid)
  | LAloop_body lid     -> LAloop_body (Z.to_int lid)
  | LAloop_continue lid -> LAloop_continue (Z.to_int lid)
  | LAloop_break lid    -> LAloop_break (Z.to_int lid)
  | LAreturn            -> LAreturn
  | LAswitch            -> LAswitch
  | LAcase              -> LAcase
  | LAdefault           -> LAdefault

  let fromCoq_cerb_attribute: CoqAnnot.cerb_attribute -> Annot.cerb_attribute = function
  | ACerb_with_address n -> ACerb_with_address n
  | ACerb_hidden -> ACerb_hidden

  let fromCoq_value_annot (v:CoqAnnot.value_annot): Annot.value_annot =
    Ainteger (fromCoq_integerType v)

  let fromCoq_annot: CoqAnnot.annot -> Annot.annot = function
  | Astd s       -> Astd s
  | Aloc loc     -> Aloc (fromCoq_location loc)
  | Auid s       -> Auid s
  | Amarker n    -> Amarker (Z.to_int n)
  | Amarker_object_types n -> Amarker_object_types (Z.to_int n)
  | Abmc ba      -> Abmc (fromCoq_annot ba)
  | Aattrs atr   -> Aattrs (fromCoq_attributes atr)
  | Atypedef s   -> Atypedef (fromCoq_Symbol_sym s)
  | Anot_explode -> Anot_explode
  | Alabel la    -> Alabel (fromCoq_label_annot la)
  | Acerb ca     -> Acerb (fromCoq_cerb_attribute ca)
  | Avalue va     -> Avalue (fromCoq_value_annot va)
  | Ainlined_label (l, s, la) ->  Ainlined_label
                                    (fromCoq_location l,
                                     fromCoq_Symbol_sym s,
                                     fromCoq_label_annot la)
  | Astmt -> Astmt
  | Aexpr -> Aexpr

  let fromCoq_basicType: CoqCtype.basicType -> basicType = function
    | Integer ity -> Integer (fromCoq_integerType ity)
    | Floating fty -> Floating (fromCoq_floatingType fty)

  let fromCoq_qualifiers (q:CoqCtype.qualifiers): qualifiers =
    {
      const    = q.const;
      restrict = q.restrict;
      volatile = q.volatile
    }

  let rec fromCoq_ctype: CoqCtype.ctype -> Ctype.ctype = function
    | Ctype (la, ct) -> Ctype (List.map fromCoq_annot la, fromCoq_ctype' ct)
  and fromCoq_ctype': CoqCtype.ctype' -> Ctype.ctype_ = function
    | Void -> Void
    | Basic bty -> Basic (fromCoq_basicType bty)
    | Array (cty, zo) -> Ctype.Array (fromCoq_ctype cty, zo)
    | Function ((q, cty),l,b) ->
       Function ((fromCoq_qualifiers q, fromCoq_ctype cty),
                 List.map (fun ((q,cty),b) -> (fromCoq_qualifiers q,fromCoq_ctype cty, b)) l,
                 b)
    | FunctionNoParams (q, cty) ->  FunctionNoParams (fromCoq_qualifiers q, fromCoq_ctype cty)
    | Pointer (q, cty) -> Pointer (fromCoq_qualifiers q, fromCoq_ctype cty)
    | Atomic cty ->  Atomic (fromCoq_ctype cty)
    | Struct s -> Struct (fromCoq_Symbol_sym s)
    | Union s -> Union (fromCoq_Symbol_sym s)

  let fromCoq_ovelap_status: MemCommonExe.overlap_status -> overlap_status = function
    | Disjoint -> Disjoint
    | ExactOverlap -> ExactOverlap
    | PartialOverlap -> PartialOverlap


  (* OCaml -> Coq type conversion *)

  open CerbTagDefs
  let toCoq_thread_id (tid:thread_id) : MemCommonExe.thread_id = Z.of_int tid

  let toCoq_unaryOperator: AilSyntax.unaryOperator -> CoqAilSyntax.unaryOperator = function
    | Plus        -> Plus
    | Minus       -> Minus
    | Bnot        -> Bnot
    | Address     -> Address
    | Indirection -> Indirection
    | PostfixIncr -> PostfixIncr
    | PostfixDecr -> PostfixDecr

  let toCoq_arithmeticOperator: AilSyntax.arithmeticOperator -> CoqAilSyntax.arithmeticOperator = function
    | Mul  -> Mul
    | Div  -> Div
    | Mod  -> Mod
    | Add  -> Add
    | Sub  -> Sub
    | Shl  -> Shl
    | Shr  -> Shr
    | Band -> Band
    | Bxor -> Bxor
    | Bor  -> Bor

  let toCoq_binaryOperator : AilSyntax.binaryOperator -> CoqAilSyntax.binaryOperator = function
    | Arithmetic ao -> Arithmetic (toCoq_arithmeticOperator ao)
    | Comma ->Comma
    | And   ->And
    | Or    ->Or
    | Lt    ->Lt
    | Gt    ->Gt
    | Le    ->Le
    | Ge    ->Ge
    | Eq    ->Eq
    | Ne    ->Ne

  let toCoq_derivecap_op: Mem_common.derivecap_op -> MemCommonExe.derivecap_op = function
    | DCunary uo -> DCunary (toCoq_unaryOperator uo)
    | DCbinary bo -> DCbinary (toCoq_binaryOperator bo)

  let toCoq_integer_operator: Mem_common.integer_operator -> MemCommonExe.integer_operator = function
  | IntAdd   -> IntAdd
  | IntSub   -> IntSub
  | IntMul   -> IntMul
  | IntDiv   -> IntDiv
  | IntRem_t -> IntRem_t
  | IntRem_f -> IntRem_f
  | IntExp   -> IntExp

  let toCoq_floating_operator: Mem_common.floating_operator -> MemCommonExe.floating_operator = function
    | FloatAdd -> FloatAdd
    | FloatSub -> FloatSub
    | FloatMul -> FloatMul
    | FloatDiv -> FloatDiv

  (* Intrinisics *)
  let fromCoq_type_predicate: MemCommonExe.type_predicate -> type_predicate = function
    | TyPred f -> TyPred (fun cty ->
                      lift_coq_serr (f (toCoq_ctype cty)))
    | TyIsPointer -> TyIsPointer

  let fromCoq_instrinsics_ret_spec: MemCommonExe.instrinsics_ret_spec -> instrinsics_ret_spec =function
    | ExactRet cty -> ExactRet (fromCoq_ctype cty)
    | CopyRet n -> CopyRet (Z.to_int n)

  let fromCoq_intrinsics_arg_spec: MemCommonExe.intrinsics_arg_spec -> intrinsics_arg_spec = function
    | ExactArg ct -> ExactArg (fromCoq_ctype ct)
    | PolymorphicArg tpl -> PolymorphicArg (List.map fromCoq_type_predicate tpl)
    | CopyArg n -> CopyArg (Z.to_int n)

  let fromCoq_intrinsics_signature ((rsig,asigs):MemCommonExe.intrinsics_signature) : Mem_common.intrinsics_signature =
    (fromCoq_instrinsics_ret_spec rsig,
     List.map fromCoq_intrinsics_arg_spec asigs)

  (* memMerror *)
  let fromCoq_memMError (e:CheriMemoryTypesExe.memMError) : mem_error Nondeterminism.kill_reason =
    match e with
    | Other me -> Other (fromCoq_mem_error me)
    | Undef0 (loc, ubs) ->
       Undef0 (fromCoq_location loc, List.map fromCoq_undefined_behaviour ubs)
    | InternalErr msg -> failwith msg


  open PPrint
  open Cerb_pp_prelude

  let string_of_provenance = function
    | CheriMemoryTypesExe.Prov_disabled ->
       "@disabled"
    | CheriMemoryTypesExe.Prov_none ->
       "@empty"
    | Prov_some alloc_id ->
       "@" ^ Z.to_string alloc_id

  let pp_pointer_value ?(is_verbose=false) (CheriMemoryTypesExe.PV (prov, ptrval_)) =
    match ptrval_ with
    | CheriMemoryTypesExe.PVfunction (FP_valid sym) ->
       !^ "Cfunction" ^^ P.parens (!^ (Pp_symbol.to_string_pretty
                                         (fromCoq_Symbol_sym sym)))
    | PVfunction (FP_invalid c) ->
       !^ "Cfunction" ^^ P.parens (!^ "invalid" ^^ P.colon ^^^ !^ (C.to_string c))
    (* !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">") *)
    | PVconcrete c ->
       if C.eqb c (C.cap_c0 ()) then
         !^ "NULL"
       else
         (* TODO: remove this idiotic hack when Lem's nat_big_num library expose "format" *)
         P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ (C.to_string c))

  let pp_integer_value = function
    | (CheriMemoryTypesExe.IV n) ->
       !^ (Z.to_string n)
    | (IC (is_signed, c)) ->
       let cs = (C.to_string c)
                ^ (if is_signed then " (signed)" else " (unsigned)")
       in
       !^ cs

  let pp_integer_value_for_core = pp_integer_value

  let pp_pretty_pointer_value = pp_pointer_value ~is_verbose:false
  let pp_pretty_integer_value ?basis ~use_upper = pp_integer_value

  let rec pp_mem_value = function
    | CheriMemoryTypesExe.MVunspecified _ ->
       PPrint.string "UNSPEC"
    | MVinteger (_, ival) ->
       pp_integer_value ival
    | MVfloating (_, fval) ->
       !^ (Float64.to_string fval)
    | MVpointer (_, ptrval) ->
       !^ "ptr" ^^ parens (pp_pointer_value ptrval)
    | MVarray mvals ->
       braces (
           comma_list pp_mem_value mvals
         )
    | MVstruct (tag_sym, xs) ->
       parens (!^ "struct" ^^^ !^ (Pp_symbol.to_string_pretty (fromCoq_Symbol_sym tag_sym))) ^^
         braces (
             comma_list (fun (ident, _, mval) ->
                 dot ^^ (Pp_symbol.pp_identifier (fromCoq_Symbol_identifier ident)) ^^ equals ^^^ pp_mem_value mval
               ) (List.map (fun ((a,b),c) -> (a,b,c)) xs)
           )
    | MVunion (tag_sym, membr_ident, mval) ->
       parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty (fromCoq_Symbol_sym tag_sym))) ^^
         braces (
             dot ^^ Pp_symbol.pp_identifier (fromCoq_Symbol_identifier membr_ident) ^^ equals ^^^
               pp_mem_value mval
           )

  let pp_pretty_mem_value ?basis ~use_upper = pp_mem_value

  (* --- debugging --- *)

  let print_allocations str st =
    Printf.fprintf stderr "BEGIN Allocation ==> %s\n" str;
    let l = ZMap.M.elements st.MM.allocations in
    List.iter (fun (aid,a) ->
        Printf.fprintf stderr "@%s: 0x%s,%s (%s,%s%s)\n"
          (Z.format "%d" aid)
          (Z.format "%x" a.CheriMemoryTypesExe.base)
          (Z.format "%d" a.size)
          (match a.taint with
           | CheriMemoryTypesExe.Exposed -> "exposed"
           | CheriMemoryTypesExe.Unexposed -> "unexposed"
          )
          (if a.is_dynamic then "dynamic" else "static")
          (if a.is_dead then ", dead" else "")
      ) l;
    prerr_endline "END Allocations"

  let print_bytemap str (st:MM.mem_state) =
    Printf.fprintf stderr "BEGIN BYTEMAP ==> %s\n" str;
    let l = AMap.M.elements st.bytemap in
    List.iter (fun (addr, b) ->
        Printf.fprintf stderr "@0x%s ==> %s: %s%s\n"
          (Z.format "%x" addr)
          (string_of_provenance b.CheriMemoryTypesExe.prov)
          (match b.CheriMemoryTypesExe.value with None -> "UNSPEC" | Some c -> string_of_int (int_of_char c))
          (match b.CheriMemoryTypesExe.copy_offset with None -> "" | Some n -> " [" ^ Z.to_string n ^ "]")
      ) l;
    prerr_endline "END BYTEMAP"

  let string_of_ghost_state (gs:CapabilitiesGS.coq_CapGhostState): string =
    let s = if gs.tag_unspecified then " notag" else "" in
    if gs.bounds_unspecified then (s ^ " nobounds") else s

  (** Prints provided capability tags table *)
  let print_captags str (st:MM.mem_state) =
    Printf.fprintf stderr "BEGIN CAPTAGS ==> %s\n" str;
    let l = AMap.M.elements st.capmeta in
    List.iter (fun (addr, (b,gs)) ->
        Printf.fprintf stderr "@0x%s ==> %s%s\n"
          (Z.format "%x" addr)
          (string_of_bool b)
          (string_of_ghost_state gs)
      ) l;
    prerr_endline "END CAPTAGS"

  (* lifting memM *)

  let lift_coq_memM ?(print_mem_state=true) label (m:'a MM.memM): 'a memM =
    ND (fun st ->
        if !Cerb_debug.debug_level >= 2 then
          Printf.fprintf stderr "MEMOP %s\n" label;
        if print_mem_state then
          if !Cerb_debug.debug_level >= 2 then
          begin
            print_allocations label st ;
            if !Cerb_debug.debug_level >= 3 then
              begin
                print_bytemap label st ;
                print_captags label st
              end
          end ;
        match m st with
        | (st', Coq_inl e) ->
           let e' = fromCoq_memMError e in
           (NDkilled e', st')
        | (st', Coq_inr a) -> (NDactive a, st')
      )

  (* --- Module implementation below *)

  (* Memory actions *)
  let allocate_object
        (tid: Mem_common.thread_id)
        (pref: Symbol.prefix)
        (int_val: integer_value)
        (ty: Ctype.ctype)
        (_: Z.num option)
        (init_opt: mem_value option): pointer_value memM
    =
    get >>= fun st ->
    Cerb_debug.print_debug 1 []
      (fun () -> "allocate_object. last_address=" ^
                   (String_nat_big_num.string_of_hexadecimal (MM.last_address st))
      );
    lift_coq_memM "allocate_object" (MM.allocate_object
                     (toCoq_thread_id tid)
                     (toCoq_Symbol_prefix pref)
                     int_val
                     (toCoq_ctype ty)
                     init_opt)


  let allocate_region
        (tid:Mem_common.thread_id)
        (pref:Symbol.prefix)
        (align_int:integer_value)
        (size_int: integer_value): pointer_value memM
    =
    get >>= fun st ->
    let label = "allocate_region " ^
                  "size=" ^ (Pp_utils.to_plain_string (pp_integer_value size_int)) ^
                    ", last_address=" ^ (String_nat_big_num.string_of_hexadecimal (MM.last_address st))
    in
    bind
      (lift_coq_memM label (MM.allocate_region
                              (toCoq_thread_id tid)
                              (toCoq_Symbol_prefix pref)
                              align_int
                              size_int))
      (fun newptr ->
        Cerb_debug.print_debug 1 []
          (fun () -> "MEMOP_RET allocate_region " ^
                       "size=" ^ (Pp_utils.to_plain_string (pp_integer_value size_int)) ^
                         " = " ^
                           Pp_utils.to_plain_string (pp_pointer_value ~is_verbose:false newptr));
        return newptr)

  let kill (loc:Cerb_location.t) (is_dyn:bool) (pv:pointer_value) : unit memM
    =
    let label = "kill "
                ^ (string_of_bool is_dyn) ^ ", "
                ^ Pp_utils.to_plain_string (pp_pointer_value ~is_verbose:false pv)
    in
    lift_coq_memM label (MM.kill (toCoq_location loc) is_dyn pv)

  let load (loc:Cerb_location.t) (ty:Ctype.ctype) (p:pointer_value): (footprint * mem_value) memM
    =
    let label = "load "
                ^ Pp_utils.to_plain_string (pp_pointer_value ~is_verbose:false p)
    in
    bind
      (lift_coq_memM label (MM.load (toCoq_location loc) (toCoq_ctype ty) p))
      (fun (fp,mval) ->
        Cerb_debug.print_debug 4 []
          (fun () -> "MEMOP_RET load =" ^ Pp_utils.to_plain_string (pp_mem_value mval));
        return (fp,mval))

  let store (loc:Cerb_location.t) (ty:Ctype.ctype) (is_locking:bool) (p:pointer_value) (mval:mem_value): footprint memM
    =
    let label = "store "
                ^ Pp_utils.to_plain_string (pp_pointer_value ~is_verbose:false p)
                ^ if !Cerb_debug.debug_level >= 4
                  then (" value="^ Pp_utils.to_plain_string (pp_mem_value mval))
                  else ""
    in
    lift_coq_memM label (MM.store (toCoq_location loc) (toCoq_ctype ty) is_locking p mval)

  let null_ptrval (ty:Ctype.ctype) : pointer_value
    = MM.null_ptrval (toCoq_ctype ty)

  let fun_ptrval (s:Symbol.sym) : pointer_value
    =
    lift_coq_serr (MM.fun_ptrval (toCoq_Symbol_sym s))

  (* Pointer value constructors *)
  let concrete_ptrval (i:Nat_big_num.num) (addr:Nat_big_num.num): pointer_value
    = lift_coq_serr (MM.concrete_ptrval i addr)

  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  (*TODO: revise that, just a hack for codegen*)
  let case_ptrval (pv:pointer_value) fnull ffun fconc =
    match pv with
    | CheriMemoryTypesExe.PV (_, PVfunction (FP_valid sym)) -> ffun (Some (fromCoq_Symbol_sym sym))
    | PV (_, PVfunction (FP_invalid c)) ->
       if MM.cap_is_null c
       then fnull Ctype.void
       else ffun None
    | PV (Prov_none, PVconcrete c)
      | PV (Prov_disabled, PVconcrete c) ->
       if MM.cap_is_null c
       then fconc None (C.cap_get_value c)
       else ffun None
    | PV (Prov_some i, PVconcrete c) ->
       if MM.cap_is_null c
       then fconc (Some i) (C.cap_get_value c)
       else ffun None

  let case_funsym_opt (st:MM.mem_state) (pv:pointer_value): Symbol.sym option
    = Option.map fromCoq_Symbol_sym (MM.case_funsym_opt st pv)

  (* Operations on pointer values *)
  let eq_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "eq_ptrval" (MM.eq_ptrval (toCoq_location loc) a b)
  let ne_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "ne_ptrval" (MM.ne_ptrval (toCoq_location loc) a b)
  let lt_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "lt_ptrval" (MM.lt_ptrval (toCoq_location loc) a b)
  let gt_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "gt_ptrval" (MM.gt_ptrval (toCoq_location loc) a b)
  let le_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "le_ptrval" (MM.le_ptrval (toCoq_location loc) a b)
  let ge_ptrval loc (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM "ge_ptrval" (MM.ge_ptrval (toCoq_location loc) a b)

  let diff_ptrval
        loc
        (diff_ty: Ctype.ctype)
        (ptrval1: pointer_value)
        (ptrval2: pointer_value)
      : integer_value memM
    =
    lift_coq_memM "diff_ptrval" (MM.diff_ptrval
                     (toCoq_location loc)
                     (toCoq_ctype diff_ty)
                     ptrval1
                     ptrval2)

  let update_prefix (pref, mval) : unit memM
    = lift_coq_memM "update_prefix" (MM.update_prefix ((toCoq_Symbol_prefix pref), mval))

  (* There is a sketch of implementation of this function in Coq but
     it requires some dependencies and fixpoint magic.  It OK to have
     in in OCaml for now *)
  let prefix_of_pointer (CheriMemoryTypesExe.PV (prov, pv)) : string option memM =
    if !Cerb_debug.debug_level >= 2 then
      Printf.fprintf stderr "MEMOP prefix_of_pointer\n";
    let open String_symbol in
    let rec aux addr (alloc:CheriMemoryTypesExe.allocation) = function
      | None
        | Some (Ctype (_, Void))
        | Some (Ctype (_, Function _))
        | Some (Ctype (_, FunctionNoParams _)) ->
         None
      | Some (Ctype (_, Basic _))
        | Some (Ctype (_, Union _))
        | Some (Ctype (_, Pointer _)) ->
         let offset = Z.sub addr alloc.base in
         Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix) ^ " + " ^ Z.to_string offset)
      | Some (Ctype (_, Struct tag_sym)) -> (* TODO: nested structs *)
         let offset = Z.sub addr alloc.base in
         let (offs, _) = lift_coq_serr (MM.offsetsof MM.coq_DEFAULT_FUEL (CerbTagDefs.tagDefs ()) (toCoq_Symbol_sym tag_sym)) in
         let offs = List.map (fun ((id,ty),n) ->(fromCoq_Symbol_identifier id,ty,n)) offs in
         let rec find = function
           | [] ->
              None
           | (Symbol.Identifier (_, memb), _, off) :: offs ->
              if offset = off
              then Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix) ^ "." ^ memb)
              else find offs
         in find offs
      | Some (Ctype (_, Array (ty, _))) ->
         let offset = Z.sub addr alloc.base in
         if Z.less offset alloc.size then
           let sz = lift_coq_serr (MM.sizeof MM.coq_DEFAULT_FUEL (Some (CerbTagDefs.tagDefs ())) (toCoq_ctype ty)) in
           let n = Z.div offset sz in
           Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix) ^ "[" ^ Z.to_string n ^ "]")
         else
           None
      | Some (Ctype (_, Atomic ty)) ->
         aux addr alloc @@ Some ty
    in
    match prov with
    | Prov_some alloc_id ->
       bind (lift_coq_memM ~print_mem_state:false "get_allocation" (MM.get_allocation alloc_id)) (fun alloc ->
           begin match pv with
           | PVconcrete addr ->
              if C.cap_get_value addr = alloc.base then
                return @@ Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix))
              else
                return @@ aux C.(cap_get_value addr) alloc (Option.map fromCoq_ctype alloc.ty)
           | _ ->
              return None
           end)
    | Prov_disabled ->
       begin match pv with
       | PVconcrete c ->
          let addr = C.cap_get_value c in
          bind (lift_coq_memM ~print_mem_state:false "find_cap_allocation" (MM.find_cap_allocation c)) (fun x ->
              let loc = Cerb_location.unknown in
              match x with
              | None -> fail ~loc (MerrAccess (LoadAccess, OutOfBoundPtr))
              | Some (alloc_id,_) ->
                 bind (lift_coq_memM ~print_mem_state:false "get_allocation" (MM.get_allocation alloc_id)) (fun alloc ->
                     if addr = alloc.base then
                       return @@ Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix))
                     else
                       return @@ aux addr alloc (Option.map fromCoq_ctype alloc.ty)
                   )
            )
       | _ ->
          return None
       end
    | _ ->
       return None

  let validForDeref_ptrval ref_ty ptrval
    = lift_coq_memM "validForDeref_ptrval" (MM.validForDeref_ptrval (toCoq_ctype ref_ty) ptrval)

  let isWellAligned_ptrval ref_ty ptrval
    = lift_coq_memM "isWellAligned_ptrval" (MM.isWellAligned_ptrval (toCoq_ctype ref_ty) ptrval)

  (* Casting operations *)
  let ptrfromint (loc:Cerb_location.t) (int_ty: Ctype.integerType) (ref_ty:Ctype.ctype) (int_v:integer_value): pointer_value memM
    = lift_coq_memM "ptrfromint" (MM.ptrfromint (toCoq_location loc) (toCoq_integerType int_ty) (toCoq_ctype ref_ty) int_v)

  let intfromptr (loc:Cerb_location.t) (ty:Ctype.ctype) (ity:Ctype.integerType) (ptr:pointer_value): integer_value memM
    = lift_coq_memM "intfromptr" (MM.intfromptr (toCoq_location loc) (toCoq_ctype ty) (toCoq_integerType ity) ptr)

  (* New operations for CHERI *)
  let derive_cap is_signed (bop:Mem_common.derivecap_op) ival1 ival2 =
    lift_coq_serr (MM.derive_cap is_signed (toCoq_derivecap_op bop) ival1 ival2)

  let cap_assign_value loc ival_cap ival_n =
    lift_coq_serr (MM.cap_assign_value (toCoq_location loc) ival_cap ival_n)

  let ptr_t_int_value v = lift_coq_serr (MM.ptr_t_int_value v)

  let null_cap = MM.null_cap

  (* Pointer shifting constructors *)
  let array_shift_ptrval p ty iv = lift_coq_serr @@ MM.array_shift_ptrval p (toCoq_ctype ty) iv
  let member_shift_ptrval p tag_sym memb_ident =
    lift_coq_serr (MM.member_shift_ptrval p (toCoq_Symbol_sym tag_sym) (toCoq_Symbol_identifier memb_ident))
  let eff_array_shift_ptrval loc ptrval ty iv =
    lift_coq_memM "eff_array_shift_ptrval" (MM.eff_array_shift_ptrval (toCoq_location loc) ptrval (toCoq_ctype ty) iv)
  let eff_member_shift_ptrval loc ptrval tag_sym memb_ident =
    lift_coq_memM "eff_member_shift_ptrval" (MM.eff_member_shift_ptrval (toCoq_location loc) ptrval (toCoq_Symbol_sym tag_sym) (toCoq_Symbol_identifier memb_ident))

  let memcpy loc ptrval1 ptrval2 size_int =
    lift_coq_memM "memcpy" (MM.memcpy (toCoq_location loc) ptrval1 ptrval2 size_int)

  let memcmp ptrval1 ptrval2 size_int =
    lift_coq_memM "memcmp" (MM.memcmp ptrval1 ptrval2 size_int)

  let realloc loc tid align ptr size =
    lift_coq_memM "realloc" (MM.realloc (toCoq_location loc) (Z.of_int tid) align ptr size)

  let va_start (args:(Ctype.ctype * pointer_value) list): integer_value memM =
    let args = List.map (fun (t,p) -> (toCoq_ctype t, p)) args in
    lift_coq_memM "va_start" (MM.va_start args)

  let va_copy (va:integer_value): integer_value memM =
    lift_coq_memM "va_copy" (MM.va_copy va)

  let va_arg (va:integer_value) (ty:Ctype.ctype): pointer_value memM =
    lift_coq_memM "va_arg" (MM.va_arg va (toCoq_ctype ty))

  let va_end (va:integer_value): unit memM =
    lift_coq_memM "va_end" (MM.va_end va)

  let va_list (va_idx:Nat_big_num.num): ((Ctype.ctype * pointer_value) list) memM =
    lift_coq_memM "va_list" (MM.va_list va_idx) >>= fun res ->
    return (List.map (fun (t,p) -> (fromCoq_ctype t, p)) res)

  let copy_alloc_id ival ptrval =
    lift_coq_memM "copy_alloc_id" (MM.copy_alloc_id ival ptrval)

  (* Integer value constructors *)
  let concurRead_ival ity sym =
    lift_coq_serr (MM.concurRead_ival (toCoq_integerType ity) (toCoq_Symbol_sym sym))

  let integer_ival = MM.integer_ival
  let max_ival ity = lift_coq_serr @@ MM.max_ival (toCoq_integerType ity)
  let min_ival ity = lift_coq_serr @@ MM.min_ival (toCoq_integerType ity)

  let op_ival iop v1 v2 =
    MM.op_ival (toCoq_integer_operator iop) v1 v2

  let offsetof_ival tagDefs tag_sym memb_ident =
    lift_coq_serr (MM.offsetof_ival
                     (toCoq_SymMap tagDefs)
                     (toCoq_Symbol_sym tag_sym)
                     (toCoq_Symbol_identifier memb_ident))

  let sizeof_ival ty = lift_coq_serr @@ MM.sizeof_ival (toCoq_ctype ty)
  let alignof_ival ty = lift_coq_serr @@ MM.alignof_ival (toCoq_ctype ty)

  let bitwise_complement_ival ity a =
    MM.bitwise_complement_ival (toCoq_integerType ity) a

  let bitwise_and_ival ity a b =
    MM.bitwise_and_ival (toCoq_integerType ity) a b
  let bitwise_or_ival ity a b =
    MM.bitwise_or_ival (toCoq_integerType ity) a b
  let bitwise_xor_ival ity a b =
    MM.bitwise_xor_ival (toCoq_integerType ity) a b

  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_integer_value v f_concrete _ =
    f_concrete (MM.num_of_int v)

  let is_specified_ival = MM.is_specified_ival

  (* Predicats on integer values *)
  let eq_ival = MM.eq_ival
  let lt_ival = MM.lt_ival
  let le_ival = MM.le_ival

  (* Floating value constructors *)
  let zero_fval = MM.zero_fval
  let one_fval = MM.one_fval
  let str_fval s = lift_coq_serr (MM.str_fval s)

  (* Floating value destructors *)
  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_fval (fval:floating_value) (_:unit -> 'a) (fconcrete:float -> 'a) : 'a
    = fconcrete (Float64.to_float fval)

  let op_fval fop a b =
    MM.op_fval (toCoq_floating_operator fop) a b

  (* Predicates on floating values *)
  let eq_fval = MM.eq_fval
  let lt_fval = MM.lt_fval
  let le_fval = MM.le_fval

  (* Integer <-> Floating casting constructors *)
  let fvfromint x = lift_coq_serr (MM.fvfromint x)
  let ivfromfloat ity fv =
    lift_coq_serr (MM.ivfromfloat (toCoq_integerType ity) fv)

  (* Memory value constructors *)
  let unspecified_mval ty =
    MM.unspecified_mval (toCoq_ctype ty)

  let integer_value_mval ity iv =
    MM.integer_value_mval (toCoq_integerType ity) iv

  let floating_value_mval fty fv =
    MM.floating_value_mval (toCoq_floatingType fty) fv

  let pointer_mval ty pv =
    MM.pointer_mval (toCoq_ctype ty) pv

  let array_mval = MM.array_mval

  let struct_mval tag_sym xs =
    MM.struct_mval
      (toCoq_Symbol_sym tag_sym)
      (List.map (fun (i,ty,v) -> ((toCoq_Symbol_identifier i, toCoq_ctype ty),v) ) xs)

  let union_mval tag_sym memb_ident mval =
    MM.union_mval (toCoq_Symbol_sym tag_sym) (toCoq_Symbol_identifier memb_ident) mval

  (* Memory value destructor *)
  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_mem_value
        (mval:mem_value)
        (f_unspec:ctype -> 'a)
        (_:Ctype.integerType -> Symbol.sym -> 'a)
        (f_ival:integerType -> integer_value -> 'a)
        (f_fval:floatingType -> floating_value -> 'a)
        (f_ptr:ctype -> pointer_value -> 'a)
        (f_array:mem_value list -> 'a)
        (f_struct: Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> 'a)
        (f_union:Symbol.sym -> Symbol.identifier -> mem_value -> 'a): 'a
    =
    match mval with
    | MVunspecified ty ->
       f_unspec (fromCoq_ctype ty)
    | MVinteger (ity, ival) ->
       f_ival (fromCoq_integerType ity) ival
    | MVfloating (fty, fval) ->
       f_fval (fromCoq_floatingType fty) fval
    | MVpointer (ref_ty, ptrval) ->
       f_ptr (fromCoq_ctype ref_ty) ptrval
    | MVarray mvals ->
       f_array mvals
    | MVstruct (tag_sym, xs) ->
       f_struct
         (fromCoq_Symbol_sym tag_sym)
         (List.map (fun ((i,ty),v) -> (fromCoq_Symbol_identifier i, fromCoq_ctype ty,v) ) xs)
    | MVunion (tag_sym, memb_ident, mval') ->
       f_union
         (fromCoq_Symbol_sym tag_sym)
         (fromCoq_Symbol_identifier memb_ident)
         mval'


  (* For race detection *)
  let sequencePoint =
    lift_coq_memM "sequencePoint" (MM.sequencePoint)

  (* Memory intrinsics (currently used in CHERI) *)
  let call_intrinsic loc name args =
    lift_coq_memM "call_intrinsic" (MM.call_intrinsic
                     (toCoq_location loc)
                     name
                     args)
    >>=
    (fun res ->
        Cerb_debug.print_debug 4 []
          (fun () ->
            match res with
            | Some mval -> "MEMOP_RET call_intrinsic = Just " ^ Pp_utils.to_plain_string (pp_mem_value mval)
            | None -> "MEMOP_RET call_intrinsic = None"
          );
        return res)

  let get_intrinsic_type_spec name =
    Option.map fromCoq_intrinsics_signature (MM.get_intrinsic_type_spec name)

  (* JSON serialisation *)
  let serialise_mem_state dig (st: mem_state) : Cerb_json.json
    = `Assoc [] (* TODO: not implemented *)

end

include CHERIMorello

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
      (* TODO: factorise *)
      let saved = !Cerb_colour.do_colour in
      Cerb_colour.do_colour := false;
      let ret = pp_mem_value mval in
      Cerb_colour.do_colour := saved;
      ret
    end
