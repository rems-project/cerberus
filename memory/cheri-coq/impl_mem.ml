[@@@warning "+8-37"]
open Ctype

(*open Ocaml_implementation*)
open Memory_model
open Mem_common
open CheriMemory
open CoqImplementation
open Morello

module MM = CheriMemory(MorelloCapability)(MorelloImpl)
module C = MorelloCapability

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
                       Debug_ocaml.print_debug 1 [] (fun () -> "HELLO: Concrete.with_constraints");
                       let rec eval_cs = function
                         | MC_empty ->
                            true
                         | MC_eq (ival1, ival2) ->
                            Stdlib.Option.value (MM.eq_ival None ival1 ival2) ~default:false
                         | MC_le (ival1, ival2) ->
                            Stdlib.Option.value (MM.le_ival None ival1 ival2) ~default:false
                         | MC_lt (ival1, ival2) ->
                            Stdlib.Option.value (MM.lt_ival None ival1 ival2) ~default:false
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
    ('a, string, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM

  let return = Nondeterminism.nd_return
  let bind = Nondeterminism.nd_bind

  let fromCoq_lexing_position (lp:CoqLocation.lexing_position): Lexing.position =
    {
      pos_fname = lp.pos_fname;
      pos_lnum = Z.to_int lp.pos_lnum;
      pos_bol = Z.to_int lp.pos_bol;
      pos_cnum = Z.to_int lp.pos_cnum;
    }

  let from_Coq_location_cursor: CoqLocation.location_cursor -> Location_ocaml.cursor = function
    | NoCursor -> NoCursor
    | PointCursor lp -> PointCursor (fromCoq_lexing_position lp)
    | RegionCursor (lp1,lp2) -> RegionCursor (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2)

  (* Coq -> OCaml type conversion *)
  let fromCoq_location: CoqLocation.location_ocaml -> Location_ocaml.t = function
    | Loc_unknown -> Location_ocaml.unknown
    | Loc_other s -> Location_ocaml.other s
    | Loc_point p -> Location_ocaml.point (fromCoq_lexing_position p)
    | Loc_region (lp1,lp2,lc) -> Location_ocaml.region (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2) (from_Coq_location_cursor lc)
    | Loc_regions (ps, lc) -> Location_ocaml.regions
                                (List.map (fun (lp1,lp2) -> (fromCoq_lexing_position lp1,fromCoq_lexing_position lp2)) ps)
                                (from_Coq_location_cursor lc)

  let fromCoq_access_kind: MM.access_kind -> access_kind = function
    | LoadAccess -> LoadAccess
    | StoreAccess -> StoreAccess

  let fromCoq_access_error: MM.access_error -> access_error = function
    | NullPtr        -> NullPtr
    | FunctionPtr    -> FunctionPtr
    | DeadPtr        -> DeadPtr
    | OutOfBoundPtr  -> OutOfBoundPtr
    | NoProvPtr      -> NoProvPtr
    | AtomicMemberof -> AtomicMemberof

  let from_Coq_vip_error (_:MM.vip_error) : vip_error =
    failwith "vip_error not supported in cheri-coq memory model"

  let from_Coq_mem_cheri_error: MM.mem_cheri_error -> mem_cheri_error = function
    | CheriErrDecodingCap -> CheriErrDecodingCap
    | CheriMerrInvalidCap -> CheriMerrInvalidCap
    | CheriMerrUnsufficientPermissions -> CheriMerrUnsufficientPermissions
    | CheriBoundsErr (((b, s), a), l) -> CheriBoundsErr ((b, s), a, l)

  let from_Coq_free_error: MM.free_error -> free_error = function
    | Free_static_allocation -> Free_static_allocation
    | Free_dead_allocation -> Free_dead_allocation
    | Free_out_of_bound -> Free_out_of_bound

  let fromCoq_mem_error: MM.mem_error -> mem_error = function
    | MerrOutsideLifetime s -> MerrOutsideLifetime s
    | MerrInternal s -> MerrInternal s
    | MerrOther s -> MerrOther s
    | MerrPtrdiff -> MerrPtrdiff
    | MerrAccess (l,k,e) -> MerrAccess (fromCoq_location l, fromCoq_access_kind k, fromCoq_access_error e)
    | MerrWriteOnReadOnly (b,l) -> MerrWriteOnReadOnly (b,fromCoq_location l)
    | MerrReadUninit l -> MerrReadUninit (fromCoq_location l)
    | MerrUndefinedFree (l,e) -> MerrUndefinedFree (fromCoq_location l, from_Coq_free_error e)
    | MerrUndefinedRealloc -> MerrUndefinedRealloc
    | MerrIntFromPtr l -> MerrIntFromPtr (fromCoq_location l)
    | MerrPtrFromInt -> MerrPtrFromInt
    | MerrPtrComparison -> MerrPtrComparison
    | MerrArrayShift l -> MerrArrayShift (fromCoq_location l)
    | MerrFreeNullPtr l -> MerrFreeNullPtr (fromCoq_location l)
    | MerrWIP s -> MerrWIP s
    | MerrVIP e -> MerrVIP (from_Coq_vip_error e)
    | MerrCHERI (l, e) -> MerrCHERI (fromCoq_location l, from_Coq_mem_cheri_error e)

  let fromCoq_undefined_behaviour (u:CoqUndefined.undefined_behaviour) : Undefined.undefined_behaviour = assert false (* TODO *)
  let fromCoq_Symbol_sym (s:CoqSymbol.sym): Symbol.sym = assert false (* TODO *)
  let fromCoq_Symbol_prefix (p:CoqSymbol.prefix) : Symbol.prefix = assert false (* TODO *)
  let fromCoq_Symbol_identifier (id:CoqSymbol.identifier) : Symbol.identifier = assert false (* TODO *)
  let fromCoq_ctype (ty:CoqCtype.ctype) : Ctype.ctype = assert false (* TODO *)
  let fromCoq_intrinsics_signature (s:MM.intrinsics_signature) : Mem_common.intrinsics_signature = assert false (* TODO *)
  let fromCoq_ovelap_status (s:MM.overlap_status) : overlap_status = assert false (* TODO *)
  let fromCoq_intgerType (s:CoqCtype.integerType) : integerType = assert false (* TODO *)
  let fromCoq_floatingType (s:CoqCtype.floatingType) : floatingType = assert false (* TODO *)

  (* OCaml -> Coq type conversion *)
  let toCoq_location (l:Location_ocaml.t): CoqLocation.location_ocaml = assert false (* TODO *)
  let toCoq_thread_id (tid:thread_id) : MM.thread_id = assert false (* TODO *)
  let toCoq_ctype (ty:Ctype.ctype) : CoqCtype.ctype = assert false (* TODO *)
  let toCoq_Symbol_prefix (p:Symbol.prefix) : CoqSymbol.prefix = assert false (* TODO *)
  let toCoq_Symbol_sym (s:Symbol.sym): CoqSymbol.sym = assert false (* TODO *)
  let toCoq_integerType (t:Ctype.integerType): CoqCtype.integerType = assert false (* TODO *)
  let toCoq_derivecap_op (o:Mem_common.derivecap_op) : MM.derivecap_op = assert false (* TODO *)
  let toCoq_Symbol_identifier (id:Symbol.identifier): CoqSymbol.identifier = assert false (* TODO *)
  let toCoq_ionteger_operator (iop:Mem_common.integer_operator) : MM.integer_operator = assert false (* TODO *)
  let toCoq_SymMap (m:(Symbol.sym, Ctype.tag_definition) Pmap.map) : CoqCtype.tag_definition CoqSymbol.SymMap.t  = assert false (* TODO *)
  let toCoq_floating_operator (fop:Mem_common.floating_operator) : MM.floating_operator = assert false (* TODO *)
  let toCoq_floatingType (fty:Ctype.floatingType) : CoqCtype.floatingType = assert false (* TODO *)

  let fromCoq_memMError (e:MM.memMError) : mem_error Nondeterminism.kill_reason =
    match e with
    | Other me -> Other (fromCoq_mem_error me)
    | Undef0 (loc, ubs) ->
       Undef0 (fromCoq_location loc, List.map fromCoq_undefined_behaviour ubs)
    | InternalErr msg -> failwith msg

  let lift_coq_memM (m:'a MM.memM): 'a memM =
    ND (fun st ->
        match m st with
        | (st', Coq_inl e) ->
           let e' = fromCoq_memMError e in
           (NDkilled e', st')
        | (st',Coq_inr a) -> (NDactive a, st')
      )

  let lift_coq_serr (s: (string, 'a) Datatypes.sum): 'a =
    match s with
    | Coq_inl errs -> failwith errs
    | Coq_inr v -> v

  let check_overlap a b = fromCoq_ovelap_status (MM.check_overlap a b)

  (* Memory actions *)
  let allocate_object
        (tid: Mem_common.thread_id)
        (pref: Symbol.prefix)
        (int_val: integer_value)
        (ty: Ctype.ctype)
        (init_opt: mem_value option): pointer_value memM
    =
    lift_coq_memM (MM.allocate_object
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
    lift_coq_memM (MM.allocate_region
                     (toCoq_thread_id tid)
                     (toCoq_Symbol_prefix pref)
                     align_int
                     size_int)

  let kill (loc:Location_ocaml.t) (is_dyn:bool) (pv:pointer_value) : unit memM
    =
    lift_coq_memM (MM.kill (toCoq_location loc) is_dyn pv)

  let load (loc:Location_ocaml.t) (ty:Ctype.ctype) (p:pointer_value): (footprint * mem_value) memM
    =
    lift_coq_memM (MM.load (toCoq_location loc) (toCoq_ctype ty) p)

  let store (loc:Location_ocaml.t) (ty:Ctype.ctype) (is_locking:bool) (p:pointer_value) (mval:mem_value): footprint memM
    =
    lift_coq_memM (MM.store (toCoq_location loc) (toCoq_ctype ty) is_locking p mval)

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
  let case_ptrval (pv:pointer_value) fnull ffun fconc _ =
    match pv with
    | MM.PV (_, PVfunction (FP_valid sym)) -> ffun (Some (fromCoq_Symbol_sym sym))
    | PV (_, PVfunction (FP_invalid c)) ->
       if MM.cap_is_null c
       then fnull ()
       else ffun None
    | PV (Prov_none, PVconcrete c) ->
       if MM.cap_is_null c
       then fconc ()
       else ffun None
    | PV (Prov_some i, PVconcrete c) ->
       if MM.cap_is_null c
       then fconc ()
       else ffun None
    | _ -> failwith "case_ptrval"

  let case_funsym_opt (st:mem_state) (pv:pointer_value): Symbol.sym option
    = Option.map fromCoq_Symbol_sym (MM.case_funsym_opt st pv)

  (* Operations on pointer values *)
  let eq_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.eq_ptrval a b)
  let ne_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.ne_ptrval a b)
  let lt_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.lt_ptrval a b)
  let gt_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.gt_ptrval a b)
  let le_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.le_ptrval a b)
  let ge_ptrval (a:pointer_value) (b:pointer_value) : bool memM =
    lift_coq_memM (MM.ge_ptrval a b)

  let diff_ptrval
        (diff_ty: Ctype.ctype)
        (ptrval1: pointer_value)
        (ptrval2: pointer_value)
      : integer_value memM
    =
    lift_coq_memM (MM.diff_ptrval
                     (toCoq_ctype diff_ty)
                     ptrval1
                     ptrval2)

  let update_prefix (pref, mval) : unit memM
    = lift_coq_memM (MM.update_prefix ((toCoq_Symbol_prefix pref), mval))

  (* There is a sketch of implementation of this function in Coq but
     it requires some dependencies and fixpoint magic.  It OK to have
     in in OCaml for now *)
  let prefix_of_pointer (MM.PV (prov, pv)) : string option memM =
    let open String_symbol in
    let rec aux addr (alloc:MM.allocation) = function
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
         let (offs, _) = lift_coq_serr (MM.offsetsof MM.coq_DEFAULT_FUEL (CoqTags.tagDefs ()) (toCoq_Symbol_sym tag_sym)) in
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
           let sz = lift_coq_serr (MM.sizeof MM.coq_DEFAULT_FUEL (Some (CoqTags.tagDefs ())) (toCoq_ctype ty)) in
           let n = Z.div offset sz in
           Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix) ^ "[" ^ Z.to_string n ^ "]")
         else
           None
      | Some (Ctype (_, Atomic ty)) ->
         aux addr alloc @@ Some ty
    in
    match prov with
    | Prov_some alloc_id ->
       bind (lift_coq_memM (MM.get_allocation alloc_id)) (fun alloc ->
           begin match pv with
           | PVconcrete addr ->
              if C.cap_get_value addr = alloc.base then
                return @@ Some (string_of_prefix (fromCoq_Symbol_prefix alloc.prefix))
              else
                return @@ aux C.(cap_get_value addr) alloc (Option.map fromCoq_ctype alloc.ty)
           | _ ->
              return None
           end)
    | _ ->
       return None

  let validForDeref_ptrval ref_ty ptrval
    = lift_coq_memM (MM.validForDeref_ptrval (toCoq_ctype ref_ty) ptrval)

  let isWellAligned_ptrval ref_ty ptrval
    = lift_coq_memM (MM.isWellAligned_ptrval (toCoq_ctype ref_ty) ptrval)

  (* Casting operations *)
  let ptrfromint (loc:Location_ocaml.t) (int_ty: Ctype.integerType) (ref_ty:Ctype.ctype) (int_v:integer_value): pointer_value memM
    = lift_coq_memM (MM.ptrfromint (toCoq_location loc) (toCoq_integerType int_ty) (toCoq_ctype ref_ty) int_v)

  let intfromptr (loc:Location_ocaml.t) (ty:Ctype.ctype) (ity:Ctype.integerType) (ptr:pointer_value): integer_value memM
    = lift_coq_memM (MM.intfromptr (toCoq_location loc) (toCoq_ctype ty) (toCoq_integerType ity) ptr)

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
    lift_coq_memM (MM.eff_array_shift_ptrval (toCoq_location loc) ptrval (toCoq_ctype ty) iv)
  let eff_member_shift_ptrval loc ptrval tag_sym memb_ident =
    lift_coq_memM (MM.eff_member_shift_ptrval (toCoq_location loc) ptrval (toCoq_Symbol_sym tag_sym) (toCoq_Symbol_identifier memb_ident))

  let memcpy ptrval1 ptrval2 size_int =
    lift_coq_memM (MM.memcpy ptrval1 ptrval2 size_int)

  let memcmp ptrval1 ptrval2 size_int =
    lift_coq_memM (MM.memcmp ptrval1 ptrval2 size_int)

  let realloc tid align ptr size =
    lift_coq_memM (MM.realloc (Z.of_int tid) align ptr size)

  (* TODO varargs not implemented *)
  let va_start (args:(Ctype.ctype * pointer_value) list): integer_value memM = assert false (* TODO *)
  let va_copy (va:integer_value): integer_value memM = assert false (* TODO *)
  let va_arg (va:integer_value) (ty:Ctype.ctype): pointer_value memM = assert false (* TODO *)
  let va_end (va:integer_value): unit memM = assert false (* TODO *)
  let va_list (va_idx:Nat_big_num.num): ((Ctype.ctype * pointer_value) list) memM = assert false (* TODO *)

  let copy_alloc_id ival ptrval =
    lift_coq_memM (MM.copy_alloc_id ival ptrval)

  (* Integer value constructors *)
  let concurRead_ival ity sym =
    lift_coq_serr (MM.concurRead_ival (toCoq_integerType ity) (toCoq_Symbol_sym sym))

  let integer_ival = MM.integer_ival
  let max_ival ity = lift_coq_serr @@ MM.max_ival (toCoq_integerType ity)
  let min_ival ity = lift_coq_serr @@ MM.min_ival (toCoq_integerType ity)

  let op_ival iop v1 v2 =
    MM.op_ival (toCoq_ionteger_operator iop) v1 v2

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
  let lt_ival = MM.eq_ival
  let le_ival = MM.le_ival

  let eval_integer_value = MM.eval_integer_value

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
       f_ival (fromCoq_intgerType ity) ival
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
    lift_coq_memM (MM.sequencePoint)

  (* Memory intrinsics (currently used in CHERI) *)
  let call_intrinsic loc name args =
    lift_coq_memM (MM.call_intrinsic
                     (toCoq_location loc)
                     name
                     args)

  let get_intrinsic_type_spec name =
    Option.map fromCoq_intrinsics_signature (MM.get_intrinsic_type_spec name)

  open PPrint
  open Pp_prelude

  let string_of_provenance = function
    | MM.Prov_none ->
       "@empty"
    | Prov_some alloc_id ->
       "@" ^ Z.to_string alloc_id
    | Prov_symbolic iota ->
       "@iota(" ^ Z.to_string iota ^ ")"
    | Prov_device ->
       "@device"

  let pp_pointer_value ?(is_verbose=false) (MM.PV (prov, ptrval_)) =
    match ptrval_ with
    | MM.PVfunction (FP_valid sym) ->
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
    | (MM.IV n) ->
       !^ (Z.to_string n)
    | (IC (is_signed, c)) ->
       let cs = (C.to_string c)
                ^ (if is_signed then " (signed)" else " (unsigned)")
       in
       !^ cs

  let pp_integer_value_for_core = pp_integer_value

  let pp_pretty_pointer_value = pp_pointer_value ~is_verbose:false
  let pp_pretty_integer_value _ = pp_integer_value

  let rec pp_mem_value = function
    | MM.MVunspecified _ ->
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

  let pp_pretty_mem_value _ = pp_mem_value

  (* JSON serialisation *)
  let serialise_mem_state dig (st: mem_state) : Json.json
    = `Assoc [] (* TODO: not implemented *)

end

include CHERIMorello

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
      (* TODO: factorise *)
      let saved = !Colour.do_colour in
      Colour.do_colour := false;
      let ret = pp_mem_value mval in
      Colour.do_colour := saved;
      ret
    end
