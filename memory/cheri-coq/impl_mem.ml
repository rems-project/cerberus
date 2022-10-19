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

  let check_overlap = MM.check_overlap

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

  (* Coq -> OCaml type conversion *)
  let fromCoq_mem_error (e:MM.mem_error) : mem_error = assert false (* TODO *)
  let fromCoq_location (l:CoqLocation.location_ocaml): Location_ocaml.t = assert false (* TODO *)
  let fromCoq_undefined_behaviour (u:CoqUndefined.undefined_behaviour) : Undefined.undefined_behaviour = assert false (* TODO *)
  let fromCoq_Symbol_sym (s:CoqSymbol.sym): Symbol.sym = assert false (* TODO *)
  let fromCoq_Symbol_prefix (p:CoqSymbol.prefix) : Symbol.prefix = assert false (* TODO *)
  let fromCoq_Symbol_identifier (id:CoqSymbol.identifier) : Symbol.identifier = assert false (* TODO *)
  let fromCoq_ctype (ty:CoqCtype.ctype) : Ctype.ctype = assert false (* TODO *)

  (* OCaml -> Coq type conversion *)
  let toCoq_thread_id (tid:thread_id) : MM.thread_id = assert false (* TODO *)
  let toCoq_ctype (ty:Ctype.ctype) : CoqCtype.ctype = assert false (* TODO *)
  let toCoq_location (l:Location_ocaml.t): CoqLocation.location_ocaml = assert false (* TODO *)
  let toCoq_Symbol_prefix (p:Symbol.prefix) : CoqSymbol.prefix = assert false (* TODO *)
  let toCoq_Symbol_sym (s:Symbol.sym): CoqSymbol.sym = assert false (* TODO *)

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
    | PV (_, PVfunction (FP_valid sym)) -> ffun (Some sym)
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

  (*

  val validForDeref_ptrval: Ctype.ctype -> pointer_value -> bool memM
  val isWellAligned_ptrval: Ctype.ctype -> pointer_value -> bool memM

  (* Casting operations *)
  (* the first ctype is the original integer type, the second is the target referenced type *)
  val ptrfromint: Location_ocaml.t -> Ctype.integerType -> Ctype.ctype -> integer_value -> pointer_value memM
  (* the first ctype is the original referenced type, the integerType is the target integer type *)
  val intfromptr: Location_ocaml.t -> Ctype.ctype -> Ctype.integerType -> pointer_value -> integer_value memM

  (* New operations for CHERI *)
  val derive_cap : bool(* is_signed *) -> Mem_common.derivecap_op -> integer_value -> integer_value -> integer_value
  val cap_assign_value: Location_ocaml.t -> integer_value -> integer_value -> integer_value
  val ptr_t_int_value: integer_value -> integer_value
  val null_cap : bool(* is_signed *) -> integer_value

  (* Pointer shifting constructors *)
  val array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value
  val member_shift_ptrval: pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value

  val eff_array_shift_ptrval: Location_ocaml.t -> pointer_value -> Ctype.ctype -> integer_value -> pointer_value memM
  val eff_member_shift_ptrval: Location_ocaml.t -> pointer_value -> Symbol.sym -> Symbol.identifier -> pointer_value memM

  val memcpy: pointer_value -> pointer_value -> integer_value -> pointer_value memM
  val memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM
  val realloc: Mem_common.thread_id -> integer_value -> pointer_value -> integer_value -> pointer_value memM

  val va_start: (Ctype.ctype * pointer_value) list -> integer_value memM
  val va_copy: integer_value -> integer_value memM
  val va_arg: integer_value -> Ctype.ctype -> pointer_value memM
  val va_end: integer_value -> unit memM
  val va_list: Nat_big_num.num -> ((Ctype.ctype * pointer_value) list) memM

  val copy_alloc_id: integer_value -> pointer_value -> pointer_value memM

  (* Integer value constructors *)
  val concurRead_ival: Ctype.integerType -> Symbol.sym -> integer_value
  val integer_ival: Nat_big_num.num -> integer_value
  val max_ival: Ctype.integerType -> integer_value
  val min_ival: Ctype.integerType -> integer_value
  val op_ival: Mem_common.integer_operator -> integer_value -> integer_value -> integer_value
  val offsetof_ival: (Symbol.sym, Ctype.tag_definition) Pmap.map -> Symbol.sym -> Symbol.identifier -> integer_value

  val sizeof_ival: Ctype.ctype -> integer_value
  val alignof_ival: Ctype.ctype -> integer_value

  val bitwise_complement_ival: Ctype.integerType -> integer_value -> integer_value
  val bitwise_and_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_or_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
  val bitwise_xor_ival: Ctype.integerType -> integer_value -> integer_value -> integer_value
   *)

  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_integer_value v f_concrete _ =
    f_concrete (MM.num_of_int v)

(*
  val is_specified_ival: integer_value -> bool

  (* Predicats on integer values *)
  val eq_ival: mem_state option -> integer_value -> integer_value -> bool option
  val lt_ival: mem_state option -> integer_value -> integer_value -> bool option
  val le_ival: mem_state option -> integer_value -> integer_value -> bool option

  val eval_integer_value: integer_value -> Nat_big_num.num option

  (* Floating value constructors *)
  val zero_fval: floating_value
  val one_fval: floating_value
  val str_fval: string -> floating_value
 *)

  (* Floating value destructors *)
  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_fval fval _ fconcrete =
    fconcrete fval

  (*
  (* Predicates on floating values *)
  val op_fval: Mem_common.floating_operator -> floating_value -> floating_value -> floating_value
  val eq_fval: floating_value -> floating_value -> bool
  val lt_fval: floating_value -> floating_value -> bool
  val le_fval: floating_value -> floating_value -> bool

  (* Integer <-> Floating casting constructors *)
  val fvfromint: integer_value -> floating_value
  val ivfromfloat: Ctype.integerType -> floating_value -> integer_value



  (* Memory value constructors *)
  (*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
  val unspecified_mval: Ctype.ctype -> mem_value
  val integer_value_mval: Ctype.integerType -> integer_value -> mem_value
  val floating_value_mval: Ctype.floatingType -> floating_value -> mem_value
  val pointer_mval: Ctype.ctype -> pointer_value -> mem_value
  val array_mval: mem_value list -> mem_value
  val struct_mval: Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> mem_value
  val union_mval: Symbol.sym -> Symbol.identifier -> mem_value -> mem_value

 *)

  (* Memory value destructor *)
  (* We have this one implemented in Coq but it looks like
     it OK to have in in OCaml for now *)
  let case_mem_value (mval:mem_value) f_unspec f_concur f_ival f_fval f_ptr f_array f_struct f_union =
    match mval with
    | MVunspecified ty ->
       f_unspec ty
    | MVinteger (ity, ival) ->
       f_ival ity ival
    | MVfloating (fty, fval) ->
       f_fval fty fval
    | MVpointer (ref_ty, ptrval) ->
       f_ptr ref_ty ptrval
    | MVarray mvals ->
       f_array mvals
    | MVstruct (tag_sym, xs) ->
       f_struct tag_sym xs
    | MVunion (tag_sym, memb_ident, mval') ->
       f_union tag_sym memb_ident mval'

(*

  (* For race detection *)
  val sequencePoint: unit memM

  (* Memory intrinsics (currently used in CHERI) *)

  val call_intrinsic: Location_ocaml.t -> string -> (mem_value list) -> (mem_value option) memM
  val get_intrinsic_type_spec: string -> Mem_common.intrinsics_signature option


  (* pretty printing *)
  val pp_pointer_value: ?is_verbose:bool -> pointer_value -> PPrint.document
  val pp_integer_value: integer_value -> PPrint.document
  val pp_integer_value_for_core: integer_value -> PPrint.document
  val pp_mem_value: mem_value -> PPrint.document
  val pp_pretty_pointer_value: pointer_value -> PPrint.document
  val pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document
  val pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document

(*
  val string_of_pointer_value: pointer_value -> string
  val string_of_integer_value: integer_value -> string
  val string_of_mem_value: mem_value -> stri(g
*)

  (* JSON serialisation *)
  val serialise_mem_state: Digest.t -> mem_state -> Json.json

                *)

end

open Morello

include CHERIMorello
