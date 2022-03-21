open Ctype

(*open Ocaml_implementation*)
open Memory_model
open Mem_common

module N = Nat_big_num

module L = struct
  include List
  include Lem_list
end

let ident_equal x y =
  Symbol.instance_Basic_classes_Eq_Symbol_identifier_dict.isEqual_method x y

let ctype_equal ty1 ty2 =
  let rec unqualify (Ctype (_, ty)) =
    match ty with
    | Void
      | Basic _
      | Struct _
      | Union _ ->
       ty
    | Function (p, (_, ret_ty), xs, b) ->
       Function (
           p,
           (no_qualifiers, Ctype ([], unqualify ret_ty)),
           List.map (fun (_, ty, _) -> (no_qualifiers, Ctype ([], unqualify ty), false)) xs,
           b
         )
    | FunctionNoParams (p, (_, ret_ty)) ->
       FunctionNoParams (
           p,
           (no_qualifiers, Ctype ([], unqualify ret_ty))
         )
    | Array (elem_ty, n_opt) ->
       Array (Ctype ([], unqualify elem_ty), n_opt)
    | Pointer (_, ref_ty) ->
       Pointer (no_qualifiers, Ctype ([], unqualify ref_ty))
    | Atomic atom_ty ->
       Atomic (Ctype ([], unqualify atom_ty))
  in Ctype.ctypeEqual (Ctype ([], unqualify ty1)) (Ctype ([], unqualify ty2))

module Eff : sig
  type ('a, 'err, 'cs, 'st) eff =
    ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff) -> ('b, 'err, 'cs, 'st) eff
  val (>>): ('a, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff
  val read: ('st -> 'a) -> ('a, 'err, 'cs, 'st) eff
  val update: ('st -> 'st) -> (unit, 'err, 'cs, 'st) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'err, 'cs, 'st) eff
  val get: ('st, 'err, 'cs, 'st) eff
  val put: 'st -> (unit, 'err, 'cs, 'st) eff
  (*  val fail: 'err -> ('a, 'err, 'cs, 'st) eff *)
  val mapM: ('a -> ('b, 'err, 'cs, 'st) eff) -> 'a list -> ('b list, 'err, 'cs, 'st) eff
  val msum: string -> (string * ('a, 'err, 'cs, 'st) eff) list -> ('a, 'err, 'cs, 'st) eff
end = struct
  type ('a, 'err, 'cs, 'st) eff =
    ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM

  let return = Nondeterminism.nd_return
  let (>>=) = Nondeterminism.nd_bind
  let (>>) k f = k >>= fun _ -> f

  let read = Nondeterminism.nd_read
  let update = Nondeterminism.nd_update
  let modify f =
    Nondeterminism.nd_get >>= fun st ->
    let (ret, st') = f st in
    Nondeterminism.nd_put st' >>= fun () ->
    return ret

  let get = Nondeterminism.nd_get
  let put = Nondeterminism.nd_put
  (*  let fail err = Nondeterminism.kill (Other err) *)
  let mapM _ _ = failwith "TODO: CHERI.Eff.mapM"

  let msum str xs =
    Nondeterminism.(
      msum Mem_common.instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict () str xs
    )
end




module IntMap = Map.Make(struct
                    type t = Nat_big_num.num
                    let compare = Nat_big_num.compare
                  end)


(* TODO: memoise this, it's stupid to recompute this every time... *)
(* NOTE: returns ([(memb_ident, type, offset)], last_offset) *)
let rec offsetsof tagDefs tag_sym =
  match Pmap.find tag_sym tagDefs with
  | StructDef (membrs_, flexible_opt) ->
     (* NOTE: the offset of a flexible array member is just like
        that of any other member *)
     let membrs = match flexible_opt with
       | None ->
          membrs_
       | Some (FlexibleArrayMember (attrs, ident, qs, ty)) ->
          membrs_ @ [(ident, (attrs, qs, ty))] in
     let (xs, maxoffset) =
       List.fold_left (fun (xs, last_offset) (membr, (_, _, ty)) ->
           let size = sizeof ~tagDefs ty in
           let align = alignof ~tagDefs ty in
           let x = last_offset mod align in
           let pad = if x = 0 then 0 else align - x in
           ((membr, ty, last_offset + pad) :: xs, last_offset + pad + size)
         ) ([], 0) membrs in
     (List.rev xs, maxoffset)
  | UnionDef membrs ->
     (List.map (fun (ident, (_, _, ty)) -> (ident, ty, 0)) membrs, 0)

and sizeof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) =
  match ty with
  | Void | Array (_, None) | Function _ | FunctionNoParams _ ->
     assert false
  | Basic (Integer ity) ->
     begin match (Ocaml_implementation.get ()).sizeof_ity ity with
     | Some n ->
        n
     | None ->
        failwith ("the concrete CHERI memory model requires a complete implementation sizeof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
     end
  | Basic (Floating fty) ->
     begin match (Ocaml_implementation.get ()).sizeof_fty fty with
     | Some n ->
        n
     | None ->
        failwith "the concrete CHERI memory model requires a complete implementation sizeof FLOAT"
     end
  | Array (elem_ty, Some n) ->
     (* TODO: what if too big? *)
     Nat_big_num.to_int n * sizeof ~tagDefs elem_ty
  | Pointer _ ->
     begin match (Ocaml_implementation.get ()).sizeof_pointer with
     | Some n ->
        n
     | None ->
        failwith "the concrete CHERI memory model requires a complete implementation sizeof POINTER"
     end
  | Atomic atom_ty ->
     sizeof ~tagDefs atom_ty
  | Struct tag_sym ->
     (* TODO: need to add trailing padding for structs with a flexible array member *)
     Debug_ocaml.warn [] (fun () -> "TODO: CHERI.sizeof doesn't add trailing padding for structs with a flexible array member");
     let (_, max_offset) = offsetsof tagDefs tag_sym in
     let align = alignof ~tagDefs cty in
     let x = max_offset mod align in
     if x = 0 then max_offset else max_offset + (align - x)
  | Union tag_sym ->
     begin match Pmap.find tag_sym (Tags.tagDefs ()) with
     | StructDef _ ->
        assert false
     | UnionDef membrs ->
        let (max_size, max_align) =
          List.fold_left (fun (acc_size, acc_align) (_, (_, _, ty)) ->
              (max acc_size (sizeof ~tagDefs ty), max acc_align (alignof ~tagDefs ty))
            ) (0, 0) membrs in
        (* NOTE: adding padding at the end to satisfy the alignment constraints *)
        let x = max_size mod max_align in
        if x = 0 then max_size else max_size + (max_align - x)
     end

and alignof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) =
  match ty with
  | Void ->
     assert false
  | Basic (Integer ity) ->
     begin match (Ocaml_implementation.get ()).alignof_ity ity with
     | Some n ->
        n
     | None ->
        failwith ("the concrete CHERI memory model requires a complete implementation alignof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
     end
  | Basic (Floating fty) ->
     begin match (Ocaml_implementation.get ()).alignof_fty fty with
     | Some n ->
        n
     | None ->
        failwith "the concrete CHERI memory model requires a complete implementation alignof FLOATING"
     end
  | Array (elem_ty, _) ->
     alignof ~tagDefs elem_ty
  | Function _
    | FunctionNoParams _ ->
     assert false
  | Pointer _ ->
     begin match (Ocaml_implementation.get ()).alignof_pointer with
     | Some n ->
        n
     | None ->
        failwith "the concrete CHERI memory model requires a complete implementation alignof POINTER"
     end
  | Atomic atom_ty ->
     alignof ~tagDefs atom_ty
  | Struct tag_sym ->
     begin match Pmap.find tag_sym tagDefs with
     | UnionDef _ ->
        assert false
     | StructDef (membrs, flexible_opt)  ->
        (* NOTE: we take into account the potential flexible array member by tweaking
           the accumulator init of the fold. *)
        let init = match flexible_opt with
          | None ->
             0
          | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
             alignof ~tagDefs (Ctype ([], Array (elem_ty, None))) in
        (* NOTE: Structs (and unions) alignment is that of the maximum alignment
           of any of their components. *)
        List.fold_left (fun acc (_, (_, _, ty)) ->
            max (alignof ~tagDefs ty) acc
          ) init membrs
     end
  | Union tag_sym ->
     begin match Pmap.find tag_sym (Tags.tagDefs ()) with
     | StructDef _ ->
        assert false
     | UnionDef membrs ->
        (* NOTE: Structs (and unions) alignment is that of the maximum alignment
           of any of their components. *)
        List.fold_left (fun acc (_, (_, _, ty)) ->
            max (alignof ~tagDefs ty) acc
          ) 0 membrs
     end

open Capability

module CHERI (C:Capability
              with type vaddr = N.num
              with type vaddr_interval = N.num*N.num
         ) : Memory = struct
  let name = "CHERI memory model"

  (* INTERNAL: only for PNVI-ae-udi (this is iota) *)
  type symbolic_storage_instance_id = N.num

  (* INTERNAL: storage_instance_id *)
  type storage_instance_id = N.num

  (* INTERNAL: provenance *)
  type provenance =
    | Prov_none
    | Prov_some of storage_instance_id
    | Prov_symbolic of symbolic_storage_instance_id (* only for PNVI-ae-udi *)
    | Prov_device

  (* Note: using Z instead of int64 because we need to be able to have
     unsigned 64bits values *)
  type pointer_value_base =
    | PVnull of ctype
    | PVfunction of Symbol.sym
    | PVconcrete of C.t

  type pointer_value =
    | PV of provenance * pointer_value_base

  type integer_value =
    | IV of provenance * Nat_big_num.num
    | IC of provenance * C.t (* for [u]intptr_t *)

  let num_of_int = function
    | IV (_,n) -> n
    | IC (_,c) -> C.cap_get_value c

  type floating_value =
    (* TODO: hack hack hack ==> OCaml's float are 64bits *)
    float

  (* same as [mem_value] but can contain [mem_error]*)
  type mem_value_with_err =
    | MVEunspecified of ctype
    | MVEinteger of integerType * integer_value
    | MVEfloating of floatingType * floating_value
    | MVEpointer of ctype * pointer_value
    | MVEarray of mem_value_with_err list
    | MVEstruct of Symbol.sym (*struct/union tag*) * (Symbol.identifier (*member*) * ctype * mem_value_with_err) list
    | MVEunion of Symbol.sym (*struct/union tag*) * Symbol.identifier (*member*) * mem_value_with_err
    | MVErr of mem_error
                 [@@warning "-37"]

  type mem_value =
    | MVunspecified of ctype
    | MVinteger of integerType * integer_value
    | MVfloating of floatingType * floating_value
    | MVpointer of ctype * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym (*struct/union tag*) * (Symbol.identifier (*member*) * ctype * mem_value) list
    | MVunion of Symbol.sym (*struct/union tag*) * Symbol.identifier (*member*) * mem_value

  type mem_iv_constraint = integer_value mem_constraint
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
                       Debug_ocaml.print_debug 1 [] (fun () -> "HELLO: CHERI.with_constraints");
                       let rec eval_cs = function
                         | MC_empty ->
                            true
                         | MC_eq (IV (prov1, n1), IV (prov2, n2)) ->
                            Nat_big_num.equal n1 n2
                         | MC_eq (IV (prov1, n), IC (prov2, c)) ->
                            Nat_big_num.equal n (C.cap_get_value c)
                         | MC_eq (IC (prov1, c), IV (prov2, n)) ->
                            Nat_big_num.equal n (C.cap_get_value c)
                         | MC_eq (IC (prov1, c1), IC (prov2, c2)) ->
                            Nat_big_num.equal (C.cap_get_value c1) (C.cap_get_value c2)
                         | MC_le (IV (prov1, n1), IV (prov2, n2)) ->
                            Nat_big_num.less_equal n1 n2
                         | MC_le (IV (prov1, n), IC (prov2, c)) ->
                            Nat_big_num.less_equal n (C.cap_get_value c)
                         | MC_le (IC (prov1, c), IV (prov2, n)) ->
                            Nat_big_num.less_equal (C.cap_get_value c) n
                         | MC_le (IC (prov1, c1), IC (prov2, c2)) ->
                            Nat_big_num.less_equal (C.cap_get_value c1) (C.cap_get_value c2)
                         | MC_lt (IV (prov1, n1), IV (prov2, n2)) ->
                            Nat_big_num.less n1 n2
                         | MC_lt (IV (prov1, n), IC (prov2, c)) ->
                            Nat_big_num.less n (C.cap_get_value c)
                         | MC_lt (IC (prov1, c), IV (prov2, n)) ->
                            Nat_big_num.less (C.cap_get_value c) n
                         | MC_lt (IC (prov1, c1), IC (prov2, c2)) ->
                            Nat_big_num.less (C.cap_get_value c1) (C.cap_get_value c2)
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

  open Eff


  (* INTERNAL: allocation *)
  type allocation = {
      prefix: Symbol.prefix;
      base: C.vaddr;
      size: N.num; (*TODO: this is probably unnecessary once we have the type *)
      ty: ctype option; (* None when dynamically allocated *)
      is_readonly: bool;
      taint: [ `Unexposed | `Exposed ]; (* NOTE: PNVI-ae, PNVI-ae-udi *)
    }

  (* INTERNAL: Abstract bytes *)
  module AbsByte = struct
    type t = {
        prov: provenance;
        copy_offset: int option;
        value: char option;
      }

    let v prov ?(copy_offset = None) value =
      { prov; copy_offset; value }

    let to_json json_of_prov b =
      `Assoc [("prov", json_of_prov b. prov);
              ("offset", Json.of_option Json.of_int b.copy_offset);
              ("value", Json.of_option Json.of_char b.value);]

    (* Given a (non-empty) list of bytes combine their provenance if their are
       compatible. Returns the empty provenance otherwise *)
    let split_bytes = function
      | [] ->
         failwith "CHERI.AbsByte.split_bytes: called on an empty list"
      | bs ->
         let (_prov, rev_values, offset_status) =
           List.fold_left (fun (prov_acc, val_acc, offset_acc) b ->
               let prov_acc' = match prov_acc, b.prov with
                 | `VALID (Prov_some alloc_id1), Prov_some alloc_id2 when alloc_id1 <> alloc_id2 ->
                    `INVALID
                 | `VALID (Prov_symbolic iota1), Prov_symbolic iota2 when iota1 <> iota2 ->
                    `INVALID
                 | `VALID (Prov_symbolic iota1), Prov_some alloc_id' ->
                    failwith "TODO(iota) split_bytes 1"
                 | `VALID (Prov_some alloc_id), Prov_symbolic iota ->
                    failwith "TODO(iota) split_bytes 2"
                 | `VALID Prov_none, (Prov_some _ as new_prov) ->
                    `VALID new_prov
                 | `VALID Prov_none, (Prov_symbolic _ as new_prov) ->
                    `VALID new_prov
                 | prev_acc, _ ->
                    prev_acc in
               let offset_acc' = match offset_acc, b.copy_offset with
                 | `PtrBytes n1, Some n2 when n1 = n2 ->
                    `PtrBytes (n1+1)
                 | _ ->
                    `OtherBytes in
               (prov_acc', b.value :: val_acc, offset_acc')
             ) (`VALID Prov_none, [], `PtrBytes 0) bs in
         ( (match _prov with `INVALID -> Prov_none | `VALID z -> z)
         , (match offset_status with `OtherBytes -> `NotValidPtrProv | _ -> `ValidPtrProv)
         , List.rev rev_values )

    (* PNVI-ae-udi *)
    let provs_of_bytes bs =
      let xs = List.fold_left (fun acc b ->
                   match b.prov with
                   | Prov_none ->
                      acc
                   | Prov_some alloc_id ->
                      alloc_id :: acc
                   | Prov_symbolic iota -> (* of symbolic_storage_instance_id (* only for PNVI-ae-udi *) *)
                      acc (* TODO(iota) *)
                   | Prov_device ->
                      acc
                 ) [] bs in
      match xs with
      | [] ->
         `NoTaint
      | _ ->
         `NewTaint xs
  end

  type mem_state = {
      next_alloc_id: storage_instance_id;
      next_iota: symbolic_storage_instance_id;
      last_address: C.vaddr;
      allocations: allocation IntMap.t;
      (* this is only for PNVI-ae-udi *)
      iota_map: [ `Single of storage_instance_id | `Double of storage_instance_id * storage_instance_id ] IntMap.t;
      funptrmap: (Digest.t * string) IntMap.t;
      varargs: (int * (ctype * pointer_value) list) IntMap.t;
      next_varargs_id: N.num;
      bytemap: AbsByte.t IntMap.t;
      captags: bool IntMap.t;

      dead_allocations: storage_instance_id list;
      dynamic_addrs: C.vaddr list;
      last_used: storage_instance_id option;
    }

  let initial_mem_state = {
      next_alloc_id= Nat_big_num.zero;
      next_iota= N.zero;
      allocations= IntMap.empty;
      iota_map= IntMap.empty;
      last_address= N.of_int 0xFFFFFFFF; (* TODO: this is a random impl-def choice *)
      funptrmap = IntMap.empty;
      varargs = IntMap.empty;
      next_varargs_id = N.zero;
      bytemap= IntMap.empty;
      captags= IntMap.empty;

      dead_allocations= [];
      dynamic_addrs= [];
      last_used= None;
    }

  type footprint =
    (* base address, size *)
    | FP of C.vaddr * N.num

  let check_overlap (FP (b1, sz1)) (FP (b2, sz2)) =
    if N.equal b1 b2 && N.equal sz1 sz2 then
      ExactOverlap
    else if N.(less_equal (add b1 sz1) b2) || N.(less_equal (add b2 sz2) b1) then
      Disjoint
    else
      PartialOverlap

  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff

  let return = Eff.return
  let bind = Eff.(>>=)

  (* TODO: hackish *)
  let fail err =
    let loc = match err with
      | MerrAccess (loc, _, _)
        | MerrWriteOnReadOnly loc
        | MerrReadUninit loc
        | MerrUndefinedFree (loc, _)
        | MerrFreeNullPtr loc
        | MerrArrayShift loc ->
         loc
      | MerrOutsideLifetime _
        | MerrInternal _
        | MerrOther _
        | MerrPtrdiff
        | MerrUndefinedRealloc
        | MerrIntFromPtr
        | MerrPtrFromInt
        | MerrPtrComparison
        | MerrWIP _
        | MerrVIP _
        | MerrCHERI _ ->
         Location_ocaml.other "Concrete" in
    let open Nondeterminism in
    match undefinedFromMem_error err with
    | Some ubs ->
       kill (Undef0 (loc, ubs))
    | None ->
       kill (Other err)



  let string_of_provenance = function
    | Prov_none ->
       "@empty"
    | Prov_some alloc_id ->
       "@" ^ N.to_string alloc_id
    | Prov_symbolic iota ->
       "@iota(" ^ N.to_string iota ^ ")"
    | Prov_device ->
       "@device"

  (* pretty printing *)
  open PPrint
  open Pp_prelude
  let pp_pointer_value (PV (prov, ptrval_))=
    match ptrval_ with
    | PVnull ty ->
       !^ "NULL" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
    | PVfunction sym ->
       !^ "Cfunction" ^^ P.parens (!^ (Pp_symbol.to_string_pretty sym))
    (* !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">") *)
    | PVconcrete n ->
       (* TODO: remove this idiotic hack when Lem's nat_big_num library expose "format" *)
       P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ (C.to_string n))

  let pp_integer_value = function
    | (IV (prov, n)) ->
       if !Debug_ocaml.debug_level >= 3 then
         !^ ("<" ^ string_of_provenance prov ^ ">:" ^ Nat_big_num.to_string n)
       else
         !^ (Nat_big_num.to_string n)
    | (IC (prov, c)) ->
       (* TODO: better pretty-printing of capabilities *)
       let n = (C.cap_get_value c) in
       if !Debug_ocaml.debug_level >= 3 then
         !^ ("<" ^ string_of_provenance prov ^ ">:" ^ Nat_big_num.to_string n)
       else
         !^ (Nat_big_num.to_string n)

  let pp_integer_value_for_core = pp_integer_value

  let rec mem_value_strip_err x =
    let open Eff in
    match x with
    | MVEunspecified x -> return (MVunspecified x)
    | MVEinteger (x,y) -> return (MVinteger (x,y))
    | MVEfloating (x,y) -> return (MVfloating (x,y))
    | MVEpointer (x,y) -> return (MVpointer (x,y))
    | MVEarray l ->
       mapM mem_value_strip_err l >>= (fun x -> return (MVarray x))
    | MVEstruct (x,y) ->
       mapM (fun (x,y,z) -> mem_value_strip_err z >>= (fun z' -> return (x,y,z'))) y
       >>= (fun y' -> return (MVstruct (x,y')))
    | MVEunion (x,y,z) -> mem_value_strip_err z >>= (fun z' ->
        return (MVunion (x,y,z')))
    | MVErr err -> fail err

  let rec pp_mem_value = function
    | MVunspecified _ ->
       PPrint.string "UNSPEC"
    | MVinteger (_, ival) ->
       pp_integer_value ival
    | MVfloating (_, fval) ->
       !^ (string_of_float fval)
    | MVpointer (_, ptrval) ->
       !^ "ptr" ^^ parens (pp_pointer_value ptrval)
    | MVarray mvals ->
       braces (
           comma_list pp_mem_value mvals
         )
    | MVstruct (tag_sym, xs) ->
       parens (!^ "struct" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
                                                                               comma_list (fun (ident, _, mval) ->
                                                                                   dot ^^ Pp_symbol.pp_identifier ident ^^ equals ^^^ pp_mem_value mval
                                                                                 ) xs
                                                                             )
    | MVunion (tag_sym, membr_ident, mval) ->
       parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
                                                                              dot ^^ Pp_symbol.pp_identifier membr_ident ^^ equals ^^^
                                                                                pp_mem_value mval
                                                                            )


  (* TODO: this is stupid, we need to allow the outside world to specify
     what memory ranges are in device memory *)
  let device_ranges : (C.vaddr * C.vaddr) list =
    (* TODO: these are some hardcoded ranges to match the Charon tests... *)
    (* NOTE: these two ranges only have 4 bytes (e.g. one int) *)
    [ (N.of_int64 0x40000000L, N.of_int64 0x40000004L)
    ; (N.of_int64 0xABCL, N.of_int64 0XAC0L) ]


  let is_PNVI () =
    (*    match Switches.(has_switch_pred (function SW_no_integer_provenance _ -> true | _ -> false)) with *)
    match Switches.(has_switch_pred (function SW_PNVI _ -> true | _ -> false)) with
    | None ->
       false
    | Some _ ->
       true

  (* NOTE: since we are fusing PVI and PVNI together any creation of an integer_value should
     be done through this function to unsure we always use Prov_none in PVNI *)
  let mk_ival prov n =
    if is_PNVI () then
      IV (Prov_none, n)
    else
      (* We are in the mode where integer values have a provenance *)
      IV (prov, n)

  (* TODO: DEBUG *)
  let print_bytemap str =
    if !Debug_ocaml.debug_level >= 3 then begin
        Printf.fprintf stderr "BEGIN BYTEMAP ==> %s\n" str;
        get >>= fun st ->
        IntMap.iter AbsByte.(fun addr b ->
          Printf.fprintf stderr "@%s ==> %s: %s%s\n"
            (N.to_string addr)
            (string_of_provenance b.prov)
            (match b.value with None -> "UNSPEC" | Some c -> string_of_int (int_of_char c))
            (match b.copy_offset with None -> "" | Some n -> " [" ^ string_of_int n ^ "]")
        ) st.bytemap;
        prerr_endline "END";
        return ()
      end else
      return ()

  let is_dynamic addr : bool memM =
    get >>= fun st ->
    return (List.mem addr st.dynamic_addrs)

  let is_dead alloc_id : bool memM =
    get >>= fun st ->
    return (List.mem alloc_id st.dead_allocations)

  let get_allocation alloc_id : allocation memM =
    get >>= fun st ->
    match IntMap.find_opt alloc_id st.allocations with
    | Some ret ->
       return ret
    | None ->
       fail (MerrOutsideLifetime ("CHERI.get_allocation, alloc_id=" ^ N.to_string alloc_id))

  let is_within_bound alloc_id lvalue_ty addr =
    get_allocation alloc_id >>= fun alloc ->
    return (N.less_equal alloc.base addr && N.less_equal (N.add addr (N.of_int (sizeof lvalue_ty))) (N.add alloc.base alloc.size))

  let is_within_device ty addr =
    return begin
        List.exists (fun (min, max) ->
            N.less_equal min addr && N.less_equal (N.add addr (N.of_int (sizeof ty))) max
          ) device_ranges
      end

  (* NOTE: this will have to change when moving to a subobject semantics *)
  let is_atomic_member_access alloc_id lvalue_ty addr =
    get_allocation alloc_id >>= fun alloc ->
    match alloc.ty with
    | Some ty when AilTypesAux.is_atomic ty ->
       if    addr = alloc.base && N.equal (N.of_int (sizeof lvalue_ty)) alloc.size
             && Ctype.ctypeEqual lvalue_ty ty then
         (* the types equality check is to deal with the case where the
            first member is accessed and their are no padding bytes ... *)
         return false
       else
         return true
    | _ ->
       return false

  (* INTERNAL: fetch_bytes *)
  let fetch_bytes bytemap base_addr n_bytes : AbsByte.t list =
    List.map (fun addr ->
        match IntMap.find_opt addr bytemap with
        | Some b ->
           b
        | None ->
           AbsByte.v Prov_none None
      ) (List.init n_bytes (fun z ->
             (* NOTE: the reversal in the offset is to model
                little-endianness *)
             (*           let offset = n_bytes - 1 - z in *)
             (*KKK*)
             let offset = z in
             Nat_big_num.(add base_addr (of_int offset))
      ))


  let write_bytes base_addr bs =
    get >>= fun st ->
    return begin
        (* NOTE: the reversal caused by the fold_left is what we want because of
           little-endianness *)
        List.fold_left (fun acc (addr, b) ->
            IntMap.add addr b acc
          ) st.bytemap begin
            List.init (List.length bs) (fun z ->
                (Nat_big_num.(add base_addr (of_int z), L.nth bs z))
              )
          end
      end

  let int_of_bytes is_signed bs =
    (* NOTE: the reverse is from little-endianness *)
    match List.rev bs with
    | [] ->
       assert false
    | cs when L.length cs > 16 ->
       assert false
    | (first::_ as cs) ->
       (* NOTE: this is to preserve the binary signedness *)
       let init =
         if is_signed && N.(equal (succ zero) (extract_num (of_int (int_of_char first)) 7 1)) then
           N.of_int (-1)
         else
           N.zero in
       let rec aux acc = function
         | [] ->
            acc
         | c::cs' ->
            aux N.(bitwise_xor (of_int (int_of_char c)) (shift_left acc 8)) cs' in
       aux init cs

  (* TODO: maybe move somewhere else *)
  let find_overlaping st addr : [ `NoAlloc
                                | `SingleAlloc of storage_instance_id
                                | `DoubleAlloc of storage_instance_id * storage_instance_id ] =
    let (require_exposed, allow_one_past) =
      match Switches.(has_switch_pred (function SW_PNVI _ -> true | _ -> false)) with
      | Some (Switches.SW_PNVI variant) ->
         begin match variant with
         | `PLAIN ->
            (false, false)
         | `AE ->
            (true, false)
         | `AE_UDI ->
            (true, true)
         end
      | Some _ ->
         assert false
      | None ->
         (false, false) in
    IntMap.fold (fun alloc_id alloc acc ->
        let new_opt =
          if    not (List.mem alloc_id st.dead_allocations)
                && N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size) then
            (* PNVI-ae, PNVI-ae-udi *)
            if require_exposed && alloc.taint <> `Exposed then
              None
            else
              Some alloc_id
          else if allow_one_past then
            (* PNVI-ae-udi *)
            if    N.equal addr (N.add alloc.base alloc.size)
                  && not (require_exposed && alloc.taint <> `Exposed) then
              Some alloc_id
            else
              None
          else
            None in
        match acc, new_opt with
        | _, None ->
           acc
        | `NoAlloc, Some alloc_id ->
           `SingleAlloc alloc_id
        | `SingleAlloc alloc_id1, Some alloc_id2 ->
           `DoubleAlloc (alloc_id1, alloc_id2)
        | `DoubleAlloc _, Some _ ->
           (* TODO: I guess there is an invariant that the new_alloc
              is either of the `DoubleAlloc *)
           acc
      (*
        if    not (List.mem alloc_id st.dead_allocations)
        && N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size) then
        (* PNVI-ae, PNVI-ae-udi *)
        if require_exposed && alloc.taint <> `Exposed then
        `NoAlloc
        else
        `SingleAlloc alloc_id
        else if allow_one_past then
        (* PNVI-ae-udi *)
        if N.equal addr (N.add alloc.base alloc.size) then
        match
        IntMap.fold (fun alloc_id' alloc' acc' ->
        match acc' with
        | Some _ ->
        acc'
        | None ->
        if addr = alloc'.base then
        Some alloc_id'
        else
        None
        ) st.allocations None
        with
        | None ->
        `SingleAlloc alloc_id
        | Some alloc_id' ->
        `DoubleAlloc (alloc_id, alloc_id')
        else
        `NoAlloc
        else
        `NoAlloc
       *)
      ) st.allocations `NoAlloc

  (* PNVI-ae *)
  let expose_allocation alloc_id =
    update begin fun st ->
      {st with allocations=
                 IntMap.update alloc_id (function
                     | Some alloc ->
                        Some {alloc with taint= `Exposed}
                     | None ->
                        None) st.allocations }
      end
  (* PNVI-ae *)
  let expose_allocations = function
    | `NoTaint ->
       return ()
    | `NewTaint xs ->
       update begin fun st ->
         {st with allocations=
                    List.fold_left (fun acc alloc_id ->
                        IntMap.update alloc_id (function
                            | Some alloc ->
                               Some {alloc with taint= `Exposed}
                            | None ->
                               None) acc
                      ) st.allocations xs }
         end

  (* PNVI-ae-udi *)
  let add_iota alloc_ids =
    get >>= fun st ->
    let iota = st.next_iota in
    put {st with next_iota= N.succ st.next_iota;
                 iota_map= IntMap.add iota (`Double alloc_ids) st.iota_map } >>= fun () ->
    return iota

  (* PNVI-ae-udi *)
  let lookup_iota iota =
    get >>= fun st ->
    return (IntMap.find iota st.iota_map)

  (* PNVI-ae-udi *)
  let resolve_iota precond iota =
    lookup_iota iota >>= begin function
                           | `Single alloc_id ->
                              begin precond alloc_id >>= function
                                    | `OK ->
                                       return alloc_id
                                    | `FAIL err ->
                                       fail err
                              end
                           | `Double (alloc_id1, alloc_id2) ->
                              begin precond alloc_id1 >>= function
                                    | `OK ->
                                       return alloc_id1
                                    | `FAIL _ ->
                                       begin precond alloc_id2 >>= function
                                             | `OK ->
                                                return alloc_id2
                                             | `FAIL err ->
                                                fail err
                                       end
                              end
                         end >>= fun alloc_id ->
    update begin fun st ->
      {st with iota_map= IntMap.add iota (`Single alloc_id) st.iota_map }
      end >>= fun () ->
    return alloc_id


  (* INTERNAL abst: ctype -> AbsByte.t list -> [`NoTaint | `NewTaint of storage_instance_id list] * mem_value * AbsByte.t list *)
  (* ASSUMES: has_size ty /\ |bs| >= sizeof ty*)
  (* property that should hold:
     forall ty bs bs' mval.
     has_size ty -> |bs| >= sizeof ty -> abst ty bs = (mval, bs') ->
     |bs'| + sizeof ty  = |bs| /\ typeof mval = ty *)
  let rec abst
            find_overlaping
            funptrmap
            (tag_query_f: C.vaddr -> bool option)
            (addr:C.vaddr)
            (Ctype (_, ty) as cty)
            (bs : AbsByte.t list)
          :
            [`NoTaint | `NewTaint of storage_instance_id list] * mem_value_with_err * AbsByte.t list
    =
    let self = abst find_overlaping funptrmap tag_query_f in
    let extract_unspec xs =
      List.fold_left (fun acc_opt c_opt ->
          match acc_opt, c_opt with
          | None, _ ->
             None
          | _, None ->
             None
          | (Some acc, Some c) ->
             Some (c :: acc)
        ) (Some []) (List.rev xs) in

    if List.length bs < sizeof cty then
      failwith "abst, |bs| < sizeof(ty)";

    let merge_taint x y =
      match x, y with
      | `NoTaint, `NoTaint ->
         `NoTaint
      | `NoTaint, `NewTaint xs
        | `NewTaint xs, `NoTaint ->
         `NewTaint xs
      | `NewTaint xs, `NewTaint ys ->
         `NewTaint (xs @ ys) in

    match ty with
    | Void
      | Array (_, None)
      | Function _
      | FunctionNoParams _ ->
       (* ty must have a known size *)
       assert false
    (* intptr_t in CHERI handled differently from other integers. *)
    | Basic (Integer ((Signed Intptr_t) as ity))
      | Basic (Integer ((Unsigned Intptr_t) as ity)) ->
       let (bs1, bs2) = L.split_at (sizeof cty) bs in
       let (prov, _, bs1') = AbsByte.split_bytes bs1 in
       (* PNVI-ae-udi *)
       ( AbsByte.provs_of_bytes bs1
       , begin match extract_unspec bs1' with
         | Some cs ->
            begin match tag_query_f addr with
            | None ->
               (* TODO(CHERI): decide on semantics *)
               failwith "unspecified tag value"
            | Some tag ->
               begin match C.decode cs tag with
               | None ->
                  (* could not decode capability *)
                  MVErr (MerrCHERI CheriErrDecodingCap)
               | Some n ->
                  MVEinteger (ity, IC (prov,n))
               end
            end
         | None ->
            MVEunspecified cty
         end , bs2)
    | Basic (Integer ity) ->
       let (bs1, bs2) = L.split_at (sizeof cty) bs in
       let (prov, _, bs1') = AbsByte.split_bytes bs1 in
       (* PNVI-ae-udi *)
       ( AbsByte.provs_of_bytes bs1
       , begin match extract_unspec bs1' with
         | Some cs ->
            MVEinteger ( ity
                      , mk_ival prov (int_of_bytes (AilTypesAux.is_signed_ity ity) cs))
         | None ->
            MVEunspecified cty
         end , bs2)
    | Basic (Floating fty) ->
       let (bs1, bs2) = L.split_at (sizeof cty) bs in
       (* we don't care about provenances for floats *)
       let (_, _, bs1') = AbsByte.split_bytes bs1 in
       ( `NoTaint
       , begin match extract_unspec bs1' with
         | Some cs ->
            MVEfloating ( fty
                       , Int64.float_of_bits (N.to_int64 (int_of_bytes true cs)) )
         | None ->
            MVEunspecified cty
         end, bs2)
    | Array (elem_ty, Some n) ->
       let rec aux n (taint_acc, mval_acc) cs =
         if n <= 0 then
           (taint_acc, MVEarray (List.rev mval_acc), cs)
         else
           let el_addr = N.add addr (N.of_int ((n-1)*(sizeof elem_ty))) in
           let (taint, mval, cs') = self el_addr elem_ty cs in
           aux (n-1) (merge_taint taint taint_acc, mval :: mval_acc) cs'
       in
       aux (Nat_big_num.to_int n) (`NoTaint, []) bs
    | Pointer (_, ref_ty) ->
       let (bs1, bs2) = L.split_at (sizeof cty) bs in
       Debug_ocaml.print_debug 1 [] (fun () -> "TODO: Concrete, assuming pointer repr is unsigned??");
       let (prov, prov_status, bs1') = AbsByte.split_bytes bs1 in
       ( `NoTaint (* PNVI-ae-udi *)
       , begin match extract_unspec bs1' with
         | Some cs ->
            begin match tag_query_f addr with
            | None ->
               (* TODO(CHERI): decide on semantics *)
               failwith "could not decode capability"
            | Some tag ->
               begin match C.decode cs tag with
               | None ->
                  (* could not decode capability *)
                  MVErr (MerrCHERI CheriErrDecodingCap)
               | Some n ->
                  begin match ref_ty with
                  | Ctype (_, Function _) ->
                     if C.eq n C.cap_c0 then
                       MVEpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                     else
                       (*
                         (* FIXME: This is wrong. A function pointer with the same id in different files might exist. *)
                         begin match IntMap.find_opt n funptrmap with
                         | Some (file_dig, name) ->
                         MVpointer (ref_ty, PV(prov, PVfunction (Symbol.Symbol (file_dig, N.to_int n, SD_Id name))))
                         | None ->
                         failwith ("unknown function pointer: " ^ C.to_string n)
                         end
                        *)
                       (* TODO: implement for CHERI. May need different approach *)
                       failwith "TODO(CHERI): implement"
                  | _ ->
                     if C.eq n C.cap_c0 then
                       MVEpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                     else
                       let prov =
                         if is_PNVI () then
                           (*
                             let () =
                             print_endline "HELLO ==> PNVI abst (ptr)";
                             print_endline "BEGIN";
                             List.iter (fun bt ->
                             let open AbsByte in
                             Printf.printf "%s: [%s] - %s\n"
                             (string_of_provenance bt.prov)
                             (match bt.copy_offset with Some n -> string_of_int n | None -> "_")
                             (match bt.value with Some c ->  Char.escaped c | None -> "unspec")
                             ) bs1;
                             print_endline "END" in
                            *)
                           match prov_status with
                           | `NotValidPtrProv ->
                              (* KKK print_endline "NotValidPtrProv"; *)
                              begin match find_overlaping (C.cap_get_value n) with
                              | `NoAlloc ->
                                 Prov_none
                              | `SingleAlloc alloc_id ->
                                 Prov_some alloc_id
                              | `DoubleAlloc (alloc_id1, alloc_id2) ->
                                 (* FIXME/HACK(VICTOR): This is wrong, but when serialising the memory in the UI, I get this failwith. *)
                                 Prov_some alloc_id1
                                           (* failwith "TODO(iota): abst => make a iota?" *)
                              end
                           | `ValidPtrProv ->
                              (* KKK print_endline ("ValidPtrProv ==> " ^ string_of_provenance prov); *)
                              prov
                         else
                           prov in
                       MVEpointer (ref_ty, PV (prov, PVconcrete n))
                  end
               end
            end
         | None ->
            MVEunspecified (Ctype ([], Pointer (no_qualifiers, ref_ty)))
         end, bs2)
    | Atomic atom_ty ->
       Debug_ocaml.print_debug 1 [] (fun () -> "TODO: Concrete, is it ok to have the repr of atomic types be the same as their non-atomic version??");
       self addr atom_ty bs
    | Struct tag_sym ->
       let (bs1, bs2) = L.split_at (sizeof cty) bs in
       let (taint, rev_xs, _, bs') = List.fold_left (fun (taint_acc, acc_xs, previous_offset, acc_bs) (memb_ident, memb_ty, memb_offset) ->
                                         let pad = memb_offset - previous_offset in
                                         let memb_addr = N.add addr (N.of_int memb_offset) in
                                         let (taint, mval, acc_bs') = self memb_addr memb_ty (L.drop pad acc_bs) in
                                         (merge_taint taint taint_acc, (memb_ident, memb_ty, mval)::acc_xs, memb_offset + sizeof memb_ty, acc_bs')
                                       ) (`NoTaint, [], 0, bs1) (fst (offsetsof (Tags.tagDefs ()) tag_sym)) in
       (* TODO: check that bs' = last padding of the struct *)
       (taint, MVEstruct (tag_sym, List.rev rev_xs), bs2)
    | Union tag_sym ->
       failwith "TODO: abst, Union (as value)"

  (* INTERNAL bytes_of_int *)
  let bytes_of_int is_signed size i : (char option) list =
    let nbits = 8 * size in
    let (min, max) =
      if is_signed then
        ( N.negate (N.pow_int (N.of_int 2) (nbits-1))
        , N.sub (N.pow_int (N.of_int 2) (nbits-1)) N.(succ zero) )
      else
        ( N.zero
        , N.sub (N.pow_int (N.of_int 2) nbits) N.(succ zero) ) in
    if not (min <= i && i <= max) || nbits > 128 then begin
        Printf.printf "failed: bytes_of_int(%s), i= %s, nbits= %d, [%s ... %s]\n"
          (if is_signed then "signed" else "unsigned")
          (N.to_string i) nbits (N.to_string min) (N.to_string max);
        assert false
      end else
      List.init size (fun n ->
          Some (char_of_int (N.to_int (N.extract_num i (8*n) 8)))
        )

  let rec typeof mval =
    Ctype ([], match mval with
               | MVunspecified (Ctype (_, ty)) ->
                  ty
               | MVinteger (ity, _) ->
                  Basic (Integer ity)
               | MVfloating (fty, _) ->
                  Basic (Floating fty)
               | MVpointer (ref_ty, _) ->
                  Pointer (no_qualifiers, ref_ty)
               | MVarray [] ->
                  (* ill-formed value *)
                  assert false
               | MVarray ((mval::_) as mvals) ->
                  (* TODO: checking all the elements would be stupidly slow, but this
                     feels wrong *)
                  Array (typeof mval, Some (N.of_int (List.length mvals)))
               | MVstruct (tag_sym, _) ->
                  Struct tag_sym
               | MVunion (tag_sym, _, _) ->
                  Union tag_sym
      )

  (* INTERNAL repr *)
  let rec repr funptrmap mval : ((Digest.t * string) IntMap.t * AbsByte.t list) =
    let ret bs = (funptrmap, bs) in
    match mval with
    | MVunspecified ty ->
       ret @@ List.init (sizeof ty) (fun _ -> AbsByte.v Prov_none None)
    | MVinteger (ity, IV (prov, n)) ->
       ret @@List.map (AbsByte.v prov) begin
                 bytes_of_int
                   (AilTypesAux.is_signed_ity ity)
                   (sizeof (Ctype ([], Basic (Integer ity)))) n
               end
    | MVinteger (ity, IC (prov, c)) ->
       (* TODO(CHERI): see if we need special handling for NULL *)
       (* TODO(CHERI): see if we need to check here validity tag *)
       ret @@ List.mapi (fun i b -> AbsByte.v prov ~copy_offset:(Some i) (Some b)) @@ C.encode c
    | MVfloating (fty, fval) ->
       ret @@ List.map (AbsByte.v Prov_none) begin
                  bytes_of_int
                    true (* TODO: check that *)
                    (sizeof (Ctype ([], Basic (Floating fty)))) (N.of_int64 (Int64.bits_of_float fval))
                end
    | MVpointer (_, PV (prov, ptrval_)) ->
       Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the sizeof pointers to 8 bytes");
       let ptr_size = match (Ocaml_implementation.get ()).sizeof_pointer with
         | None ->
            failwith "the concrete memory model requires a complete implementation"
         | Some z ->
            z in
       begin match ptrval_ with
       | PVnull _ ->
          Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the representation of all NULL pointers to be C0");
          ret @@ List.map (fun b -> AbsByte.v Prov_none (Some b)) @@ C.encode C.cap_c0
       | PVfunction (Symbol.Symbol (file_dig, n, opt_name)) ->
          (* TODO(CHERI): *)
          (begin match opt_name with
           | SD_Id name -> IntMap.add (N.of_int n) (file_dig, name) funptrmap
           | SD_ObjectAddress _ -> funptrmap
           | SD_Return -> funptrmap
           | SD_FunArg _ -> funptrmap
           (* | SD_Pointee _ -> funptrmap *)
           (* | SD_PredOutput _ -> funptrmap *)
           | SD_None -> funptrmap
                          (* TODO(CHERI): this is wrong. Need to be fixed to return encoded capability, not encoded address *)
           end, List.map (AbsByte.v prov) begin
                    bytes_of_int
                      false
                      ptr_size (N.of_int n)
                  end)
       | PVconcrete addr ->
          ret @@ List.mapi (fun i b -> AbsByte.v prov ~copy_offset:(Some i) (Some b)) @@ C.encode addr
       end
    | MVarray mvals ->
       let (funptrmap, bs_s) =
         List.fold_left begin fun (funptrmap, bs) mval ->
           let (funptrmap, bs') = repr funptrmap mval in
           (funptrmap, bs' :: bs)
           end (funptrmap, []) mvals in
       (* TODO: use a fold? *)
       (funptrmap, L.concat @@ List.rev bs_s)
    | MVstruct (tag_sym, xs) ->
       let padding_byte _ = AbsByte.v Prov_none None in
       let (offs, last_off) = offsetsof (Tags.tagDefs ()) tag_sym in
       let final_pad = sizeof (Ctype ([], Struct tag_sym)) - last_off in
       (* TODO: rewrite now that offsetsof returns the paddings *)
       let (funptrmap, _, bs) = List.fold_left2 begin fun (funptrmap, last_off, acc) (ident, ty, off) (_, _, mval) ->
                                  let pad = off - last_off in
                                  let (funptrmap, bs) = repr funptrmap mval in
                                  (funptrmap, off + sizeof ty, acc @ List.init pad padding_byte @ bs)
                                  end (funptrmap, 0, []) offs xs
       in
       (funptrmap, bs @ List.init final_pad padding_byte)
    | MVunion (tag_sym, memb_ident, mval) ->
       let size = sizeof (Ctype ([], Union tag_sym)) in
       let (funptrmap', bs) = repr funptrmap mval in
       (funptrmap', bs @ List.init (size - List.length bs) (fun _ -> AbsByte.v Prov_none None))


  (* BEGIN DEBUG *)
  (*
  let dot_of_mem_state st =
    let get_value alloc =
      let bs = fetch_bytes st.bytemap alloc.base (N.to_int alloc.size) in
      match alloc.ty with
      | Some ty ->
         let (_, mval, _) = abst (find_overlaping st) st.funptrmap ty bs in
         mval
      | None ->
         failwith "CHERI.dot_of_mem_state: alloc.ty = None"
    in
    let xs = IntMap.fold (fun alloc_id alloc acc ->
                 Printf.sprintf "alloc%s [shape=\"record\", label=\"{ addr: %s | sz: %s | %s }\"];"
                   (N.to_string alloc_id)
                   (N.to_string alloc.base)
                   (N.to_string alloc.size)
                   (Pp_utils.to_plain_string (pp_mem_value (get_value alloc))) :: acc
               ) st.allocations [] in
    prerr_endline "digraph G{";
    List.iter prerr_endline xs;
    prerr_endline "}"
   *)
  (* END DEBUG *)


  (* TODO: this module should be made parametric in this function (i.e. the allocator should be impl-def) *)
  let allocator (size: N.num) (align: N.num) : (storage_instance_id * C.vaddr) memM =
    get >>= fun st ->
    let alloc_id = st.next_alloc_id in
    begin
      let open N in
      let z = sub st.last_address size in
      let (q,m) = quomod z align in
      let z' = sub z (if less q zero then negate m else m) in
      if less_equal z' zero then
        fail (MerrOther "CHERI.allocator: failed (out of memory)")
      else
        return z'
    end >>= fun addr ->
    put { st with
        next_alloc_id= Nat_big_num.succ alloc_id;
        last_used= Some alloc_id;
        last_address= addr
      } >>= fun () ->
    return (alloc_id, addr)


  let allocate_object tid pref int_val ty init_opt : pointer_value memM =
    let align = num_of_int int_val in
    (*    print_bytemap "ENTERING ALLOC_STATIC" >>= fun () -> *)
    let sz = sizeof ty in
    let size = N.of_int sz in
    allocator size align >>= fun (alloc_id, addr) ->
    Debug_ocaml.print_debug 10(*KKK*) [] (fun () ->
        "STATIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^
          " --> alloc_id= " ^ N.to_string alloc_id ^
            ", size= " ^ N.to_string size ^
              ", addr= " ^ N.to_string addr
      );
    begin match init_opt with
    | None ->
       let alloc = {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= false; taint= `Unexposed} in
       update (fun st ->
           { st with allocations= IntMap.add alloc_id alloc st.allocations; }
         )
    | Some mval ->
       let alloc = {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= true; taint= `Unexposed} in
       (* TODO: factorise this with do_store inside CHERI.store *)
       update (fun st ->
           let (funptrmap, pre_bs) = repr st.funptrmap mval in
           assert (List.length pre_bs == sz) ;
           let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
           { st with
             allocations= IntMap.add alloc_id alloc st.allocations;
             bytemap=
               List.fold_left (fun acc (addr, b) ->
                   IntMap.add addr b acc
                 ) st.bytemap bs;
             funptrmap= funptrmap; }
         )
    end >>= fun () ->
    (* memory allocation on stack *)
    return (PV (Prov_some alloc_id, PVconcrete (C.alloc_cap addr size)))

  let update_prefix (pref, mval) =
    match mval with
    | MVpointer (_, PV (Prov_some alloc_id, _)) ->
       let upd_alloc = function
         | Some alloc ->
            Some { alloc with prefix = pref }
         | None ->
            Debug_ocaml.warn [] (fun () -> "update_prefix: allocation does not exist");
            None
       in
       update (fun st -> { st with allocations= IntMap.update alloc_id upd_alloc st.allocations })
    | _ ->
       Debug_ocaml.warn [] (fun () -> "update_prefix: wrong arguments");
       return ()

  let prefix_of_pointer (PV (prov, pv)) : string option memM =
    let open String_symbol in
    let rec aux addr alloc = function
      | None
        | Some (Ctype (_, Void))
        | Some (Ctype (_, Function _))
        | Some (Ctype (_, FunctionNoParams _)) ->
         None
      | Some (Ctype (_, Basic _))
        | Some (Ctype (_, Union _))
        | Some (Ctype (_, Pointer _)) ->
         let offset = N.sub addr alloc.base in
         Some (string_of_prefix alloc.prefix ^ " + " ^ N.to_string offset)
      | Some (Ctype (_, Struct tag_sym)) -> (* TODO: nested structs *)
         let offset = N.to_int @@ N.sub addr alloc.base in
         let (offs, _) = offsetsof (Tags.tagDefs ()) tag_sym in
         let rec find = function
           | [] ->
              None
           | (Symbol.Identifier (_, memb), _, off) :: offs ->
              if offset = off then
                Some (string_of_prefix alloc.prefix ^ "." ^ memb)
              else
                find offs
         in find offs
      | Some (Ctype (_, Array (ty, _))) ->
         let offset = N.sub addr alloc.base in
         if N.less offset alloc.size then
           let n = (N.to_int offset) / sizeof ty in
           Some (string_of_prefix alloc.prefix ^ "[" ^ string_of_int n ^ "]")
         else
           None
      | Some (Ctype (_, Atomic ty)) ->
         aux addr alloc @@ Some ty
    in
    match prov with
    | Prov_some alloc_id ->
       get_allocation alloc_id >>= fun alloc ->
       begin match pv with
       | PVconcrete addr ->
          if C.cap_get_value addr = alloc.base then
            return @@ Some (string_of_prefix alloc.prefix)
          else
            return @@ aux C.(cap_get_value addr) alloc alloc.ty
       | PVnull ty ->
          if Some ty = alloc.ty then
            return @@ Some (string_of_prefix alloc.prefix)
          else
            return None
       | _ ->
          return None
       end
    | _ ->
       return None

  (** Checks if memory region starting from [addr] and
      of size [sz] fits withing inclusuvive interval [b1,b2] *)
  let cap_bounds_check (b1,b2) addr sz =
    N.less_equal b1 addr
    && N.less_equal addr b2
    && N.less_equal (N.add addr sz) (N.succ b2)

  let allocate_region tid pref align_int size_int =
    let align_n = num_of_int align_int in
    let size_n = num_of_int size_int in
    allocator size_n align_n >>= fun (alloc_id, addr) ->
    Debug_ocaml.print_debug 1 [] (fun () ->
        "DYNAMIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^ (* pref will always be Core *)
          " --> alloc_id= " ^ N.to_string alloc_id ^
            ", size= " ^ N.to_string size_n ^
              ", addr= " ^ N.to_string addr
      );
    (* TODO: why aren't we using the argument pref? *)
    let alloc = {prefix= Symbol.PrefMalloc; base= addr; size= size_n; ty= None; is_readonly= false; taint= `Unexposed} in
    update (fun st ->
        { st with
          allocations= IntMap.add alloc_id alloc st.allocations;
          dynamic_addrs= addr :: st.dynamic_addrs }
      ) >>= fun () ->
    (* malloc *)
    return (PV (Prov_some alloc_id, PVconcrete (C.alloc_cap addr size_n)))

  (* zap (make unspecified) any pointer in the memory with provenance matching a
     given allocation id *)
  let zap_pointers alloc_id = failwith "zap_pointers is not supported"

  let kill loc is_dyn : pointer_value -> unit memM = function
    | PV (_, PVnull _) ->
       if Switches.(has_switch SW_forbid_nullptr_free) then
         fail (MerrFreeNullPtr loc)
       else
         return ()
    | PV (_, PVfunction _) ->
       fail (MerrOther "attempted to kill with a function pointer")
    | PV (Prov_none, PVconcrete _) ->
       fail (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV (Prov_device, PVconcrete _) ->
       (* TODO: should that be an error ?? *)
       return ()

    (* PNVI-ae-udi *)
    | PV (Prov_symbolic iota, PVconcrete addr) ->
       let precondition z =
         is_dead z >>= function
         | true ->
            return (`FAIL (MerrUndefinedFree (loc, Free_static_allocation)))
         | false ->
            get_allocation z >>= fun alloc ->
            if N.equal (C.cap_get_value addr) alloc.base then
              return `OK
            else
              return (`FAIL (MerrUndefinedFree (loc, Free_out_of_bound))) in
       begin if is_dyn then
               (* this kill is dynamic one (i.e. free() or friends) *)
               is_dynamic (C.cap_get_value addr) >>= begin function
                                     | false ->
                                        fail (MerrUndefinedFree (loc, Free_static_allocation))
                                     | true ->
                                        return ()
                                   end
             else
               return ()
       end >>= fun () ->
       resolve_iota precondition iota >>= fun alloc_id ->
       (* TODO: this is duplicated code from the Prov_some case (I'm keeping
          PNVI-ae-udi stuff separated to avoid polluting the
          vanilla PNVI code) *)
       update begin fun st ->
         {st with dead_allocations= alloc_id :: st.dead_allocations;
                  last_used= Some alloc_id;
                  allocations= IntMap.remove alloc_id st.allocations}
         end >>= fun () ->
       if Switches.(has_switch SW_zap_dead_pointers) then
         zap_pointers alloc_id
       else
         return ()

    | PV (Prov_some alloc_id, PVconcrete addr) ->
       begin if is_dyn then
               (* this kill is dynamic one (i.e. free() or friends) *)
               is_dynamic (C.cap_get_value addr) >>= begin function
                                     | false ->
                                        fail (MerrUndefinedFree (loc, Free_static_allocation))
                                     | true ->
                                        return ()
                                   end
             else
               return ()
       end >>= fun () ->
       is_dead alloc_id >>= begin function
                              | true ->
                                 if is_dyn then
                                   fail (MerrUndefinedFree (loc, Free_dead_allocation))
                                 else
                                   failwith "Concrete: FREE was called on a dead allocation"
                              | false ->
                                 get_allocation alloc_id >>= fun alloc ->
                                 if N.equal (C.cap_get_value addr) alloc.base then begin
                                     Debug_ocaml.print_debug 1 [] (fun () ->
                                         "KILLING alloc_id= " ^ N.to_string alloc_id
                                       );
                                     update begin fun st ->
                                       {st with dead_allocations= alloc_id :: st.dead_allocations;
                                                last_used= Some alloc_id;
                                                allocations= IntMap.remove alloc_id st.allocations}
                                       end >>= fun () ->
                                     if Switches.(has_switch SW_zap_dead_pointers) then
                                       zap_pointers alloc_id
                                     else
                                       return ()
                                   end else
                                   fail (MerrUndefinedFree (loc, Free_out_of_bound))
                            end

  let load loc ty (PV (prov, ptrval_)) =
    Debug_ocaml.print_debug 10(*KKK*) [] (fun () ->
        "ENTERING LOAD: " ^ Location_ocaml.location_to_string loc
      );
    let do_load alloc_id_opt addr sz =
      get >>= fun st ->
      let bs = fetch_bytes st.bytemap addr sz in
      let tag_query a =
        match (Ocaml_implementation.get ()).alignof_pointer with
        | None -> failwith "alignof_pointer must be specified in Ocaml_implementation"
        | Some v ->
           let (q,m) = N.quomod a (N.of_int v) in
           if m <> N.zero then failwith "Unaligned address in load"
           else IntMap.find_opt q st.captags
      in
      let (taint, mval, bs') = abst (find_overlaping st) st.funptrmap tag_query addr ty bs in
      mem_value_strip_err mval >>= fun mval ->
      (* PNVI-ae-udi *)
      begin if Switches.(has_switch (SW_PNVI `AE) || has_switch (SW_PNVI `AE_UDI)) then
              expose_allocations taint
            else
              return ()
      end >>= fun () ->
      update (fun st -> { st with last_used= alloc_id_opt }) >>= fun () ->
      let fp = FP (addr, (N.of_int (sizeof ty))) in
      begin match bs' with
      | [] ->
         (* controls reads from uninitialized memory *)
         if Switches.(has_switch SW_strict_reads) then
           match mval with
           | MVunspecified _ ->
              fail (MerrReadUninit loc)
           | _ ->
              return (fp, mval)
         else
           return (fp, mval)
      | _ ->
         fail (MerrWIP "load, bs' <> []")
      end in
    let do_load_cap alloc_id_opt c sz =
      if C.cap_is_valid c then
        let addr = C.cap_get_value c in
        if C.P.perm_is_load (C.get_perms c) then
          let bounds = C.cap_get_bounds c in
          let nsz = N.of_int sz in
          if cap_bounds_check bounds addr nsz then
            do_load alloc_id_opt addr sz
          else
            fail (MerrCHERI
                    (CheriBoundsErr (bounds, addr, nsz)))
        else
          fail (MerrCHERI CheriMerrUnsufficientPermissions)
      else
        fail (MerrCHERI CheriMerrInvalidCap)
    in
    match (prov, ptrval_) with
    | (_, PVnull _) ->
       fail (MerrAccess (loc, LoadAccess, NullPtr))
    | (_, PVfunction _) ->
       fail (MerrAccess (loc, LoadAccess, FunctionPtr))
    | (Prov_none, _) ->
       fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
    | (Prov_device, PVconcrete c) ->
       begin is_within_device ty (C.cap_get_value c) >>= function
             | false ->
                fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
             | true ->
                do_load_cap None c (sizeof ty)
       end

    (* PNVI-ae-udi *)
    | (Prov_symbolic iota, PVconcrete addr) ->
       (* TODO: this is duplicated code from the Prov_some case (I'm keeping
          PNVI-ae-udi stuff separated to avoid polluting the
          vanilla PNVI code) *)
       let precondition z =
         is_dead z >>= begin function
                         | true ->
                            return (`FAIL (MerrAccess (loc, LoadAccess, DeadPtr)))
                         | false ->
                            begin is_within_bound z ty (C.cap_get_value addr) >>= function
                                  | false ->
                                     return (`FAIL (MerrAccess (loc, LoadAccess, OutOfBoundPtr)))
                                  | true ->
                                     begin is_atomic_member_access z ty (C.cap_get_value addr) >>= function
                                           | true ->
                                              return (`FAIL (MerrAccess (loc, LoadAccess, AtomicMemberof)))
                                           | false ->
                                              return `OK
                                     end
                            end
                       end in
       resolve_iota precondition iota >>= fun alloc_id ->
       do_load_cap (Some alloc_id) addr (sizeof ty)

    | (Prov_some alloc_id, PVconcrete addr) ->
       is_dead alloc_id >>= begin function
                              | true ->
                                 fail (MerrAccess (loc, LoadAccess, DeadPtr))
                              | false ->
                                 return ()
                            end >>= fun () ->
       begin is_within_bound alloc_id ty (C.cap_get_value addr) >>= function
             | false ->
                Debug_ocaml.print_debug 1 [] (fun () ->
                    "LOAD out of bound, alloc_id=" ^ N.to_string alloc_id
                  );
                fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
             | true ->
                begin is_atomic_member_access alloc_id ty (C.cap_get_value addr) >>= function
                      | true ->
                         fail (MerrAccess (loc, LoadAccess, AtomicMemberof))
                      | false ->
                         do_load_cap (Some alloc_id) addr (sizeof ty)
                end
       end


  let store loc ty is_locking (PV (prov, ptrval_)) mval =
    Debug_ocaml.print_debug 10(*KKK*) [] (fun () ->
        "ENTERING STORE: ty=" ^ String_core_ctype.string_of_ctype ty ^
          " -> @" ^ Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
            ", mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
      );
    if not (ctype_equal (unatomic ty) (unatomic (typeof mval))) then begin
        Printf.printf "STORE ty          ==> %s\n"
          (String_core_ctype.string_of_ctype ty);
        Printf.printf "STORE typeof mval ==> %s\n"
          (String_core_ctype.string_of_ctype (typeof mval));
        Printf.printf "STORE ==> %s\n" (Location_ocaml.location_to_string loc);
        Printf.printf "STORE mval ==> %s\n"
          (Pp_utils.to_plain_string (pp_mem_value mval));
        fail (MerrOther "store with an ill-typed memory value")
      end else
      let do_store_cap alloc_id_opt c =
        if C.cap_is_valid c then
          let addr = C.cap_get_value c in
          let sz = sizeof ty in
          if C.P.perm_is_store (C.get_perms c) then
            let bounds = C.cap_get_bounds c in
            let nsz = N.of_int sz in
            if cap_bounds_check bounds addr nsz then
              begin
               update begin fun st ->
                 let (funptrmap, pre_bs) = repr st.funptrmap mval in
                 assert (List.length pre_bs == sz) ;
                 let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
                 { st with last_used= alloc_id_opt;
                           bytemap=
                             List.fold_left (fun acc (addr, b) ->
                                 IntMap.add addr b acc
                               ) st.bytemap bs;
                           funptrmap= funptrmap; }
                 end >>= fun () ->
               print_bytemap ("AFTER STORE => " ^ Location_ocaml.location_to_string loc) >>= fun () ->
               return (FP (addr, nsz))
               end
            else
              fail (MerrCHERI
                      (CheriBoundsErr (bounds, addr, N.of_int sz)))
          else
            fail (MerrCHERI CheriMerrUnsufficientPermissions)
        else
          fail (MerrCHERI CheriMerrInvalidCap)
      in
      match (prov, ptrval_) with
      | (_, PVnull _) ->
         fail (MerrAccess (loc, StoreAccess, NullPtr))
      | (_, PVfunction _) ->
         fail (MerrAccess (loc, StoreAccess, FunctionPtr))
      | (Prov_none, _) ->
         fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
      | (Prov_device, PVconcrete addr) ->
         begin is_within_device ty (C.cap_get_value addr) >>= function
               | false ->
                  fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
               | true ->
                  do_store_cap None addr
         end

      (* PNVI-ae-udi *)
      | (Prov_symbolic iota, PVconcrete addr) ->
         (* TODO: this is duplicated code from the Prov_some case (I'm keeping
            PNVI-ae-udi stuff separated to avoid polluting the
            vanilla PNVI code) *)
         let precondition z =
           is_within_bound z ty (C.cap_get_value addr) >>= function
           | false ->
              return (`FAIL (MerrAccess (loc, StoreAccess, OutOfBoundPtr)))
           | true ->
              get_allocation z >>= fun alloc ->
              if alloc.is_readonly then
                return (`FAIL (MerrWriteOnReadOnly loc))
              else
                begin is_atomic_member_access z ty (C.cap_get_value addr) >>= function
                      | true ->
                         return (`FAIL (MerrAccess (loc, LoadAccess, AtomicMemberof)))
                      | false ->
                         return `OK
                end in
         resolve_iota precondition iota >>= fun alloc_id ->
         do_store_cap (Some alloc_id) addr >>= fun fp ->
         begin if is_locking then
                 Eff.update (fun st ->
                     { st with allocations=
                                 IntMap.update alloc_id (function
                                     | Some alloc -> Some { alloc with is_readonly= true }
                                     | None       -> None
                                   ) st.allocations }
                   )
               else
                 return ()
         end >>= fun () ->
         return fp

      | (Prov_some alloc_id, PVconcrete addr) ->
         begin is_within_bound alloc_id ty (C.cap_get_value addr) >>= function
               | false ->
                  fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
               | true ->
                  get_allocation alloc_id >>= fun alloc ->
                  if alloc.is_readonly then
                    fail (MerrWriteOnReadOnly loc)
                  else
                    begin is_atomic_member_access alloc_id ty (C.cap_get_value addr) >>= function
                          | true ->
                             fail (MerrAccess (loc, LoadAccess, AtomicMemberof))
                          | false ->
                             do_store_cap (Some alloc_id) addr >>= fun fp ->
                             if is_locking then
                               Eff.update (fun st ->
                                   { st with allocations=
                                               IntMap.update alloc_id (function
                                                   | Some alloc -> Some { alloc with is_readonly= true }
                                                   | None       -> None
                                                 ) st.allocations }
                                 ) >>= fun () ->
                               return fp
                             else
                               return fp
                    end
         end

  (*
    (* TODO: DEBUG: *)
    >>= fun ret ->
    get >>= fun st ->
    dot_of_mem_state st;
    return ret
   *)

  let null_ptrval ty =
    PV (Prov_none, PVnull ty)

  let fun_ptrval sym =
    PV (Prov_none, PVfunction sym)

  let concrete_ptrval i addr = failwith "concrete_ptrval: integer to pointer cast is not supported"

  let case_ptrval pv fnull ffun fconc _ =
    match pv with
    | PV (_, PVnull ty) -> fnull ty
    | PV (_, PVfunction f) -> ffun f
    | PV (Prov_none, PVconcrete addr) -> fconc ()
    | PV (Prov_some i, PVconcrete addr) -> fconc ()
    | _ -> failwith "case_ptrval"

  let case_funsym_opt st (PV (_, ptrval)) =
    match ptrval with
    | PVfunction sym -> Some sym
    | PVconcrete addr ->
       (* FIXME: This is wrong. A function pointer with the same id in different files might exist. *)
       (*
       begin match IntMap.find_opt addr st.funptrmap with
       | Some (file_dig, name) ->
          Some (Symbol.Symbol (file_dig, N.to_int addr, SD_Id name))
       | None ->
          None
       end
        *)
       (* TODO(CHERI): implement for CHERI. May need different approach *)
       failwith "TODO"
    | _ -> None


  let eq_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVnull _, PVnull _) ->
       return true
    | (PVnull _, _)
      | (_, PVnull _) ->
       return false
    | (PVfunction sym1, PVfunction sym2) ->
       return (Symbol.instance_Basic_classes_Eq_Symbol_sym_dict.Lem_pervasives.isEqual_method sym1 sym2)
    | (PVfunction _, _)
      | (_, PVfunction _) ->
       return false
    | (PVconcrete addr1, PVconcrete addr2) ->
       if Switches.(has_switch SW_strict_pointer_equality) then
         return (C.value_compare addr1 addr2 == 0)
       else begin match (prov1, prov2) with
            | (Prov_none, Prov_none) ->
               return true
            | (Prov_some alloc_id1, Prov_some alloc_id2) ->
               return (N.equal alloc_id1 alloc_id2)
            | (Prov_device, Prov_device) ->
               return true
            | (Prov_symbolic iota1, Prov_symbolic iota2) ->
               (* PNVI-ae-udi *)
               lookup_iota iota1 >>= fun ids1 ->
               lookup_iota iota2 >>= fun ids2 ->
               begin match (ids1, ids2) with
               | (`Single alloc_id1, `Single alloc_id2) ->
                  return (N.equal alloc_id1 alloc_id2)
               | _ ->
                  return false
               end
            | _ ->
               return false
            end >>= begin function
                      | true ->
                         return (C.value_compare addr1 addr2 == 0)
                      | false ->
                         Eff.msum "pointer equality"
                           [ ("using provenance", return false)
                           ; ("ignoring provenance", return (C.value_compare addr1 addr2 == 0)) ]
                    end

  let ne_ptrval ptrval1 ptrval2 =
    eq_ptrval ptrval1 ptrval2 >>= fun b ->
    return (not b)

  let lt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
       if Switches.(has_switch SW_strict_pointer_relationals) then
         match prov1, prov2 with
         | Prov_some alloc1, Prov_some alloc2 when N.equal alloc1 alloc2 ->
            return (C.value_compare addr1 addr2 < 0)
         | _ ->
            (* TODO: one past case *)
            fail MerrPtrComparison
       else
         return (C.value_compare addr1 addr2 < 0)
    | (PVnull _, _)
      | (_, PVnull _) ->
       fail (MerrWIP "lt_ptrval ==> one null pointer")
    | _ ->
       fail (MerrWIP "lt_ptrval")

  let gt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
       if Switches.(has_switch SW_strict_pointer_relationals) then
         match prov1, prov2 with
         | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
            return (C.value_compare addr1 addr2 > 0)
         | _ ->
            (* TODO: one past case *)
            fail MerrPtrComparison
       else
         return (C.value_compare addr1 addr2 > 0)
    | _ ->
       fail (MerrWIP "gt_ptrval")

  let le_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
       if Switches.(has_switch SW_strict_pointer_relationals) then
         match prov1, prov2 with
         | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
            return (C.value_compare addr1 addr2 <= 0)
         | _ ->
            (* TODO: one past case *)
            fail MerrPtrComparison
       else
         return (C.value_compare addr1 addr2 <= 0)
    | _ ->
       fail (MerrWIP "le_ptrval")

  let ge_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
       if Switches.(has_switch SW_strict_pointer_relationals) then
         match prov1, prov2 with
         | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
            return (C.value_compare addr1 addr2 >= 0)
         | _ ->
            (* TODO: one past case *)
            fail MerrPtrComparison
       else
         return (C.value_compare addr1 addr2 >= 0)
    | _ ->
       fail (MerrWIP "ge_ptrval")


  let diff_ptrval diff_ty ptrval1 ptrval2 =
    let precond alloc addr1 addr2 =
      N.less_equal alloc.base addr1
      && N.less_equal addr1 (N.add alloc.base alloc.size)
      && N.less_equal alloc.base addr2
      && N.less_equal addr2 (N.add alloc.base alloc.size) in

    let valid_postcond addr1 addr2 =
      let diff_ty' = match diff_ty with
        | Ctype (_, Array (elem_ty, _)) ->
           elem_ty
        | _ ->
           diff_ty in
      return (IV (Prov_none, N.div (N.sub addr1 addr2) (N.of_int (sizeof diff_ty')))) in
    let error_postcond =
      fail MerrPtrdiff in
    if Switches.(has_switch (SW_pointer_arith `PERMISSIVE)) then
      match ptrval1, ptrval2 with
      | PV (_, PVconcrete addr1), PV (_, PVconcrete addr2) ->
         valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
      | _ ->
         error_postcond
    else match ptrval1, ptrval2 with
         | PV (Prov_some alloc_id1, (PVconcrete addr1)), PV (Prov_some alloc_id2, (PVconcrete addr2)) ->
            if N.equal alloc_id1 alloc_id2 then
              get_allocation alloc_id1 >>= fun alloc ->
              if precond alloc (C.cap_get_value addr1) (C.cap_get_value addr2) then
                valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
              else
                error_postcond
            else
              error_postcond

         (* PNVI-ae-udi *)
         | PV (Prov_symbolic iota, PVconcrete addr1), PV (Prov_some alloc_id', PVconcrete addr2)
           | PV (Prov_some alloc_id', PVconcrete addr1), PV (Prov_symbolic iota, PVconcrete addr2) ->
            (* if A(iota) = {i1, i2} then
               alloc_id' = (i1 or i2) AND precond valid AND iota collapses
               else
               UB *)
            lookup_iota iota >>= begin function
                                   | `Single alloc_id ->
                                      if N.equal alloc_id alloc_id' then
                                        get_allocation alloc_id >>= fun alloc ->
                                        if precond alloc (C.cap_get_value addr1) (C.cap_get_value addr2) then
                                          valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
                                        else
                                          error_postcond
                                      else
                                        error_postcond
                                   | `Double (alloc_id1, alloc_id2) ->
                                      if N.equal alloc_id1 alloc_id' || N.equal alloc_id2 alloc_id' then
                                        get_allocation alloc_id' >>= fun alloc ->
                                        if precond alloc (C.cap_get_value addr1) (C.cap_get_value addr2) then
                                          update begin fun st ->
                                            {st with iota_map= IntMap.add iota (`Single alloc_id') st.iota_map }
                                            end >>= fun () ->
                                          valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
                                        else
                                          error_postcond
                                      else
                                        error_postcond
                                 end

         (* PNVI-ae-udi *)
         | PV (Prov_symbolic iota1, PVconcrete addr1), PV (Prov_symbolic iota2, PVconcrete addr2) ->
            (* IF A(iota1) INTER A(iota2) = { i } AND precond valid THEN collapse iota1 and iota2 to i *)
            (* IF A(iota1) INTER A(iota2) = { i1, i2 } AND (precond valid for i1 AND i2) THEN NO collapse *)
            lookup_iota iota1 >>= fun ids1 ->
            lookup_iota iota2 >>= fun ids2 ->
            let inter_ids =
              match ids1, ids2 with
              | `Single x, `Single y ->
                 if N.equal x y then
                   `Single x
                 else
                   `None
              | `Single x, `Double (y, z)
                | `Double (y, z), `Single x ->
                 if N.equal x y || N.equal x z then
                   `Single x
                 else
                   `None
              | `Double (x1, x2), `Double (y1, y2) ->
                 if N.equal x1 y1 then
                   if N.equal x2 y2 then
                     `Double (x1, x2)
                   else
                     `Single x1
                 else if N.equal x2 y2 then
                   `Single x2
                 else
                   `None in
            begin match inter_ids with
            | `None ->
               error_postcond
            | `Single alloc_id' ->
               update begin fun st ->
                 {st with iota_map= IntMap.add iota1 (`Single alloc_id')
                                      (IntMap.add iota2 (`Single alloc_id') st.iota_map) }
                 end >>= fun () ->
               valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2)
            | `Double (alloc_id1, alloc_id2) ->
               if C.value_compare addr1 addr2 == 0 then
                 valid_postcond (C.cap_get_value addr1) (C.cap_get_value addr2) (* zero *)
               else
                 fail (MerrOther "in `diff_ptrval` invariant of PNVI-ae-udi failed: ambiguous iotas with addr1 <> addr2")
            end
         | _ ->
            error_postcond

  let isWellAligned_ptrval ref_ty ptrval =
    (* TODO: catch builtin function types *)
    match unatomic_ ref_ty with
    | Void
      | Function _ ->
       fail (MerrOther "called isWellAligned_ptrval on void or a function type")
    | _ ->
       begin match ptrval with
       | PV (_, PVnull _) ->
          return true
       | PV (_, PVfunction _) ->
          fail (MerrOther "called isWellAligned_ptrval on function pointer")
       | PV (_, PVconcrete addr) ->
          (*
            Printf.printf "addr: %s\n" (Nat_big_num.to_string addr);
            Printf.printf "align: %d\n" (alignof ref_ty);
           *)
          return (N.(equal (modulus (C.cap_get_value addr) (of_int (alignof ref_ty))) zero))
       end

  (* Following §6.5.3.3, footnote 102) *)
  (* TODO(CHERI): This check is not suffficient for CHERI. See notes *)
  let validForDeref_ptrval ref_ty ptrval =
    (*
      begin
      Printf.printf "validForDeref: ref_ty= %s, ptrval= %s\n"
      (String_core_ctype.string_of_ctype ref_ty)
      (Pp_utils.to_plain_string (pp_pointer_value ptrval))
      end;
     *)
    let cap_check c =
      if C.cap_is_valid c then
        let sz = sizeof ref_ty in
        let addr = C.cap_get_value c in
        let bounds = C.cap_get_bounds c in
        let nsz = N.of_int sz in
        if cap_bounds_check bounds addr nsz then
          return ()
        else
          fail (MerrCHERI
                  (CheriBoundsErr (bounds, addr, nsz)))
      else
        fail (MerrCHERI CheriMerrInvalidCap)
    in
    let do_test alloc_id =
      is_dead alloc_id >>= function
      | true ->
         return false
      | false ->
         isWellAligned_ptrval ref_ty ptrval in
    match ptrval with
    | PV (_, PVnull _)
      | PV (_, PVfunction _) ->
       return false
    | PV (Prov_device, PVconcrete c) as ptrval ->
       cap_check c >> isWellAligned_ptrval ref_ty ptrval
    (* PNVI-ae-udi *)
    | PV (Prov_symbolic iota, PVconcrete c) ->
       cap_check c >>
       lookup_iota iota >>= begin function
                              | `Single alloc_id ->
                                 do_test alloc_id
                              | `Double (alloc_id1, alloc_id2) ->
                                 do_test alloc_id1 >>= begin function
                                                         | false ->
                                                            do_test alloc_id2
                                                         | true ->
                                                            return true
                                                       end
                            end
    | PV (Prov_some alloc_id, PVconcrete c) ->
       cap_check c >> do_test alloc_id
    | PV (Prov_none, _) ->
       return false

  (* _ is integer type *)
  let ptrfromint (int_cty:ctype) ref_ty int_v =
    match int_cty with
    | Ctype (_, (Basic (Integer int_ty)))
      -> begin
        match int_ty, int_v with
        | ((Unsigned Intptr_t),(IC (prov, c)) | (Signed Intptr_t),(IC (prov, c))) ->
           begin
             let addr = C.cap_get_value c in
             if is_PNVI () then
               (* TODO(CHERI): not sure if this whole branch is correct for CHERI *)
               (* TODO: device memory? *)
               if N.equal addr N.zero then
                 return (PV (Prov_none, PVnull ref_ty))
               else
                 get >>= fun st ->
                 begin match find_overlaping st addr with
                 | `NoAlloc ->
                    return Prov_none
                 | `SingleAlloc alloc_id ->
                    return (Prov_some alloc_id)
                 | `DoubleAlloc alloc_ids ->
                    add_iota alloc_ids >>= fun iota ->
                    return (Prov_symbolic iota)
                 end >>= fun prov ->
                 (* cast int to pointer *)
                 return (PV (prov, PVconcrete c))
             else
               match prov with
               | Prov_none ->
                  (* TODO: check (in particular is that ok to only allow device pointers when there is no provenance? *)
                  if List.exists (fun (min, max) -> N.less_equal min addr && N.less_equal addr max) device_ranges then
                    return (PV (Prov_device, PVconcrete c))
                  else if N.equal addr N.zero then
                    (* All 0-address capabilities regardless of their
                       validity decoded as NULL. This is defacto behaviour
                       of morello Clang. See intptr3.c example.  *)
                    return (PV (Prov_none, PVnull ref_ty))
                  else
                    (* C could be an invalid cap. Consider raising error instead *)
                    return (PV (Prov_none, PVconcrete c))
               | _ ->
                  (* C could be an invalid cap. Consider raising error instead *)
                  return (PV (prov, PVconcrete c))
           end
        | (Ctype.(Unsigned Intptr_t),(IV (_, _)) | Ctype.(Signed Intptr_t),(IV (_, _))) ->
           failwith "ptrfromint: invalid encoding for [u]intptr_t"
        | _, (IV (prov, n)) ->
           if N.equal n N.zero then
             if is_PNVI () then
               (* TODO: device memory? *)
               return (PV (Prov_none, PVnull ref_ty))
             else
               (* All 0-address capabilities regardless of their
                  validity decoded as NULL. This is defacto behaviour
                  of morello Clang. See intptr3.c example.  *)
               return (PV (Prov_none, PVnull ref_ty))
           else
             let c = C.cap_c0 in
             let c = C.cap_set_value c n in
             return (PV (prov, PVconcrete c))
        | _, IC _ ->
           failwith "invalid integer value (capability for non- [u]intptr_t"
      end
    | _ ->
       (* [ptrfromint] in memory model Lem should be changed to have
          [integerType] instead of [ctype] as argument. *)
       failwith "ptrfromint called with non-int type"

  let offsetof_ival tagDefs tag_sym memb_ident =
    let (xs, _) = offsetsof tagDefs tag_sym in
    let pred (ident, _, _) =
      ident_equal ident memb_ident in
    match List.find_opt pred xs with
    | Some (_, _, offset) ->
       IV (Prov_none, N.of_int offset)
    | None ->
       failwith "CHERI.offsetof_ival: invalid memb_ident"

  let array_shift_ptrval (PV (prov, ptrval_)) ty _ =
    failwith "pure array_shift_ptrval not used in CHERI"

  (* TODO(CHERI): use effectful variant instead, which needs to be added.column
     One added, replace this one with ~failwith~.
   *)
  let member_shift_ptrval (PV (prov, ptrval_)) tag_sym memb_ident =
    let offset =
      match offsetof_ival (Tags.tagDefs ()) tag_sym memb_ident with
      | IV (_, offset) -> offset
      | IC (_, c) -> C.cap_get_value c
    in
    PV (prov, match ptrval_ with
              | PVnull ty ->
                 (* TODO: unsure, this might just be undefined (gcc-torture assumes the
                    following behaviour though) *)
                 if N.equal N.zero offset then
                   PVnull ty
                 else
                   (* The value of C0 could not be changed. *)
                   failwith "CHERI.member_shift_ptrval, shifting NULL"
              | PVfunction _ ->
                 failwith "CHERI.member_shift_ptrval, PVfunction"
              | PVconcrete c ->
                 let addr = C.cap_get_value c in
                 let c = C.cap_set_value c (N.add addr offset) in
                 PVconcrete c)

  (* this will be used for pointer arithmetics *)
  let eff_array_shift_ptrval loc ptrval ty ival_int =
    let ival = num_of_int ival_int in
    (* KKK print_endline ("HELLO eff_array_shift_ptrval ==> " ^ Pp_utils.to_plain_string (pp_pointer_value ptrval)); *)
    let offset = (Nat_big_num.(mul (of_int (sizeof ty)) ival)) in
    match ptrval with
    | PV (_, PVnull _) ->
       (* TODO: this seems to be undefined in ISO C *)
       (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
       failwith "TODO(shift a null pointer should be undefined behaviour)"
    | PV (_, PVfunction _) ->
       failwith "CHERI.eff_array_shift_ptrval, PVfunction"

    (* PNVI-ae-udi *)
    | PV (Prov_symbolic iota as prov, PVconcrete c) ->
       (* KKK print_endline ("HELLO iota ==> " ^ Pp_utils.to_plain_string (pp_pointer_value ptrval)); *)
       (* TODO: this is duplicated code from the Prov_some case (I'm keeping
          PNVI-ae-udi stuff separated to avoid polluting the
          vanilla PNVI code) *)
       let shifted_addr = N.add (C.cap_get_value c) offset in
       let precond z =
         (* TODO: is it correct to use the "ty" as the lvalue_ty? *)
         if    Switches.(has_switch (SW_pointer_arith `STRICT))
               || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
           get_allocation z >>= fun alloc ->
           if    N.less_equal alloc.base shifted_addr
                 && N.less_equal (N.add shifted_addr (N.of_int (sizeof ty)))
                      (N.add (N.add alloc.base alloc.size) (N.of_int (sizeof ty))) then
             return true
           else
             return false
         else
           return true in
       lookup_iota iota >>=
         begin function
           | `Double (alloc_id1, alloc_id2) ->
              if not (N.equal ival N.zero) then
                (* TODO: this is yucky *)
                precond alloc_id1 >>=
                  begin function
                    | true ->
                       precond alloc_id2 >>=
                         begin function
                           | true ->
                              if Switches.(has_switch (SW_pointer_arith `PERMISSIVE)) then
                                return `NoCollapse
                              else begin
                                  Printf.printf "id1= %s, id2= %s ==> addr= %s\n"
                                    (N.to_string alloc_id1) (N.to_string alloc_id2)
                                    (N.to_string shifted_addr);
                                  fail (MerrOther "(PNVI-ae-uid) ambiguous non-zero array shift")
                                end
                           | false ->
                              return (`Collapse alloc_id1)
                         end
                    | false ->
                       precond alloc_id2 >>=
                         begin function
                           | true ->
                              return (`Collapse alloc_id2)
                           | false ->
                              fail (MerrArrayShift loc)
                         end
                  end >>=
                  begin function
                    | `Collapse alloc_id ->
                       update begin fun st ->
                         {st with iota_map= IntMap.add iota (`Single alloc_id) st.iota_map }
                         end
                    | `NoCollapse ->
                       return ()
                  end >>= fun () ->
                (* Could produce invalid cap. Consider raising error instead *)
                return (PV (prov, PVconcrete (C.cap_set_value c shifted_addr)))
              else
                (* TODO: this is yucky *)
                precond alloc_id1 >>=
                  begin function
                    | true ->
                       return ()
                    | false ->
                       precond alloc_id2 >>=
                         begin function
                           | true ->
                              return ()
                           | false ->
                              fail (MerrArrayShift loc)
                         end
                  end >>= fun () ->
                (* Could produce invalid cap. Consider raising error instead *)
                return (PV (prov, PVconcrete (C.cap_set_value c shifted_addr)))
           | `Single alloc_id ->
              precond alloc_id >>=
                begin function
                  | true ->
                     (* Could produce invalid cap. Consider raising error instead *)
                     return (PV (prov, PVconcrete (C.cap_set_value c shifted_addr)))
                  | false ->
                     fail (MerrArrayShift loc)
                end
         end

    | PV (Prov_some alloc_id, PVconcrete c) ->
       (* TODO: is it correct to use the "ty" as the lvalue_ty? *)
       let shifted_addr = N.add (C.cap_get_value c) offset in
       if    Switches.(has_switch (SW_pointer_arith `STRICT))
             || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
         get_allocation alloc_id >>= fun alloc ->
         if    N.less_equal alloc.base shifted_addr
               && N.less_equal (N.add shifted_addr (N.of_int (sizeof ty)))
                    (N.add (N.add alloc.base alloc.size) (N.of_int (sizeof ty))) then
           (* Could produce invalid cap. Consider raising error instead *)
           return (PV (Prov_some alloc_id, PVconcrete (C.cap_set_value c shifted_addr)))
         else
           fail (MerrArrayShift loc)
       else
         (* Could produce invalid cap. Consider raising error instead *)
         return (PV (Prov_some alloc_id, PVconcrete (C.cap_set_value c shifted_addr)))
    | PV (Prov_none, PVconcrete c) ->
       let shifted_addr = N.add (C.cap_get_value c) offset in
       if    Switches.(has_switch (SW_pointer_arith `STRICT))
             || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
         fail (MerrOther "out-of-bound pointer arithmetic (Prov_none)")
       else
         (* Could produce invalid cap. Consider raising error instead *)
         return (PV (Prov_none, PVconcrete (C.cap_set_value c shifted_addr)))
    | PV (Prov_device, PVconcrete c) ->
       let shifted_addr = N.add (C.cap_get_value c) offset in
       (* Could produce invalid cap. Consider raising error instead *)
       return (PV (Prov_device, PVconcrete (C.cap_set_value c shifted_addr)))

  let concurRead_ival ity sym =
    failwith "TODO: concurRead_ival"

  let integer_ival n =
    IV (Prov_none, n)

  let max_ival ity =
    let open Nat_big_num in
    let signed_max n =
      sub (pow_int (of_int 2) (8*n-1)) (of_int 1) in
    let unsigned_max n =
      sub (pow_int (of_int 2) (8*n)) (of_int 1) in
    IV (Prov_none,
        match ity with
        | Signed Intptr_t -> signed_max (C.sizeof_vaddr)
        | Unsigned Intptr_t -> unsigned_max (C.sizeof_vaddr)
        | _ ->
           begin match (Ocaml_implementation.get ()).sizeof_ity ity with
           | Some n ->
              begin match ity with
              | Char ->
                 if (Ocaml_implementation.get ()).is_signed_ity Char then
                   signed_max n
                 else
                   unsigned_max n
              | Bool ->
                 (* TODO: not sure about this (maybe it should be 1 and not 255? *)
                 unsigned_max n
              | Size_t
                | Wchar_t (* TODO: it is implementation defined if unsigned *)
                | Unsigned _ ->
                 unsigned_max n
              | Ptrdiff_t
                | Wint_t (* TODO *)
                | Signed _ ->
                 signed_max n
              | Enum _ ->
                 (* TODO: hack, assuming like int *)
                 signed_max 4
              end
           | None ->
              failwith "the concrete memory model requires a complete implementation MAX"
           end)

  let min_ival ity =
    let open Nat_big_num in
    let signed_min n = negate (pow_int (of_int 2) (8*n-1)) in
    IV (Prov_none,
        begin match ity with
        | Char ->
           if (Ocaml_implementation.get ()).is_signed_ity Char then
             signed_min 8
           else
             zero
        | Bool
          | Size_t
          | Wchar_t (* TODO: it is implementation defined if unsigned *)
          | Wint_t
          | Unsigned _ ->
           (* all of these are unsigned *)
           zero
        | Signed Intptr_t -> signed_min C.sizeof_vaddr
        | Ptrdiff_t
          | Signed _ ->
           (* and all of these are signed *)
           begin match (Ocaml_implementation.get ()).sizeof_ity ity with
           | Some n ->
              signed_min n
           | None ->
              failwith "the concrete memory model requires a complete implementation MIN"
           end
        | Enum _ ->
           (* TODO: hack, assuming like int *)
           signed_min 4
        end)

  (* TODO: conversion? *)
  let intfromptr _ ity (PV (prov, ptrval_)) =
    match ptrval_ with
    | PVnull _ ->
       return (mk_ival prov Nat_big_num.zero)
    | PVfunction (Symbol.Symbol (_, n, _)) ->
       return (mk_ival prov (Nat_big_num.of_int n))
    | PVconcrete c ->
       begin if Switches.(has_switch (SW_PNVI `AE) || has_switch (SW_PNVI `AE_UDI)) then
               (* PNVI-ae, PNVI-ae-udi *)
               match prov with
               | Prov_some alloc_id ->
                  expose_allocation alloc_id
               | _ ->
                  return ()
             else
               return ()
       end >>= fun () ->
          match ity with
          | Signed Intptr_t
            | Unsigned Intptr_t ->
          return (IC (prov, c))
       | _ ->
          let ity_max = num_of_int (max_ival ity) in
          let ity_min = num_of_int (min_ival ity) in
          let addr = C.cap_get_value c in
          if N.(less addr ity_min || less ity_max addr) then
            fail MerrIntFromPtr
          else
            return (mk_ival prov addr)

  let combine_prov prov1 prov2 =
    match (prov1, prov2) with
    | (Prov_none, Prov_none) ->
       Prov_none
    | (Prov_none, Prov_some id) ->
       Prov_some id
    | (Prov_none, Prov_device) ->
       Prov_device
    | (Prov_some id, Prov_none) ->
       Prov_some id
    | (Prov_some id1, Prov_some id2) ->
       if id1 = id2 then
         Prov_some id1
       else
         Prov_none
    | (Prov_some _, Prov_device) ->
       Prov_device
    | (Prov_device, Prov_none) ->
       Prov_device
    | (Prov_device, Prov_some _) ->
       Prov_device
    | (Prov_device, Prov_device) ->
       Prov_device

    (* PNVI-ae-udi *)
    (* TODO: this is improvised, need to check with P *)
    | (Prov_symbolic _, _)
      | (_, Prov_symbolic _) ->
       failwith "CHERI.combine_prov: found a Prov_symbolic"

  let int_bin pf vf v1 v2 =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    match v1,v2 with
    | IV (prov1, n1), IV (prov2, n2)
      -> IV (pf prov1 prov2, vf n1 n2)
    | IC (prov1, c), IV (prov2, n2)
      ->
       let n1 = C.cap_get_value c in
       let c = C.cap_set_value c (vf n1 n2) in
       IC (pf prov1 prov2, c)
    | IV (prov1, n1), IC (prov2, c)
      ->
       let n2 = C.cap_get_value c in
       let c = C.cap_set_value c (vf n1 n2) in
       IC (pf prov1 prov2, c)
    | IC (prov1, c1), IC (prov2, c2)
      ->
       let n1 = C.cap_get_value c1 in
       let n2 = C.cap_get_value c2 in
       (* Arbitrary deciding to use 1st cap. TODO: check if it is right *)
       let c = C.cap_set_value c1 (vf n1 n2) in
       IC (pf prov1 prov2, c)

  let op_ival iop v1 v2 =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    match iop with
    | IntAdd -> int_bin combine_prov Nat_big_num.add v1 v2
    | IntSub -> int_bin
                  (fun prov1 prov2 ->
                    match prov1, prov2 with
                    | Prov_some _, Prov_some _
                      | Prov_none, _ ->
                       Prov_none
                    | _ ->
                       prov1)
                  Nat_big_num.sub v1 v2
    | IntMul -> int_bin combine_prov Nat_big_num.mul v1 v2
    | IntDiv -> int_bin combine_prov
                  (fun n1 n2 -> Nat_big_num.(if equal n2 zero then zero else integerDiv_t n1 n2))
                  v1 v2
    | IntRem_t -> int_bin combine_prov Nat_big_num.integerRem_t v1 v2
    | IntRem_f -> int_bin combine_prov Nat_big_num.integerRem_f v1 v2
    | IntExp ->
       (* NOTE: this operation doesn't exists in C, but is used in the elaboration of the
          shift operators. And for these we want the provenance of the left operand to be
          the one that is forwarded *)
       (* TODO: fail properly when y is too big? *)
       int_bin combine_prov (fun n1 n2 ->
           Nat_big_num.pow_int n1 (Nat_big_num.to_int n2))
         v1 v2

  let sizeof_ival ty =
    IV (Prov_none, Nat_big_num.of_int (sizeof ty))
  let alignof_ival ty =
    IV (Prov_none, Nat_big_num.of_int (alignof ty))

  let bitwise_complement_ival _ = function
    | (IV (prov, n)) ->
        (* NOTE: for PNVI we assume that prov = Prov_none *)
        (* TODO *)
        (* prerr_endline "CHERI.bitwise_complement ==> HACK"; *)
        IV (prov, Nat_big_num.(sub (negate n) (of_int 1)))
    | (IC (prov, c)) ->
        let n = C.cap_get_value c in
        let c = C.cap_set_value c n in
        IC (prov, c)

  let bitwise_and_ival _  = int_bin combine_prov Nat_big_num.bitwise_and

  let bitwise_or_ival _ = int_bin combine_prov Nat_big_num.bitwise_or

  let bitwise_xor_ival _ = int_bin combine_prov Nat_big_num.bitwise_xor

  let case_integer_value v f_concrete _ =
    f_concrete (num_of_int v)

  let is_specified_ival ival =
    true

  let zero_fval =
    0.0
  let one_fval =
    1.0
  let str_fval str =
    float_of_string str

  let case_fval fval _ fconcrete =
    fconcrete fval

  let op_fval fop fval1 fval2 =
    match fop with
    | FloatAdd ->
       fval1 +. fval2
    | FloatSub ->
       fval1 -. fval2
    | FloatMul ->
       fval1 *. fval2
    | FloatDiv ->
       fval1 /. fval2

  let eq_fval fval1 fval2 =
    fval1 = fval2

  let lt_fval fval1 fval2 =
    fval1 < fval2

  let le_fval fval1 fval2 =
    fval1 <= fval2

  let fvfromint ni =
    let n = num_of_int ni in
    (* NOTE: if n is too big, the float will be truncated *)
    float_of_string (N.to_string n)

  let ivfromfloat ity fval =
    (* TODO: hack maybe the elaboration should do that?? *)
    match ity with
    | Bool ->
       IV (Prov_none, if fval = 0.0 then N.zero else N.(succ zero))
    | _ ->
       let nbytes = match (Ocaml_implementation.get ()).sizeof_ity ity with
         | None ->
            assert false
         | Some z ->
            z in
       let nbits = 8 * nbytes in
       let is_signed = AilTypesAux.is_signed_ity ity in
       let (min, max) =
         if is_signed then
           ( N.negate (N.pow_int (N.of_int 2) (nbits-1))
           , N.sub (N.pow_int (N.of_int 2) (nbits-1)) N.(succ zero) )
         else
           ( N.zero
           , N.sub (N.pow_int (N.of_int 2) nbits) N.(succ zero) ) in
       let wrapI n =
         let dlt = N.succ (N.sub max min) in
         let r = N.integerRem_f n dlt in
         if N.less_equal r max then
           r
         else
           N.sub r dlt in
       IV (Prov_none, (wrapI (N.of_int64 (Int64.of_float fval))))

  let eq_ival _ n1 n2 =
    Some (Nat_big_num.equal (num_of_int n1) (num_of_int n2))
  let lt_ival _ n1 n2 =
    Some (Nat_big_num.compare (num_of_int n1) (num_of_int n2) = -1)
  let le_ival _ n1 n2 =
    let cmp = Nat_big_num.compare (num_of_int n1) (num_of_int n2) in
    Some (cmp = -1 || cmp = 0)

  let eval_integer_value n =
    Some (num_of_int n)

  let unspecified_mval ty =
    MVunspecified ty
  let integer_value_mval ity ival =
    MVinteger (ity, ival)
  let floating_value_mval fty fval =
    MVfloating (fty, fval)
  let pointer_mval ref_ty ptrval =
    MVpointer (ref_ty, ptrval)
  let array_mval mvals =
    MVarray mvals
  let struct_mval tag_sym xs =
    MVstruct (tag_sym, xs)
  let union_mval tag_sym memb_ident mval =
    MVunion (tag_sym, memb_ident, mval)

  let case_mem_value mval f_unspec f_concur f_ival f_fval f_ptr f_array f_struct f_union =
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

  let sequencePoint =
    return ()




  let pp_pretty_pointer_value = pp_pointer_value
  let pp_pretty_integer_value _ = pp_integer_value
  let pp_pretty_mem_value _ = pp_mem_value

  (* TODO check *)
  let memcpy ptrval1 ptrval2 size_int =
    let size_n = num_of_int size_int in
    let loc = Location_ocaml.other "memcpy" in
    (* TODO: if ptrval1 and ptrval2 overlap ==> UB *)
    (* TODO: copy ptrval2 into ptrval1 *)
    let rec aux i =
      if Nat_big_num.less i size_n then
        load loc Ctype.unsigned_char (array_shift_ptrval ptrval2 Ctype.unsigned_char (IV (Prov_none, i))) >>= fun (_, mval) ->
        store loc Ctype.unsigned_char false (array_shift_ptrval ptrval1 Ctype.unsigned_char (IV (Prov_none, i))) mval >>= fun _ ->
        aux (Nat_big_num.succ i)
      else
        return ptrval1 in
    aux Nat_big_num.zero


  (* TODO: validate more, but looks good *)
  let memcmp ptrval1 ptrval2 size_int =
    let size_n = num_of_int size_int in
    let rec get_bytes ptrval acc = function
      | 0 ->
         return (List.rev acc)
      | size ->
         load Location_ocaml.unknown Ctype.unsigned_char ptrval >>= function
         | (_, MVinteger (_, (IV (byte_prov, byte_n)))) ->
            let ptr' = array_shift_ptrval ptrval Ctype.unsigned_char (IV (Prov_none, Nat_big_num.(succ zero))) in
            get_bytes ptr' (byte_n :: acc) (size-1)
         | _ ->
            assert false in
    get_bytes ptrval1 [] (Nat_big_num.to_int size_n) >>= fun bytes1 ->
    get_bytes ptrval2 [] (Nat_big_num.to_int size_n) >>= fun bytes2 ->

    let open Nat_big_num in
    return (IV (Prov_none, List.fold_left (fun acc (n1, n2) ->
                               if equal acc zero then of_int (Nat_big_num.compare n1 n2) else acc
                             ) zero (List.combine bytes1 bytes2)))

  let realloc tid align ptr size : pointer_value memM =
    match ptr with
    | PV (Prov_none, PVnull _) ->
       allocate_region tid (Symbol.PrefOther "realloc") align size
    | PV (Prov_none, _) ->
       fail (MerrWIP "realloc no provenance")
    | PV (Prov_some alloc_id, PVconcrete c) ->
       let addr = C.cap_get_value c in
       is_dynamic addr >>= begin function
                             | false ->
                                fail (MerrUndefinedRealloc)
                             | true ->
                                get_allocation alloc_id >>= fun alloc ->
                                if alloc.base = addr then
                                  allocate_region tid (Symbol.PrefOther "realloc") align size >>= fun new_ptr ->
                                  let size_to_copy =
                                    let size_n = num_of_int size in
                                    IV (Prov_none, Nat_big_num.min alloc.size size_n) in
                                  memcpy new_ptr ptr size_to_copy >>= fun _ ->
                                  kill (Location_ocaml.other "realloc") true ptr >>= fun () ->
                                  return new_ptr
                                else
                                  fail (MerrWIP "realloc: invalid pointer")
                           end
    | PV _ ->
       fail (MerrWIP "realloc: invalid pointer")

  let va_start args =
    get >>= fun st ->
    let id = st.next_varargs_id in
    update (fun st -> { st with varargs = IntMap.add id (0, args) st.varargs;
                                next_varargs_id = N.succ st.next_varargs_id;
      } ) >>= fun _ ->
    return (IV (Prov_none, id))

  let va_copy va =
    match va with
    | IV (Prov_none, id) ->
       get >>= fun st ->
       begin match IntMap.find_opt id st.varargs with
       | Some args ->
          let id = st.next_varargs_id in
          update (fun st -> { st with varargs = IntMap.add id args st.varargs;
                                      next_varargs_id = N.succ st.next_varargs_id;
            } ) >>= fun _ ->
          return (IV (Prov_none, id))
       | None ->
          fail (MerrWIP "va_copy: not initiliased")
       end
    | _ ->
       fail (MerrWIP "va_copy: invalid va_list")

  let va_arg va ty =
    match va with
    | IV (Prov_none, id) ->
       get >>= fun st ->
       begin match IntMap.find_opt id st.varargs with
       | Some (i, args) ->
          begin match List.nth_opt args i with
          | Some (_, ptr) -> (* TODO: check type is compatible *)
             update (fun st -> { st with varargs = IntMap.add id (i+1, args) st.varargs })
             >>= fun _ ->
             return ptr
          | None ->
             fail (MerrWIP "va_arg: invalid number of arguments")
          end
       | None ->
          fail (MerrWIP "va_arg: not initiliased")
       end
    | _ ->
       fail (MerrWIP "va_arg: invalid va_list")

  let va_end va =
    match va with
    | IV (Prov_none, id) ->
       get >>= fun st ->
       begin match IntMap.find_opt id st.varargs with
       | Some _ ->
          update (fun st -> { st with varargs = IntMap.remove id st.varargs })
       | None ->
          fail (MerrWIP "va_end: not initiliased")
       end
    | _ ->
       fail (MerrWIP "va_end: invalid va_list")

  let va_list va_idx =
    get >>= fun st ->
    begin match IntMap.find_opt va_idx st.varargs with
    | Some (n, args) ->
       assert (n = 0); (* not sure what happens with n <> 0 *)
       return args
    | None ->
       fail (MerrWIP "va_list")
    end

  let copy_alloc_id ival ptrval =
    (* cast_ptrval_to_ival(uintptr_t,𝑝1),cast_ival_to_ptrval(void,𝑥) *)
    (* the first ctype is the original referenced type, the integerType is the target integer type *)
    intfromptr Ctype.void Ctype.(Unsigned Intptr_t) ptrval >>= fun _ ->
    ptrfromint
      (Ctype ([], (Basic (Integer (Unsigned Intptr_t)))))
      Ctype.void ival

  (* JSON serialisation: Memory layout for UI *)

  type ui_value =
    { kind: [ `Unspec | `Basic | `Char | `Pointer | `Unspecptr
              | `Funptr | `Intptr | `Padding ];
      size: int; (* number of square on the left size of the row *)
      path: string list; (* tag list *)
      value: string;
      prov: provenance;
      bytes: AbsByte.t list option;
      typ: ctype option;
    }

  type ui_alloc =
    { id: int;
      base: string;
      prefix: Symbol.prefix;
      dyn: bool; (* dynamic memory *)
      typ: ctype;
      size: int;
      values: ui_value list;
      exposed: bool;
    }

  let rec mk_ui_values
            st
            (tag_query_f: C.vaddr -> bool option)
            (addr:C.vaddr)
            bs ty mval : ui_value list =
    let mk_ui_values = mk_ui_values st tag_query_f in
    let mk_scalar kind v p bs_opt =
      [{ kind; size = sizeof ty; path = []; value = v;
         prov = p; typ = Some ty; bytes = bs_opt }] in
    let mk_pad n v =
      { kind = `Padding; size = n; typ = None; path = []; value = v;
        prov = Prov_none; bytes = None } in
    let add_path p r = { r with path = p :: r.path } in
    match mval with
    | MVEunspecified (Ctype (_, Pointer _)) ->
       mk_scalar `Unspecptr "unspecified" Prov_none (Some bs)
    | MVEunspecified _ ->
       mk_scalar `Unspec "unspecified" Prov_none (Some bs)
    | MVEinteger (cty, IV(prov, n)) ->
       begin match cty with
       | Char | Signed Ichar | Unsigned Ichar ->
          mk_scalar `Char (N.to_string n) prov None
       | Ptrdiff_t | Signed Intptr_t | Unsigned Intptr_t ->
          mk_scalar `Intptr (N.to_string n) prov None
       | _ ->
          mk_scalar `Basic (N.to_string n) prov None
       end
    | MVEinteger (cty, IC(prov, c)) ->
       begin match cty with
       | Signed Intptr_t | Unsigned Intptr_t ->
          (* TODO(CHERI): better JSON representation of caps *)
          mk_scalar `Intptr (N.to_string (C.cap_get_value c)) prov None
       | _ ->
          failwith "mk_ui_values invalid encoding of [u]intptr_t"
       end
    | MVEfloating (_, f) ->
       mk_scalar `Basic (string_of_float f) Prov_none None
    | MVEpointer (_, PV(prov, pv)) ->
       begin match pv with
       | PVnull _ ->
          mk_scalar `Pointer "NULL" Prov_none None
       | PVconcrete c ->
          (* TODO(CHERI): better JSON representation of caps *)
          mk_scalar `Pointer (N.to_string (C.cap_get_value c)) prov (Some bs)
       | PVfunction sym ->
          mk_scalar `Funptr (Pp_symbol.to_string_pretty sym) Prov_none None
       end
    | MVEarray mvals ->
       begin match ty with
       | Ctype (_, Array (elem_ty, _)) ->
          let size = sizeof elem_ty in
          let (rev_rows, _, _) = List.fold_left begin fun (acc, i, acc_bs) mval ->
                                   let row = List.map (add_path (string_of_int i))
                                             @@ mk_ui_values
                                                  (* TODO(CHERI): Check if anything special needs to be done about alignment here *)                                                                                      (N.add addr (N.of_int (i*(sizeof elem_ty))))
                                                  acc_bs elem_ty mval in
                                   (row::acc, i+1, L.drop size acc_bs)
                                   end ([], 0, bs) mvals
          in List.concat @@ (List.rev rev_rows)
       | _ ->
          failwith "mk_ui_values: array type is wrong"
       end
    | MVEstruct (tag_sym, _) ->
       (* NOTE: we recombine the bytes to get paddings *)
       let (bs1, bs2) = L.split_at (sizeof ty) bs in
       let (rev_rowss, _, bs') = List.fold_left begin
                                     fun (acc_rowss, previous_offset, acc_bs) (Symbol.Identifier (_, memb), memb_ty, memb_offset) ->
                                     let pad = memb_offset - previous_offset in
                                     let acc_bs' = L.drop pad acc_bs in
                                     let memb_addr = N.add addr (N.of_int memb_offset) in

                                     let (_, mval, acc_bs'') = abst (find_overlaping st) st.funptrmap tag_query_f memb_addr memb_ty acc_bs' in
                                     let rows = mk_ui_values memb_addr acc_bs' memb_ty mval in
                                     let rows' = List.map (add_path memb) rows in
                                     (* TODO: set padding value here *)
                                     let rows'' = if pad = 0 then rows' else mk_pad pad "" :: rows' in
                                     (rows''::acc_rowss, memb_offset + sizeof memb_ty, acc_bs'')
                                   end ([], 0, bs1) (fst (offsetsof (Tags.tagDefs ()) tag_sym))
       in List.concat (List.rev rev_rowss)
    | MVEunion (tag_sym, Symbol.Identifier (_, memb), mval) ->
       List.map (add_path memb) (mk_ui_values addr bs ty mval) (* FIXME: THE TYPE IS WRONG *)
    | MVErr _ -> failwith "TODO(CHERI) serialize errors"

  let mk_ui_alloc st id alloc : ui_alloc =
    let ty = match alloc.ty with Some ty -> ty | None -> Ctype ([], Array (Ctype ([], Basic (Integer Char)), Some alloc.size)) in
    let size = N.to_int alloc.size in
    let bs = fetch_bytes st.bytemap alloc.base size in
    let tag_query a =
      match (Ocaml_implementation.get ()).alignof_pointer with
      | None -> failwith "alignof_pointer must be specified in Ocaml_implementation"
      | Some v ->
         let (q,m) = N.quomod a (N.of_int v) in
         if m <> N.zero then failwith "Unaligned address in mk_ui_alloc"
         else IntMap.find_opt q st.captags
    in
    let (_, mval, _) = abst (find_overlaping st) st.funptrmap tag_query alloc.base ty bs in
    { id = id;
      base = N.to_string alloc.base;
      prefix = alloc.prefix;
      dyn = List.mem alloc.base st.dynamic_addrs;
      typ = ty;
      size = size;
      values = mk_ui_values st tag_query alloc.base bs ty mval;
      exposed = (alloc.taint = `Exposed);
    }

  let serialise_prefix = function
    | Symbol.PrefOther s ->
       (* TODO: this should not be possible anymore *)
       `Assoc [("kind", `String "other"); ("name", `String s)]
    | Symbol.PrefMalloc ->
       `Assoc [("kind", `String "malloc");
               ("scope", `Null);
               ("name", `String "malloc'd");
               ("loc", `Null)]
    | Symbol.PrefStringLiteral (loc, _) ->
       `Assoc [("kind", `String "string literal");
               ("scope", `Null);
               ("name", `String "literal");
               ("loc", Location_ocaml.to_json loc)]
    | Symbol.PrefCompoundLiteral (loc, _) ->
       `Assoc [("kind", `String "compound literal");
               ("scope", `Null);
               ("name", `String "literal");
               ("loc", Location_ocaml.to_json loc)]
    | Symbol.PrefFunArg (loc, _, n) ->
       `Assoc [("kind", `String "arg");
               ("scope", `Null);
               ("name", `String ("arg" ^ string_of_int n));
               ("loc", Location_ocaml.to_json loc)]
    | Symbol.PrefSource (_, []) ->
       failwith "serialise_prefix: PrefSource with an empty list"
    | Symbol.PrefSource (loc, [name]) ->
       `Assoc [("kind", `String "source");
               ("name", `String (Pp_symbol.to_string_pretty name));
               ("scope", `Null);
               ("loc", Location_ocaml.to_json loc);]
    | Symbol.PrefSource (loc, [scope; name]) ->
       `Assoc [("kind", `String "source");
               ("name", `String (Pp_symbol.to_string_pretty name));
               ("scope", `String (Pp_symbol.to_string_pretty scope));
               ("loc", Location_ocaml.to_json loc);]
    | Symbol.PrefSource (_, _) ->
       failwith "serialise_prefix: PrefSource with more than one scope"

  let serialise_prov st = function
    | Prov_some n ->
       `Assoc [("kind", `String "prov");
               ("value", `Int (N.to_int n))]
    | Prov_symbolic i ->
       `Assoc [("kind", `String "iota");
               ("value", `Int (N.to_int i));
               ("iota", match IntMap.find_opt i st.iota_map with
                        | None ->
                           `Null (* it should be impossible *)
                        | Some (`Single n) ->
                           `List [`Int (N.to_int n)]
                        | Some (`Double (n1, n2)) ->
                           `List [`Int (N.to_int n1);
                                  `Int (N.to_int n2)])]
    | _ ->
       `Assoc [("kind", `String "empty")]

  let serialise_map f m : Json.json =
    let serialise_entry (k, v) = (N.to_string k, f (N.to_int k) v)
    in `Assoc (List.map serialise_entry (IntMap.bindings m))

  let serialise_ui_values st (v:ui_value) : Json.json =
    let string_of_kind = function
      | `Unspec -> "unspecified"
      | `Basic -> "basic"
      | `Pointer -> "pointer"
      | `Funptr -> "funptr"
      | `Intptr -> "intptr"
      | `Unspecptr -> "unspecptr"
      | `Char -> "char"
      | `Padding -> "padding"
    in
    `Assoc [("kind"), `String (string_of_kind v.kind);
            ("size", `Int v.size);
            ("path", `List (List.map Json.of_string v.path));
            ("value", `String v.value);
            ("prov", serialise_prov st v.prov);
            ("type", Json.of_option (fun ty -> `String (String_core_ctype.string_of_ctype ty)) v.typ);
            ("bytes", Json.of_option (fun bs -> `List (List.map (AbsByte.to_json (serialise_prov st)) bs)) v.bytes); ]

  let serialise_ui_alloc st (a:ui_alloc) : Json.json =
    `Assoc [("id", `Int a.id);
            ("base", `String a.base);
            ("prefix", serialise_prefix a.prefix);
            ("dyn", `Bool a.dyn);
            ("type", `String (String_core_ctype.string_of_ctype a.typ));
            ("size", `Int a.size);
            ("values", `List (List.map (serialise_ui_values st) a.values));
            ("exposed", `Bool a.exposed);
      ]

  let serialise_mem_state dig (st: mem_state) : Json.json =
    let allocs = IntMap.filter (fun _ (alloc : allocation) ->
                     match alloc.prefix with
                     | Symbol.PrefSource (_, syms) -> List.exists (fun (Symbol.Symbol (hash, _, _)) -> hash = dig) syms
                     | Symbol.PrefStringLiteral (_, hash) -> hash = dig
                     | Symbol.PrefCompoundLiteral (_, hash) -> hash = dig
                     | Symbol.PrefFunArg (_, hash, _) -> hash = dig
                     | Symbol.PrefMalloc -> true
                     | _ -> false
                   ) st.allocations in
    `Assoc [("map", serialise_map (fun id alloc -> serialise_ui_alloc st @@ mk_ui_alloc st id alloc) allocs);
            ("last_used", Json.of_option (fun v -> `Int (N.to_int v)) st.last_used);]


end

open Morello

module CHERIMorello = CHERI(Morello_capability)
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
