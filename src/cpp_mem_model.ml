(* C++17 error:
 * page 558: ... is implicitly declared reachable (see 21.06.4#3) *
 *)

(*
 * A byte of storage is reachable through a pointer value that points to an
 * object Y if it is within the storage occupied by Y, an object that is
 * pointer-interconvertible with Y, or the immediately-enclosing array object
 * if Y is an array element.  *)

open Mem_common
open Memory_model
open Core_ctype
open Ocaml_implementation

module IntMap = Map.Make(struct type t = int let compare = compare end)

(* copied from defacto *)
module Eff : sig
  type ('a, 'err, 'cs, 'st) eff =
    ('a, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff) -> ('b, 'err, 'cs, 'st) eff
  val (>>): ('a, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff
  val read: ('st -> 'a) -> ('a, 'err, 'cs, 'st) eff
  val update: ('st -> 'st) -> (unit, 'err, 'cs, 'st) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'err, 'cs, 'st) eff
  val get: ('st, 'err, 'cs, 'st) eff
  val put: 'st -> (unit, 'err, 'cs, 'st) eff
  val fail: 'err -> ('a, 'err, 'cs, 'st) eff
  val mapM: ('a -> ('b, 'err, 'cs, 'st) eff) -> 'a list -> ('b list, 'err, 'cs, 'st) eff
  val msum: string -> (string * ('a, 'err, 'cs, 'st) eff) list -> ('a, 'err, 'cs, 'st) eff
end = struct
  type ('a, 'err, 'cs, 'st) eff =
    ('a, 'err, 'cs, 'st) Nondeterminism.ndM

  let return = Nondeterminism.nd_return
  let (>>=) = Nondeterminism.nd_bind
  let (>>) f g = f >>= (fun _ -> g)

  let read = Nondeterminism.nd_read
  let update = Nondeterminism.nd_update
  let modify f = 
    Nondeterminism.nd_get >>= fun st ->
    let (ret, st') = f st in
    Nondeterminism.nd_put st' >>= fun () ->
    return ret

  let get = Nondeterminism.nd_get
  let put = Nondeterminism.nd_put
  let fail err = Nondeterminism.kill (Other err)
  let mapM _ _ = failwith "TODO: mapM"

  let msum str xs =
    Nondeterminism.(
      msum Mem_common.instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict str xs
    )
end

module CppMemModel : Memory = struct
  let name = "I am the C++ memory model"

  (* Missing pointer-to-member types *)
  type cpptype = ctype0

  let rec is_scalar = function
    | Basic0 _
    | Builtin0 _
    | Pointer0 _ -> true
    | Atomic0 ty -> is_scalar ty (* TODO: not sure *)
    | _ -> false

  let rec is_literal ty =
    if is_scalar ty then true
    else match ty with
      | Void0 -> true
      | Array0 (ty_elem, _)  -> is_literal ty_elem
      | _ -> false

  (* nullptr_t is a fundamental type *)
  let rec is_fundamental_type = function
    | Void0
    | Function0 _
    | Builtin0 _ -> true
    | Atomic0 ty -> is_fundamental_type ty
    | _ -> false

  let rec is_compound_type = function
    | Pointer0 _
    | Struct0 _
    | Union0 _ -> true
    | Atomic0 ty -> is_compound_type ty
    | _ -> false

  (* memory location = scalar type or a sequence of adjacent bits *)
  (* object = created by a definition, malloc, changing union or ?temporary? *)
  (* object occupies *region of storage* *)
  (* subobject = a member or an array element *)
  (* an array *provides storages* to objects *)
  (* nested objects *)
  (* complete objects *)
  (* potentially-overlapping subobjects  --> probably irrelevant *)

  (* lifetime begins when the storage with proper alignment and size of type T
   * is obtained *)
  (* if has ?non-vacuous initialisation?, its init is complete *)

  (* object pointer value *)


  (* definition of pointer-terconvertible *)




  (*
  type traceable_pointer =
    | TPpv of pointer_value
    | TPiv of integer_value (* it should be at least as large as std::intptr_t *)
    | TParray of  byte list (* a sequence of elements in an array of narrow
                               character type (6.7.1), where the size and
                               alignment of the sequence match those of some
                               object pointer type. *)
*)
  (* safely-derived pointer (* has type of pointer value *)
   *  - from malloc
   *  - using &
   *  - ?well-defined? pointer arithmetic
   *  - ?well-defined? pointer conversion
   *  - "the value of an object whose value was copied from a traceable pointer
   *  object, where at the time of the copy the source object contained a copy
   *  of a safely-derived pointer value."
   *)

  (* an integer value is an integer representation of a safely-derived pointer if
   * is at least large as intptr_t
   * - ?valid conversion from a safely-derived pointer?
   * - "the value of an object whose value was copied from a traceable pointer
   *    object, where at the time of the copy the source object contained an
   *    integer representation of a safely-derived pointer value;"
   * - additive and bitwise operations *)

  (* difference between relaxed or struct pointer safety *)

(*

  (* When storage for an object with automatic or dynamic storage duration is obtained, the object has an indeterminate value, and if no initialization is performed for the object, that object retains an indeterminate value until that value is replaced *)


  (* the lifetime of a reference begins when its initalisation is complete *)

  (* the address of a object is the address of its first byte *)

  (* The object representation of an object of type T is the sequence of N
   * unsigned char objects taken up by the object of type T, where N equals
   * sizeof(T). *)

  (* The value representation of an object is the set of bits that hold the
   * value of type T. Bits in the object representation that are not part of
   * the value representation are padding bits. For trivially copyable types,
   * the value representation is a set of bits in the object representation
   * that determines a value, which is one discrete element of an
   * implementation-defined set of values. ? *)

  type subobject =
    | SubobjectMember
    | SubobjectArrayElement
    | SubjectComplete (* ??? *)

        (* only for array of unsigned char or std::byte *)

  (* the memory model creates a list of region_of_storage with sizes *)

  (* ? storage duration ? *)

(* an object a is nested in b --> a is suboject of b, b provides storage for a or
 * ?c. a is nested within c and c is nested within b *)

  let complete_object (x: object_): object_ =
    failwith "If x is a complete object, then the complete object of x is
    itself. Otherwise, the complete object of x is the complete object of the
    (unique) object that contains x."
*)

  type address = int

  type object_id = int

  type size = int

  type object_represenation = char list

  type storage_duration =
    | SDstatic
    | SDthread
    | SDautomatic
    | SDdynamic

  type object_ =
      (* the lifetime of an object begin when storage with the proper alignment
       * and size for the type is obtained *)
    { lifetime: address option; (* lifetime is a region storage id *)
      ty: cpptype; (* TODO: does this make sense? what about malloc? *)
      storage_duration: storage_duration;
    }

  type integer_value = Nat_big_num.num

  (* WARN: using 64 bits Ocaml's float, not the correct standard *)
  type floating_value = float

  type pointer_value =
    | PVstorage of address  (* a pointer to a storage location *)
    | PVobject of object_id (* a pointer to an object or function *)
    | PVend of object_id    (* a pointer past the end of an object *)
    | PVnull of ctype0      (* the null pointer value *)
    | PVinvalid             (* an invalid pointer value *)

  type mem_value =
    | MVindeterminate of ctype0
    | MVinteger of AilTypes.integerType * integer_value
    | MVfloat of AilTypes.floatingType * floating_value
    | MVpointer of ctype0 * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym * member_field list
    | MVunion of Symbol.sym * member_field
  and member_field = Cabs.cabs_identifier * mem_value

  type block = (* or region of storage *)
    { size: int;
      value: mem_value option; (* indeterminate value *)
    }

  type mem_state =
    { next_oid: object_id;
      next_address: address;
      objects: object_ IntMap.t;
      storage: block IntMap.t;
    }

  let initial_mem_state =
    { next_oid = 0;
      next_address = 0xFF;
      objects = IntMap.empty;
      storage = IntMap.empty;
    }

  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  let return = Eff.return
  let bind = Eff.(>>=)
  let (>>=) = bind

  type mem_iv_constraint = integer_value Mem_common.mem_constraint
  let cs_module = (module struct
    type t = mem_iv_constraint
    let negate x = failwith "Cpp_mem_mode.cs_module.negate"
    type 'a eff = NoEff of 'a
    let return x = failwith "Cpp_mem_mode.cs_module.return"
    let bind m f = failwith "Cpp_mem_mode.cs_module.bind"
    let foldlM f x = failwith "Cpp_mem_mode.cs_module.foldlM"
    let runEff m = failwith "Cpp_mem_mode.cs_module.runEff"
    let string_of_solver = failwith "Cpp_mem_mode.cs_module.string_of_solver"
    let check_sat = failwith "Cpp_mem_mode.cs_module.check_sat"
    let with_constraints x = failwith "Cpp_mem_mode.cs_module.with_constraints"
  end : Constraints with type t = mem_iv_constraint)

  type footprint = Footprint
  let do_overlap fp1 fp2 = failwith "footprint:do_overlap"

  let fromImpl = function
    | Some x -> x
    | None -> failwith "the memory model requires a complete implementation"

  (* copied from defacto *)
  let rec offsetsof tag_sym =
    match Pmap.find tag_sym (Tags.tagDefs ()) with
    | Tags.StructDef membrs ->
      let (xs, maxoffset) =
        List.fold_left (fun (xs, last_offset) (membr, ty) ->
          let size = sizeof ty in
          let align = alignof ty in
          let x = last_offset mod align in
          let pad = if x = 0 then 0 else align - x in
          ((membr, ty, last_offset + pad) :: xs, last_offset + pad + size)
        ) ([], 0) membrs in
      (List.rev xs, maxoffset)
    | Tags.UnionDef membrs ->
      (List.map (fun (ident, ty) -> (ident, ty, 0)) membrs, 0)
  and sizeof = function
    | Void0 | Array0 (_, None) | Function0 _ -> assert false
    | Basic0 (Integer ity) -> fromImpl @@ Impl.sizeof_ity ity
    | Basic0 (Floating fty) ->fromImpl @@ Impl.sizeof_fty fty
    | Array0 (elem_ty, Some n) -> Nat_big_num.to_int n * sizeof elem_ty
    | Pointer0 _ -> fromImpl @@ Impl.sizeof_pointer
    | Atomic0 atom_ty -> sizeof atom_ty
    | Struct0 tag_sym as ty ->
        let (_, max_offset) = offsetsof tag_sym in
        let align = alignof ty in
        let x = max_offset mod align in
        if x = 0 then max_offset else max_offset + (align - x)
    | Union0 tag_sym ->
        begin match Pmap.find tag_sym (Tags.tagDefs ()) with
          | Tags.StructDef _ -> assert false
          | Tags.UnionDef membrs ->
              let (max_size, max_align) =
                List.fold_left (fun (acc_size, acc_align) (_, ty) ->
                  (max acc_size (sizeof ty), max acc_align (alignof ty))
                ) (0, 0) membrs in
              (* NOTE: adding padding at the end to satisfy
               * alignment constraints *)
              let x = max_size mod max_align in
              if x = 0 then max_size else max_size + (max_align - x)
        end
    | Builtin0 str ->
       failwith "TODO: sizeof Builtin"
  and alignof = function
    | Void0 -> assert false
    | Basic0 (Integer ity) -> fromImpl @@ Impl.alignof_ity ity
    | Basic0 (Floating fty) -> fromImpl @@ Impl.alignof_fty fty
    | Array0 (_, None) -> assert false
    | Array0 (elem_ty, Some n) -> alignof elem_ty
    | Function0 _ -> assert false
    | Pointer0 _ -> fromImpl @@ Impl.alignof_pointer
    | Atomic0 atom_ty -> alignof atom_ty
    | Struct0 tag_sym ->
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
        | Tags.UnionDef _ -> assert false
        | Tags.StructDef membrs  ->
          (* NOTE: Structs (and unions) alignment is that of the maximum
           * alignment of any of their components. *)
          List.fold_left (fun acc (_, ty) -> max (alignof ty) acc ) 0 membrs
      end
    | Union0 tag_sym ->
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
        | Tags.StructDef _ -> assert false
        | Tags.UnionDef membrs ->
          (* NOTE: Structs (and unions) alignment is that of fromImpl maximum
           * alignment of any of their components. *)
          List.fold_left (fun acc (_, ty) -> max (alignof ty) acc) 0 membrs
      end
    | Builtin0 str ->
       failwith "TODO: sizeof Builtin"

  let get_aligned_address align addr =
    let m = addr mod align in
    if m = 0  then addr else addr + (align - m)


  (* Memory actions *)
  let allocate_object _ _ align ty init_opt =
    Eff.modify begin fun st ->
      let size = sizeof ty in
      let block = { size = size;
                    value = init_opt;
                  }
      in
      let obj = { lifetime = Some st.next_oid;
                  ty = ty;
                  storage_duration = SDautomatic;
                }
      in
      let addr = get_aligned_address (Nat_big_num.to_int align) st.next_address in
      let st' = { next_address = addr + size;
                  next_oid = st.next_oid + 1;
                  objects = IntMap.add st.next_oid obj st.objects;
                  storage = IntMap.add addr block st.storage;
                }
      in (PVobject st.next_oid, st')
    end

  (* An allocation function attempts to allocate the requested amount of
   * storage. If it is successful, it returns the address of the start of a
   * block of storage whose length in bytes is at least as large as the
   * requested size. The order, contiguity, and initial value of storage
   * allocated by successive calls to an allocation function are unspecified.
   * For an allocation function other than a reserved placement allocation
   * function (21.6.2.3), the pointer returned is suitably aligned so that it
   * can be converted to a pointer to any suitable complete object type
   * (21.6.2.1) and then used to access the object or array in the storage
   * allocated (until the storage is explicitly deallocated by a call to a
   * corresponding deallocation function). Even if the size of the space
   * requested is zero, the request can fail. If the request succeeds, the
   * value returned by a replaceable allocation function is a non-null pointer
   * value (7.11) p0 different from any previously returned value p1, unless
   * that value p1 was subsequently passed to a replaceable deallocation
   * function. Furthermore, for the library allocation functions in 21.6.2.1
   * and 21.6.2.2, p0 represents the address of a block of storage disjoint
   * from the storage for any other object accessible to the caller. The effect
   * of indirecting through a pointer returned from a request for zero size is
   * undefined.36
   *)
  (* C++ differs from C in requiring a zero request to return a non-null pointer.*)
  (* 23.10.12#4: [... newly written code is strongly encouraged to treat memory
   * allocated with these functions as though it were allocated with operator
   * new.] *)
  let allocate_region _ _ align iv_size =
    let size = Nat_big_num.to_int iv_size in
    Eff.modify begin fun st ->
      let block = { size = size;
                    value = None;
                  }
      in
      let addr = get_aligned_address (Nat_big_num.to_int align) st.next_address in
      let st' = { next_address = addr + size;
                  next_oid = st.next_oid + 1;
                  objects = st.objects;
                  storage = IntMap.add addr block st.storage;
                }
      in (PVstorage addr, st')
    end

  let undefined str = Eff.fail (MerrOther str)

  let kill = function
    | PVnull _ -> undefined "attempted to kill a null pointer"
    | PVend _ -> undefined "attempted to kill a pointer past the object"
    | PVinvalid -> undefined "attempted to kill an invalid pointer"
    | PVobject oid ->
      Eff.modify begin fun st ->
        match IntMap.find_opt oid st.objects with
        | None ->
          failwith "attempted to kill an object that it does not exist"
        | Some obj ->
          match obj.lifetime with
          | None ->
            failwith "attempted to kill an object that had its lifetime ended"
          | Some addr ->
            let st' = { st with storage = IntMap.remove addr st.storage } in
            ((), st')
      end
    | PVstorage addr ->
      Eff.modify begin fun st ->
        let st' = { st with storage = IntMap.remove addr st.storage } in
        ((), st')
      end

  let load loc cty pv =
    let get_value = function
      | None -> MVindeterminate cty
      | Some mv -> mv
    in
    Eff.get >>= fun st ->
    match pv with
    | PVnull _ -> undefined "attempt to load a null pointer"
    | PVend _ -> undefined "attempt to load a point past the end of an object"
    | PVinvalid -> undefined "attempt to load an invalid pointer"
    | PVobject oid ->
      begin match IntMap.find_opt oid st.objects with
        | None -> undefined "attempt to load an object that it does not exist"
        | Some obj ->
          match obj.lifetime with
          | None ->
            undefined "attempt to load an object that had its lifetime ended"
          | Some addr ->
            begin match IntMap.find_opt addr st.storage with
              | None -> failwith "panic: object is trying to load from a storage
                                  location that does not exist"
              | Some block -> return (Footprint, get_value block.value)
            end
      end
    | PVstorage addr ->
      (* TODO: What to do here? Create object? Start lifetime? Undef? *)
      undefined "TODO"


  let store loc cty pv mv = failwith "store"

  (* Pointer value constructors *)
  let null_ptrval cty = failwith "null_ptrval"
  let fun_ptrval sym = failwith "fun_ptrval"

  (* Operations on pointer values *)
  let eq_ptrval pv1 pv2 = failwith "pvops"
  let ne_ptrval pv1 pv2 = failwith "pvops"
  let lt_ptrval pv1 pv2 = failwith "pvops"
  let gt_ptrval pv1 pv2 = failwith "pvops"
  let le_ptrval pv1 pv2 = failwith "pvops"
  let ge_ptrval pv1 pv2 = failwith "pvops"
  let diff_ptrval cty pv1 pv2 = failwith "diff pv ops"

  let validForDeref_ptrval pv = failwith "validforderef"
  let isWellAligned_ptrval cty pv = failwith "iswellaligned"

  (* Casting operations *)
  let ptrcast_ival cty_original cty_target iv = failwith "ptrcast_ival"
  let intcast_ptrval cty_original aty_target pv = failwith "intcast"

  (* Pointer shifting constructors *)
  let array_shift_ptrval pv cty iv = failwith "array_shift"
  let member_shift_ptrval pv sym cid = failwith "member shift"

  let memcmp pv1 pv2 iv_size = failwith "memcmp"

  (* Integer value constructors *)
  let concurRead_ival aty sym = failwith "concurRead"
  let integer_ival n = failwith "integer_ival"
  let max_ival aty = failwith "max_ival"
  let min_ival aty = failwith "min_ival"
  let op_ival iop iv1 iv2 = failwith "op_ival"
  let offsetof_ival sym cid = failwith "offsetof"

  let sizeof_ival cty = failwith "sizeof"
  let alignof_ival cty = failwith "alignof"

  let bitwise_complement_ival aty iv = failwith "bitwise_complement"
  let bitwise_and_ival aty iv = failwith "bitwise_and"
  let bitwise_or_ival aty iv1 iv2 = failwith "bitwise_or"
  let bitwise_xor_ival aty iv1 iv2 = failwith "bitwise_xor"

  (* extracting in case concrete value *)
  let case_integer_value: (* TODO: expose more ctors *)
    integer_value ->
    (Nat_big_num.num -> 'a) ->
    (unit -> 'a) ->
    'a = fun iv f g -> failwith "case_int"

  let is_specified_ival iv = failwith "is_spec"

  (* Predicats on integer values *)
  let eq_ival m iv1 iv2 = failwith "ieq"
  let lt_ival m iv1 iv2 = failwith "ilt"
  let le_ival m iv1 iv2 = failwith "ile"

  let eval_integer_value iv = failwith "eval_int"

  (* Floating value constructors *)
  let zero_fval = 0.
  let str_fval = float_of_string

  (* Floating value destructors *)
  let case_fval x _ f = f x

  (* Predicates on floating values *)
  let op_fval = function
    | FloatAdd -> ( +. )
    | FloatSub -> ( -. )
    | FloatMul -> ( *. )
    | FloatDiv -> ( /. )
  let eq_fval = ( = )
  let lt_fval = ( < )
  let le_fval = ( <= )

  (* Integer <-> Floating casting constructors *)
  let fvfromint iv = failwith "fvfromint"
  let ivfromfloat aty x = failwith "ivfromfloat"

  (* Memory value constructors *)
  (*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
  let unspecified_mval cty = failwith "unspecified"
  let integer_value_mval aty iv = failwith "integer_value_mval"
  let floating_value_mval aty x = failwith "floating_value"
  let pointer_mval cty pv = failwith "pointer"
  let array_mval mv = failwith "array"
  let struct_mval sym members = failwith "struct"
  let union_mval sym cid mv = failwith "union"

  (* Memory value destructor *)
  let case_mem_value mv case_unspec case_conc_read case_iv case_fv case_pv
    case_array case_struct case_member = failwith "case_mem"

  (* For race detection *)
  let sequencePoint = return ()

  (* pretty printing *)
  let pp_pointer_value pv = failwith "pp pointer"
  let pp_integer_value iv = failwith "iv pointer"
  let pp_integer_value_for_core iv = failwith "pp int"
  let pp_mem_value m = failwith "pp mem"
  let pp_pretty_pointer_value pv = failwith "pp pretty pv"
  let pp_pretty_integer_value fmt iv = failwith "pp pretty int"
  let pp_pretty_mem_value fmt mv = failwith "pp pretty mv"

  (* JSON serialisation *)
  let serialise_mem_state mem = failwith "serialise mem state"
end

include CppMemModel
