open Memory_model

module ND = Nondeterminism
module MC = Mem_common

open Caesium
open Ctype

let name : string = "RefinedC's Caesium memory model"

type pointer_value =
  | PVnull of Ctype.ctype
  | PVptr of Caesium.loc
  | PVfun of Symbol.sym

type integer_value = Caesium.int_repr

type floating_value = float

type mem_value =
  Ctype.ctype * Caesium.value

type mem_iv_constraint = integer_value MC.mem_constraint
let cs_module = (module struct
open Mem_common
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
  let rec eval_cs = function
    | MC_empty ->
        true
    | MC_eq (ival1, ival2) ->
        Nat_big_num.equal (int_repr_to_Z ival1) (int_repr_to_Z ival2)
    | MC_le (ival1, ival2) ->
        Nat_big_num.less_equal (int_repr_to_Z ival1) (int_repr_to_Z ival2)
    | MC_lt (ival1, ival2) ->
        Nat_big_num.less (int_repr_to_Z ival1) (int_repr_to_Z ival2)
    | MC_in_device _ ->
        failwith "TODO: Caesium, with_constraints: MC_in_device"
    | MC_or (cs1, cs2) ->
        eval_cs cs1 || eval_cs cs2
    | MC_conj css ->
        List.for_all (fun z -> eval_cs z) css
    | MC_not cs ->
        not (eval_cs cs)
  in
  Eff (fun b -> ma (b && eval_cs cs))
end : Constraints with type t = mem_iv_constraint)

type footprint = FOOTPRINT
let do_overlap _ _ =
  (* TODO: no unseq-race detection for now *)
  false

type mem_state = {
  next_alloc_id: Caesium.alloc_id;
  last_address: Caesium.addr;
  state: Caesium.state;
}

let initial_mem_state: mem_state =
  { next_alloc_id= Z.zero
  ; last_address= Z.of_int 0xFFFFFFFF
  ; state= Caesium.initial_state }

type 'a memM =
  ('a, string, MC.mem_error, integer_value MC.mem_constraint, mem_state) ND.ndM
let return: 'a -> 'a memM =
  ND.nd_return
let bind: 'a memM -> ('a -> 'b memM) -> 'b memM =
  ND.nd_bind

let fail err =
  let loc = match err with
    | MC.MerrAccess (loc, _, _)
    | MerrWriteOnReadOnly loc
    | MerrUndefinedFree (loc, _) ->
        loc
    | MerrOutsideLifetime _
    | MerrInternal _
    | MerrOther _
    | MerrPtrdiff
    | MerrUndefinedRealloc
    | MerrIntFromPtr
    | MerrPtrFromInt
    | MerrPtrComparison
    | MerrArrayShift
    | MerrWIP _ ->
        Location_ocaml.other "Caesium" in
  let open Nondeterminism in
  match MC.undefinedFromMem_error err with
    | Some ubs ->
        kill (Undef0 (loc, ubs))
    | None ->
        kill (Other err)

let (>>=) = bind

let mk_unspecified ty : mem_value =
  (ty, List.init (Common.sizeof ty) (fun _ -> Caesium.MPoison))

let pick_location size align : Caesium.loc memM =
  ND.nd_get >>= fun st ->
  let alloc_id = st.next_alloc_id in
  begin
    let open Nat_big_num in
    let z = sub st.last_address size in
    let (q,m) = quomod z align in
    let z' = sub z (if less q zero then negate m else m) in
    if less_equal z' zero then
      fail (MC.MerrOther "Caesium.allocator: failed (out of memory)")
    else
      return z'
  end >>= fun addr ->
    ND.nd_put { st with
      next_alloc_id= Nat_big_num.succ alloc_id;
      last_address= addr
    } >>= fun () ->
    return (Some alloc_id, addr)

(* Memory actions *)
(* NOTE for Rodolphe: the spec of this actions for Core is that if an init
   value is provided, the newly allocated object is set to read-only.Nat_big_num *)
let allocate_object tid pref align_ival ty init_opt =
  let al = Caesium.int_repr_to_Z align_ival in
  let sz = Z.of_int (Common.sizeof ty) in
  let v  = snd (Option.value init_opt ~default:(mk_unspecified ty)) in
  pick_location sz al >>= fun loc ->
  ND.nd_get >>= fun st ->
  match Caesium.alloc_new_block loc v st.state.st_heap with
    | None ->
        assert false
    | Some heap_st' ->
        ND.nd_put { st with state = { st.state with st_heap = heap_st' } } >>= fun () ->
        return (PVptr loc)


let allocate_region:
     MC.thread_id      (* the allocating thread *)
  -> Symbol.prefix  (* symbols coming from the Core/C program, for debugging purpose *)
  -> integer_value  (* alignment constraint *)
  -> integer_value  (* size *)
  -> pointer_value memM =
  fun _ _ _ _ ->
    return (failwith "WIP: allocate_region")
    (* return (PVnull (Ctype ([], Void))) (* TODO *) *)

let kill loc is_dyn = function
  | PVnull _ ->
      if Switches.(has_switch SW_forbid_nullptr_free) then
        fail (MerrOther "attempted to kill with a null pointer")
      else
        return ()
  | PVfun _ ->
      fail (MerrOther "attempted to kill with a function pointer")
  | PVptr loc ->
      (* TODO: if [is_dym], we must fail if the alloc is not dynamics *)
      (* TODO: if [is_dym] and the alloc is dead, we raise UB *)
        (* begin match Caesium.free_block loc with
        |
      end *)
      failwith "WIP: Caesium.kill"

let update_heap f error =
  ND.nd_get >>= fun st ->
  match f st.state.st_heap.hs_heap with
    | None ->
        error
    | Some heap' ->
        let st_heap = { st.state.st_heap with hs_heap = heap' } in
        ND.nd_put { st with state = { st.state with st_heap }}

let read_heap f error =
  ND.nd_get >>= fun st ->
  match f st.state.st_heap.hs_heap with
    | None ->
        error
    | Some (z, heap') ->
        let st_heap = { st.state.st_heap with hs_heap = heap' } in
        ND.nd_put { st with state = { st.state with st_heap }} >>= fun () ->
        return z

let load loc ty  ptrval =
  (* TODO do atomic based on [ty] *)
  let sz = Common.sizeof ty in
  match ptrval with
    | PVnull _ ->
      fail (MC.MerrAccess (loc, MC.LoadAccess, MC.NullPtr))
    | PVfun _ ->
      fail (MC.MerrAccess (loc, MC.LoadAccess, MC.FunctionPtr))
    | PVptr loc ->
        update_heap
          (Caesium.na_prepare_read loc sz)
          (fail (MC.MerrOther "in load(), na_prepare_read failed")) >>= fun () ->
        read_heap
          (Caesium.na_read loc sz)
          (fail (MC.MerrOther "in load(), na_read failed")) >>= fun z ->
        return (FOOTPRINT, (ty, z))

let store loc ty is_locking ptrval mval =
  (* TODO do atomic based on [ty] *)
  match ptrval with
    | PVnull _ ->
      fail (MC.MerrAccess (loc, MC.StoreAccess, MC.NullPtr))
    | PVfun _ ->
      fail (MC.MerrAccess (loc, MC.StoreAccess, MC.FunctionPtr))  
    | PVptr loc ->
        let (val_ty, bs) = mval in
        assert (AilTypesAux.are_compatible
                 (Ctype.no_qualifiers, ty)
                 (Ctype.no_qualifiers, val_ty) );
        update_heap
          (Caesium.na_prepare_write loc bs)
          (fail (MC.MerrOther "in store(), na_prepare_write failed")) >>= fun () ->
        update_heap
          (Caesium.na_write loc bs)
          (fail (MC.MerrOther "in store(), na_write failed")) >>= fun () ->
        return FOOTPRINT


(* Pointer value constructors *)
let null_ptrval ty =
  PVnull ty

let fun_ptrval sym =
  PVfun sym

(*TODO: revise that, just a hack for codegen*)
let concrete_ptrval i addr =
  assert false (* TODO *)
let case_ptrval (* ptrval f_null f_fptr f_ptr f_unspec =
  match ptrval with
    | PVnull ty ->
        f_null ty
        *)
  : pointer_value ->
 (* null pointer *) (Ctype.ctype -> 'a) ->
 (* function pointer *) (Symbol.sym -> 'a) ->
 (* concrete pointer *) (Nat_big_num.num option -> Nat_big_num.num -> 'a) ->
 (* unspecified value *) (unit -> 'a) -> 'a =
   (* TODO *)
  fun _ _ _ _ _ -> assert false

let case_funsym_opt: mem_state -> pointer_value -> Symbol.sym option =
  fun _ _ -> assert false (* TODO *)

(* Operations on pointer values *)
let eq_ptrval ptrval1 ptrval2 : bool memM =
  ND.nd_get >>= fun st ->
  match ptrval1, ptrval2 with
    | PVnull _, PVnull _ ->
      return true
    | PVnull _, _
    | _, PVnull _ ->
        return false
    | PVptr loc1, PVptr loc2 ->
        begin
          match Caesium.(ptr_eq st.state.st_heap loc1 loc2) with
          | None    -> assert false (* TODO *)
          | Some(b) -> return b
        end
    | PVfun sym1, PVfun sym2 ->
        return (Symbol.symbolEquality sym1 sym2)
    | PVfun _, PVptr _
    | PVptr _, PVfun _ ->
        return false
  
let ne_ptrval ptrval1 ptrval2 =
  eq_ptrval ptrval1 ptrval2 >>= fun b ->
  return (not b)
let lt_ptrval: pointer_value -> pointer_value -> bool memM =
  fun _ _ -> assert false (* TODO *)
let gt_ptrval: pointer_value -> pointer_value -> bool memM =
  fun _ _ -> assert false (* TODO *)
let le_ptrval: pointer_value -> pointer_value -> bool memM =
  fun _ _ -> assert false (* TODO *)
let ge_ptrval: pointer_value -> pointer_value -> bool memM =
  fun _ _ -> assert false (* TODO *)
let diff_ptrval: Ctype.ctype -> pointer_value -> pointer_value -> integer_value memM =
fun _ _ _ -> assert false (* TODO *)

let update_prefix: (Symbol.prefix * mem_value) -> unit memM =
  fun _ -> assert false (* TODO *)
let prefix_of_pointer: pointer_value -> string option memM =
  fun _ -> return None (* TODO *)

let validForDeref_ptrval: Ctype.ctype -> pointer_value -> bool memM =
  fun _ v ->
  match v with
  | PVnull _
  | PVfun _ -> return false
  | PVptr l  -> return true (* FIXME *)

let isWellAligned_ptrval: Ctype.ctype -> pointer_value -> bool memM =
  fun _ _ -> assert false (* TODO *)

(* Casting operations *)
(* the first ctype is the original integer type, the second is the target referenced type *)
let ptrcast_ival: Ctype.ctype -> Ctype.ctype -> integer_value -> pointer_value memM =
  fun _ _ i -> return (PVptr(Caesium.int_repr_to_loc i))

(* the first ctype is the original referenced type, the integerType is the target integer type *)
let intcast_ptrval: Ctype.ctype -> Ctype.integerType -> pointer_value -> integer_value memM =
  fun _ _ pv ->
  match pv with
  | PVptr l  -> return (IRLoc l)
  | PVnull _ -> assert false (* TODO *)
  | PVfun _ -> assert false (* TODO should be UB I think *)

let offsetof_ival tagDefs tag_sym memb_ident =
  let (xs, _) = Common.offsetsof tagDefs tag_sym in
  let pred (ident, _, _) =
    Common.ident_equal ident memb_ident in
  match List.find_opt pred xs with
    | Some (_, _, offset) ->
        IRInt (Z.of_int offset)
    | None ->
        failwith "Caesium.offsetof_ival: invalid memb_ident"

(* Pointer shifting constructors *)
let array_shift_ptrval ptrval ty ival =
  match ptrval with
    | PVnull _ ->
        failwith "TODO: array_shift_ptrval"
    | PVptr (alloc_id_opt, addr) ->
        let sz = Z.of_int (Common.sizeof ty) in
        let addr' = Z.add addr (Z.mul sz (Caesium.int_repr_to_Z ival)) in
        (* NOTE Rodolphe: here we don't have any overflow check here
           (eff_array_shift_ptrval is the one doing it, when using the strict ISO switch) *)
        Printf.fprintf stderr "Shifting %a to %a\n%!"
          Caesium.pp_loc (alloc_id_opt, addr)
          Caesium.pp_loc (alloc_id_opt, addr');
        PVptr (alloc_id_opt, addr')
    | PVfun _ ->
        assert false

let member_shift_ptrval ptrval tag_sym memb_ident =
  let offset = offsetof_ival (Tags.tagDefs ()) tag_sym memb_ident in
  match ptrval with
    | PVnull ty ->
        (* NOTE: see the concrete model, gcc-torture accepts this behaviour*)
        if Nat_big_num.(equal zero (Caesium.int_repr_to_Z offset)) then
          PVnull ty
        else
          PVptr (Caesium.int_repr_to_loc offset)
    | PVfun _ ->
        failwith "Caesium.member_shift_ptrval, PVfun"
    | PVptr (alloc_id_opt, addr) ->
        PVptr (alloc_id_opt, Z.add addr (Caesium.int_repr_to_Z offset))

let eff_array_shift_ptrval:  pointer_value -> Ctype.ctype -> integer_value -> pointer_value memM =
  fun _ _ _ -> assert false (* TODO *)

let memcpy: pointer_value -> pointer_value -> integer_value -> pointer_value memM =
  fun _ _ _ -> assert false (* TODO *)
let memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM =
  fun _ _ _ -> assert false (* TODO *)
let realloc: MC.thread_id -> integer_value -> pointer_value -> integer_value -> pointer_value memM =
  fun _ _ _ _ -> assert false (* TODO *)

let va_start: (Ctype.ctype * pointer_value) list -> integer_value memM =
  fun _ -> assert false (* TODO *)
let va_copy: integer_value -> integer_value memM =
  fun _ -> assert false (* TODO *)
let va_arg: integer_value -> Ctype.ctype -> pointer_value memM =
  fun _ _ -> assert false (* TODO *)
let va_end: integer_value -> unit memM =
  fun _ -> assert false (* TODO *)
let va_list: Nat_big_num.num -> ((Ctype.ctype * pointer_value) list) memM =
  fun _ -> assert false (* TODO *)


(* Integer value constructors *)
let to_int_type (ity: Ctype.integerType) : Caesium.int_type =
  let impl = Ocaml_implementation.get () in
  let sz = match impl.sizeof_ity ity with
    | Some z -> z
    | None   -> failwith "the Caesium memory model requires a complete implementation (to_int_type)" in
  let ret =
    { it_bytes_per_int_log= Z.(log2 (of_int sz))
    ; it_signed= impl.is_signed_ity ity } in
  (* Printf.printf "to_int_type ==> { it_bytes_per_int_log= %d, it_signed= %s }\n"
    ret.it_bytes_per_int_log
    (if ret.it_signed then "true" else "false"); *)
  ret

let concurRead_ival: Ctype.integerType -> Symbol.sym -> integer_value =
  fun _ _ -> assert false (* TODO *)
let integer_ival n =
  IRInt n

let max_ival ity =
  let open Nat_big_num in
  IRInt begin
    match (Ocaml_implementation.get ()).sizeof_ity ity with
      | Some n ->
          let signed_max =
            sub (pow_int (of_int 2) (8*n-1)) (of_int 1) in
          let unsigned_max =
            sub (pow_int (of_int 2) (8*n)) (of_int 1) in
          begin match ity with
            | Char ->
                if (Ocaml_implementation.get ()).is_signed_ity Char then
                  signed_max
                else
                  unsigned_max
            | Bool ->
                (* TODO: not sure about this (maybe it should be 1 and not 255? *)
                unsigned_max
            | Size_t
            | Wchar_t (* TODO: it is implementation defined if unsigned *)
            | Unsigned _ ->
                unsigned_max
            | Ptrdiff_t
            | Wint_t (* TODO *)
            | Signed _ ->
                signed_max
            | Enum _ ->
                (* TODO: hack, assuming like int *)
                sub (pow_int (of_int 2) (8*4-1)) (of_int 1)
          end
      | None ->
          failwith "the Caesium memory model requires a complete implementation MAX"
    end

let min_ival ity =
  let open Nat_big_num in
  IRInt begin match ity with
    | Char ->
        if (Ocaml_implementation.get ()).is_signed_ity Char then
          negate (pow_int (of_int 2) (8-1))
        else
          zero
    | Bool
    | Size_t
    | Wchar_t (* TODO: it is implementation defined if unsigned *)
    | Wint_t
    | Unsigned _ ->
        (* all of these are unsigned *)
        zero
    | Ptrdiff_t
    | Signed _ ->
        (* and all of these are signed *)
        begin match (Ocaml_implementation.get ()).sizeof_ity ity with
          | Some n ->
              negate (pow_int (of_int 2) (8*n-1))
          | None ->
              failwith "the Caesium memory model requires a complete implementation MIN"
        end
    | Enum _ ->
        (* TODO: hack, assuming like int *)
        negate (pow_int (of_int 2) (8*4-1))
  end

  let op_ival op ival1 ival2 =
  let open MC in
  let op = match op with
    | IntAdd   -> Z.add
    | IntSub   -> Z.sub
    | IntMul   -> Z.mul
    | IntDiv   -> fun x y -> if Z.(equal y zero) then Z.zero else Z.div x y
    | IntRem_t -> Nat_big_num.integerRem_t
    | IntRem_f -> Nat_big_num.integerRem_f
    | IntExp   -> fun x y -> Nat_big_num.pow_int x (Nat_big_num.to_int y) in
  IRInt (op (int_repr_to_Z ival1) (int_repr_to_Z ival2))

let sizeof_ival ty =
  IRInt (Z.of_int (Common.sizeof ty))

let alignof_ival ty =
  IRInt (Z.of_int (Common.alignof ty))

let bitwise_complement_ival _ ival =
  let n = Caesium.int_repr_to_Z ival in
  IRInt (Nat_big_num.(sub (negate n) (of_int 1)))
  let bitwise_and_ival _ ival1 ival2 =
  let n1 = Caesium.int_repr_to_Z ival1 in
  let n2 = Caesium.int_repr_to_Z ival2 in
  IRInt (Nat_big_num.bitwise_and n1 n2)
let bitwise_or_ival _ ival1 ival2 =
  let n1 = Caesium.int_repr_to_Z ival1 in
  let n2 = Caesium.int_repr_to_Z ival2 in
  IRInt (Nat_big_num.bitwise_or n1 n2)
let bitwise_xor_ival _ ival1 ival2 =
  let n1 = Caesium.int_repr_to_Z ival1 in
  let n2 = Caesium.int_repr_to_Z ival2 in
  IRInt (Nat_big_num.bitwise_xor n1 n2)

let case_integer_value: (* TODO: expose more ctors *)
  integer_value ->
  (Nat_big_num.num -> 'a) ->
  (unit -> 'a) ->
  'a =
  fun _ _ _ -> assert false (* TODO *)

let is_specified_ival: integer_value -> bool =
  fun _ -> assert false (* TODO *)

(* Predicats on integer values *)
let eq_ival _ ival1 ival2 =
  Some (Z.equal (Caesium.int_repr_to_Z ival1) (Caesium.int_repr_to_Z ival2))
let lt_ival _ ival1 ival2 =
  Some (Z.lt (Caesium.int_repr_to_Z ival1) (Caesium.int_repr_to_Z ival2))
let le_ival _ ival1 ival2 =
  Some (Z.leq (Caesium.int_repr_to_Z ival1) (Caesium.int_repr_to_Z ival2))

let eval_integer_value ival =
  Some (int_repr_to_Z ival)

(* Floating value constructors *)
let zero_fval: floating_value =
  0.0
let one_fval: floating_value =
  1.0
let str_fval str =
  Stdlib.Float.of_string str


(* Floating value destructors *)
let case_fval: floating_value -> (unit -> 'a) -> (float -> 'a) -> 'a =
  fun _ _ _ -> assert false (* TODO *)

(* Predicates on floating values *)
let op_fval: MC.floating_operator -> floating_value -> floating_value -> floating_value =
  fun _ _ _-> assert false (* TODO *)
let eq_fval: floating_value -> floating_value -> bool =
  fun _ _ -> assert false (* TODO *)
let lt_fval: floating_value -> floating_value -> bool =
  fun _ _ -> assert false (* TODO *)
let le_fval: floating_value -> floating_value -> bool =
  fun _ _ -> assert false (* TODO *)

(* Integer <-> Floating casting constructors *)
let fvfromint: integer_value -> floating_value =
  fun _ -> assert false (* TODO *)
let ivfromfloat: Ctype.integerType -> floating_value -> integer_value =
  fun _ _ -> assert false (* TODO *)



(* Memory value constructors *)
(*symbolic_mval: Symbolic.symbolic mem_value pointer_value -> mem_value *)
let unspecified_mval ty : mem_value =
  (ty, List.init (Common.sizeof ty) (fun _ -> MPoison))

let integer_value_mval ity ival =
  match val_of_int_repr ival (to_int_type ity) with
    | Some bs ->
        (mk_ctype_integer ity, bs)
    | None ->
        failwith "TODO: not sure what to do here"

let floating_value_mval: Ctype.floatingType -> floating_value -> mem_value =
  fun _ _ -> assert false (* TODO *)
let pointer_mval ref_ty ptrval =
  let ty = mk_ctype_pointer no_qualifiers ref_ty in
  (ty, match ptrval with
    | PVnull _ ->
        (* TODO Rodolphe: not sure about uintptr_t *)
        begin match Caesium.(val_of_Z Z.zero uintptr_t) with
          | None ->
              assert false
          | Some z ->
              z
        end
    | PVptr loc ->
        val_of_loc loc
    | PVfun (Symbol.Symbol (_, n, _)) ->
        begin match Caesium.(val_of_Z (Z.of_int n) uintptr_t) with
          | None ->
              failwith "Caesium.pointer_mval PVfun"
          | Some z ->
               z
        end 
  )

let array_mval mvals =
  match mvals with
    | [] ->
        assert false
    | (elem_ty, mval) :: xs ->
        assert (List.for_all (fun z -> Ctype.ctypeEqual elem_ty (fst z)) xs);
        (Ctype ([], Array (elem_ty, None)), List.fold_left (fun acc (_, z) -> acc @ z) [] mvals)

let struct_mval tag_sym (membs: (Symbol.identifier * Ctype.ctype * mem_value) list) : mem_value =
  let struct_ty = Ctype ([], Struct tag_sym) in
  let (offs, last_off) = Common.offsetsof (Tags.tagDefs ()) tag_sym in
  let final_pad = Common.sizeof struct_ty - last_off in
  let (_, bs) =
    List.fold_left2 begin fun (last_off, acc) (ident, ty, off) (_, _, (membs_ty, membs_bs)) ->
      let pad = off - last_off in
      (off + Common.sizeof membs_ty, acc @ List.init pad (fun _ -> Caesium.MPoison) @ membs_bs)
    end (0, []) offs membs in
  (struct_ty, bs @ List.init final_pad (fun _ -> Caesium.MPoison))

let union_mval: Symbol.sym -> Symbol.identifier -> mem_value -> mem_value =
  fun _ _ _ -> assert false (* TODO *)

(* Memory value destructor *)
let string_of_mbytes xs =
  let aux = function
    | MByte n ->
        "mbyte(" ^ string_of_int n ^ ")"
    | MPtrFrag ((_, addr), i) ->
        "mptrfrag(" ^ Z.to_string addr ^ ", " ^ string_of_int i ^ ")"
    | MPoison ->
        "mpoison" in
  "[" ^ String.concat "; " (List.map aux xs) ^ "]"

let case_mem_value (ty, bs) f_unspec _ f_int f_float f_ptr f_array f_struct f_union =
  if List.exists (function MPoison -> true | _ -> false) bs then
    (* NOTE Rodolphe: making the value unspecified if one byte is poison,
       is that correct for Caesium?*)
    f_unspec ty
  else match ty with
    | Ctype.(Ctype (_, Basic (Integer ity))) ->
        let int_ty = to_int_type ity in
        begin match Caesium.val_to_int_repr bs int_ty with
          | None ->
              Printf.printf "==> %s\n" (string_of_mbytes bs);
              failwith "case_mem_value, integer, None"
          | Some ival ->
              f_int ity ival
        end
    | Ctype.(Ctype (_, Pointer(_,ty))) ->
        begin match Caesium.val_to_loc bs with
          | None ->
              Printf.printf "==> %s\n" (string_of_mbytes bs);
              failwith "case_mem_value, pointer, None"
          | Some l ->
              f_ptr ty (PVptr l)
        end
    | _ ->
        failwith ("case_mem_value ==> " ^ String_core_ctype.string_of_ctype ty)

(*
  Ctype.ctype * Caesium.value

  
  :
  mem_value ->
  (Ctype.ctype -> 'a) -> (* unspecified case *)
  (Ctype.integerType -> Symbol.sym -> 'a) -> (* concurrency read case *)
  (Ctype.integerType -> integer_value -> 'a) ->
  (Ctype.floatingType -> floating_value -> 'a) ->
  (Ctype.ctype -> pointer_value -> 'a) ->
  (mem_value list -> 'a) ->
  (Symbol.sym -> (Symbol.identifier * Ctype.ctype * mem_value) list -> 'a) ->
  (Symbol.sym -> Symbol.identifier -> mem_value -> 'a) ->
  'a =
  fun _ _ _ _ _ _ _ _ _ -> failwith "case_mem_value" (* TODO *)
*)

(* For race detection *)
let sequencePoint: unit memM =
  return ()

(* pretty printing *)
open PPrint
open Pp_prelude
let pp_pointer_value = function
  | PVnull ty ->
      !^ "null" ^^ parens (Pp_core_ctype.pp_ctype ty)
  | PVptr (alloc_id_opt, addr) ->
    let str_alloc_id = match alloc_id_opt with
      | None ->
          "@none"
      | Some alloc_id ->
          "@" ^ Z.to_string alloc_id in
    parens (!^ str_alloc_id ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string addr))))
  | PVfun sym ->
      !^ "funptr" ^^ parens (!^ (Pp_symbol.to_string sym))

let pp_integer_value = function
  | Caesium.IRInt n ->
      !^ (Z.to_string n)
  | Caesium.IRLoc loc ->
      (* TODO: ahem *)
      !^ "loc" ^^ parens (pp_pointer_value (PVptr loc))
let pp_integer_value_for_core ival =
  !^ (Z.to_string (Caesium.int_repr_to_Z ival))
let pp_mem_value (ty, bs) =
  parens (Pp_core_ctype.pp_ctype ty ^^ colon ^^^ !^ (string_of_mbytes bs))
let pp_pretty_pointer_value: pointer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_pretty_integer_value: Boot_printf.formatting -> integer_value -> PPrint.document =
  fun _ -> assert false (* TODO *)
let pp_pretty_mem_value: Boot_printf.formatting -> mem_value -> PPrint.document =
  fun _ -> assert false (* TODO *)

let serialise_mem_state: Digest.t -> mem_state -> Json.json =
  fun _ _ -> assert false (* TODO *)


let string_of_integer_value: integer_value -> string =
  fun _ -> assert false (* TODO *)
let string_of_mem_value (ty, bs) =
  "(" ^ "TODO_caesium_value" ^ ": " ^ String_core_ctype.string_of_ctype ty ^ ")"
