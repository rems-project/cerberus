module N = Nat_big_num

open Ctype
open Memory_model
module MC = Mem_common

module L = struct
  include List
  include Lem_list
end

(* INTERNAL: allocation_id *)
type allocation_id =
  N.num

(* INTERNAL: provenance *)
type provenance =
  | Prov_empty
  | Prov_some of allocation_id

type address =
  N.num

(* INTERNAL: location *)
type location =
  provenance * address


(* INTERNAL: Abstract bytes *)
module AbsByte = struct
  (* 'Memory byte' in the paper *)
  type t = {
    prov: provenance;
    value: char option; (* None case is 'unspec' from the paper *)
    ptrfrag_idx: int option; (* None case is 'none' from the paper *)
  }

end


(* EXTERNAL *)
let name = "VIP memory model"

(* EXTERNAL *)
type pointer_value =
  | PVnull
  | PVloc of location
  | PVfunptr of Symbol.sym

(* EXTERNAL *)
type integer_value =
  | IVloc of location
  | IVint of N.num

(* EXTERNAL *)
type floating_value =
  | TODO_floating_value


  (* INTERNAL *)
let ival_to_int: integer_value -> N.num = function
  | IVloc (_, z) -> z
  | IVint z      -> z


(* EXTERNAL *)
type mem_value =
  | MVunspecified of ctype
  | MVinteger of integerType * integer_value
(* | MVfloating of floatingType * floating_value *)
  | MVpointer of ctype * pointer_value
  | MVarray of mem_value list
  | MVstruct of Symbol.sym (*struct/union tag*) * (Symbol.identifier (*member*) * ctype * mem_value) list
(* | MVunion of Symbol.sym (*struct/union tag*) * Symbol.identifier (*member*) * mem_value *)

type mem_iv_constraint = integer_value MC.mem_constraint
let cs_module = (module struct
open MC
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
        N.equal (ival_to_int ival1) (ival_to_int ival2)
    | MC_le (ival1, ival2) ->
        N.less_equal (ival_to_int ival1) (ival_to_int ival2)
    | MC_lt (ival1, ival2) ->
        N.less (ival_to_int ival1) (ival_to_int ival2)
    | MC_in_device _ ->
        false (* no device memory *)
    | MC_or (cs1, cs2) ->
        eval_cs cs1 || eval_cs cs2
    | MC_conj css ->
        List.for_all (fun z -> eval_cs z) css
    | MC_not cs ->
        not (eval_cs cs)
  in
  Eff (fun b -> ma (b && eval_cs cs))
end : Constraints with type t = mem_iv_constraint)

type footprint =
  FOOTPRINT

let do_overlap _ _ =
  (* No unsequenced races detection *)
  false


module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = N.compare
end)

type allocation = {
  base: address;
  length: N.num; (* INVARIANT >= 0 *)
  killed: bool;
}

type mem_state = {
  allocations: allocation IntMap.t; (* 'A' in the paper *)
  bytemap: AbsByte.t IntMap.t;      (* 'M' in the paper *) (* INVARIANT dom(M) \subset valid_addresses *)
  
  funptrmap: (Digest.t * string) IntMap.t;

  (* implementation stuff not visible in paper's math *)
  next_alloc_id: allocation_id;
  last_address: address;

  (* Web user-interface stuff *)
  last_used: allocation_id option;
}

let initial_mem_state: mem_state =
  { allocations= IntMap.empty
  ; bytemap= IntMap.empty
  ; funptrmap= IntMap.empty
  ; next_alloc_id= Z.zero
  ; last_address= Z.of_int 0xFFFFFFFF
  ; last_used= None }

type 'a memM =
  ('a, string, MC.mem_error, integer_value MC.mem_constraint, mem_state) Nondeterminism.ndM

let return: 'a -> 'a memM =
  Nondeterminism.nd_return
let bind: 'a memM -> ('a -> 'b memM) -> 'b memM =
  Nondeterminism.nd_bind

let (>>=) = bind
let get = Nondeterminism.nd_get
let put = Nondeterminism.nd_put
let update = Nondeterminism.nd_update

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
        Location_ocaml.other "VIP WIP error" in
  let open Nondeterminism in
  match MC.undefinedFromMem_error err with
    | Some ubs ->
        kill (Undef0 (loc, ubs))
    | None ->
        kill (Other err)

(* ********************************************************************************************* *)
(* let is_live_address allocs addr =
   *)
let allocator (size: N.num) (align: N.num) : (allocation_id * address) memM =
  get >>= fun st ->
  let alloc_id = st.next_alloc_id in
  begin
    let open N in
    let z = sub st.last_address size in
    let (q,m) = quomod z align in
    let z' = sub z (if less q zero then negate m else m) in
    if less_equal z' zero then
      fail (MerrOther "Concrete.allocator: failed (out of memory)")
    else
      return z'
  end >>= fun addr ->
  put { st with
    next_alloc_id= Nat_big_num.succ alloc_id;
    last_used= Some alloc_id;
    last_address= addr
  } >>= fun () ->
  return (alloc_id, addr)

let set_range bs base length f_init =
  let max = Z.(base + length - one) in
  let rec aux acc i =
    let acc = IntMap.add i (f_init i) acc in
    if i <= max then
      aux acc (Z.succ i)
    else
      acc in
  aux bs base

let lookup_alloc alloc_id : allocation memM =
  get >>= fun st ->
  match IntMap.find_opt alloc_id st.allocations with
    | None ->
        fail (MC.MerrInternal "lookup_alloc failed")
    | Some alloc ->
        return alloc


(* "addr \not\in [a_i .. a_i + n_i]" *)
let in_bounds addr alloc =
  N.less_equal alloc.base addr && N.(less_equal addr (add alloc.base alloc.length))


let allocate_object tid pref al_ival ty init_opt : pointer_value memM =
  let n = Z.of_int (Common.sizeof ty) in
  allocator n (ival_to_int al_ival) >>= fun (alloc_id, addr) ->
  update (fun st ->
    { st with
      allocations= IntMap.add alloc_id {base= addr; length= n; killed= false} st.allocations;
      bytemap= set_range st.bytemap addr n (fun _ -> AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None})
    }
  ) >>= fun () ->
  return (PVloc (Prov_some alloc_id, addr))


let allocate_region tid pref al_ival sz_ival : pointer_value memM =
  failwith "TODO VIP.allocate_region"

let kill loc is_dyn ptrval : unit memM =
  match ptrval with
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          (* TODO: this should be a Cerberus internal error *)
          fail (MerrOther "attempted to kill dead allocation")
        else
          update (fun st ->
            { st with allocations= IntMap.add alloc_id {alloc with killed= true} st.allocations}
          )
    | _ ->
        fail (MerrOther "VIP.kill() invalid pointer value (NULL, @empty prov, or funptr)")


(* [a .. a + sizeof(ty) − 1] ⊆ [a_i .. a_i + n_1 - 1] *)
let check_bounds addr ty alloc =
     N.less_equal alloc.base addr
  && N.less_equal (N.add addr (N.pred (N.of_int (Common.sizeof ty))))
                  (N.add alloc.base (N.pred alloc.length))


let fetch_bytes bytemap base_addr n_bytes : AbsByte.t list =
    List.map (fun addr ->
      match IntMap.find_opt addr bytemap with
        | Some b ->
            b
        | None ->
            failwith "AbsByte.{ prov= Prov_empty; value= None; ptrfrag_idx= None }"
    ) (List.init n_bytes (fun z ->
           (* NOTE: the reversal in the offset is to model
              little-endianness *)
(*           let offset = n_bytes - 1 - z in *)
         let offset = z in
         N.(add base_addr (of_int offset))
       ))

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

let rec repr funptrmap mval : ((Digest.t * string) IntMap.t * AbsByte.t list) =
  let ret bs = (funptrmap, bs) in
  match mval with
    | MVunspecified ty ->
        ret @@ List.init (Common.sizeof ty)
          (fun _ -> AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None})
    | MVinteger (ity, ival) ->
        let (prov, z) =
          match ival with
            | IVint z ->
                (Prov_empty, z)
            | IVloc (prov, z) ->
                (prov, z) in
        ret @@ List.map (fun value -> AbsByte.{prov; value; ptrfrag_idx= None}) begin
          bytes_of_int
            (AilTypesAux.is_signed_ity ity)
            (Common.sizeof (Ctype ([], Basic (Integer ity)))) z
        end
    (* | MVfloating (fty, fval) ->
        ret @@ List.map (AbsByte.v Prov_none) begin
          bytes_of_int
            true (* TODO: check that *)
            (sizeof (Ctype ([], Basic (Floating fty)))) (N.of_int64 (Int64.bits_of_float fval))
        end *)
    | MVpointer (_, ptrval) ->
        Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the sizeof pointers to 8 bytes");
        let ptr_size = match (Ocaml_implementation.get ()).sizeof_pointer with
          | None ->
              failwith "the VIP memory model requires a complete implementation"
          | Some z ->
              z in
        begin match ptrval with
          | PVnull ->
              Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the representation of all NULL pointers to be 0x0");
              ret @@ List.init ptr_size
                (fun _ -> AbsByte.{prov= Prov_empty; value= (Some '\000'); ptrfrag_idx= None})
          | PVfunptr (Symbol.Symbol (file_dig, n, opt_name)) ->
              (* TODO: *)
              failwith "TODO repr funptr"
              (* (begin match opt_name with
                | Some name -> IntMap.add (N.of_int n) (file_dig, name) funptrmap
                | None -> funptrmap
              end, List.map (AbsByte.v prov) begin
                bytes_of_int
                    false
                    ptr_size (N.of_int n)
                end) *)
          | PVloc (prov, addr) ->
              ret @@ List.mapi (fun i value -> AbsByte.{prov; value; ptrfrag_idx= Some i})
                begin
                  bytes_of_int
                    false (* we model address as unsigned *)
                    ptr_size addr
                end
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
        let padding_byte _ = AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None} in
        let (offs, last_off) = Common.offsetsof (Tags.tagDefs ()) tag_sym in
        let final_pad = Common.sizeof (Ctype ([], Struct tag_sym)) - last_off in
        (* TODO: rewrite now that offsetsof returns the paddings *)
        let (funptrmap, _, bs) = List.fold_left2 begin fun (funptrmap, last_off, acc) (ident, ty, off) (_, _, mval) ->
            let pad = off - last_off in
            let (funptrmap, bs) = repr funptrmap mval in
            (funptrmap, off + Common.sizeof ty, acc @ List.init pad padding_byte @ bs)
          end (funptrmap, 0, []) offs xs
        in
        (funptrmap, bs @ List.init final_pad padding_byte)
    (* | MVunion (tag_sym, memb_ident, mval) ->
        let size = sizeof (Ctype ([], Union tag_sym)) in
        let (funptrmap', bs) = repr funptrmap mval in
        (funptrmap', bs @ List.init (size - List.length bs) (fun _ -> AbsByte.v Prov_none None)) *)


let rec abst allocations (*funptrmap*) (Ctype (_, ty) as cty) (bs : AbsByte.t list) : mem_value * AbsByte.t list =
  let self ty bs = abst allocations ty bs in
  let extract_unspec xs =
    List.fold_left (fun acc_opt mbyte ->
      match acc_opt, mbyte.AbsByte.value with
        | None, _ ->
            None
        | _, None ->
            None
        | (Some (alloc_id_opt, acc), Some c) ->
            let alloc_id_opt' =
                match alloc_id_opt, mbyte.AbsByte.prov with
                  | Some alloc_id1, Prov_some alloc_id2 ->
                      if N.equal alloc_id1 alloc_id2 then
                        alloc_id_opt
                      else
                        None
                  | None, Prov_some alloc_id2 ->
                      Some alloc_id2
                  | _, Prov_empty ->
                      alloc_id_opt in
            Some (alloc_id_opt', c :: acc)
    ) (Some (None, [])) (List.rev xs) in

  if List.length bs < Common.sizeof cty then
    failwith "abst, |bs| < sizeof(ty)";
  
  match ty with
    | Void
    | Array (_, None)
    | Function _ ->
        (* ty must have a known size *)
        assert false
    | Basic (Integer ity) ->
        let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
        ( begin match extract_unspec bs1 with
            | Some (alloc_id_opt, cs) ->
                let n = int_of_bytes (AilTypesAux.is_signed_ity ity) cs in
                MVinteger ( ity
                          , match alloc_id_opt with
                              | None ->
                                  IVint n
                              | Some alloc_id ->
                                  IVloc (Prov_some alloc_id, n))
            | None ->
                MVunspecified cty
          end , bs2)
    | Basic (Floating fty) ->
        failwith "TODO: abst Floating"
    | Array (elem_ty, Some n) ->
        let rec aux n mval_acc cs =
          if n <= 0 then
            (MVarray (List.rev mval_acc), cs)
          else
            let (mval, cs') = self elem_ty cs in
            aux (n-1) (mval :: mval_acc) cs'
        in
        aux (N.to_int n) [] bs
    | Pointer (_, ref_ty) ->
       failwith "TODO: abst Pointer"
       (* need to add ptrfrag stuff to extract_unspec*)
       
        (* let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
        ( begin match extract_unspec bs1 with
            | Some (alloc_id_opt, cs) ->
                let n = int_of_bytes false cs in
                MVpointer ( ref_ty
                          , if Z.(equal n zero) then
                              PVnull
                            else
                              (* TODO: funptr *)
                              | None ->
                                  IVint n
                              | Some alloc_id ->
                                  IVloc (Prov_some alloc_id, n))
            | None ->
                MVunspecified cty
          end , bs2) *)
    | Atomic atom_ty ->
        failwith "TODO: abst Atomic"
    | Struct tag_sym ->
        failwith "TODO: abst Struct"
    | Union tag_sym ->
        failwith "TODO: abst, Union (as value)"



let load loc ty ptrval : (footprint * mem_value) memM =
  match ptrval with
    | PVnull ->
        fail (MerrAccess (loc, LoadAccess, NullPtr))
    | PVloc (Prov_empty, _) ->
        fail (MerrAccess (loc, LoadAccess, NoProvPtr))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail (MerrAccess (loc, LoadAccess, DeadPtr))
        else if not (check_bounds addr ty alloc) then
          fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
        else
          get >>= fun st ->
          put { st with last_used= Some alloc_id } >>= fun () ->
          let bs = fetch_bytes st.bytemap alloc.base (Common.sizeof ty) in
          return (FOOTPRINT, fst (abst st.allocations ty bs))
    | PVfunptr _ ->
      fail (MerrAccess (loc, LoadAccess, FunctionPtr))

let store loc ty is_locking ptrval mval : footprint memM =
  match ptrval with
    | PVnull ->
        fail (MerrAccess (loc, StoreAccess, NullPtr))
    | PVloc (Prov_empty, _) ->
        fail (MerrAccess (loc, StoreAccess, NoProvPtr))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail (MerrAccess (loc, StoreAccess, DeadPtr))
        else if not (check_bounds addr ty alloc) then
          fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
        else
          update begin fun st ->
            let (funptrmap, pre_bs) = repr st.funptrmap mval in
            let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
            { st with last_used= Some alloc_id;
                      bytemap=
                        List.fold_left (fun acc (addr, b) ->
                        IntMap.add addr b acc
                      ) st.bytemap bs;
                      funptrmap= funptrmap; }
          end >>= fun () ->
          return FOOTPRINT
    | PVfunptr _ ->
      fail (MerrAccess (loc, StoreAccess, FunctionPtr))


let null_ptrval _ =
  PVnull

let fun_ptrval sym =
  PVfunptr sym

(*TODO: revise that, just a hack for codegen*)
let concrete_ptrval alloc_id addr =
  PVloc (Prov_some alloc_id, addr)
let case_ptrval ptrval f_null f_funptr f_concrete _ =
  match ptrval with
    | PVnull ->
        f_null Ctype.void (*TODO: hack*)
    | PVloc (Prov_empty, addr) ->
        f_concrete None addr
    | PVloc (Prov_some alloc_id, addr) ->
        f_concrete (Some alloc_id) addr
    | PVfunptr sym ->
        f_funptr sym

let case_funsym_opt _ ptrval : Symbol.sym option =
  match ptrval with
    | PVfunptr sym ->
        Some sym
    | _ ->
        (* TODO *)
        None

(* Operations on pointer values *)
let eq_ptrval ptrval1 ptrval2 : bool memM =
  return begin match ptrval1, ptrval2 with
    | PVnull, PVnull ->
        true
    | PVfunptr sym1, PVfunptr sym2 ->
        (Symbol.symbolEquality sym1 sym2)
    | PVloc (_, addr1), PVloc (_, addr2) ->
        (N.equal addr1 addr2)
    | _ ->
        false
  end

let ne_ptrval ptrval1 ptrval2 : bool memM =
  eq_ptrval ptrval1 ptrval2 >>= function
    | true  -> return false
    | false -> return true

let rel_op_ptrval f_op ptrval1 ptrval2 : bool memM =
  match ptrval1, ptrval2 with
    | PVloc (Prov_some alloc_id1, addr1)
    , PVloc (Prov_some alloc_id2, addr2) when N.equal alloc_id1 alloc_id2 ->
        lookup_alloc alloc_id1 >>= fun alloc ->
        if alloc.killed then
          failwith "TODO: UB rel_op_ptrval ==> killed allocation"
        else if not (in_bounds addr1 alloc && in_bounds addr2 alloc) then
          failwith "TODO: UB rel_op_ptrval ==> out of bound allocation"
        else
          (* VIP-rel-op-ptr *)
          return (f_op addr1 addr2)
    | _ ->
        failwith "TODO: UB rel_op_ptrval ==> invalid pointer"

let lt_ptrval ptrval1 ptrval2 : bool memM =
  rel_op_ptrval N.less ptrval1 ptrval2
let gt_ptrval ptrval1 ptrval2 : bool memM =
  rel_op_ptrval N.greater ptrval1 ptrval2
let le_ptrval ptrval1 ptrval2 : bool memM =
  rel_op_ptrval N.less_equal ptrval1 ptrval2
let ge_ptrval ptrval1 ptrval2 : bool memM =
  rel_op_ptrval N.greater_equal ptrval1 ptrval2

let diff_ptrval diff_ty ptrval1 ptrval2 : integer_value memM =
  match ptrval1, ptrval2 with
    | PVloc (Prov_some alloc_id1, addr1)
    , PVloc (Prov_some alloc_id2, addr2) when Z.equal alloc_id1 alloc_id2 ->
        lookup_alloc alloc_id1 >>= fun alloc ->
        if alloc.killed then
          failwith "TODO: UB diff_ptrval ==> killed alloc"
        else if in_bounds addr1 alloc && in_bounds addr2 alloc then
          let diff_ty' = match diff_ty with
            | Ctype (_, Array (elem_ty, _)) ->
                elem_ty
            | _ ->
                diff_ty in
          return (IVint (N.div (N.sub addr1 addr2) (N.of_int (Common.sizeof diff_ty'))))
        else
          assert false (* TODO *)
    | _ ->
        failwith "TODO: UB diff_ptrval"

let update_prefix: (Symbol.prefix * mem_value) -> unit memM =
  fun _ ->
    prerr_endline "TODO: VIP.update_prefix isn't doing anything";
    return ()
let prefix_of_pointer: pointer_value -> string option memM =
  fun _ -> return None (* TODO *)

let isWellAligned_ptrval ref_ty ptrval =
  (* TODO: catch builtin function types *)
  match unatomic_ ref_ty with
    | Void
    | Function _ ->
        fail (MerrOther "called isWellAligned_ptrval on void or a function type")
    | _ ->
        begin match ptrval with
          | PVnull ->
              return true
          | PVloc (_, addr) ->
              return (N.(equal (modulus addr (of_int (Common.alignof ref_ty))) zero))
          | PVfunptr _ ->
              fail (MerrOther "called isWellAligned_ptrval on function pointer")
        end

(* Following §6.5.3.3, footnote 102) *)
let validForDeref_ptrval ref_ty ptrval =
  let do_test alloc_id =
    lookup_alloc alloc_id >>= fun alloc ->
    if alloc.killed then
      return false
    else
      isWellAligned_ptrval ref_ty ptrval in
  match ptrval with
    | PVloc (Prov_some alloc_id, _) ->
        do_test alloc_id
    | _ ->
        return false
  
let in_range n ity =
  N.(less_equal (Common.ity_min ity) n && less_equal n (Common.ity_max ity))

(* Casting operations *)
(* 'cast_ival_to_ptrval()' in the paper *)
(* the first ctype is the original integer type, the second is the target referenced type *)
let ptrcast_ival ity ref_ty ival : pointer_value memM =
  match ival with
    | IVloc (Prov_empty, _) ->
        failwith "TODO: UB, ptrcast_ival() @empty"
    | IVloc (Prov_some alloc_id, a) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if N.(equal a zero) then
          return PVnull
        else if failwith "𝑎 = address_of_function(ident)" then
          failwith "funptr(ident)"
        else if    not alloc.killed
                && N.less_equal alloc.base a
                && N.less_equal a (N.add alloc.base alloc.length) then
          return (PVloc (Prov_some alloc_id, a))
        else
          return (PVloc (Prov_empty, a))
    | IVint a ->
        if N.(equal a zero) then
          return PVnull
        else if failwith "𝑎 = address_of_function(ident)" then
          failwith "funptr(ident)"
        else
          return (PVloc (Prov_empty, a))



(* 'cast_ptrval_to_ival()' in the paper *)
(* the first ctype is the original referenced type, the integerType is the target integer type *)
let intcast_ptrval ref_ty ity ptrval : integer_value memM =
  match ptrval with
    | PVnull ->
        (* VIP-cast-ptr-to-int-null *)
        return (IVint N.zero)
    | PVloc (Prov_empty, addr) ->
        failwith "TODO: UB, intcast_ptrval() @empty pointer"
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          failwith "TODO: UB, intcast_ptrval() killed"
        else if not (in_range addr ity) then
          failwith "TODO: UB, intcast_ptrval() address not in_range"
        else
          (* VIP-cast-int-to-ptr-int *)
          return (IVloc (Prov_some alloc_id, addr))
    | PVfunptr sym ->
        failwith "TODO: intcast_ptrval() fun pointer"

(* Pointer shifting constructors *)
let array_shift_ptrval ptrval ty ival : pointer_value =
  (* failwith "VIP memory model should be called SWITCH strict_pointer_arith" *)
  match ptrval with
    | PVnull ->
      failwith "TODO UB, array_offset ==> NULL"
    | PVloc (Prov_empty, _) ->
      failwith "TODO UB, array_offset ==> @empty"
    | PVloc (Prov_some alloc_id, addr) ->
        (* lookup_alloc alloc_id >>= fun alloc -> *)
        let addr' = N.add addr (N.of_int (Common.sizeof ty)) in
        (* if alloc.killed then
          failwith "TODO UB, array_offset ==> killed"
        else if not (in_bounds addr' alloc) then
          failwith "TODO UB, array_offset ==> out-of-bound"
        else *)
          (* TODO: hack *)
          PVloc (Prov_some alloc_id, addr')
    | PVfunptr sym ->
      failwith "TODO UB, array_offset ==> funptr"

let member_shift_ptrval ptrval tag_sym membr_ident : pointer_value =
  match ptrval with
    | PVnull ->
      failwith "TODO UB, member_offset ==> NULL"
    | PVloc (Prov_empty, _) ->
      failwith "TODO UB, member_offset ==> @empty"
    | PVloc (Prov_some alloc_id, addr) ->
        failwith "TODO: member_shift_ptrval"
        (* lookup_alloc alloc_id >>= fun alloc ->
        let addr' = N.add addr (N.of_int (Common.sizeof ty)) in
        if alloc.killed then
          failwith "TODO UB, member_offset ==> killed"
        else if not (in_bounds addr' alloc) then
          failwith "TODO UB, member_offset ==> out-of-bound"
        else
          PVloc (Prov_some alloc_id, addr') *)
    | PVfunptr sym ->
      failwith "TODO UB, member_offset ==> funptr"

let eff_array_shift_ptrval ptrval ty ival : pointer_value memM =
  match ptrval with
    | PVnull ->
      failwith "TODO UB, array_offset ==> NULL"
    | PVloc (Prov_empty, _) ->
      failwith "TODO UB, array_offset ==> @empty"
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        let addr' = N.add addr (N.of_int (Common.sizeof ty)) in
        if alloc.killed then
          failwith "TODO UB, array_offset ==> killed"
        else if not (in_bounds addr' alloc) then
          failwith "TODO UB, array_offset ==> out-of-bound"
        else
          return (PVloc (Prov_some alloc_id, addr'))
    | PVfunptr sym ->
      failwith "TODO UB, array_offset ==> funptr"
      

let memcpy: pointer_value -> pointer_value -> integer_value -> pointer_value memM =
  fun _ _ _ -> failwith "TODO: VIP.memcpy"
let memcmp: pointer_value -> pointer_value -> integer_value -> integer_value memM =
  fun _ _ _ -> failwith "TODO: VIP.memcmp"
let realloc tid al_ival ptrval size_ival : pointer_value memM =
  failwith "TODO: VIP.realloc"


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


let copy_alloc_id ival ptrval : pointer_value memM =
  match ptrval with
    | PVloc (Prov_some alloc_id, _) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          failwith "TODO: UB, copy_alloc_id() killed"
        else
          let n = ival_to_int ival in
          if not N.(less_equal alloc.base n && less_equal n (add alloc.base alloc.length)) then
            failwith "TODO: UB, copy_alloc_id() out of bound"
          else
            return (PVloc (Prov_some alloc_id, n))
    | _ ->
        failwith "TODO: copy_alloc_id"

(* Integer value constructors *)
let concurRead_ival: Ctype.integerType -> Symbol.sym -> integer_value =
  fun _ _ -> assert false (* TODO *)

let integer_ival n =
  IVint n
let max_ival ity =
  IVint (Common.ity_max ity)
let min_ival ity =
  IVint (Common.ity_min ity)

(* 'arith_bin_op()' in the paper *)
let op_ival op ival1 ival2 : integer_value =
  let open MC in
  let op = match op with
    | IntAdd   -> N.add
    | IntSub   -> N.sub
    | IntMul   -> N.mul
    | IntDiv   -> fun x y -> if N.(equal y zero) then N.zero else N.div x y
    | IntRem_t -> N.integerRem_t
    | IntRem_f -> N.integerRem_f
    | IntExp   -> fun x y -> N.pow_int x (N.to_int y) in
  IVint (op (ival_to_int ival1) (ival_to_int ival2))

let offsetof_ival tagDefs tag_sym membr_ident =
  let (xs, _) = Common.offsetsof tagDefs tag_sym in
  let pred (ident, _, _) =
    Common.ident_equal ident membr_ident in
  match List.find_opt pred xs with
    | Some (_, _, offset) ->
        IVint (N.of_int offset)
    | None ->
        failwith "VIP.offsetof_ival: invalid membr_ident"

let sizeof_ival ty = IVint (N.of_int (Common.sizeof ty))
let alignof_ival ty = IVint (N.of_int (Common.alignof ty))

let bitwise_complement_ival _ ival =
  IVint (N.(sub (negate (ival_to_int ival)) (of_int 1)))
let bitwise_and_ival _ ival1 ival2 =
  IVint (N.bitwise_and (ival_to_int ival1) (ival_to_int ival2))
let bitwise_or_ival _ ival1 ival2 =
  IVint (N.bitwise_or (ival_to_int ival1) (ival_to_int ival2))
let bitwise_xor_ival _ ival1 ival2 =
  IVint (N.bitwise_xor (ival_to_int ival1) (ival_to_int ival2))

let case_integer_value ival f_concrete _ =
  f_concrete (ival_to_int ival)

let is_specified_ival _ =
  true

(* Predicats on integer values *)
let eq_ival _ ival1 ival2 =
  Some (N.equal (ival_to_int ival1) (ival_to_int ival2))
let lt_ival _ ival1 ival2 =
Some (N.less (ival_to_int ival1) (ival_to_int ival2))
let le_ival _ ival1 ival2 =
Some (N.less_equal (ival_to_int ival1) (ival_to_int ival2))

let eval_integer_value ival =
  Some (ival_to_int ival)

(* Floating value constructors *)
let zero_fval = TODO_floating_value
let one_fval = TODO_floating_value
let str_fval _ = failwith "VIP.str_fval"

(* Floating value destructors *)
let case_fval _ _ _ = failwith "VIP.case_fval"

(* Predicates on floating values *)
let op_fval _ _ _ = failwith "VIP.op_fval"
let eq_fval _ _ = failwith "VIP.eq_fval"
let lt_fval _ _ = failwith "VIP.lt_fval"
let le_fval _ _ = failwith "VIP.le_fval"

(* Integer <-> Floating casting constructors *)
let fvfromint ival =
  failwith "VIP.fvfromint"
let ivfromfloat ity fval =
  failwith "VIP.ivfromfloat"


(* Memory value constructors *)
let unspecified_mval ty =
  MVunspecified ty
let integer_value_mval ity ival =
  MVinteger (ity, ival)
let floating_value_mval fty fval =
  failwith "TODO: MVfloating (fty, fval)"
let pointer_mval ref_ty ptrval =
  MVpointer (ref_ty, ptrval)
let array_mval mvals =
  MVarray mvals
let struct_mval tag_sym xs =
  MVstruct (tag_sym, xs)
let union_mval tag_sym memb_ident mval =
  failwith "TODO: MVunion (tag_sym, memb_ident, mval)"

(* Memory value destructor *)
let case_mem_value mval f_unspec f_concur f_ival f_fval f_ptr f_array f_struct f_union =
  match mval with
    | MVunspecified ty ->
        f_unspec ty
    | MVinteger (ity, ival) ->
        f_ival ity ival
    (* | MVfloating (fty, fval) ->
        f_fval fty fval *)
    | MVpointer (ref_ty, ptrval) ->
        f_ptr ref_ty ptrval
    | MVarray mvals ->
        f_array mvals
    | MVstruct (tag_sym, xs) ->
        f_struct tag_sym xs
    (* | MVunion (tag_sym, memb_ident, mval') ->
        f_union tag_sym memb_ident mval' *)

(* For race detection *)
let sequencePoint : unit memM =
  (* No unseq-race detection *)
  return ()

(* pretty printing *)
open PPrint
open Pp_prelude

let string_of_provenance = function
  | Prov_empty ->
      "@empty"
  | Prov_some alloc_id ->
      "@" ^ Nat_big_num.to_string alloc_id

let pp_pointer_value = function
  | PVnull ->
      !^ "NULL"
  | PVloc (prov, addr) ->
      (* TODO: remove this idiotic hack when Lem's nat_big_num library expose "format" *)
      P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string addr))))
  | PVfunptr sym ->
      !^ "Cfunction" ^^ P.parens (!^ (Pp_symbol.to_string_pretty sym))

let pp_integer_value = function
  | IVint n ->
      !^ "Int" ^^ P.parens (!^ (Nat_big_num.to_string n))
  | IVloc (prov, addr) ->
      !^ "Loc" ^^ P.parens (P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^
                                      !^ (Nat_big_num.to_string addr)))

let pp_integer_value_for_core = function
  | IVint n ->
      !^ (Nat_big_num.to_string n)
  | IVloc (prov, addr) ->
      (* TODO: should this not be an error? *)
      !^ "Loc" ^^ P.parens (P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^
                                      !^ (Nat_big_num.to_string addr)))

let rec pp_mem_value = function
  | MVunspecified _ ->
      PPrint.string "UNSPEC"
  | MVinteger (_, ival) ->
      pp_integer_value ival
  (* | MVfloating (_, fval) ->
      !^ (string_of_float fval) *)
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
  (* | MVunion (tag_sym, membr_ident, mval) ->
      parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
        dot ^^ Pp_symbol.pp_identifier membr_ident ^^ equals ^^^
        pp_mem_value mval
      ) *)

let pp_pretty_pointer_value = pp_pointer_value
let pp_pretty_integer_value _ = pp_integer_value
let pp_pretty_mem_value _ = pp_mem_value

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

(* JSON serialisation *)
let serialise_mem_state dig st : Json.json =
  failwith "VIP.serialise_mem_state"
