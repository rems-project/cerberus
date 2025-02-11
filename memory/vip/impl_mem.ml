open Ctype
open Memory_model
open Memory_utils
module MC = Mem_common

module L = struct
  include List
  include Lem_list
end

let not_implemented str =
  failwith ("NOT SUPPORTED: "^ str)

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

  let to_json json_of_prov b : Cerb_json.json =
    `Assoc [ ("prov", json_of_prov b. prov)
           ; ("value", Cerb_json.of_option Cerb_json.of_char b.value)
           ; ("ptrfrag_idx", Cerb_json.of_option Cerb_json.of_int b.ptrfrag_idx) ]
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
  (* NOTE: simplistic handling of floating values *)
  float

  (* INTERNAL *)
let ival_to_int: integer_value -> N.num = function
  | IVloc (_, z) -> z
  | IVint z      -> z


(* EXTERNAL *)
type mem_value =
  | MVunspecified of ctype
  | MVinteger of integerType * integer_value
  | MVfloating of floatingType * floating_value
  | MVpointer of ctype * pointer_value
  | MVarray of mem_value list
  | MVstruct of Symbol.sym (*struct/union tag*) * (Symbol.identifier (*member*) * ctype * mem_value) list
  | MVunion of Symbol.sym (*struct/union tag*) * Symbol.identifier (*member*) * mem_value

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

let overlapping _ _ =
  (* No unsequenced races detection *)
  false


(* module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = N.compare
end) *)

type allocation = {
  base: address;
  length: N.num; (* INVARIANT >= 0 *)
  killed: bool;
  (* NON-semantics fields *)
  ty: Ctype.ctype;
  prefix: Symbol.prefix;
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
} [@@warning "-unused-field"]

let initial_mem_state: mem_state =
  { allocations= IntMap.empty
  ; bytemap= IntMap.empty
  ; funptrmap= IntMap.empty
  ; next_alloc_id= Z.zero
  ; last_address= Z.of_int 0xFFFFFFFFFFFF
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

let fail ?(loc=Cerb_location.other "VIP") err =
  let open Nondeterminism in
  match MC.undefinedFromMem_error err with
    | Some ub ->
        kill (Undef0 (loc, [ub]))
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
    if i <= max then
      let acc = IntMap.add i (f_init i) acc in
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

(* [a .. a + sizeof(ty) − 1] ⊆ [a_i .. a_i + n_1 - 1] *)
let check_bounds addr ty alloc =
  N.less_equal alloc.base addr
&& N.less_equal (N.add addr (N.pred (N.of_int (Common.sizeof ty))))
               (N.add alloc.base (N.pred alloc.length))


let fetch_bytes bytemap base_addr n_bytes : AbsByte.t list =
 List.map (fun addr ->
   match IntMap.find_opt addr bytemap with
     | Some b ->
(*         if b.AbsByte.value = None then
            Printf.printf "FETCH WTF ==> %s\n" (N.to_string addr); *)
         b
     | None ->
         failwith "INTERNAL ERROR: Vip.AbsByte.{ prov= Prov_empty; value= None; ptrfrag_idx= None }"
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
    | MVfloating (fty, fval) ->
      ret @@ List.map (fun value -> AbsByte.{prov= Prov_empty; value; ptrfrag_idx= None}) begin
        bytes_of_int
          true
          (Common.sizeof (Ctype ([], Basic (Floating fty)))) (N.of_int64 (Int64.bits_of_float fval))
      end
    | MVpointer (_, ptrval) ->
        Cerb_debug.print_debug 1 [] (fun () -> "NOTE: we fix the sizeof pointers to 8 bytes");
        let ptr_size = match (Ocaml_implementation.get ()).sizeof_pointer with
          | None ->
              failwith "INTERNAL ERROR: the VIP memory model requires a complete implementation"
          | Some z ->
              z in
        begin match ptrval with
          | PVnull ->
              Cerb_debug.print_debug 1 [] (fun () -> "NOTE: we fix the representation of all NULL pointers to be 0x0");
              ret @@ List.init ptr_size
                (fun _ -> AbsByte.{prov= Prov_empty; value= (Some '\000'); ptrfrag_idx= None})
          | PVfunptr (Symbol.Symbol (file_dig, n, opt_name)) ->
              (* TODO: *)
              not_implemented "VIP.repr => function pointer"
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
        (funptrmap, L.concat @@ List.rev bs_s)
    | MVstruct (tag_sym, xs) ->
        let padding_byte _ = AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None} in
        let (offs, last_off) = Common.offsetsof (Tags.tagDefs ()) tag_sym in
        let final_pad = Common.sizeof (Ctype ([], Struct tag_sym)) - last_off in
        let (funptrmap, _, bs) = List.fold_left2 begin fun (funptrmap, last_off, acc) (ident, ty, off) (_, _, mval) ->
            let pad = off - last_off in
            let (funptrmap, bs) = repr funptrmap mval in
            (funptrmap, off + Common.sizeof ty, acc @ List.init pad padding_byte @ bs)
          end (funptrmap, 0, []) offs xs
        in
        (funptrmap, bs @ List.init final_pad padding_byte)
    | MVunion (tag_sym, memb_ident, mval) ->
        let padding_byte _ = AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None} in
        let size = Common.sizeof (Ctype ([], Union tag_sym)) in
        let (funptrmap', bs) = repr funptrmap mval in
        (funptrmap', bs @ List.init (size - List.length bs) padding_byte)


let rec abst (*allocations*) (*funptrmap*) (Ctype (_, ty) as cty) (bs : AbsByte.t list) : mem_value * AbsByte.t list =
let self ty bs = abst (*allocations*) ty bs in
let interp_bytes xs : [ `SPECIFIED of   [ `PROV of allocation_id | `NOPROV ]
                                     * [ `PROV2 of allocation_id | `NOPROV2 ]
                                     * char list
                                     * [ `VALID_PTRFRAG of int | `INVALID_PTRFRAG ]
                     | `UNSPECIFIED ] =
 List.fold_left (fun acc mbyte ->
   match acc, mbyte.AbsByte.value with
     | `UNSPECIFIED, _ ->
         `UNSPECIFIED
     | _, None ->
         (* if any byte is 'unspec' the value we are building is unspecified *)
         `UNSPECIFIED
     | (`SPECIFIED (prov_status, prov2_status, cs, ptrfrag_status), Some c) ->
         let prov_status' =
           match prov_status, mbyte.AbsByte.prov with
             | `PROV alloc_id1, Prov_some alloc_id2 ->
                 if N.equal alloc_id1 alloc_id2 then
                   prov_status
                 else
                   (* if any two bytes have different @i provenances,
                      the value loose the provenance *)
                   `NOPROV
             | `NOPROV, Prov_some alloc_id ->
                 `PROV alloc_id
             | _, Prov_empty ->
                 prov_status in
         let prov2_status' =
           match prov2_status, mbyte.AbsByte.prov with
             | `PROV2 alloc_id1, Prov_some alloc_id2 ->
                 if N.equal alloc_id1 alloc_id2 || mbyte.AbsByte.ptrfrag_idx <> None then
                   prov2_status
                 else
                   (* if any two bytes have different @i provenances,
                      the value loose the provenance *)
                   `NOPROV2
             | `NOPROV2, Prov_some alloc_id ->
                 `PROV2 alloc_id
             | _, Prov_empty ->
                 prov2_status in
         let ptrfrag_status' =
           match ptrfrag_status, mbyte.AbsByte.ptrfrag_idx with
             | `VALID_PTRFRAG idx1, Some idx2 when idx1 = idx2 ->
                 `VALID_PTRFRAG (idx1+1)
             | _, _ ->
                 `INVALID_PTRFRAG in
           `SPECIFIED (prov_status', prov2_status', c :: cs, ptrfrag_status')
 ) (`SPECIFIED (`NOPROV, `NOPROV2, [], `VALID_PTRFRAG 0)) (List.rev xs) in
if List.length bs < Common.sizeof cty then
 failwith "INTERNAL ERROR: Vip.abst, |bs| < sizeof(ty)";
match ty with
 | Void
 | Array (_, None)
 | Function _
 | FunctionNoParams _ ->
     (* ty must have a known size *)
     assert false
 | Basic (Integer ity) ->
     let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
     ( begin match interp_bytes bs1 with
         | `SPECIFIED (prov_status, _, cs, _) ->
             let n = int_of_bytes (AilTypesAux.is_signed_ity ity) cs in
             MVinteger ( ity
                       , match prov_status with
                           | `NOPROV ->
                               IVint n
                           | `PROV alloc_id ->
                               (* Printf.printf "IN abst() ==> cs: %s ==> IVloc n: %s\n"
                                 (String.concat ", " (List.map (fun c -> string_of_int (int_of_char c)) cs))
                                 (N.to_string n); *)
                               IVloc (Prov_some alloc_id, n))
         | `UNSPECIFIED ->
             MVunspecified cty
       end , bs2)
 | Basic (Floating fty) ->
     let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
     (* let (_, _, bs1') = AbsByte.split_bytes bs1 in *)
     ( begin match interp_bytes bs1 with
         | `SPECIFIED (_, _, cs, _) ->
              MVfloating ( fty
              , Int64.float_of_bits (N.to_int64 (int_of_bytes true cs)) )
         | `UNSPECIFIED ->
              MVunspecified cty
       end , bs2)
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
     let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
     ( begin match interp_bytes bs1 with
         | `SPECIFIED (_, prov2_status, cs, ptrfrag_status) ->
             let addr = int_of_bytes false cs in
             if N.(equal addr zero) then
               MVpointer (ref_ty, PVnull)
                     (* TODO: fix this when implementing funptr *)
             else if false then
               not_implemented "Vip.abst ==> function pointer"
             else begin match prov2_status, ptrfrag_status with
               | `PROV2 alloc_id, `VALID_PTRFRAG _ ->
                   (* TODO: I think that if we have a VALID_PTRFRAG,
                      then idx = |bs| (???) so no check needed *)
                   MVpointer (ref_ty, PVloc (Prov_some alloc_id, addr))
               | `NOPROV2, `VALID_PTRFRAG _ ->
                   assert false
               | `PROV2 alloc_id, `INVALID_PTRFRAG ->
                   MVpointer (ref_ty, PVloc (Prov_some alloc_id, addr))
               | `NOPROV2, `INVALID_PTRFRAG ->
                   MVpointer (ref_ty, PVloc (Prov_empty, addr))
             end
         | `UNSPECIFIED ->
             MVunspecified cty
       end , bs2)
 | Atomic atom_ty ->
     (* NOTE: we are giving the same representation for atomic types as
              the type they are derived from *)
     self atom_ty bs
 | Struct tag_sym ->
     let (bs1, bs2) = L.split_at (Common.sizeof cty) bs in
     let (rev_xs, _, bs') = List.fold_left (fun (acc_xs, previous_offset, acc_bs) (memb_ident, memb_ty, memb_offset) ->
       let pad = memb_offset - previous_offset in
       let (mval, acc_bs') = self memb_ty (L.drop pad acc_bs) in
       ((memb_ident, memb_ty, mval)::acc_xs, memb_offset + Common.sizeof memb_ty, acc_bs')
     ) ([], 0, bs1) (fst (Common.offsetsof (Tags.tagDefs ()) tag_sym)) in
     (* TODO: check that bs' = last padding of the struct *)
     (MVstruct (tag_sym, List.rev rev_xs), bs2)
| Union tag_sym ->
     not_implemented "Vip.abst, Union (as value)"


(* "addr \not\in [a_i .. a_i + n_i]" *)
let in_bounds addr alloc =
  N.less_equal alloc.base addr && N.(less_equal addr (add alloc.base alloc.length))


let allocate_object tid prefix al_ival ty _ init_opt : pointer_value memM =
  let n = Z.of_int (Common.sizeof ty) in
  allocator n (ival_to_int al_ival) >>= fun (alloc_id, addr) ->
  let init_mval =
    match init_opt with
      | None -> MVunspecified ty
      | Some mval -> mval in
  update (fun st ->
    let (funptrmap, pre_bs) = repr st.funptrmap init_mval in
    let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
    { st with
      allocations= IntMap.add alloc_id {base= addr; length= n; killed= false; ty; prefix} st.allocations;
      (* bytemap= set_range st.bytemap addr n (fun _ -> AbsByte.{prov= Prov_empty; value= None; ptrfrag_idx= None}) *)
      bytemap=
        List.fold_left (fun acc (addr, b) ->
        IntMap.add addr b acc
      ) st.bytemap bs;
      funptrmap= funptrmap;
    }
  ) >>= fun () ->
  return (PVloc (Prov_some alloc_id, addr))


let allocate_region tid pref al_ival sz_ival : pointer_value memM =
  fail (MerrOther "VIP does not support allocate_region()")


let kill loc is_dyn ptrval : unit memM =
  (* TODO: implement the forbid_nullptr_free switch *)
  match ptrval with
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          (* TODO: this should be a Cerberus internal error *)
          fail ~loc (MerrUndefinedFree Free_dead_allocation)
        else
          update (fun st ->
            { st with allocations= IntMap.add alloc_id {alloc with killed= true} st.allocations}
          )
    | _ ->
        fail (MerrVIP (VIP_free_invalid_pointer loc))


let load loc ty ptrval : (footprint * mem_value) memM =
  match ptrval with
    | PVnull ->
        fail ~loc (MerrAccess (LoadAccess, NullPtr))
    | PVloc (Prov_empty, _) ->
        fail ~loc (MerrAccess (LoadAccess, NoProvPtr))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail ~loc (MerrAccess (LoadAccess, DeadPtr))
        else if not (check_bounds addr ty alloc) then
          fail ~loc (MerrAccess (LoadAccess, OutOfBoundPtr))
        else
          get >>= fun st ->
          put { st with last_used= Some alloc_id } >>= fun () ->
          let bs = fetch_bytes st.bytemap addr (Common.sizeof ty) in
          return (FOOTPRINT, fst (abst (*st.allocations*) ty bs))
    | PVfunptr _ ->
      fail ~loc (MerrAccess (LoadAccess, FunctionPtr))


let store loc ty is_locking ptrval mval : footprint memM =
  match ptrval with
    | PVnull ->
        fail ~loc (MerrAccess (StoreAccess, NullPtr))
    | PVloc (Prov_empty, _) ->
        fail ~loc (MerrAccess (StoreAccess, NoProvPtr))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail ~loc (MerrAccess (StoreAccess, DeadPtr))
        else if not (check_bounds addr ty alloc) then
          fail ~loc (MerrAccess (StoreAccess, OutOfBoundPtr))
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
      fail ~loc (MerrAccess (StoreAccess, FunctionPtr))


let null_ptrval _ =
  PVnull

let fun_ptrval sym =
  PVfunptr sym

let concrete_ptrval alloc_id addr =
  PVloc (Prov_some alloc_id, addr)
let case_ptrval ptrval f_null f_funptr f_concrete =
  match ptrval with
    | PVnull ->
        f_null Ctype.void (*TODO: hack*)
    | PVloc (Prov_empty, addr) ->
        f_concrete None addr
    | PVloc (Prov_some alloc_id, addr) ->
        f_concrete (Some alloc_id) addr
    | PVfunptr sym ->
        f_funptr (Some sym)

let case_funsym_opt _ ptrval : Symbol.sym option =
  match ptrval with
    | PVfunptr sym ->
        Some sym
    | _ ->
        (* TODO *)
        None

(* Operations on pointer values *)
let eq_ptrval _ ptrval1 ptrval2 : bool memM =
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

let ne_ptrval loc ptrval1 ptrval2 : bool memM =
  eq_ptrval loc ptrval1 ptrval2 >>= function
    | true  -> return false
    | false -> return true

let rel_op_ptrval loc f_op ptrval1 ptrval2 : bool memM =
  match ptrval1, ptrval2 with
    | PVloc (Prov_some alloc_id1, addr1)
    , PVloc (Prov_some alloc_id2, addr2) when N.equal alloc_id1 alloc_id2 ->
        lookup_alloc alloc_id1 >>= fun alloc ->
        if alloc.killed then
          fail ~loc (MerrVIP VIP_relop_killed)
        else if not (in_bounds addr1 alloc && in_bounds addr2 alloc) then
          fail ~loc (MerrVIP VIP_relop_out_of_bound)
        else
          (* VIP-rel-op-ptr *)
          return (f_op addr1 addr2)
    | _ ->
        fail ~loc (MerrVIP VIP_relop_invalid)

let lt_ptrval loc ptrval1 ptrval2 : bool memM =
  rel_op_ptrval loc N.less ptrval1 ptrval2
let gt_ptrval loc ptrval1 ptrval2 : bool memM =
  rel_op_ptrval loc N.greater ptrval1 ptrval2
let le_ptrval loc ptrval1 ptrval2 : bool memM =
  rel_op_ptrval loc N.less_equal ptrval1 ptrval2
let ge_ptrval loc ptrval1 ptrval2 : bool memM =
  rel_op_ptrval loc N.greater_equal ptrval1 ptrval2

let diff_ptrval loc diff_ty ptrval1 ptrval2 : integer_value memM =
  match ptrval1, ptrval2 with
    | PVloc (Prov_some alloc_id1, addr1)
    , PVloc (Prov_some alloc_id2, addr2) when Z.equal alloc_id1 alloc_id2 ->
        lookup_alloc alloc_id1 >>= fun alloc ->
        if alloc.killed then
          (* TODO: more precise error message? *)
          fail ~loc MerrPtrdiff
        else if in_bounds addr1 alloc && in_bounds addr2 alloc then
          let diff_ty' = match diff_ty with
            | Ctype (_, Array (elem_ty, _)) ->
                elem_ty
            | _ ->
                diff_ty in
          return (IVint (N.div (N.sub addr1 addr2) (N.of_int (Common.sizeof diff_ty'))))
        else
          fail ~loc (MerrVIP VIP_diffptr_out_of_bound)
    | _ ->
      fail ~loc MerrPtrdiff

let update_prefix: (Symbol.prefix * mem_value) -> unit memM =
  fun _ ->
    (* TODO: VIP.update_prefix isn't doing anything *)
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
let ptrfromint _ ity ref_ty ival : pointer_value memM =
  match ival with
    | IVloc (Prov_empty, _) ->
        fail (MerrVIP VIP_ptrcast_empty)
    | IVloc (Prov_some alloc_id, a) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if N.(equal a zero) then
          return PVnull
                (* TODO: fix this when implementing funptr *)
                (* if addr = address_of_function(ident) then PVfunptr(ident) *)
        else if false then
          not_implemented "Vip.ptrcast_ival => function pointer (IVloc)"
        else if    not alloc.killed
                && N.less_equal alloc.base a
                && N.less_equal a (N.add alloc.base alloc.length) then
          return (PVloc (Prov_some alloc_id, a))
        else
          return (PVloc (Prov_empty, a))
    | IVint a ->
        if N.(equal a zero) then
          return PVnull
                (* TODO: fix this when implementing funptr *)
                (* if addr = address_of_function(ident) then PVfunptr(ident) *)
        else if false then
          not_implemented "Vip.ptrcast_ival => function pointer (IVint)"
        else
          return (PVloc (Prov_empty, a))



(* 'cast_ptrval_to_ival()' in the paper *)
(* the first ctype is the original referenced type, the integerType is the target integer type *)
let intfromptr _ ref_ty ity ptrval : integer_value memM =
  match ptrval with
    | PVnull ->
        (* VIP-cast-ptr-to-int-null *)
        return (IVint N.zero)
    | PVloc (Prov_empty, addr) ->
        fail (MerrVIP (VIP_intcast VIP_empty))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail (MerrVIP (VIP_intcast VIP_killed))
        else if not (in_range addr ity) then
          fail (MerrVIP VIP_intcast_not_in_range)
        else
          return (IVloc (Prov_some alloc_id, addr))
    | PVfunptr sym ->
      fail (MerrVIP (VIP_intcast VIP_funptr))

let derive_cap _ _ _ _ : integer_value =
  assert false (* CHERI only *)

let cap_assign_value _ _ _ : integer_value =
  assert false (* CHERI only *)

let ptr_t_int_value ival =
  ival

let null_cap _ : integer_value =
  assert false (* CHERI only *)

let get_intrinsic_type_spec _ =
  assert false (* CHERI only *)

let call_intrinsic _ _ _ =
  assert false (* CHERI only *)

let intcast _ _ ival =
  Either.Right ival

(* Pointer shifting constructors *)
let array_shift_ptrval ptrval ty ival : pointer_value =
  (* TODO: "VIP memory model should be called SWITCH strict_pointer_arith" *)
  match ptrval with
    | PVnull ->
        (* TODO *)
        failwith "UB: array_offset ==> NULL"
    | PVloc (Prov_empty, _) ->
        (* TODO *)
        failwith "UB: array_offset ==> @empty"
    | PVloc (Prov_some alloc_id, addr) ->
        (* lookup_alloc alloc_id >>= fun alloc -> *)
        let addr' = N.(add addr (mul (ival_to_int ival) (N.of_int (Common.sizeof ty)))) in
        (* TODO *)
        (* if alloc.killed then
          failwith "TODO UB, array_offset ==> killed"
        else if not (in_bounds addr' alloc) then
          failwith "TODO UB, array_offset ==> out-of-bound"
        else *)
          (* TODO: hack *)
          PVloc (Prov_some alloc_id, addr')
    | PVfunptr sym ->
        (* TODO *)
        failwith "UB: array_offset ==> funptr"

let offsetof_ival tagDefs tag_sym membr_ident =
  let (xs, _) = Common.offsetsof tagDefs tag_sym in
  let pred (ident, _, _) =
    Common.ident_equal ident membr_ident in
  match List.find_opt pred xs with
    | Some (_, _, offset) ->
        IVint (N.of_int offset)
    | None ->
        (* NOTE: this is an internal error *)
        failwith "VIP.offsetof_ival: invalid membr_ident"

let member_shift_ptrval ptrval tag_sym membr_ident : pointer_value =
  (* TODO: need an effectful variant in the interface to have the errors inside the monad *)
  match ptrval with
    | PVnull ->
        failwith "UB: member_offset ==> NULL"
    | PVloc (Prov_empty, _) ->
        failwith "UB: member_offset ==> @empty"
    | PVloc (Prov_some alloc_id, addr) ->
        let addr' = N.(add addr (ival_to_int (offsetof_ival (Tags.tagDefs ()) tag_sym membr_ident))) in
        PVloc (Prov_some alloc_id, addr')
        (* lookup_alloc alloc_id >>= fun alloc ->
        let addr' = N.add addr (N.of_int (Common.sizeof ty)) in
        if alloc.killed then
          failwith "TODO UB, member_offset ==> killed"
        else if not (in_bounds addr' alloc) then
          failwith "TODO UB, member_offset ==> out-of-bound"
        else
          PVloc (Prov_some alloc_id, addr') *)
    | PVfunptr sym ->
        failwith "UB: member_offset ==> funptr"

let eff_array_shift_ptrval loc ptrval ty ival : pointer_value memM =
  match ptrval with
    | PVnull ->
        fail (MerrVIP (VIP_array_shift VIP_null))
    | PVloc (Prov_empty, _) ->
        fail (MerrVIP (VIP_array_shift VIP_empty))
    | PVloc (Prov_some alloc_id, addr) ->
        lookup_alloc alloc_id >>= fun alloc ->
          let addr' = N.(add addr (mul (ival_to_int ival) (N.of_int (Common.sizeof ty)))) in
        if not (in_bounds addr' alloc) then
          fail (MerrVIP (VIP_array_shift VIP_out_of_bound))
        else
          return (PVloc (Prov_some alloc_id, addr'))
    | PVfunptr sym ->
        fail (MerrVIP (VIP_array_shift VIP_funptr))

let eff_member_shift_ptrval _ tag_sym membr_ident ptrval =
  return (member_shift_ptrval tag_sym membr_ident ptrval)

let memcpy loc ptrval1 ptrval2 sz_ival : pointer_value memM =
  let sz = ival_to_int sz_ival in
  (* TODO: if ptrval1 and ptrval2 overlap ==> UB *)
  (* TODO: copy ptrval2 into ptrval1 *)
  (* NOTE: we are using the pure array_shift because if we go out of bound there is a UB right away *)
  let rec aux i =
    if Nat_big_num.less i sz then
      load loc Ctype.unsigned_char (array_shift_ptrval ptrval2 Ctype.unsigned_char (IVint i)) >>= fun (_, mval) ->
      store loc Ctype.unsigned_char false (array_shift_ptrval ptrval1 Ctype.unsigned_char (IVint i)) mval >>= fun _ ->
      aux (N.succ i)
    else
      return ptrval1 in
  aux N.zero

let memcmp ptrval1 ptrval2 sz_ival : integer_value memM =
  let size_n = ival_to_int sz_ival in
  let rec get_bytes ptrval acc = function
  | 0 ->
      return (List.rev acc)
  | size ->
      load Cerb_location.unknown Ctype.unsigned_char ptrval >>= function
        | (_, MVinteger (_, byte_ival)) ->
            let ptr' = array_shift_ptrval ptrval Ctype.unsigned_char (IVint N.(succ zero)) in
            get_bytes ptr' (ival_to_int byte_ival :: acc) (size-1)
        | _ ->
            assert false in
  get_bytes ptrval1 [] (Nat_big_num.to_int size_n) >>= fun bytes1 ->
  get_bytes ptrval2 [] (Nat_big_num.to_int size_n) >>= fun bytes2 ->
  
  let open N in
  return (
    IVint (
      List.fold_left (fun acc (n1, n2) ->
        if equal acc zero then of_int (N.compare n1 n2) else acc
      ) zero (List.combine bytes1 bytes2)))

let realloc _ tid al_ival ptrval size_ival : pointer_value memM =
  not_implemented "VIP.realloc"


let va_start: (Ctype.ctype * pointer_value) list -> integer_value memM =
  fun _ -> not_implemented "VIP.va_start"
let va_copy: integer_value -> integer_value memM =
  fun _ -> not_implemented "VIP.va_copy"
let va_arg: integer_value -> Ctype.ctype -> pointer_value memM =
  fun _ _ -> not_implemented "VIP.va_arg"
let va_end: integer_value -> unit memM =
  fun _ -> not_implemented "VIP.va_end"
let va_list: Nat_big_num.num -> ((Ctype.ctype * pointer_value) list) memM =
  fun _ -> not_implemented "VIP.va_list"


let copy_alloc_id ival ptrval : pointer_value memM =
  match ptrval with
    | PVloc (Prov_some alloc_id, _) ->
        lookup_alloc alloc_id >>= fun alloc ->
        if alloc.killed then
          fail (MerrVIP (VIP_copy_alloc_id VIP_killed))
        else
          let n = ival_to_int ival in
          if not N.(less_equal alloc.base n && less_equal n (add alloc.base alloc.length)) then
            fail (MerrVIP (VIP_copy_alloc_id VIP_out_of_bound))
          else
            return (PVloc (Prov_some alloc_id, n))
    | _ ->
        fail (MerrVIP VIP_copy_alloc_id_invalid)

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
let eq_ival ival1 ival2 =
  Some (N.equal (ival_to_int ival1) (ival_to_int ival2))
let lt_ival ival1 ival2 =
Some (N.less (ival_to_int ival1) (ival_to_int ival2))
let le_ival ival1 ival2 =
Some (N.less_equal (ival_to_int ival1) (ival_to_int ival2))

let eval_integer_value ival =
  Some (ival_to_int ival)

(* Floating value constructors *)
let zero_fval =
  0.0
let one_fval =
  1.0
let str_fval str =
  float_of_string str

(* Floating value destructors *)
let case_fval fval _ fconcrete =
  fconcrete fval

(* Predicates on floating values *)
let op_fval fop fval1 fval2 =
  match fop with
    | MC.FloatAdd ->
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

(* Integer <-> Floating casting constructors *)
let fvfromint ival =
  (* NOTE: if n is too big, the float will be truncated *)
  float_of_string (N.to_string (ival_to_int ival))

  let ivfromfloat _ fval =
    IVint (N.of_float fval)


(* Memory value constructors *)
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

(* Memory value destructor *)
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

(* For race detection *)
let sequencePoint : unit memM =
  (* No unseq-race detection *)
  return ()

(* pretty printing *)
open PPrint
open Cerb_pp_prelude

let string_of_provenance = function
  | Prov_empty ->
      "@empty"
  | Prov_some alloc_id ->
      "@" ^ Nat_big_num.to_string alloc_id

let pp_pointer_value ?(is_verbose=false) = function
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
    !^ "Loc" ^^ P.parens (P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string addr)))))

let pp_integer_value_for_core = function
  | IVint n ->
      !^ (Nat_big_num.to_string n)
  | IVloc (prov, addr) ->
      (* TODO: should this not be an error? *)
      !^ "Loc" ^^ P.parens (P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string addr)))))


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

let pp_pretty_pointer_value = pp_pointer_value ~is_verbose:false
let pp_pretty_integer_value ?basis ~use_upper = pp_integer_value
let pp_pretty_mem_value ?basis ~use_upper = pp_mem_value

(* Coq pretty printing *)

let pp_pair_for_coq p1 p2 (a, b) = P.parens (p1 a ^^ !^"," ^^ p2 b)

let pp_triple_for_coq p1 p2 p3 (a, b, c) = P.parens (p1 a ^^ !^"," ^^ p2 b ^^ !^"," ^^ p3 c)

let pp_list_for_coq pp_elem xs =
  !^"["
  ^^^ List.fold_left
        (fun acc x ->
          if acc == P.empty then
            pp_elem x
          else
            acc ^^ !^";" ^^^ pp_elem x)
        P.empty
        xs
  ^^^ !^"]"

(* internal *)
let pp_address_for_coq n = !^(N.to_string n)

let pp_provenance_for_coq = function
  | Prov_empty -> !^"Prov_empty"
  | Prov_some alloc_id -> !^"(Prov_some" ^^^ !^(Nat_big_num.to_string alloc_id) ^^ !^")"

let pp_location_for_coq (prov, addr) =
  pp_pair_for_coq pp_provenance_for_coq pp_address_for_coq (prov, addr) 

let pp_integer_value_for_coq = function
  | IVloc loc -> 
    !^"(Mem.IVloc" ^^^  pp_location_for_coq loc ^^ !^")"
  | IVint n -> !^"(Mem.IVint" ^^^ (pp_address_for_coq n) ^^ !^")"

let pp_floating_value_for_coq (f:floating_value) = !^ (string_of_float f)

 let pp_pointer_value_for_coq pp_symbol = function
   | PVnull -> !^"PVnull"
   | PVloc loc -> !^"(PVloc" ^^^ pp_location_for_coq loc ^^ !^")"
   | PVfunptr sym -> !^"(PVfunptr" ^^^ pp_symbol sym ^^ !^")"


let rec pp_mem_value_for_coq pp_symbol pp_integer_type pp_floating_type pp_ctype pp_identifier = function
  | MVunspecified ct -> 
    !^"(Mem.MVunspecified" ^^^ pp_ctype ct ^^ !^")"
  | MVinteger (ity, ival) ->
    !^"(Mem.MVinteger" ^^^ pp_pair_for_coq pp_integer_type pp_integer_value_for_coq (ity, ival) ^^ !^")"
  | MVfloating (fty, fval) ->
    !^"(Mem.MVfloating" ^^^ pp_pair_for_coq pp_floating_type pp_floating_value_for_coq (fty, fval) ^^ !^")"
  | MVpointer (ct, pval) ->
    !^"(Mem.MVpointer" ^^^ pp_pair_for_coq pp_ctype (pp_pointer_value_for_coq pp_symbol) (ct, pval) ^^ !^")"
  | MVarray vals ->
    !^"(Mem.MVarray" ^^^ pp_list_for_coq (pp_mem_value_for_coq pp_symbol pp_integer_type pp_floating_type pp_ctype pp_identifier) vals ^^ !^")"
  | MVstruct (sym, fields) ->
    !^"(Mem.MVstruct" ^^^ pp_symbol sym ^^^
    pp_list_for_coq (fun (id, ct, mv) -> 
      pp_triple_for_coq pp_identifier pp_ctype (pp_mem_value_for_coq pp_symbol pp_integer_type pp_floating_type pp_ctype pp_identifier) (id, ct, mv)) fields ^^ !^")"
  | MVunion (sym, id, mv) ->
    !^"(Mem.MVunion" ^^^ pp_symbol sym ^^^ pp_identifier id ^^^ (pp_mem_value_for_coq pp_symbol pp_integer_type pp_floating_type pp_ctype pp_identifier) mv ^^ !^")"

(* Helper for triple printing *)
and pp_triple p1 p2 p3 (a, b, c) = 
  P.parens (p1 a ^^ !^"," ^^ p2 b ^^ !^"," ^^ p3 c)

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


(* JSON serialisation *)
type ui_value = {
  kind: [ `Unspec | `Basic | `Char | `Pointer | `Unspecptr
        | `Funptr | `Intptr | `Padding ];
  size: int; (* number of square on the left size of the row *)
  path: string list; (* tag list *)
  value: string;
  prov: provenance;
  bytes: AbsByte.t list option;
  typ: ctype option;
}


(* 
   
type allocation = {
  base: address;
  length: N.num; (* INVARIANT >= 0 *)
  killed: bool;
  (* NON-semantics fields *)
  ty: Ctype.ctype;
  prefix: Symbol.prefix;
}

*)

type ui_alloc = {
  id: int;
  base: string;
  length: int;
  killed: bool;
  prefix: Symbol.prefix;
  (* dyn: bool; (* dynamic memory *) *)
  ty: ctype;
  values: ui_value list;
}

let rec mk_ui_values st bs ty mval : ui_value list =
  let mk_ui_values = mk_ui_values st in
  let mk_scalar kind v p bs_opt =
    [{ kind; size = Common.sizeof ty; path = []; value = v;
       prov = p; typ = Some ty; bytes = bs_opt }] in
  let mk_pad n v =
    { kind = `Padding; size = n; typ = None; path = []; value = v;
      prov = Prov_empty; bytes = None } in
  let add_path p r = { r with path = p :: r.path } in
  match mval with
    | MVunspecified (Ctype (_, Pointer _)) ->
        mk_scalar `Unspecptr "unspecified" Prov_empty (Some bs)
    | MVunspecified _ ->
        mk_scalar `Unspec "unspecified" Prov_empty (Some bs)
    | MVinteger (cty, ival) ->
      let (prov, n) = match ival with
        | IVloc (prov, addr) -> (prov, addr)
        | IVint n -> (Prov_empty, n) in
      begin match cty with
        | Char | Signed Ichar | Unsigned Ichar ->
          mk_scalar `Char (N.to_string n) prov None
        | Ptrdiff_t | Signed Intptr_t | Unsigned Intptr_t ->
          mk_scalar `Intptr (N.to_string n) prov None
        | _ ->
          mk_scalar `Basic (N.to_string n) prov None
      end
    | MVfloating (_, f) ->
        mk_scalar `Basic (string_of_float f) Prov_empty None
    | MVpointer (_, ptrval) ->
      begin match ptrval with
        | PVnull ->
            mk_scalar `Pointer "NULL" Prov_empty None
        | PVloc (prov, addr) ->
            mk_scalar `Pointer (N.to_string addr) prov (Some bs)
        | PVfunptr sym ->
            mk_scalar `Funptr (Pp_symbol.to_string_pretty sym) Prov_empty None
      end
    | MVarray mvals ->
      begin match ty with
        | Ctype (_, Array (elem_ty, _)) ->
          (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs/unions *)
          let size = Common.sizeof elem_ty in
          let (rev_rows, _, _) = List.fold_left begin fun (acc, i, acc_bs) mval ->
              let row = List.map (add_path (string_of_int i)) @@ mk_ui_values acc_bs elem_ty mval in
              (row::acc, i+1, L.drop size acc_bs)
            end ([], 0, bs) mvals
          in List.concat @@ (List.rev rev_rows)
        | _ ->
          failwith "mk_ui_values: array type is wrong"
      end
    | MVstruct (tag_sym, _) ->
        let open N in
        (* NOTE: we recombine the bytes to get paddings *)
        (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs *)
        let (bs1, bs2) = L.split_at (Common.sizeof ty) bs in
            let (rev_rowss, _, bs') = List.fold_left begin
            fun (acc_rowss, previous_offset, acc_bs) (Symbol.Identifier (_, memb), memb_ty, memb_offset_) ->
              let memb_offset = of_int memb_offset_ in
              let pad = to_int (sub memb_offset previous_offset) in
              let acc_bs' = L.drop pad acc_bs in
              let (mval, acc_bs'') = abst memb_ty acc_bs' in
              let rows = mk_ui_values acc_bs' memb_ty mval in
              let rows' = List.map (add_path memb) rows in
              (* TODO: set padding value here *)
              let rows'' = if pad = 0 then rows' else mk_pad pad "" :: rows' in
              (rows''::acc_rowss, N.add memb_offset (of_int (Common.sizeof memb_ty)), acc_bs'')
          end ([], N.zero, bs1) (fst (Common.offsetsof (Tags.tagDefs ()) tag_sym))
        in List.concat (List.rev rev_rowss)
    | MVunion (tag_sym, Symbol.Identifier (_, memb), mval) ->
        List.map (add_path memb) (mk_ui_values bs ty mval) (* FIXME: THE TYPE IS WRONG *)

let mk_ui_alloc st id (alloc: allocation) : ui_alloc =
  (* let ty = match alloc.ty with Some ty -> ty | None -> Ctype ([], Array (Ctype ([], Basic (Integer Char)), Some alloc.length)) in *)
  let length = N.to_int alloc.length in
  let bs = fetch_bytes st.bytemap alloc.base length in
  let (mval, _) = abst alloc.ty bs in
  {
    id;
    base = N.to_string alloc.base;
    length;
    killed = alloc.killed;
    (* dyn = List.mem alloc.base st.dynamic_addrs; *)
    ty = alloc.ty;
    prefix = alloc.prefix;
    values = mk_ui_values st bs alloc.ty mval;
  }

let serialise_prov = function
  | Prov_empty ->
      `Assoc [ ("kind", `String "empty") ]
  | Prov_some n ->
      `Assoc [ ("kind", `String "prov")
             ; ("value", `Int (N.to_int n)) ]

  let serialise_ui_values (v:ui_value) : Cerb_json.json =
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
            ("path", `List (List.map Cerb_json.of_string v.path));
            ("value", `String v.value);
            ("prov", serialise_prov v.prov);
            ("type", Cerb_json.of_option (fun ty -> `String (String_core_ctype.string_of_ctype ty)) v.typ);
            ("bytes", Cerb_json.of_option (fun bs -> `List (List.map (AbsByte.to_json serialise_prov) bs)) v.bytes); ]

let serialise_ui_alloc (a:ui_alloc) : Cerb_json.json =
  `Assoc [ ("id", `Int a.id)
         ; ("base", `String a.base)
         ; ("prefix", serialise_prefix a.prefix)
         ; ("dyn", `Bool false) (* TODO *)
         ; ("type", `String (String_core_ctype.string_of_ctype a.ty))
         ; ("size", `Int a.length)
         ; ("values", `List (List.map serialise_ui_values a.values))
         ; ("exposed", `Bool false); (* TODO *) ]

let serialise_mem_state dig (st: mem_state) : Cerb_json.json =
  let allocs =
    IntMap.filter (fun _ (alloc : allocation) ->
      match alloc.prefix with
        | Symbol.PrefSource (_, syms) -> List.exists (fun (Symbol.Symbol (hash, _, _)) -> hash = dig) syms
        | Symbol.PrefStringLiteral (_, hash) -> hash = dig
        | Symbol.PrefCompoundLiteral (_, hash) -> hash = dig
        | Symbol.PrefFunArg (_, hash, _) -> hash = dig
        | Symbol.PrefMalloc -> true
        | _ -> false
    ) st.allocations in
  `Assoc [ ("map", serialise_int_map (fun id alloc -> serialise_ui_alloc @@ mk_ui_alloc st id alloc) allocs)
         ; ("last_used", Cerb_json.of_option (fun v -> `Int (N.to_int v)) st.last_used); ]
  (* not_implemented "VIP.serialise_mem_state" *)
