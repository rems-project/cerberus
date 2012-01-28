open AST
open BinInt
open BinPos
open Coqlib
open Datatypes
open Integers
open Memdata
open Memtype
open Values
open Wf_Z

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val update : coq_Z -> 'a1 -> (coq_Z -> 'a1) -> coq_Z -> 'a1 **)

let update x v f y =
  if zeq y x then v else f y

module Mem = 
 struct 
  type mem_ = { mem_contents : (block -> coq_Z -> memval);
                mem_access : (block -> coq_Z -> permission option);
                bounds : (block -> coq_Z*coq_Z); nextblock : 
                block; maxaddress : coq_Z;
                ptr2int : (block -> coq_Z -> coq_Z option);
                int2ptr : (coq_Z -> (block*coq_Z) option) }
  
  (** val mem__rect :
      ((block -> coq_Z -> memval) -> (block -> coq_Z -> permission option) ->
      (block -> coq_Z*coq_Z) -> block -> coq_Z -> (block -> coq_Z -> coq_Z
      option) -> (coq_Z -> (block*coq_Z) option) -> __ -> __ -> __ -> __ ->
      __ -> __ -> 'a1) -> mem_ -> 'a1 **)
  
  let mem__rect f m =
    let { mem_contents = x; mem_access = x0; bounds = x1; nextblock = x2;
      maxaddress = x3; ptr2int = x4; int2ptr = x5 } = m
    in
    f x x0 x1 x2 x3 x4 x5 __ __ __ __ __ __
  
  (** val mem__rec :
      ((block -> coq_Z -> memval) -> (block -> coq_Z -> permission option) ->
      (block -> coq_Z*coq_Z) -> block -> coq_Z -> (block -> coq_Z -> coq_Z
      option) -> (coq_Z -> (block*coq_Z) option) -> __ -> __ -> __ -> __ ->
      __ -> __ -> 'a1) -> mem_ -> 'a1 **)
  
  let mem__rec f m =
    let { mem_contents = x; mem_access = x0; bounds = x1; nextblock = x2;
      maxaddress = x3; ptr2int = x4; int2ptr = x5 } = m
    in
    f x x0 x1 x2 x3 x4 x5 __ __ __ __ __ __
  
  (** val mem_contents : mem_ -> block -> coq_Z -> memval **)
  
  let mem_contents x = x.mem_contents
  
  (** val mem_access : mem_ -> block -> coq_Z -> permission option **)
  
  let mem_access x = x.mem_access
  
  (** val bounds : mem_ -> block -> coq_Z*coq_Z **)
  
  let bounds x = x.bounds
  
  (** val nextblock : mem_ -> block **)
  
  let nextblock x = x.nextblock
  
  (** val maxaddress : mem_ -> coq_Z **)
  
  let maxaddress x = x.maxaddress
  
  (** val ptr2int : mem_ -> block -> coq_Z -> coq_Z option **)
  
  let ptr2int x = x.ptr2int
  
  (** val int2ptr : mem_ -> coq_Z -> (block*coq_Z) option **)
  
  let int2ptr x = x.int2ptr
  
  type mem = mem_
  
  (** val perm_order_dec : permission -> permission -> bool **)
  
  let perm_order_dec p1 p2 =
    match p1 with
      | Freeable -> true
      | Writable -> (match p2 with
                       | Freeable -> false
                       | _ -> true)
      | Readable ->
          (match p2 with
             | Readable -> true
             | Nonempty -> true
             | _ -> false)
      | Nonempty -> (match p2 with
                       | Nonempty -> true
                       | _ -> false)
  
  (** val perm_order'_dec : permission option -> permission -> bool **)
  
  let perm_order'_dec op p =
    match op with
      | Some p0 -> perm_order_dec p0 p
      | None -> false
  
  (** val perm_dec : mem -> block -> coq_Z -> permission -> bool **)
  
  let perm_dec m b ofs p =
    perm_order'_dec (m.mem_access b ofs) p
  
  (** val range_perm_dec :
      mem -> block -> coq_Z -> coq_Z -> permission -> bool **)
  
  let range_perm_dec m b lo hi p =
    let h =
      natlike_rec2 true (fun z _ h0 ->
        if h0 then perm_dec m b (coq_Zplus lo z) p else false)
    in
    let s = zlt lo hi in if s then h (coq_Zminus hi lo) else true
  
  (** val valid_access_dec :
      mem -> memory_chunk -> block -> coq_Z -> permission -> bool **)
  
  let valid_access_dec m chunk b ofs p =
    let s = range_perm_dec m b ofs (coq_Zplus ofs (size_chunk chunk)) p in
    if s then coq_Zdivide_dec (align_chunk chunk) ofs else false
  
  (** val valid_pointer : mem -> block -> coq_Z -> bool **)
  
  let valid_pointer m b ofs =
    proj_sumbool (perm_dec m b ofs Nonempty)
  
  (** val empty : mem **)
  
  let empty =
    { mem_contents = (fun b ofs -> Undef); mem_access = (fun b ofs -> None);
      bounds = (fun b -> Z0,Z0); nextblock = (Zpos Coq_xH); maxaddress = Z0;
      ptr2int = (fun b ofs -> None); int2ptr = (fun z -> None) }
  
  (** val nullptr : block **)
  
  let nullptr =
    Z0
  
  (** val update_int2ptr :
      (coq_Z -> (block*coq_Z) option) -> block -> coq_Z -> coq_Z -> nat ->
      coq_Z -> (block*coq_Z) option **)
  
  let rec update_int2ptr f b maxaddress0 lo = function
    | O -> f
    | S ofs' ->
        update
          (coq_Zplus (coq_Zplus maxaddress0 (Zpos Coq_xH))
            (coq_Z_of_nat ofs')) (Some
          (b,(coq_Zplus lo (coq_Z_of_nat ofs'))))
          (update_int2ptr f b maxaddress0 lo ofs')
  
  (** val alloc : mem -> coq_Z -> coq_Z -> mem_*block **)
  
  let alloc m lo hi =
    { mem_contents = (update m.nextblock (fun ofs -> Undef) m.mem_contents);
      mem_access =
      (update m.nextblock (fun ofs ->
        if if proj_sumbool (zle lo ofs)
           then proj_sumbool (zlt ofs hi)
           else false
        then Some Freeable
        else None) m.mem_access); bounds =
      (update m.nextblock (lo,hi) m.bounds); nextblock =
      (coq_Zsucc m.nextblock); maxaddress =
      (coq_Zplus m.maxaddress (if zlt lo hi then coq_Zminus hi lo else Z0));
      ptr2int =
      (update m.nextblock (fun ofs ->
        if if proj_sumbool (zle lo ofs)
           then proj_sumbool (zlt ofs hi)
           else false
        then Some
               (coq_Zplus (coq_Zplus m.maxaddress (Zpos Coq_xH))
                 (coq_Zminus ofs lo))
        else None) m.ptr2int); int2ptr =
      (update_int2ptr m.int2ptr m.nextblock m.maxaddress lo
        (nat_of_Z (coq_Zminus hi lo))) },m.nextblock
  
  (** val clearN :
      (block -> coq_Z -> memval) -> block -> coq_Z -> coq_Z -> block -> coq_Z
      -> memval **)
  
  let clearN m b lo hi b' ofs =
    if zeq b' b
    then if if proj_sumbool (zle lo ofs)
            then proj_sumbool (zlt ofs hi)
            else false
         then Undef
         else m b' ofs
    else m b' ofs
  
  (** val clear_ptr2int :
      (block -> coq_Z -> coq_Z option) -> block -> coq_Z -> coq_Z -> block ->
      coq_Z -> coq_Z option **)
  
  let clear_ptr2int f b lo hi b' ofs =
    if zeq b' b
    then if if proj_sumbool (zle lo ofs)
            then proj_sumbool (zlt ofs hi)
            else false
         then None
         else f b' ofs
    else f b' ofs
  
  (** val clear_int2ptr :
      (coq_Z -> (block*coq_Z) option) -> block -> coq_Z -> coq_Z -> coq_Z ->
      (block*coq_Z) option **)
  
  let clear_int2ptr f b lo hi i =
    match f i with
      | Some p ->
          let b',ofs = p in
          if zeq b' b
          then if if proj_sumbool (zle lo ofs)
                  then proj_sumbool (zlt ofs hi)
                  else false
               then None
               else Some (b',ofs)
          else Some (b',ofs)
      | None -> None
  
  (** val unchecked_free : mem -> block -> coq_Z -> coq_Z -> mem **)
  
  let unchecked_free m b lo hi =
    { mem_contents = (clearN m.mem_contents b lo hi); mem_access =
      (update b (fun ofs ->
        if if proj_sumbool (zle lo ofs)
           then proj_sumbool (zlt ofs hi)
           else false
        then None
        else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
      nextblock = m.nextblock; maxaddress = m.maxaddress; ptr2int =
      m.ptr2int; int2ptr = m.int2ptr }
  
  (** val free : mem -> block -> coq_Z -> coq_Z -> mem option **)
  
  let free m b lo hi =
    if range_perm_dec m b lo hi Freeable
    then Some (unchecked_free m b lo hi)
    else None
  
  (** val free_list : mem -> ((block*coq_Z)*coq_Z) list -> mem option **)
  
  let rec free_list m = function
    | [] -> Some m
    | p::l' ->
        let p0,hi = p in
        let b,lo = p0 in
        (match free m b lo hi with
           | Some m' -> free_list m' l'
           | None -> None)
  
  (** val getN : nat -> coq_Z -> (coq_Z -> memval) -> memval list **)
  
  let rec getN n p c =
    match n with
      | O -> []
      | S n' -> (c p)::(getN n' (coq_Zplus p (Zpos Coq_xH)) c)
  
  (** val load : memory_chunk -> mem -> block -> coq_Z -> coq_val option **)
  
  let load chunk m b ofs =
    if valid_access_dec m chunk b ofs Readable
    then Some
           (decode_val chunk
             (getN (size_chunk_nat chunk) ofs (m.mem_contents b)))
    else None
  
  (** val loadv : memory_chunk -> mem -> coq_val -> coq_val option **)
  
  let loadv chunk m = function
    | Vptr (b, ofs) ->
        load chunk m b
          (Int.signed (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) ofs)
    | _ -> None
  
  (** val loadbytes :
      mem -> block -> coq_Z -> coq_Z -> memval list option **)
  
  let loadbytes m b ofs n =
    if range_perm_dec m b ofs (coq_Zplus ofs n) Readable
    then Some (getN (nat_of_Z n) ofs (m.mem_contents b))
    else None
  
  (** val setN :
      memval list -> coq_Z -> (coq_Z -> memval) -> coq_Z -> memval **)
  
  let rec setN vl p c =
    match vl with
      | [] -> c
      | v::vl' -> setN vl' (coq_Zplus p (Zpos Coq_xH)) (update p v c)
  
  (** val store :
      memory_chunk -> mem -> block -> coq_Z -> coq_val -> mem option **)
  
  let store chunk m b ofs v =
    if valid_access_dec m chunk b ofs Writable
    then Some { mem_contents =
           (update b (setN (encode_val chunk v) ofs (m.mem_contents b))
             m.mem_contents); mem_access = m.mem_access; bounds = m.bounds;
           nextblock = m.nextblock; maxaddress = m.maxaddress; ptr2int =
           m.ptr2int; int2ptr = m.int2ptr }
    else None
  
  (** val storev :
      memory_chunk -> mem -> coq_val -> coq_val -> mem option **)
  
  let storev chunk m addr v =
    match addr with
      | Vptr (b, ofs) ->
          store chunk m b
            (Int.signed (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))) ofs) v
      | _ -> None
  
  (** val drop_perm :
      mem -> block -> coq_Z -> coq_Z -> permission -> mem option **)
  
  let drop_perm m b lo hi p =
    if range_perm_dec m b lo hi p
    then Some { mem_contents =
           (update b (fun ofs ->
             if if if proj_sumbool (zle lo ofs)
                   then proj_sumbool (zlt ofs hi)
                   else false
                then negb (proj_sumbool (perm_order_dec p Readable))
                else false
             then Undef
             else m.mem_contents b ofs) m.mem_contents); mem_access =
           (update b (fun ofs ->
             if if proj_sumbool (zle lo ofs)
                then proj_sumbool (zlt ofs hi)
                else false
             then Some p
             else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
           nextblock = m.nextblock; maxaddress = m.maxaddress; ptr2int =
           m.ptr2int; int2ptr = m.int2ptr }
    else None
  
  (** val valid_access_store :
      mem -> memory_chunk -> block -> coq_Z -> coq_val -> mem **)
  
  let valid_access_store m1 chunk b ofs v =
    let s = valid_access_dec m1 chunk b ofs Writable in
    if s
    then { mem_contents =
           (update b (setN (encode_val chunk v) ofs (m1.mem_contents b))
             m1.mem_contents); mem_access = m1.mem_access; bounds =
           m1.bounds; nextblock = m1.nextblock; maxaddress = m1.maxaddress;
           ptr2int = m1.ptr2int; int2ptr = m1.int2ptr }
    else assert false (* absurd case *)
  
  (** val range_perm_free : mem -> block -> coq_Z -> coq_Z -> mem **)
  
  let range_perm_free m1 b lo hi =
    unchecked_free m1 b lo hi
  
  (** val range_perm_drop_2 :
      mem -> block -> coq_Z -> coq_Z -> permission -> mem **)
  
  let range_perm_drop_2 m b lo hi p =
    let s = range_perm_dec m b lo hi p in
    if s
    then { mem_contents =
           (update b (fun ofs ->
             if if if proj_sumbool (zle lo ofs)
                   then proj_sumbool (zlt ofs hi)
                   else false
                then negb (proj_sumbool (perm_order_dec p Readable))
                else false
             then Undef
             else m.mem_contents b ofs) m.mem_contents); mem_access =
           (update b (fun ofs ->
             if if proj_sumbool (zle lo ofs)
                then proj_sumbool (zlt ofs hi)
                else false
             then Some p
             else m.mem_access b ofs) m.mem_access); bounds = m.bounds;
           nextblock = m.nextblock; maxaddress = m.maxaddress; ptr2int =
           m.ptr2int; int2ptr = m.int2ptr }
    else assert false (* absurd case *)
  
  (** val mem_inj_rect : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let mem_inj_rect f m1 m2 f0 =
    f0 __ __
  
  (** val mem_inj_rec : meminj -> mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let mem_inj_rec f m1 m2 f0 =
    f0 __ __
  
  (** val extends__rect : mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let extends__rect m1 m2 f =
    f __ __
  
  (** val extends__rec : mem -> mem -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let extends__rec m1 m2 f =
    f __ __
  
  (** val inject__rect :
      meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a1 **)
  
  let inject__rect f m1 m2 f0 =
    f0 __ __ __ __ __ __
  
  (** val inject__rec :
      meminj -> mem -> mem -> (__ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a1 **)
  
  let inject__rec f m1 m2 f0 =
    f0 __ __ __ __ __ __
  
  (** val flat_inj : block -> meminj **)
  
  let flat_inj thr b =
    if zlt b thr then Some (b,Z0) else None
 end

