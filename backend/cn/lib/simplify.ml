module LC = LogicalConstraints
module IT = IndexTerms
open IndexTerms
open Terms

module ITPair = struct
  type it_pair = IT.t * IT.t [@@deriving eq, ord]

  type t = it_pair

  let equal = equal_it_pair

  let compare = compare_it_pair
end

module ITPairMap = Map.Make (ITPair)
module ITSet = Set.Make (IT)

type simp_ctxt =
  { global : Global.t;
    values : IT.t Sym.Map.t;
    simp_hook : IT.t -> IT.t option
  }

let default global = { global; values = Sym.Map.empty; simp_hook = (fun _ -> None) }

let do_ctz_z z =
  let rec loop z found =
    if Z.equal Z.zero z then
      assert false
    else (
      let q, r = Z.div_rem z (Z.of_int 2) in
      if Z.equal r Z.zero then loop q (found + 1) else found)
  in
  if Z.equal Z.zero z then None else Some (loop z 0)


module IndexTerms = struct
  let z1 = z_ Z.one (Cerb_location.other __FUNCTION__)

  let z0 = z_ Z.zero (Cerb_location.other __FUNCTION__)

  let rec dest_int_addition ts it =
    let loc = IT.loc it in
    match IT.term it with
    | Const (Z i1) ->
      if fst ts || ITSet.mem z1 (snd ts) then ([ (z1, i1) ], z0) else ([], it)
    | Binop (Add, a, b) ->
      let a_xs, a_r = dest_int_addition ts a in
      let b_xs, b_r = dest_int_addition ts b in
      ( a_xs @ b_xs,
        if IT.equal a_r z0 then
          b_r
        else if IT.equal b_r z0 then
          a_r
        else
          add_ (a_r, b_r) loc )
    | Binop (Sub, a, b) ->
      let a_xs, a_r = dest_int_addition ts a in
      let b_xs, b_r = dest_int_addition ts b in
      let b_xs_neg = List.map (fun (it, i) -> (it, Z.sub Z.zero i)) b_xs in
      (a_xs @ b_xs_neg, if IT.equal b_r z0 then a_r else sub_ (a_r, b_r) loc)
    | Binop (Mul, a, IT (Const (Z b_i), _, z_loc)) ->
      let a_xs, a_r = dest_int_addition ts a in
      let a_xs_mul = List.map (fun (it, i) -> (it, Z.mul i b_i)) a_xs in
      (a_xs_mul, if IT.equal a_r z0 then z0 else mul_ (a_r, z_ b_i z_loc) loc)
    | Binop (Mul, IT (Const (Z a_i), _, _z_loc), b) ->
      let b_xs, b_r = dest_int_addition ts b in
      let b_xs_mul = List.map (fun (it, i) -> (it, Z.mul i a_i)) b_xs in
      (b_xs_mul, if IT.equal b_r z0 then z0 else mul_ (z_ a_i loc, b_r) loc)
    | _ -> if fst ts || ITSet.mem it (snd ts) then ([ (it, Z.of_int 1) ], z0) else ([], it)


  (* group a list into adjacent equal sublists *)
  let group eq xs =
    let rec f y ys gps zs =
      match zs with
      | [] -> (y :: ys) :: gps
      | z :: tl_zs when eq z y -> f y (z :: ys) gps tl_zs
      | z :: tl_zs -> f z [] ((y :: ys) :: gps) tl_zs
    in
    match xs with [] -> [] | x :: xs -> f x [] [] xs


  let simp_int_comp a b loc =
    let a_elems = dest_int_addition (true, ITSet.empty) a |> fst |> List.map fst in
    let b_elems = dest_int_addition (true, ITSet.empty) b |> fst |> List.map fst in
    let repeated =
      List.sort IT.compare (a_elems @ b_elems)
      |> group IT.equal
      |> List.filter (fun xs -> List.length xs >= 2)
      |> List.map List.hd
      |> ITSet.of_list
    in
    let a_xs, a_r = dest_int_addition (false, repeated) a in
    let b_xs, b_r = dest_int_addition (false, repeated) b in
    let a_xs_neg = List.map (fun (it, i) -> (it, Z.sub Z.zero i)) a_xs in
    let xs =
      List.sort (fun a b -> IT.compare (fst a) (fst b)) (a_xs_neg @ b_xs)
      |> group (fun a b -> IT.equal (fst a) (fst b))
      |> List.map (fun xs ->
        (fst (List.hd xs), List.fold_left Z.add Z.zero (List.map snd xs)))
      |> List.filter (fun t -> not (Z.equal (snd t) Z.zero))
    in
    let mul_z t i =
      if Z.equal i Z.one then
        t
      else if IT.equal z1 t then
        z_ i loc
      else
        mul_ (t, z_ i loc) loc
    in
    let add_x t (x, i) =
      if Z.equal i Z.zero then
        t
      else if Z.gt i (Z.of_int 0) then
        if IT.equal t z0 then mul_z x i else add_ (t, mul_z x i) loc
      else
        sub_ (t, mul_z x (Z.sub Z.zero i)) loc
    in
    (a_r, List.fold_left add_x b_r xs)


  let simp_comp_if_int a b loc =
    if BaseTypes.equal (IT.basetype a) BaseTypes.Integer then
      simp_int_comp a b loc
    else
      (a, b)


  let rec record_member_reduce it member =
    let loc = IT.loc it in
    match IT.term it with
    | Record members -> List.assoc Id.equal member members
    | RecordUpdate ((t, m), v) ->
      if Id.equal m member then
        v
      else
        record_member_reduce t member
    | ITE (cond, it1, it2) ->
      ite_ (cond, record_member_reduce it1 member, record_member_reduce it2 member) loc
    | _ ->
      let member_tys = BT.record_bt (IT.bt it) in
      let member_bt = List.assoc Id.equal member member_tys in
      IT.recordMember_ ~member_bt (it, member) loc


  (* let rec datatype_member_reduce it member member_bt = *)
  (*   match IT.term it with *)
  (*     | DatatypeCons (nm, members_rec) -> *)
  (*       let members = BT.record_bt (IT.bt members_rec) in *)
  (*       if List.exists (Id.equal member) (List.map fst members) *)
  (*       then record_member_reduce members_rec member *)
  (*       else IT.IT (DatatypeMember (it, member), member_bt) *)
  (*     | ITE (cond, it1, it2) -> *)
  (*       ite_ (cond, datatype_member_reduce it1 member member_bt, *)
  (*           datatype_member_reduce it2 member member_bt) *)
  (*     | _ -> IT.IT (DatatypeMember (it, member), member_bt) *)

  let rec tuple_nth_reduce it n item_bt =
    let loc = IT.loc it in
    match IT.term it with
    | Tuple items -> List.nth items n
    | ITE (cond, it1, it2) ->
      ite_ (cond, tuple_nth_reduce it1 n item_bt, tuple_nth_reduce it2 n item_bt) loc
    | _ -> IT.nthTuple_ ~item_bt (n, it) loc


  let rec accessor_reduce (f : IT.t -> IT.t option) it =
    let bt = IT.bt it in
    let step, it2 =
      match IT.term it with
      | RecordMember (t, m) -> (true, record_member_reduce (accessor_reduce f t) m)
      (* | DatatypeMember (t, m) -> *)
      (*     (true, datatype_member_reduce (accessor_reduce f t) m bt) *)
      | NthTuple (n, t) -> (true, tuple_nth_reduce (accessor_reduce f t) n bt)
      | _ -> (false, it)
    in
    if step && not (IT.equal it it2) then
      accessor_reduce f it2
    else (
      match f it with None -> it | Some it3 -> accessor_reduce f it3)


  let cast_reduce bt it =
    let loc = IT.loc it in
    match (bt, IT.is_const it) with
    | _, _ when BT.equal (IT.bt it) bt -> it
    | BT.Bits (sign, sz), Some (Terms.Bits ((sign2, sz2), z), _) ->
      let z = BT.normalise_to_range (sign, sz) (BT.normalise_to_range (sign2, sz2) z) in
      num_lit_ z bt loc
    | _ -> IT (Cast (bt, it), bt, loc)


  let num_lit_norm bt z =
    match bt with
    | BT.Bits (sign, sz) -> IT.num_lit_ (BT.normalise_to_range (sign, sz) z) bt
    | _ -> IT.num_lit_ z bt


  let rec simp ?(inline_functions = false) simp_ctxt =
    let aux it = simp ~inline_functions simp_ctxt it in
    fun it ->
      let the_term = match simp_ctxt.simp_hook it with None -> it | Some it' -> it' in
      let (IT (the_term_, the_bt, the_loc)) = the_term in
      match the_term_ with
      | Sym _ when BT.equal the_bt BT.Unit -> unit_ the_loc
      | Sym sym ->
        (match Sym.Map.find_opt sym simp_ctxt.values with
         | Some (IT ((Const _ | Sym _), _, _) as v) -> v
         | _ -> the_term)
      | Const _ -> the_term
      | Binop (Add, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b, IT.get_num_z a, IT.get_num_z b) with
         | _, _, Some i1, Some i2 -> num_lit_norm the_bt (Z.add i1 i2) the_loc
         | IT (Const (Q q1), _, _), IT (Const (Q q2), _, _), _, _ ->
           IT (Const (Q (Q.add q1 q2)), the_bt, the_loc)
         | a, _, _, Some z when Z.equal z Z.zero -> a
         | _, b, Some z, _ when Z.equal z Z.zero -> b
         | ( IT (Binop (Add, c, IT (Const (Z i1), _, _)), _, _),
             IT (Const (Z i2), _, _),
             _,
             _ ) ->
           add_ (c, z_ (Z.add i1 i2) the_loc) the_loc
         | _, _, _, _ -> IT (Binop (Add, a, b), the_bt, the_loc))
      | Binop (Sub, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b, the_bt, IT.get_num_z a, IT.get_num_z b) with
         | _, _, BT.Integer, _, _ when IT.equal a b -> int_ 0 the_loc
         | _, _, BT.Real, _, _ when IT.equal a b -> q_ (0, 1) the_loc
         | _, _, _, Some i1, Some i2 -> num_lit_norm the_bt (Z.sub i1 i2) the_loc
         | IT (Const (Q q1), _, _), IT (Const (Q q2), _, _), _, _, _ ->
           IT (Const (Q (Q.sub q1 q2)), the_bt, the_loc)
         | a, _, _, _, Some z when Z.equal z Z.zero -> a
         | IT (Binop (Add, c, d), _, _), _, _, _, _ when IT.equal c b ->
           (* (c + d) - b when c = b *)
           d
         | _, _, _, _, _ -> IT (Binop (Sub, a, b), the_bt, the_loc))
      | Binop (Mul, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b) with
         | _, IT (Const (Z i2), _, _) when Z.equal i2 Z.zero -> int_ 0 the_loc
         | IT (Const (Z i1), _, _), _ when Z.equal i1 Z.zero -> int_ 0 the_loc
         | _, IT (Const (Z i2), _, _) when Z.equal i2 Z.one -> a
         | IT (Const (Z i1), _, _), _ when Z.equal i1 Z.one -> b
         | IT (Const (Z i1), _, _), IT (Const (Z i2), _, _) ->
           IT (Const (Z (Z.mul i1 i2)), the_bt, the_loc)
         | _ -> IT (Binop (Mul, a, b), the_bt, the_loc))
      | Binop (Div, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b) with
         | IT (Const (Z a), _, _), IT (Const (Z b), _, _) ->
           assert (Z.lt Z.zero b);
           z_ (Z.div a b) the_loc
         | IT (Const (Z a), _, _), _ when Z.equal a Z.zero -> int_ 0 the_loc
         | _, IT (Const (Z b), _, _) when Z.equal b Z.one -> a
         | IT (Binop (Mul, b', c), _, _), _ when IT.equal b' b -> c
         | _ -> IT (Binop (Div, a, b), the_bt, the_loc))
      | Binop (Exp, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b, get_num_z a, get_num_z b) with
         | IT (Const (Z a), _, _), IT (Const (Z b), _, _), _, _ when Z.fits_int b ->
           z_ (Z.pow a (Z.to_int b)) the_loc
         | _, _, Some a, Some b when Z.fits_int b ->
           num_lit_norm the_bt (Z.pow a (Z.to_int b)) the_loc
         | _ -> IT.exp_ (a, b) the_loc)
      | Binop (Rem, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b) with
         | IT (Const (Z z1), _, _), IT (Const (Z z2), _, _)
           when Z.geq z1 Z.zero && Z.gt z2 Z.zero ->
           IT (Const (Z (Z.rem z1 z2)), the_bt, the_loc)
         | IT (Const (Z a), _, _), _ when Z.equal a Z.zero -> int_ 0 the_loc
         | IT (Binop (Mul, IT (Const (Z y), _, _), _), _, _), IT (Const (Z y'), _, _)
           when Z.equal y y' && Z.gt y Z.zero ->
           int_ 0 the_loc
         | _, IT (Const (Z b), _, _) when Z.equal b Z.one -> int_ 0 the_loc
         | _ -> IT (Binop (Rem, a, b), the_bt, the_loc))
      | Binop (Mod, a, b) ->
        let a = aux a in
        let b = aux b in
        (match (a, b, get_num_z a, get_num_z b) with
         | _, _, Some a, Some b when Z.geq a Z.zero && Z.gt b Z.zero ->
           num_lit_norm the_bt (Z.rem a b) the_loc
         | _, _, Some a, _ when Z.equal a Z.zero -> int_lit_ 0 the_bt the_loc
         | ( IT (Binop (Mul, IT (Const (Z y), _, _), _), _, _),
             IT (Const (Z y'), _, _),
             _,
             _ )
           when Z.equal y y' && Z.gt y Z.zero ->
           int_ 0 the_loc
         | _, _, _, Some b when Z.equal b Z.one -> int_lit_ 0 the_bt the_loc
         | _ -> IT (Binop (Mod, a, b), the_bt, the_loc))
      | Binop (LT, a, b) ->
        let a = aux a in
        let b = aux b in
        let a, b = simp_comp_if_int a b the_loc in
        (match (a, b) with
         | IT (Const (Z z1), _, _), IT (Const (Z z2), _, _) ->
           IT (Const (Bool (Z.lt z1 z2)), the_bt, the_loc)
         | IT (Const (Q q1), _, _), IT (Const (Q q2), _, _) ->
           IT (Const (Bool (Q.lt q1 q2)), the_bt, the_loc)
         | _, _ -> IT (Binop (LT, a, b), the_bt, the_loc))
      | Binop (LE, a, b) ->
        let a = aux a in
        let b = aux b in
        let a, b = simp_comp_if_int a b the_loc in
        (match (a, b, IT.get_num_z a, IT.get_num_z b) with
         | _, _, Some z1, Some z2 -> IT (Const (Bool (Z.leq z1 z2)), the_bt, the_loc)
         | IT (Const (Q q1), _, _), IT (Const (Q q2), _, _), _, _ ->
           IT (Const (Bool (Q.leq q1 q2)), the_bt, the_loc)
         | _, _, _, _ when IT.equal a b -> bool_ true the_loc
         | ( IT (Binop (Rem, _, IT (Const (Z z1), _, _)), _, _),
             IT (Const (Z z2), _, _),
             _,
             _ )
         | ( IT (Binop (Mod, _, IT (Const (Z z1), _, _)), _, _),
             IT (Const (Z z2), _, _),
             _,
             _ )
           when Z.gt z1 Z.zero && Z.gt z2 Z.zero && Z.equal z1 (Z.add z2 Z.one) ->
           bool_ true the_loc
         | _, _, _, _ -> IT (Binop (LE, a, b), the_bt, the_loc))
      | Binop (Min, a, b) ->
        let a = aux a in
        let b = aux b in
        if IT.equal a b then
          a
        else
          IT (Binop (Min, a, b), the_bt, the_loc)
      | Binop (Max, a, b) ->
        let a = aux a in
        let b = aux b in
        if IT.equal a b then
          a
        else
          IT (Binop (Max, a, b), the_bt, the_loc)
      | Binop (And, it1, it2) ->
        let it1 = aux it1 in
        let it2 = aux it2 in
        (match (it1, it2) with
         | IT (Const (Bool true), _, _), _ -> it2
         | _, IT (Const (Bool true), _, _) -> it1
         | IT (Const (Bool false), _, _), _ -> bool_ false the_loc
         | _, IT (Const (Bool false), _, _) -> bool_ false the_loc
         | _ when IT.equal it1 it2 -> it1
         | _ -> IT (Binop (And, it1, it2), the_bt, the_loc))
      | Binop (Or, it1, it2) ->
        let it1 = aux it1 in
        let it2 = aux it2 in
        (match (it1, it2) with
         | IT (Const (Bool true), _, _), _ -> bool_ true the_loc
         | _, IT (Const (Bool true), _, _) -> bool_ true the_loc
         | IT (Const (Bool false), _, _), _ -> it2
         | _, IT (Const (Bool false), _, _) -> it1
         | _ when IT.equal it1 it2 -> it1
         | _ -> IT (Binop (Or, it1, it2), the_bt, the_loc))
      | Binop (Implies, a, b) ->
        let a = aux a in
        let b = aux b in
        if IT.equal a b then
          IT (Const (Bool true), the_bt, the_loc)
        else (
          match (a, b) with
          | IT (Const (Bool false), _, _), _ -> IT (Const (Bool true), the_bt, the_loc)
          | _, IT (Const (Bool true), _, _) -> IT (Const (Bool true), the_bt, the_loc)
          | IT (Const (Bool true), _, _), _ -> b
          | _, IT (Const (Bool false), _, _) -> not_ a the_loc
          | _ -> IT (Binop (Implies, a, b), the_bt, the_loc))
      | Unop (op, a) ->
        let a = aux a in
        (match (op, IT.term a) with
         | Not, Const (Bool b) -> bool_ (not b) the_loc
         | Not, Unop (Not, x) -> x
         | Negate, Unop (Negate, x) -> x
         | Negate, Const (Z z) -> z_ (Z.neg z) the_loc
         | Negate, Const (Bits ((sign, width), z)) ->
           num_lit_ (Z.neg z) (BT.Bits (sign, width)) the_loc
         | Negate, Const (Q q) -> q1_ (Q.neg q) the_loc
         | BW_CTZ_NoSMT, Const (Z z) ->
           (match do_ctz_z z with
            | None -> IT (Unop (op, a), the_bt, the_loc)
            | Some i -> int_ i the_loc)
         | BW_CTZ_NoSMT, Const (Bits (bits, z)) ->
           (match do_ctz_z (BT.normalise_to_range bits z) with
            | None -> IT (Unop (op, a), the_bt, the_loc)
            | Some i -> int_lit_ i the_bt the_loc)
         | BW_FFS_NoSMT, Const (Z z) ->
           if Z.equal z Z.zero then
             int_ 0 the_loc
           else
             int_ (Option.get (do_ctz_z z) + 1) the_loc
         | BW_FFS_NoSMT, Const (Bits (bits, z)) ->
           let z = BT.normalise_to_range bits z in
           if Z.equal z Z.zero then
             int_lit_ 0 the_bt the_loc
           else
             int_lit_ (Option.get (do_ctz_z z) + 1) the_bt the_loc
         | _, _ -> IT (Unop (op, a), the_bt, the_loc))
      | ITE (a, b, c) ->
        let a = aux a in
        let b = aux b in
        let c = aux c in
        (match a with
         | IT (Const (Bool true), _, _) -> b
         | IT (Const (Bool false), _, _) -> c
         | _ when IT.equal b c -> b
         | _ -> IT (ITE (a, b, c), the_bt, the_loc))
      | Binop (EQ, a, b) ->
        let a = aux a in
        let b = aux b in
        let is_c t = Option.is_some (IT.is_const t) in
        (match (a, b) with
         | _ when IT.equal a b -> IT (Const (Bool true), the_bt, the_loc)
         | IT (Const (Z z1), _, _), IT (Const (Z z2), _, _) ->
           bool_ (Z.equal z1 z2) the_loc
         | ( IT (Const (Bits (bits_info1, z1)), _, _),
             IT (Const (Bits (bits_info2, z2)), _, _) ) ->
           let z1 = BT.normalise_to_range bits_info1 z1 in
           let z2 = BT.normalise_to_range bits_info2 z2 in
           bool_ (Z.equal z1 z2) the_loc
         (* Work-around for https://github.com/Z3Prover/z3/issues/7352 *)
         | ( IT (ArrayShift { base = base1; ct = ct1; index = index1 }, _, _),
             IT (ArrayShift { base = base2; ct = ct2; index = index2 }, _, _) )
           when Sctypes.equal ct1 ct2 && IT.equal index1 index2 ->
           eq_ (base1, base2) the_loc
         (* (cond ? const-1 : const-2) == const-3 *)
         | IT (ITE (cond, t1, t2), _, _), t3 when (is_c t1 || is_c t2) && is_c t3 ->
           aux
             (and_
                [ impl_ (cond, eq_ (t1, t3) the_loc) the_loc;
                  impl_ (not_ cond the_loc, eq_ (t2, t3) the_loc) the_loc
                ]
                the_loc)
         | t3, IT (ITE _, _, _) when is_c t3 -> aux (eq_ (b, a) the_loc)
         | IT (Tuple items1, _, _), IT (Tuple items2, _, _) ->
           aux (and_ (List.map2 (fun a b -> eq__ a b the_loc) items1 items2) the_loc)
         | IT (Record members1, _, _), IT (Record members2, _, _) ->
           assert (List.for_all2 (fun x y -> Id.equal (fst x) (fst y)) members1 members2);
           aux
             (and_
                (List.map2 (fun x y -> eq_ (snd x, snd y) the_loc) members1 members2)
                the_loc)
         | _, _ -> eq_ (a, b) the_loc)
      | EachI ((i1, (s, s_bt), i2), t) ->
        let s' = Sym.fresh_same s in
        let t = IndexTerms.subst (make_rename ~from:s ~to_:s') t in
        let t = aux t in
        IT (EachI ((i1, (s', s_bt), i2), t), the_bt, the_loc)
      | Tuple its ->
        let its = List.map aux its in
        IT (Tuple its, the_bt, the_loc)
      | NthTuple (n, it) ->
        let it = aux it in
        tuple_nth_reduce it n the_bt
      | Struct (tag, members) ->
        (match members with
         | (_, IT (StructMember (str, _), _, _)) :: _
           when BT.equal (Struct tag) (IT.bt str)
                && List.for_all
                     (function
                       | mem, IT (StructMember (str', mem'), _, _) ->
                         Id.equal mem mem' && IT.equal str str'
                       | _ -> false)
                     members ->
           str
         | _ ->
           let members = List.map (fun (member, it) -> (member, aux it)) members in
           IT (Struct (tag, members), the_bt, the_loc))
      | StructMember (s_it, member) ->
        let s_it = aux s_it in
        let rec make t =
          match t with
          | IT (Struct (_, members), _, _) -> List.assoc Id.equal member members
          | IT (ITE (cond, it1, it2), _, _) ->
            (* (if cond then it1 else it2) . member --> (if cond then it1.member else
               it2.member) *)
            ite_ (cond, make it1, make it2) the_loc
          | _ -> IT (StructMember (t, member), the_bt, the_loc)
        in
        make s_it
      | StructUpdate ((t, m), v) ->
        let t = aux t in
        let v = aux v in
        IT (StructUpdate ((t, m), v), the_bt, the_loc)
      | Record members ->
        let members = List.map (fun (member, it) -> (member, aux it)) members in
        IT (Record members, the_bt, the_loc)
      | RecordMember (it, member) ->
        let it = aux it in
        record_member_reduce it member
      | RecordUpdate ((t, m), v) ->
        let t = aux t in
        let v = aux v in
        IT (RecordUpdate ((t, m), v), the_bt, the_loc)
      (* TODO (DCM, VIP) revisit *)
      | Binop (LTPointer, a, b) ->
        let a = aux a in
        let b = aux b in
        if isIntegerToPointerCast a || isIntegerToPointerCast b then (
          let loc = Cerb_location.other __FUNCTION__ in
          aux (lt_ (addr_ a loc, addr_ b loc) the_loc))
        else if IT.equal a b then
          bool_ false the_loc
        else
          IT (Binop (LTPointer, a, b), the_bt, the_loc)
      | Binop (LEPointer, a, b) ->
        let a = aux a in
        let b = aux b in
        if isIntegerToPointerCast a || isIntegerToPointerCast b then (
          let loc = Cerb_location.other __FUNCTION__ in
          aux (le_ (addr_ a loc, addr_ b loc) the_loc))
        else if IT.equal a b then
          bool_ true the_loc
        else
          IT (Binop (LEPointer, a, b), the_bt, the_loc)
      | Binop (op, a, b) -> IT (Binop (op, aux a, aux b), the_bt, the_loc)
      | Constructor (ctor, ts) ->
        IT (Constructor (ctor, List.map_snd aux ts), the_bt, the_loc)
      | WrapI (ity, t) ->
        let t = aux t in
        (match get_num_z t with
         | None -> IT (WrapI (ity, t), the_bt, the_loc)
         | Some z ->
           (match Memory.bt_of_sct (Sctypes.Integer ity) with
            | BT.Bits _ -> num_lit_norm the_bt z the_loc
            | _ -> IT (WrapI (ity, t), the_bt, the_loc)))
      | Cast (cbt, a) ->
        let a = aux a in
        cast_reduce cbt a
      | MemberShift (t, tag, member) ->
        IT (MemberShift (aux t, tag, member), the_bt, the_loc)
      | ArrayShift { base; ct; index } ->
        let base = aux base in
        let base, index =
          match base with
          | IT (ArrayShift { base = base2; ct = ct2; index = i2 }, _, _)
            when Sctypes.equal ct ct2 ->
            (base2, IT.add_ (index, i2) the_loc)
          | _ -> (base, index)
        in
        let index = aux index in
        (match get_num_z index with
         | Some z when Z.equal Z.zero z -> base
         | _ -> IT (ArrayShift { base; ct; index }, the_bt, the_loc))
      | SizeOf ct -> int_lit_ (Memory.size_of_ctype ct) Memory.size_bt the_loc
      | Representable (ct, t) -> IT (Representable (ct, aux t), the_bt, the_loc)
      | Good (ct, t) -> IT (Good (ct, aux t), the_bt, the_loc)
      | Aligned a -> IT (Aligned { t = aux a.t; align = aux a.align }, the_bt, the_loc)
      | MapConst (index_bt, t) ->
        let t = aux t in
        IT (MapConst (index_bt, t), the_bt, the_loc)
      | MapSet (t1, t2, t3) ->
        let t1 = aux t1 in
        let t2 = aux t2 in
        let t3 = aux t3 in
        IT (MapSet (t1, t2, t3), the_bt, the_loc)
      | MapGet (map, index) ->
        let map = aux map in
        let index = aux index in
        let rec make map index =
          match map with
          | IT (MapDef ((s, abt), body), _, _) ->
            assert (BT.equal abt (IT.bt index));
            aux (IT.subst (IT.make_subst [ (s, index) ]) body)
          | IT (MapSet (map', index', value'), _, _) ->
            (match (index, index') with
             | _, _ when IT.equal index index' -> value'
             | IT (Const (Z z), _, _), IT (Const (Z z'), _, _) when not (Z.equal z z') ->
               make map' index
             | _ -> IT (MapGet (map, index), the_bt, the_loc))
          (* | IT (Bool_op (ITE (cond, map1, map2)), bt') -> *)
          (*    (\* (if cond then map1 else map2)[index] --> *)
          (*     * if cond then map1[index] else map2[index] *\) *)
          (*    ite_ (cond,  *)
          (*          make map1 index,  *)
          (*          make map2 index) *)
          | _ -> IT (MapGet (map, index), the_bt, the_loc)
        in
        make map index
      | MapDef ((s, abt), body) ->
        let s' = Sym.fresh_same s in
        let body = IndexTerms.subst (make_rename ~from:s ~to_:s') body in
        let body = aux body in
        IT (MapDef ((s', abt), body), the_bt, the_loc)
      | Apply (name, args) ->
        let args = List.map aux args in
        let t = IT (Apply (name, args), the_bt, the_loc) in
        if not inline_functions then
          t
        else (
          let def = Sym.Map.find name simp_ctxt.global.logical_functions in
          match Definition.Function.try_open_fun def args with
          | Some inlined -> aux inlined
          | None -> t)
      | _ ->
        (* FIXME: it's problematic that some term shapes aren't even explored *)
        it


  let simp_flatten simp_ctxt term =
    match simp simp_ctxt term with
    | IT (Const (Bool true), _, _) -> []
    | IT (Binop (And, lc1, lc2), _, _) -> [ lc1; lc2 ]
    | lc -> [ lc ]


  let eval simp_ctxt = simp ~inline_functions:true simp_ctxt
end

module LogicalConstraints = struct
  open IndexTerms

  let simp ?(inline_functions = false) simp_ctxt lc =
    match lc with
    | LC.T it -> LC.T (simp ~inline_functions simp_ctxt it)
    | LC.Forall ((q, qbt), body) ->
      let q, body = IT.alpha_rename q body in
      let body = simp ~inline_functions simp_ctxt body in
      (match body with
       | IT (Const (Bool true), _, _) -> LC.T (bool_ true (IT.loc body))
       | _ -> LC.Forall ((q, qbt), body))
end

module Request = struct
  module Predicate = struct
    open Request.Predicate

    let simp simp_ctxt (p : t) =
      { name = p.name;
        pointer = IndexTerms.simp simp_ctxt p.pointer;
        iargs = List.map (IndexTerms.simp simp_ctxt) p.iargs
      }
  end

  module QPredicate = struct
    open Request.QPredicate

    let simp simp_ctxt (qp : t) =
      let qp = alpha_rename qp in
      let permission = IndexTerms.simp_flatten simp_ctxt qp.permission in
      Request.QPredicate.
        { name = qp.name;
          pointer = IndexTerms.simp simp_ctxt qp.pointer;
          q = qp.q;
          q_loc = qp.q_loc;
          step = IndexTerms.simp simp_ctxt qp.step;
          permission = and_ permission (IT.loc qp.permission);
          iargs = List.map (IndexTerms.simp simp_ctxt) qp.iargs
        }
  end

  let simp simp_ctxt : Request.t -> Request.t = function
    | P p -> P (Predicate.simp simp_ctxt p)
    | Q qp -> Q (QPredicate.simp simp_ctxt qp)
end
