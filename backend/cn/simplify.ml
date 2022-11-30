module LC = LogicalConstraints
module IT = IndexTerms
open IndexTerms
open Terms


module ITPair = struct 
  type it_pair = IT.t * IT.t
  [@@deriving eq, ord]
  type t = it_pair
  let equal = equal_it_pair
  let compare = compare_it_pair
end

module ITPairMap = Map.Make(ITPair)

module ITSet = Set.Make(IT)
module LCSet = Set.Make(LC)


type simp_ctxt = {
    global : Global.t;
    values : IT.t SymMap.t;
    equalities: bool ITPairMap.t;
    lcs : LCSet.t;
  }

let default global = {global;
    values = SymMap.empty; equalities = ITPairMap.empty; lcs = LCSet.empty}




module IndexTerms = struct

  let z1 = z_ Z.one
  let z0 = z_ Z.zero

  let rec dest_int_addition ts it = match IT.term it with
      | Lit (Z i1) -> if fst ts || ITSet.mem z1 (snd ts) then ([(z1, i1)], z0) else ([], it)
      | Arith_op (Add (a, b)) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let (b_xs, b_r) = dest_int_addition ts b in
          (a_xs @ b_xs, if IT.equal a_r z0 then b_r else if IT.equal b_r z0 then a_r
              else add_ (a_r, b_r))
      | Arith_op (Sub (a, b)) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let (b_xs, b_r) = dest_int_addition ts b in
          let b_xs_neg = List.map (fun (it, i) -> (it, Z.sub Z.zero i)) b_xs in
          (a_xs @ b_xs_neg, if IT.equal b_r z0 then a_r else sub_ (a_r, b_r))
      | Arith_op (Mul (a, IT (Lit (Z b_i), _))) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let a_xs_mul = List.map (fun (it, i) -> (it, Z.mul i b_i)) a_xs in
          (a_xs_mul, if IT.equal a_r z0 then z0 else mul_ (a_r, z_ b_i))
      | Arith_op (Mul (IT (Lit (Z a_i), _), b)) ->
          let (b_xs, b_r) = dest_int_addition ts b in
          let b_xs_mul = List.map (fun (it, i) -> (it, Z.mul i a_i)) b_xs in
          (b_xs_mul, if IT.equal b_r z0 then z0 else mul_ (z_ a_i, b_r))
      | _ -> if fst ts || ITSet.mem it (snd ts) then ([(it, Z.of_int 1)], z0) else ([], it)

  (* group a list into adjacent equal sublists *)
  let group eq xs =
      let rec f y ys gps zs = match zs with
        | [] -> ((y :: ys) :: gps)
        | (z :: tl_zs) when eq z y -> f y (z :: ys) gps tl_zs
        | (z :: tl_zs) -> f z [] ((y :: ys) :: gps) tl_zs
      in
      match xs with
        | [] -> []
        | (x :: xs) -> f x [] [] xs

  let simp_int_comp a b =
      let a_elems = dest_int_addition (true, ITSet.empty) a |> fst |> List.map fst in
      let b_elems = dest_int_addition (true, ITSet.empty) b |> fst |> List.map fst in
      let repeated = List.sort IT.compare (a_elems @ b_elems)
          |> group IT.equal
          |> List.filter (fun xs -> List.length xs >= 2)
          |> List.map List.hd |> ITSet.of_list in
      let (a_xs, a_r) = dest_int_addition (false, repeated) a in
      let (b_xs, b_r) = dest_int_addition (false, repeated) b in
      let a_xs_neg = List.map (fun (it, i) -> (it, Z.sub Z.zero i)) a_xs in
      let xs = List.sort (fun a b -> IT.compare (fst a) (fst b)) (a_xs_neg @ b_xs)
          |> group (fun a b -> IT.equal (fst a) (fst b))
          |> List.map (fun xs -> (fst (List.hd xs), List.fold_left Z.add Z.zero (List.map snd xs)))
          |> List.filter (fun t -> not (Z.equal (snd t) Z.zero))
      in
      let mul_z t i = if Z.equal i Z.one then t
          else if IT.equal z1 t then z_ i else mul_ (t, z_ i) in
      let add_x t (x, i) = if Z.equal i Z.zero then t
        else if Z.gt i (Z.of_int 0) then
          (if IT.equal t z0 then mul_z x i else add_ (t, mul_z x i))
        else sub_ (t, mul_z x (Z.sub Z.zero i))
      in
      (a_r, List.fold_left add_x b_r xs)

  let simp_comp_if_int a b = if BaseTypes.equal (IT.basetype a) BaseTypes.Integer
      then simp_int_comp a b else (a, b)



  let flatten = function
    | IT (Bool_op (And fs), _) -> List.map LC.t_ fs
    | f -> [LC.t_ f]


  let rec record_member_reduce it member =
    match IT.term it with
      | Record_op (Record members) -> List.assoc Sym.equal member members
      | Record_op (RecordUpdate ((t, m), v)) ->
        if Sym.equal m member then v
        else record_member_reduce t member
      | Bool_op (ITE (cond, it1, it2)) ->
        ite_ (cond, record_member_reduce it1 member, record_member_reduce it2 member)
      | _ ->
        let member_tys = BT.record_bt (IT.bt it) in
        let member_bt = List.assoc Sym.equal member member_tys in
        IT.recordMember_ ~member_bt (it, member)

  let rec datatype_member_reduce it member member_bt =
    match IT.term it with
      | Datatype_op (DatatypeCons (nm, members_rec)) ->
        let members = BT.record_bt (IT.bt members_rec) in
        if List.exists (Sym.equal member) (List.map fst members)
        then record_member_reduce members_rec member
        else IT.IT (Datatype_op (DatatypeMember (it, member)), member_bt)
      | Bool_op (ITE (cond, it1, it2)) ->
        ite_ (cond, datatype_member_reduce it1 member member_bt,
            datatype_member_reduce it2 member member_bt)
      | _ -> IT.IT (Datatype_op (DatatypeMember (it, member)), member_bt)

  let rec tuple_nth_reduce it n item_bt =
    match IT.term it with
      | Tuple_op (Tuple items) -> List.nth items n
      | Bool_op (ITE (cond, it1, it2)) ->
        ite_ (cond, tuple_nth_reduce it1 n item_bt, tuple_nth_reduce it2 n item_bt)
      | _ -> IT.nthTuple_ ~item_bt (n, it)

  let rec accessor_reduce (f : IT.t -> IT.t option) it =
    let bt = IT.bt it in
    let (step, it2) = match IT.term it with
      | Record_op (RecordMember (t, m)) ->
          (true, record_member_reduce (accessor_reduce f t) m)
      | Datatype_op (DatatypeMember (t, m)) ->
          (true, datatype_member_reduce (accessor_reduce f t) m bt)
      | Tuple_op (NthTuple (n, t)) ->
          (true, tuple_nth_reduce (accessor_reduce f t) n bt)
      | _ -> (false, it)
    in
    if step && not (IT.equal it it2)
    then accessor_reduce f it2
    else begin match f it with
      | None -> it
      | Some it3 -> accessor_reduce f it3
    end

  let rec simp ?(inline_functions=false) simp_ctxt =

    let add_known_facts new_facts lcs = 
      List.fold_right LCSet.add (List.concat_map flatten new_facts) lcs
    in


    let aux2 lcs it = simp { simp_ctxt with lcs } it in
    let aux it = simp simp_ctxt it in

    let lit it bt = 
      match it with
      | Sym _ when BT.equal bt BT.Unit ->
         unit_ 
      | Sym sym ->
         begin match SymMap.find_opt sym simp_ctxt.values with
         | Some it when Option.is_some (is_lit it) -> it
         | _ -> IT (Lit (Sym sym), bt)
         end
      | Z z ->
         IT (Lit (Z z), bt)
      | Q q ->
         IT (Lit (Q q), bt)
      | Pointer z ->
         IT (Lit (Pointer z), bt)
      | Bool b ->
         IT (Lit (Bool b), bt)
      | Unit ->
         IT (Lit Unit, bt)
      | Default bt' -> 
         IT (Lit (Default bt'), bt)
      | Null -> 
         IT (Lit Null, bt)
    in

    let arith_op it bt = 
      match it with
      | Add (a, b) ->
         let a = aux a in
         let b = aux b in
         begin match a, b with
         | IT (Lit (Z i1), _), IT (Lit (Z i2), _) ->
            IT (Lit (Z (Z.add i1 i2)), bt)
         | IT (Lit (Q q1), _), IT (Lit (Q q2), _) ->
            IT (Lit (Q (Q.add q1 q2)), bt) 
         | a, IT (Lit (Z z), _) when Z.equal z Z.zero ->
            a
         | IT (Lit (Z z), _), a when Z.equal z Z.zero ->
            a
         | IT (Arith_op (Add (c, IT (Lit (Z i1), _))), _), 
           IT (Lit (Z i2), _) ->
            add_ (c, z_ (Z.add i1 i2))
         | _, _ ->
            IT (Arith_op (Add (a, b)), bt)
         end
      | Sub (a, b) ->
         let a = aux a in
         let b = aux b in
         begin match a, b, bt with
         | _, _, BT.Integer when IT.equal a b ->
            int_ 0
         | _, _, BT.Real when IT.equal a b ->
            q_ (0, 1)
         | IT (Lit (Z i1), _), IT (Lit (Z i2), _), _ ->
            IT (Lit (Z (Z.sub i1 i2)), bt)
         | IT (Lit (Q q1), _), IT (Lit (Q q2), _), _ ->
            IT (Lit (Q (Q.sub q1 q2)), bt)
         | _, IT (Lit (Z i2), _), _ when Z.equal i2 Z.zero ->
            a
         | IT (Arith_op (Add (c, d)), _), _, _ when IT.equal c b ->
            (* (c + d) - b  when  c = b *)
            d
         | _, _, _ ->
            IT (Arith_op (Sub (a, b)), bt) 
         end
      | Mul (a, b) ->
         let a = aux a in
         let b = aux b in
         begin match a, b with
         | _, IT (Lit (Z i2), _) when Z.equal i2 Z.zero ->
            int_ 0
         | IT (Lit (Z i1), _), _ when Z.equal i1 Z.zero ->
            int_ 0
         | _, IT (Lit (Z i2), _) when Z.equal i2 Z.one ->
            a
         | IT (Lit (Z i1), _), _ when Z.equal i1 Z.one ->
            b
         | IT (Lit (Z i1), _), IT (Lit (Z i2), _) ->
            IT (Lit (Z (Z.mul i1 i2)), bt)
         | _ ->
            IT (Arith_op (Mul (a, b)), bt)
         end
      | MulNoSMT (a, b) ->
         IT (Arith_op (MulNoSMT (aux a, aux b)), bt)
      | Div (a, b) ->
         let a = aux a in
         let b = aux b in 
         begin match a, b with
         | IT (Lit (Z a), _), IT (Lit (Z b), _) ->
            z_ (Z.div a b)
         | IT (Lit (Z a), _), _ when Z.equal a (Z.zero) -> 
            int_ 0
         | _, IT (Lit (Z b), _) when Z.equal b Z.one -> 
            a
         | IT (Arith_op (Mul (b', c)), _), _ when IT.equal b' b ->
            c
         | _ ->
            IT (Arith_op (Div (a, b)), bt) 
         end
      | DivNoSMT (a, b) ->
         IT (Arith_op (DivNoSMT (aux a, aux b)), bt)
      | Exp (a, b) ->
         let a = aux a in
         let b = aux b in
         begin match a, b with
         | IT (Lit (Z a), _), IT (Lit (Z b), _) when Z.fits_int b ->
            z_ (Z.pow a (Z.to_int b))
         | _ ->
            IT.exp_ (a, b)
         end
      | ExpNoSMT (a, b) ->
         let a = aux a in
         let b = aux b in
         IT.exp_no_smt_ (a, b)
      | Rem (a, b) ->
         let a = aux a in
         let b = aux b in 
         begin match a, b with
         | IT (Lit (Z z1), _), IT (Lit (Z z2), _) when Z.geq z1 Z.zero && Z.gt z2 Z.zero ->
           IT (Lit (Z (Z.rem z1 z2)), bt)
         | IT (Lit (Z a), _), _ when Z.equal a (Z.zero) -> 
            int_ 0
         | IT (Arith_op (Mul (IT (Lit (Z y), _), _)), _), 
           IT (Lit (Z y'), _) when Z.equal y y' && Z.gt y Z.zero ->
            int_ 0
         | _, IT (Lit (Z b), _) when Z.equal b Z.one ->
            int_ 0
         | _ ->
            IT (Arith_op (Rem (a, b)), bt) 
         end
      | RemNoSMT (a, b) ->
         IT (Arith_op (RemNoSMT (aux a, aux b)), bt)
      | Mod (a, b) ->
         let a = aux a in
         let b = aux b in
         begin match a, b with
         | IT (Lit (Z a), _), _ when Z.equal a (Z.zero) ->
            int_ 0
         | IT (Arith_op (Mul (IT (Lit (Z y), _), _)), _), 
           IT (Lit (Z y'), _) when Z.equal y y' && Z.gt y Z.zero ->
            int_ 0
         | _, IT (Lit (Z b), _) when Z.equal b Z.one ->
            int_ 0
         | _ ->
            IT (Arith_op (Mod (a, b)), bt) 
         end
      | ModNoSMT (a, b) ->
         IT (Arith_op (ModNoSMT (aux a, aux b)), bt)
      | LT (a, b) -> 
        let a = aux a in
        let b = aux b in
        let (a, b) = simp_comp_if_int a b in
        begin match a, b with
        | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
           IT (Lit (Bool (Z.lt z1 z2)), bt)
        | IT (Lit (Q q1), _), IT (Lit (Q q2), _) ->
           IT (Lit (Bool (Q.lt q1 q2)), bt)
        | _, _ ->
           IT (Arith_op (LT (a, b)), bt)
        end
      | LE (a, b) -> 
        let a = aux a in
        let b = aux b in
        let (a, b) = simp_comp_if_int a b in
        begin match a, b with
        | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
           IT (Lit (Bool (Z.leq z1 z2)), bt)
        | IT (Lit (Q q1), _), IT (Lit (Q q2), _) ->
           IT (Lit (Bool (Q.leq q1 q2)), bt)
        | _, _ when IT.equal a b ->
           bool_ true
        | IT (Arith_op (Rem (_, IT (Lit (Z z1), _))), _), 
          IT (Lit (Z z2), _) 
        | IT (Arith_op (Mod (_, IT (Lit (Z z1), _))), _), 
          IT (Lit (Z z2), _) 
             when
               Z.gt z1 Z.zero &&
                 Z.gt z2 Z.zero &&
                   Z.equal z1 (Z.add z2 Z.one) ->
           bool_ true
        | _, _ ->
           IT (Arith_op (LE (a, b)), bt)
        end
      | Min (a, b) ->
         let a = aux a in
         let b = aux b in
         if IT.equal a b then a else
         IT (Arith_op (Min (a, b)), bt)
      | Max (a, b) ->
         let a = aux a in
         let b = aux b in
         if IT.equal a b then a else
         IT (Arith_op (Max (a, b)), bt)
      | IntToReal a ->
         let a = aux a in
         IT (Arith_op (IntToReal a), bt)
      | RealToInt a ->
         let a = aux a in
         IT (Arith_op (RealToInt a), bt)
      | XORNoSMT (a, b) ->
         IT (Arith_op (XORNoSMT (aux a, aux b)), bt)

    in

    let bool_op it bt = 
      match it with
      | And its ->
         let rec make acc = function
           | [] -> 
              begin match acc with
              | [] -> bool_ true
              | [r] -> r
              | _ -> and_ (List.rev acc)
              end
           | it :: its ->
              let it = aux2 (add_known_facts acc simp_ctxt.lcs) it in
              begin match it with
              | IT (Lit (Bool true), _) -> make acc its
              | IT (Lit (Bool false), _) -> bool_ false
              | _ when List.exists (fun c -> IT.equal (not_ c) it || IT.equal c (not_ it)) acc -> bool_ false
              | _ when List.mem IT.equal it acc -> make acc its
              | IT (Bool_op (Not (IT (Bool_op (Or ys), _))), _) -> make acc ((List.map not_ ys) @ its)
              | IT (Bool_op (And ys), _) -> make acc (ys @ its)
              | _ -> make (it :: acc) its
              end
         in
         make [] its
      | Or its ->
         let its = List.map aux its in
         let rec make acc = function
           | [] ->
              begin match acc with
              | [] -> bool_ false
              | [r] -> r
              | _ -> or_ (List.rev acc)
              end
           | it :: its ->
              begin match it with
              | IT (Lit (Bool true), _) -> bool_ true
              | IT (Lit (Bool false), _) -> make acc its
              | _ when List.exists (fun c -> IT.equal (not_ c) it || IT.equal c (not_ it)) acc -> bool_ true 
              | _ when List.mem IT.equal it acc -> make acc its
              | IT (Bool_op (Not (IT (Bool_op (And ys), _))), _) -> make acc ((List.map not_ ys) @ its)
              | IT (Bool_op (Or ys), _) -> make acc (ys @ its)
              | _ -> make (it :: acc) its
              end
         in
         make [] its
      | Impl (a, b) ->
         let a = aux a in
         let b = aux b in
         if IT.equal a b then IT (Lit (Bool true), bt)
         else
         begin match a, b with
         | IT (Lit (Bool false), _), _ ->
            IT (Lit (Bool true), bt) 
         | _, IT (Lit (Bool true), _) ->
            IT (Lit (Bool true), bt)
         | IT (Lit (Bool true), _), _ ->
            b
         | _, IT (Lit (Bool false), _) ->
            not_ a
         | _ ->
            IT (Bool_op (Impl (a, b)), bt)
         end
      | Not a ->
         let a = aux a in
         begin match a with
         | IT (Lit (Bool b), _) ->
            bool_ (not b)
         | IT (Bool_op (Not b), _) ->
            b
         | _ -> 
            IT (Bool_op (Not a), bt)
         end
      | ITE (a, b, c) ->
         let a = aux a in
         let b = aux2 (add_known_facts [a] simp_ctxt.lcs) b in
         let c = aux2 (add_known_facts [not_ a] simp_ctxt.lcs) c in
         begin match a with
         | IT (Lit (Bool true), _) -> b
         | IT (Lit (Bool false), _) -> c
         | _ when IT.equal b c -> b
         | _ -> IT (Bool_op (ITE (a, b, c)), bt)
         end
      | EQ (a, b) ->
         let a = aux a in
         let b = aux b in
         if isIntegerToPointerCast a || isIntegerToPointerCast b
         then
         aux (eq_ (pointerToIntegerCast_ a, pointerToIntegerCast_ b))
         else
         begin match a, b with
         | _ when IT.equal a b ->
           IT (Lit (Bool true), bt) 
         | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
            bool_ (Z.equal z1 z2)
         (* (cond ? z1 : z2) == z3 *)
         | IT (Bool_op (ITE (cond, 
                             IT (Lit (Z z1), _), 
                             IT (Lit (Z z2), _))), _),
           IT (Lit (Z z3), _)

         | IT (Lit (Z z3), _),
           IT (Bool_op (ITE (cond, 
                             IT (Lit (Z z1), _), 
                             IT (Lit (Z z2), _))), _) ->

            aux (
              and_ [impl_ (cond, bool_ (Z.equal z1 z3));
                    impl_ (not_ cond, bool_ (Z.equal z2 z3))]
              )
         | a, b
            when ITPairMap.mem (a,b) simp_ctxt.equalities ||
                   ITPairMap.mem (b,a) simp_ctxt.equalities 
           ->
            begin match ITPairMap.find_opt (a,b) simp_ctxt.equalities, 
                        ITPairMap.find_opt (b,a) simp_ctxt.equalities with
            | Some bool, _ -> bool_ bool
            | _, Some bool -> bool_ bool
            | _ -> eq_ (a, b)
            end
         | IT (Tuple_op (Tuple items1), _),
           IT (Tuple_op (Tuple items2), _)  ->
            aux (and_ (List.map2 eq__ items1 items2))
         | IT (Record_op (Record members1), _),
           IT (Record_op (Record members2), _)  ->
            assert (List.for_all2 (fun x y -> Sym.equal (fst x) (fst y)) members1 members2);
            aux (and_ (List.map2 (fun x y -> eq_ (snd x, snd y)) members1 members2))
         | IT (Datatype_op (DatatypeCons (nm1, members1)), _),
           IT (Datatype_op (DatatypeCons (nm2, members2)), _)  ->
            if Sym.equal nm1 nm2
            then aux (eq_ (members1, members2))
            else bool_ false
         | IT (Pointer_op (IntegerToPointerCast a), _), 
           IT (Pointer_op (IntegerToPointerCast b), _) ->
            eq_ (a, b)
         | IT (Pointer_op (PointerToIntegerCast a), _), 
           IT (Pointer_op (PointerToIntegerCast b), _) ->
            eq_ (a, b)
         | IT (Pointer_op (PointerToIntegerCast a), _), b ->
            eq_ (a, integerToPointerCast_ b)
         | _, _ ->
            eq_ (a, b)
         end
      | EachI ((i1, s, i2), t) ->
         let s' = Sym.fresh_same s in 
         let t = IndexTerms.subst (make_subst [(s, sym_ (s', bt))]) t in
         let t = aux t in
         IT (Bool_op (EachI ((i1, s', i2), t)), bt)
    in


    let tuple_op it bt = 
      match it with
      | Tuple its ->
         let its = List.map aux its in
         IT (Tuple_op (Tuple its), bt)
      | NthTuple (n, it) ->
         let it = aux it in
         tuple_nth_reduce it n bt
    in


    let struct_op it bt = 
      match it with
      | IT.Struct (tag, members) ->
         begin match members with
         | (_, IT (Struct_op (StructMember (str, _)), _)) :: _ when 
                BT.equal (Struct tag) (IT.bt str) &&
                List.for_all (function 
                    | (mem, IT (Struct_op (StructMember (str', mem')), _)) ->
                      Id.equal mem mem' && IT.equal str str'
                    | _ -> false
                  ) members
            ->
             str
         | _ ->
            let members = 
              List.map (fun (member, it) ->
                  (member, aux it)
                ) members
            in
            IT (Struct_op (IT.Struct (tag, members)), bt)
         end
      | IT.StructMember (it, member) ->
         let it = aux it in
         let rec make it = 
           match it with
           | IT (Struct_op (Struct (_, members)), _) ->
              List.assoc Id.equal member members
           | IT (Bool_op (ITE (cond, it1, it2)), _) ->
              (* (if cond then it1 else it2) . member -->
               (if cond then it1.member else it2.member) *)
              ite_ (cond, make it1, make it2)
           | _ ->
              IT (Struct_op (IT.StructMember (it, member)), bt)
         in
         make it
      | IT.StructUpdate ((t, m), v) ->
         let t = aux t in
         let v = aux v in
         IT (Struct_op (StructUpdate ((t, m), v)), bt)
    in

    let record_op it bt = 
      match it with
      | IT.Record members ->
         let members = 
           List.map (fun (member, it) ->
               (member, aux it)
             ) members
         in
         IT (Record_op (IT.Record members), bt)
      | IT.RecordMember (it, member) ->
         let it = aux it in
         record_member_reduce it member
      | IT.RecordUpdate ((t, m), v) ->
         let t = aux t in
         let v = aux v in
         IT (Record_op (RecordUpdate ((t, m), v)), bt)
    in


    let datatype_op it bt =
      match it with
      | IT.DatatypeCons (nm, members_rec) ->
         IT (Datatype_op (IT.DatatypeCons (nm, aux members_rec)), bt)
      | IT.DatatypeMember (it, member) ->
         let it = aux it in
         datatype_member_reduce it member bt
      | IT.DatatypeIsCons (nm, it) ->
         let it = aux it in
         datatype_is_cons_ nm it
    in



    (* revisit when memory model changes *)
    let pointer_op it bt = 
      match it with
      | LTPointer (a, b) ->
         let a = aux a in
         let b = aux b in
         if isIntegerToPointerCast a || isIntegerToPointerCast b
         then
         aux (lt_ (pointerToIntegerCast_ a, pointerToIntegerCast_ b))
         else if IT.equal a b
         then bool_ false
         else IT (Pointer_op (LTPointer (a, b)), bt)
      | LEPointer (a, b) ->
         let a = aux a in
         let b = aux b in
         if isIntegerToPointerCast a || isIntegerToPointerCast b
         then
         aux (le_ (pointerToIntegerCast_ a, pointerToIntegerCast_ b))
         else if IT.equal a b
         then bool_ true
         else IT (Pointer_op (LEPointer (a, b)), bt)
      | IntegerToPointerCast a ->
         let a = aux a in
         begin match a with
         | IT (Pointer_op (PointerToIntegerCast b), _) ->
            b
         | _ ->
            IT (Pointer_op (IntegerToPointerCast a), bt)
         end
      | PointerToIntegerCast a ->
         let a = aux a in
         begin match a with
         | IT (Pointer_op (IntegerToPointerCast b), _) ->
            b
         | _ ->
            IT (Pointer_op (PointerToIntegerCast a), bt)
         end
      | MemberOffset (tag, member) ->
         let layout = SymMap.find tag simp_ctxt.global.struct_decls in
         int_ (Option.get (Memory.member_offset layout member))
      | ArrayOffset (ct, t) ->
         let t = aux t in
         begin match is_z t with
         | Some z when Z.equal Z.zero z -> int_ 0
         | _ -> mul_ (int_ (Memory.size_of_ctype ct), t)
            (* IT (Pointer_op (ArrayOffset (ct, t)), bt) *)
         end
    in

    let ct_pred it bt = 
      match it with
      | Representable (ct, t) ->
         IT (CT_pred (Representable (ct, aux t)), bt)
      | Good (ct, t) ->
         IT (CT_pred (Good (ct, aux t)), bt)
      | AlignedI a -> 
         IT (CT_pred (AlignedI {t = aux a.t; align = aux a.align}), bt)
      | Aligned (t, ct) ->
         IT (CT_pred (Aligned (aux t, ct)), bt)
    in


    let map_op it bt = 
      match it with
      | Const (index_bt, t) ->
         let t = aux t in
         IT (Map_op (Const (index_bt, t)), bt)
      | Set (t1, t2, t3) ->
         let t1 = aux t1 in
         let t2 = aux t2 in
         let t3 = aux t3 in
         IT (Map_op (Set (t1, t2, t3)), bt)
      | Get (map, index) ->
         let map = aux map in
         let index = aux index in
         let rec make map index = 
           begin match map with
           | IT (Map_op (Def ((s, abt), body)), _) ->
              assert (BT.equal abt (IT.bt index));
              aux (IT.subst (IT.make_subst [(s, index)]) body)
           | IT (Map_op (Set (map', index', value')), _) ->
              begin match index, index' with
              | _, _ when IT.equal index index' ->
                 value'
              | IT (Lit (Z z), _), IT (Lit (Z z'), _) when not (Z.equal z z') ->
                 make map' index
              | _ ->
                 IT (Map_op (Get (map, index)), bt)
              end
           | IT (Bool_op (ITE (cond, map1, map2)), bt') ->
              (* (if cond then map1 else map2)[index] -->
               * if cond then map1[index] else map2[index] *)
              ite_ (cond, 
                    make map1 index, 
                    make map2 index)
           | _ ->
              IT (Map_op (Get (map, index)), bt)
           end
         in
         make map index
      | Def ((s, abt), body) ->
         let s' = Sym.fresh_same s in 
         let body = IndexTerms.subst (make_subst [(s, sym_ (s', abt))]) body in
         let body = aux body in
         IT (Map_op (Def ((s', abt), body)), bt)
    in

    (* let option_op o bt =  *)
    (*   match o with *)
    (*   | Nothing vbt ->  *)
    (*      IT (Option_op (Nothing vbt), bt) *)
    (*   | Something t ->  *)
    (*      let t = aux t in *)
    (*      IT (Option_op (Something t), bt) *)
    (*   | Is_nothing t -> *)
    (*      let t = aux t in *)
    (*      IT (Option_op (Is_nothing t), bt) *)
    (*   | Is_something t -> *)
    (*      let t = aux t in *)
    (*      IT (Option_op (Is_something t), bt) *)
    (*   | Get_some_value t -> *)
    (*      let t = aux t in *)
    (*      IT (Option_op (Get_some_value t), bt) *)
    (* in *)

    (* let letb (s, bound) body bt = *)
    (*   let bound = aux bound in *)
    (*   let s' = Sym.fresh_same s in *)
    (*   let body = IndexTerms.subst (make_subst [(s, sym_ (s', IT.bt bound))]) body in *)
    (*   let body = aux body in *)
    (*   IT (Let ((s', bound), body), bt) *)
    (* in *)

    let pred name args bt =
      let args = List.map aux args in
      let def = SymMap.find name simp_ctxt.global.logical_predicates in
      let t = IT (Pred (name, args), bt) in
      if not inline_functions then t else 
        match LogicalPredicates.try_open_pred_to_term def name args with
        | Some inlined -> aux inlined
        | None -> t
    in

    fun it ->
    if LCSet.mem (LC.T it) simp_ctxt.lcs then bool_ true else
    if LCSet.mem (LC.T (not_ it)) simp_ctxt.lcs then bool_ false else
      let (IT (it_, bt)) = it in
      match it_ with
      | Lit l -> lit l bt
      | Arith_op a -> arith_op a bt
      | Bool_op b -> bool_op b bt
      | Tuple_op t -> tuple_op t bt
      | Struct_op s -> struct_op s bt
      | Record_op r -> record_op r bt
      | Datatype_op r -> datatype_op r bt
      | Pointer_op p -> pointer_op p bt
      | List_op l -> IT (List_op l, bt)
      | Set_op s -> IT (Set_op s, bt)
      | CT_pred c -> ct_pred c bt
      | Map_op a -> map_op a bt
      | Pred (name, args) -> pred name args bt
      (* | Option_op o -> option_op o bt *)
      (* | Let ((s, bound), body) -> letb (s, bound) body bt *)


  (* let simp a b c d e it =  *)
  (*   let open Pp in *)
  (*   print stdout (item "simplifying" (IT.pp it)); *)
  (*   let it = simp a b c d e it in *)
  (*   print stdout (item "simplified" (IT.pp it)); *)
  (*   it *)



  let simp_flatten simp_ctxt term =
    match simp simp_ctxt term with
    | IT (Lit (Bool true), _) -> []
    | IT (Bool_op (And lcs), _) -> lcs
    | lc -> [lc]



  let eval simp_ctxt = 
    simp ~inline_functions:true 
      { global = simp_ctxt.global; 
        values = simp_ctxt.values; 
        equalities = ITPairMap.empty;
        lcs = LCSet.empty }

end

module LogicalConstraints = struct

  open IndexTerms

  let simp simp_ctxt lc =
    match lc with
    | LC.T it -> LC.T (simp simp_ctxt it)
    | LC.Forall ((q, qbt), body) ->
       let q, body = IT.alpha_rename (q, qbt) body in
       let body = simp simp_ctxt body in
       begin match body with
       | IT (Lit (Bool true), _) -> LC.T (bool_ true)
       | _ -> LC.Forall ((q, qbt), body)
       end

end



module ResourceTypes = struct

  open IndexTerms
  open ResourceTypes

  let simp_predicate_type simp_ctxt (p : predicate_type) = {
      name = p.name; 
      pointer = simp simp_ctxt p.pointer;
      permission = simp simp_ctxt p.permission;
      iargs = List.map (simp simp_ctxt) p.iargs;
    }

  let simp_qpredicate_type simp_ctxt (qp : qpredicate_type) =
    let qp = alpha_rename_qpredicate_type_ (Sym.fresh_same qp.q) qp in
    let permission = simp_flatten simp_ctxt qp.permission in
    let permission_lcs = LCSet.of_list (List.map LC.t_ permission) in
    let simp_lcs = LCSet.union permission_lcs simp_ctxt.lcs in
    {
      name = qp.name;
      pointer = simp simp_ctxt qp.pointer;
      q = qp.q;
      step = simp simp_ctxt qp.step;
      permission = and_ permission;
      iargs = List.map (simp { simp_ctxt with lcs = simp_lcs }) qp.iargs;
    }



  let simp simp_ctxt = function
    | P p -> P (simp_predicate_type simp_ctxt p)
    | Q qp -> Q (simp_qpredicate_type simp_ctxt qp)



  let simp_or_empty simp_ctxt resource =
    match simp simp_ctxt resource with
    | P p when IT.is_false p.permission -> None
    | Q p when IT.is_false p.permission -> None
    | re -> Some re

end
