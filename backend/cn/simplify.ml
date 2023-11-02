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
    simp_hook : IT.t -> IT.t option;
  }

let default global = {
    global;
    values = SymMap.empty;
    simp_hook = (fun _ -> None);
  }




module IndexTerms = struct

  let z1 = z_ Z.one
  let z0 = z_ Z.zero

  let rec dest_int_addition ts it = match IT.term it with
      | Const (Z i1) -> if fst ts || ITSet.mem z1 (snd ts) then ([(z1, i1)], z0) else ([], it)
      | Binop (Add, a, b) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let (b_xs, b_r) = dest_int_addition ts b in
          (a_xs @ b_xs, if IT.equal a_r z0 then b_r else if IT.equal b_r z0 then a_r
              else add_ (a_r, b_r))
      | Binop (Sub, a, b) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let (b_xs, b_r) = dest_int_addition ts b in
          let b_xs_neg = List.map (fun (it, i) -> (it, Z.sub Z.zero i)) b_xs in
          (a_xs @ b_xs_neg, if IT.equal b_r z0 then a_r else sub_ (a_r, b_r))
      | Binop (Mul, a, IT (Const (Z b_i), _)) ->
          let (a_xs, a_r) = dest_int_addition ts a in
          let a_xs_mul = List.map (fun (it, i) -> (it, Z.mul i b_i)) a_xs in
          (a_xs_mul, if IT.equal a_r z0 then z0 else mul_ (a_r, z_ b_i))
      | Binop (Mul, IT (Const (Z a_i), _), b) ->
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





  let rec record_member_reduce it member =
    match IT.term it with
      | Record members -> List.assoc Id.equal member members
      | RecordUpdate ((t, m), v) ->
        if Id.equal m member then v
        else record_member_reduce t member
      | ITE (cond, it1, it2) ->
        ite_ (cond, record_member_reduce it1 member, record_member_reduce it2 member)
      | _ ->
        let member_tys = BT.record_bt (IT.bt it) in
        let member_bt = List.assoc Id.equal member member_tys in
        IT.recordMember_ ~member_bt (it, member)

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
    match IT.term it with
      | Tuple items -> List.nth items n
      | ITE (cond, it1, it2) ->
        ite_ (cond, tuple_nth_reduce it1 n item_bt, tuple_nth_reduce it2 n item_bt)
      | _ -> IT.nthTuple_ ~item_bt (n, it)

  let rec accessor_reduce (f : IT.t -> IT.t option) it =
    let bt = IT.bt it in
    let (step, it2) = match IT.term it with
      | RecordMember (t, m) ->
          (true, record_member_reduce (accessor_reduce f t) m)
      (* | DatatypeMember (t, m) -> *)
      (*     (true, datatype_member_reduce (accessor_reduce f t) m bt) *)
      | NthTuple (n, t) ->
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

    let aux it = simp ~inline_functions:inline_functions simp_ctxt it in

    fun it ->
    let the_term = match simp_ctxt.simp_hook it with
    | None -> it
    | Some it' -> it'
    in
    let (IT (the_term_, the_bt)) = the_term in
    match the_term_ with
    | Sym _ when BT.equal the_bt BT.Unit -> 
       unit_
    | Sym sym ->
       begin match SymMap.find_opt sym simp_ctxt.values with
       | Some (IT ((Const _ | Sym _), _) as v) ->
          v
       | _ ->
          the_term
       end
    | Const _ ->
       the_term

    | Binop (Add, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Const (Z i1), _), IT (Const (Z i2), _) ->
          IT (Const (Z (Z.add i1 i2)), the_bt)
       | IT (Const (Q q1), _), IT (Const (Q q2), _) ->
          IT (Const (Q (Q.add q1 q2)), the_bt) 
       | a, IT (Const (Z z), _) when Z.equal z Z.zero ->
          a
       | IT (Const (Z z), _), a when Z.equal z Z.zero ->
          a
       | IT (Binop (Add,c, IT (Const (Z i1), _)), _), 
         IT (Const (Z i2), _) ->
          add_ (c, z_ (Z.add i1 i2))
       | _, _ ->
          IT (Binop (Add, a, b), the_bt)
       end
    | Binop (Sub, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b, the_bt with
       | _, _, BT.Integer when IT.equal a b ->
          int_ 0
       | _, _, BT.Real when IT.equal a b ->
          q_ (0, 1)
       | IT (Const (Z i1), _), IT (Const (Z i2), _), _ ->
          IT (Const (Z (Z.sub i1 i2)), the_bt)
       | IT (Const (Q q1), _), IT (Const (Q q2), _), _ ->
          IT (Const (Q (Q.sub q1 q2)), the_bt)
       | _, IT (Const (Z i2), _), _ when Z.equal i2 Z.zero ->
          a
       | IT (Binop (Add, c, d), _), _, _ when IT.equal c b ->
          (* (c + d) - b  when  c = b *)
          d
       | _, _, _ ->
          IT (Binop (Sub, a, b), the_bt) 
       end
    | Binop (Mul, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _, IT (Const (Z i2), _) when Z.equal i2 Z.zero ->
          int_ 0
       | IT (Const (Z i1), _), _ when Z.equal i1 Z.zero ->
          int_ 0
       | _, IT (Const (Z i2), _) when Z.equal i2 Z.one ->
          a
       | IT (Const (Z i1), _), _ when Z.equal i1 Z.one ->
          b
       | IT (Const (Z i1), _), IT (Const (Z i2), _) ->
          IT (Const (Z (Z.mul i1 i2)), the_bt)
       | _ ->
          IT (Binop (Mul, a, b), the_bt)
       end
    | Binop (Div, a, b) ->
       let a = aux a in
       let b = aux b in 
       begin match a, b with
       | IT (Const (Z a), _), IT (Const (Z b), _) ->
            assert (Z.lt Z.zero b);
          z_ (Z.div a b)
       | IT (Const (Z a), _), _ when Z.equal a (Z.zero) -> 
          int_ 0
       | _, IT (Const (Z b), _) when Z.equal b Z.one -> 
          a
       | IT (Binop (Mul, b', c), _), _ when IT.equal b' b ->
          c
       | _ ->
          IT (Binop (Div, a, b), the_bt) 
       end
    | Binop (Exp, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Const (Z a), _), IT (Const (Z b), _) when Z.fits_int b ->
          z_ (Z.pow a (Z.to_int b))
       | _ ->
          IT.exp_ (a, b)
       end
    | Binop (Rem, a, b) ->
       let a = aux a in
       let b = aux b in 
       begin match a, b with
       | IT (Const (Z z1), _), IT (Const (Z z2), _) when Z.geq z1 Z.zero && Z.gt z2 Z.zero ->
         IT (Const (Z (Z.rem z1 z2)), the_bt)
       | IT (Const (Z a), _), _ when Z.equal a (Z.zero) -> 
          int_ 0
       | IT (Binop (Mul, IT (Const (Z y), _), _), _), 
         IT (Const (Z y'), _) when Z.equal y y' && Z.gt y Z.zero ->
          int_ 0
       | _, IT (Const (Z b), _) when Z.equal b Z.one ->
          int_ 0
       | _ ->
          IT (Binop (Rem, a, b), the_bt) 
       end
    | Binop (Mod, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Const (Z a), _), _ when Z.equal a (Z.zero) ->
          int_ 0
       | IT (Binop (Mul, IT (Const (Z y), _), _), _), 
         IT (Const (Z y'), _) when Z.equal y y' && Z.gt y Z.zero ->
          int_ 0
       | _, IT (Const (Z b), _) when Z.equal b Z.one ->
          int_ 0
       | _ ->
          IT (Binop (Mod, a, b), the_bt) 
       end
    | Binop (LT, a, b) -> 
      let a = aux a in
      let b = aux b in
      let (a, b) = simp_comp_if_int a b in
      begin match a, b with
      | IT (Const (Z z1), _), IT (Const (Z z2), _) ->
         IT (Const (Bool (Z.lt z1 z2)), the_bt)
      | IT (Const (Q q1), _), IT (Const (Q q2), _) ->
         IT (Const (Bool (Q.lt q1 q2)), the_bt)
      | _, _ ->
         IT (Binop (LT, a, b), the_bt)
      end
    | Binop (LE, a, b) -> 
      let a = aux a in
      let b = aux b in
      let (a, b) = simp_comp_if_int a b in
      begin match a, b with
      | IT (Const (Z z1), _), IT (Const (Z z2), _) ->
         IT (Const (Bool (Z.leq z1 z2)), the_bt)
      | IT (Const (Q q1), _), IT (Const (Q q2), _) ->
         IT (Const (Bool (Q.leq q1 q2)), the_bt)
      | _, _ when IT.equal a b ->
         bool_ true
      | IT (Binop (Rem, _, IT (Const (Z z1), _)), _), 
        IT (Const (Z z2), _) 
      | IT (Binop (Mod, _, IT (Const (Z z1), _)), _), 
        IT (Const (Z z2), _) 
           when
             Z.gt z1 Z.zero &&
               Z.gt z2 Z.zero &&
                 Z.equal z1 (Z.add z2 Z.one) ->
         bool_ true
      | _, _ ->
         IT (Binop (LE, a, b), the_bt)
      end
    | Binop (Min, a, b) ->
       let a = aux a in
       let b = aux b in
       if IT.equal a b then a else
       IT (Binop (Min, a, b), the_bt)
    | Binop (Max, a, b) ->
       let a = aux a in
       let b = aux b in
       if IT.equal a b then a else
       IT (Binop (Max, a, b), the_bt)
    | Binop (And, it1, it2) ->
      let it1 = aux it1 in
      let it2 = aux it2 in
      begin match it1, it2 with
      | IT (Const (Bool true), _), _ -> it2
      | _, IT (Const (Bool true), _) -> it1
      | IT (Const (Bool false), _), _ -> bool_ false
      | _, IT (Const (Bool false), _) -> bool_ false
      | _ when IT.equal it1 it2 -> it1
      | _ -> IT (Binop (And, it1, it2), the_bt)
      end
    | Binop (Or, it1, it2) ->
      let it1 = aux it1 in
      let it2 = aux it2 in
      begin match it1, it2 with
      | IT (Const (Bool true), _), _ -> bool_ true
      | _, IT (Const (Bool true), _) -> bool_ true
      | IT (Const (Bool false),_), _ -> it2
      | _, IT (Const (Bool false),_) -> it1
      | _ when IT.equal it1 it2 -> it1
      | _ -> IT (Binop (Or, it1, it2), the_bt)
      end
    | Binop (Impl, a, b) ->
       let a = aux a in
       let b = aux b in
       if IT.equal a b then IT (Const (Bool true), the_bt)
       else
       begin match a, b with
       | IT (Const (Bool false), _), _ ->
          IT (Const (Bool true), the_bt) 
       | _, IT (Const (Bool true), _) ->
          IT (Const (Bool true), the_bt)
       | IT (Const (Bool true), _), _ ->
          b
       | _, IT (Const (Bool false), _) ->
          not_ a
       | _ ->
          IT (Binop (Impl, a, b), the_bt)
       end
    | Unop (Not, a) ->
       let a = aux a in
       begin match a with
       | IT (Const (Bool b), _) ->
          bool_ (not b)
       | IT (Unop (Not, b), _) ->
          b
       | _ -> 
          IT (Unop (Not, a), the_bt)
       end
    | ITE (a, b, c) ->
       let a = aux a in
       let b = aux b in
       let c = aux c in
       begin match a with
       | IT (Const (Bool true), _) -> b
       | IT (Const (Bool false), _) -> c
       | _ when IT.equal b c -> b
       | _ -> IT (ITE (a, b, c), the_bt)
       end
    | Binop (EQ, a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _ when IT.equal a b ->
         IT (Const (Bool true), the_bt) 
       | IT (Const (Z z1), _), IT (Const (Z z2), _) ->
          bool_ (Z.equal z1 z2)
       (* (cond ? z1 : z2) == z3 *)
       | IT (ITE (cond, 
                  IT (Const (Z z1), _), 
                  IT (Const (Z z2), _)), _),
         IT (Const (Z z3), _)

       | IT (Const (Z z3), _),
         IT (ITE (cond, 
                  IT (Const (Z z1), _), 
                  IT (Const (Z z2), _)), _) ->

          aux (
            and_ [impl_ (cond, bool_ (Z.equal z1 z3));
                  impl_ (not_ cond, bool_ (Z.equal z2 z3))]
            )
       | IT (Tuple items1, _),
         IT (Tuple items2, _)  ->
          aux (and_ (List.map2 eq__ items1 items2))
       | IT (Record members1, _),
         IT (Record members2, _)  ->
          assert (List.for_all2 (fun x y -> Id.equal (fst x) (fst y)) members1 members2);
          aux (and_ (List.map2 (fun x y -> eq_ (snd x, snd y)) members1 members2))
       | _, _ ->
          eq_ (a, b)
       end
    | EachI ((i1, (s, s_bt), i2), t) ->
       let s' = Sym.fresh_same s in 
       let t = IndexTerms.subst (make_subst [(s, sym_ (s', the_bt))]) t in
       let t = aux t in
       IT (EachI ((i1, (s', s_bt), i2), t), the_bt)

    | Tuple its ->
       let its = List.map aux its in
       IT (Tuple its, the_bt)
    | NthTuple (n, it) ->
       let it = aux it in
       tuple_nth_reduce it n the_bt
    | IT.Struct (tag, members) ->
       begin match members with
       | (_, IT (StructMember (str, _), _)) :: _ when 
              BT.equal (Struct tag) (IT.bt str) &&
              List.for_all (function 
                  | (mem, IT (StructMember (str', mem'), _)) ->
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
          IT (IT.Struct (tag, members), the_bt)
       end
    | IT.StructMember (s_it, member) ->
       let s_it = aux s_it in
       let rec make t = 
         match t with
         | IT (Struct (_, members), _) ->
            List.assoc Id.equal member members
         | IT (ITE (cond, it1, it2), _) ->
            (* (if cond then it1 else it2) . member -->
             (if cond then it1.member else it2.member) *)
            ite_ (cond, make it1, make it2)
         | _ ->
            IT (IT.StructMember (t, member), the_bt)
       in
       make s_it
    | IT.StructUpdate ((t, m), v) ->
       let t = aux t in
       let v = aux v in
       IT (StructUpdate ((t, m), v), the_bt)
    | IT.Record members ->
       let members = 
         List.map (fun (member, it) ->
             (member, aux it)
           ) members
       in
       IT (IT.Record members, the_bt)
    | IT.RecordMember (it, member) ->
       let it = aux it in
       record_member_reduce it member
    | IT.RecordUpdate ((t, m), v) ->
       let t = aux t in
       let v = aux v in
       IT (RecordUpdate ((t, m), v), the_bt)
    (* revisit when memory model changes *)
    | Binop (LTPointer, a, b) ->
       let a = aux a in
       let b = aux b in
       if isIntegerToPointerCast a || isIntegerToPointerCast b
       then
       aux (lt_ (pointerToIntegerCast_ a, pointerToIntegerCast_ b))
       else if IT.equal a b
       then bool_ false
       else IT (Binop (LTPointer, a, b), the_bt)
    | Binop (LEPointer, a, b) ->
       let a = aux a in
       let b = aux b in
       if isIntegerToPointerCast a || isIntegerToPointerCast b
       then
       aux (le_ (pointerToIntegerCast_ a, pointerToIntegerCast_ b))
       else if IT.equal a b
       then bool_ true
       else IT (Binop (LEPointer, a, b), the_bt)
    | Binop (op, a, b) ->
       IT (Binop (op, aux a, aux b), the_bt)
    | Unop (op, a) ->
       IT (Unop (op, aux a), the_bt)
    | Constructor (ctor, ts) ->
       IT (Constructor (ctor, List.map_snd aux ts), the_bt)
    | WrapI (act, t) ->
       IT (WrapI (act, aux t), the_bt)
    | Cast (cbt, a) ->
       let a = aux a in
       IT (Cast (cbt, a), the_bt)
    | MemberShift (t, tag, member) ->
      IT (MemberShift (aux t, tag, member), the_bt)
    | ArrayShift { base; ct; index } ->
       let base = aux base in
       let index = aux index in
       begin match is_z index with
       | Some z when Z.equal Z.zero z -> base
       | _ -> IT (ArrayShift { base; ct; index }, the_bt)
       end
    | SizeOf ct ->
       int_ (Memory.size_of_ctype ct)
    | Representable (ct, t) ->
       IT (Representable (ct, aux t), the_bt)
    | Good (ct, t) ->
       IT (Good (ct, aux t), the_bt)
    | Aligned a -> 
       IT (Aligned {t = aux a.t; align = aux a.align}, the_bt)
    | MapConst (index_bt, t) ->
       let t = aux t in
       IT (MapConst (index_bt, t), the_bt)
    | MapSet (t1, t2, t3) ->
       let t1 = aux t1 in
       let t2 = aux t2 in
       let t3 = aux t3 in
       IT (MapSet (t1, t2, t3), the_bt)
    | MapGet (map, index) ->
       let map = aux map in
       let index = aux index in
       let rec make map index = 
         begin match map with
         | IT (MapDef ((s, abt), body), _) ->
            assert (BT.equal abt (IT.bt index));
            aux (IT.subst (IT.make_subst [(s, index)]) body)
         | IT (MapSet (map', index', value'), _) ->
            begin match index, index' with
            | _, _ when IT.equal index index' ->
               value'
            | IT (Const (Z z), _), IT (Const (Z z'), _) when not (Z.equal z z') ->
               make map' index
            | _ ->
               IT (MapGet (map, index), the_bt)
            end
         (* | IT (Bool_op (ITE (cond, map1, map2)), bt') -> *)
         (*    (\* (if cond then map1 else map2)[index] --> *)
         (*     * if cond then map1[index] else map2[index] *\) *)
         (*    ite_ (cond,  *)
         (*          make map1 index,  *)
         (*          make map2 index) *)
         | _ ->
            IT (MapGet (map, index), the_bt)
         end
       in
       make map index
    | MapDef ((s, abt), body) ->
       let s' = Sym.fresh_same s in 
       let body = IndexTerms.subst (make_subst [(s, sym_ (s', abt))]) body in
       let body = aux body in
       IT (MapDef ((s', abt), body), the_bt)

    | Apply (name, args) ->

      let args = List.map aux args in
      let def = SymMap.find name simp_ctxt.global.logical_functions in
      let t = IT (Apply (name, args), the_bt) in
      if not inline_functions then t else 
        begin match LogicalFunctions.try_open_fun def args with
        | Some inlined -> aux inlined
        | None -> t
        end
    | _ ->
      (* FIXME: it's problematic that some term shapes aren't even explored *)
      it


  let simp_flatten simp_ctxt term =
    match simp simp_ctxt term with
    | IT (Const (Bool true), _) -> []
    | IT (Binop (And, lc1, lc2), _) -> [lc1;lc2]
    | lc -> [lc]



  let eval simp_ctxt =
    simp ~inline_functions:true simp_ctxt

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
       | IT (Const (Bool true), _) -> LC.T (bool_ true)
       | _ -> LC.Forall ((q, qbt), body)
       end

end



module ResourceTypes = struct

  open IndexTerms
  open ResourceTypes

  let simp_predicate_type simp_ctxt (p : predicate_type) = {
      name = p.name; 
      pointer = simp simp_ctxt p.pointer;
      iargs = List.map (simp simp_ctxt) p.iargs;
    }

  let simp_qpredicate_type simp_ctxt (qp : qpredicate_type) =
    let qp = alpha_rename_qpredicate_type_ (Sym.fresh_same qp.q) qp in
    let permission = simp_flatten simp_ctxt qp.permission in
    {
      name = qp.name;
      pointer = simp simp_ctxt qp.pointer;
      q = qp.q;
      step = simp simp_ctxt qp.step;
      permission = and_ permission;
      iargs = List.map (simp simp_ctxt) qp.iargs;
    }



  let simp simp_ctxt = function
    | P p -> P (simp_predicate_type simp_ctxt p)
    | Q qp -> Q (simp_qpredicate_type simp_ctxt qp)




end
