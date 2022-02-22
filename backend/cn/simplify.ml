module LC = LogicalConstraints
module IT = IndexTerms
module ITSet = Set.Make(IT)
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

let rec simp (struct_decls : Memory.struct_decls) values equalities some_known_facts =

  let flatten_and = function
    | IT (Bool_op (And fs), _) -> fs
    | f -> [f]
  in

  let add_known_fact f some_known_facts = 
    flatten_and f @ some_known_facts
  in

  let add_known_facts fs some_known_facts =
    List.concat_map flatten_and fs @ some_known_facts
  in


  let aux it =
    simp struct_decls values equalities some_known_facts it in
  let aux2 some_known_facts it = 
    simp struct_decls values equalities some_known_facts it in
  
  let lit it bt = 
    match it with
    | Sym _ when BT.equal bt BT.Unit ->
       unit_ 
    | Sym sym ->
       begin match SymMap.find_opt sym values with
       | Some it -> it
       | None -> IT (Lit (Sym sym), bt)
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
    | Exp (a, b) ->
       IT (Arith_op (Exp (aux a, aux b)), bt) 
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
    | FlipBit {bit; t} ->
       let bit = aux bit in
       let t = aux t in
       IT (Arith_op (FlipBit {bit; t}), bt)
    | XOR (ity, a, b) -> 
       let a = aux a in
       let b = aux b in
       IT (Arith_op (XOR (ity, a, b)), bt)
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
            let it = aux2 (add_known_facts acc some_known_facts) it in
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
       let b = aux2 (add_known_fact a some_known_facts) b in
       let c = aux2 (add_known_fact (not_ a) some_known_facts) c in
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
          when ITPairMap.mem (a,b) equalities ||
                 ITPairMap.mem (b,a) equalities 
         ->
          begin match ITPairMap.find_opt (a,b) equalities, 
                      ITPairMap.find_opt (b,a) equalities with
          | Some bool, _ -> bool_ bool
          | _, Some bool -> bool_ bool
          | _ -> eq_ (a, b)
          end
       | IT (Tuple_op (Tuple items1), _), 
         IT (Tuple_op (Tuple items2), _)  ->
          and_ (List.map2 eq__ items1 items2)
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
       IT (Tuple_op (NthTuple (n, it)), bt)
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
       let layout = SymMap.find tag struct_decls in
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

  let letb (s, bound) body bt =
    let bound = aux bound in
    let s' = Sym.fresh_same s in
    let body = IndexTerms.subst (make_subst [(s, sym_ (s', IT.bt bound))]) body in
    let body = aux body in
    IT (Let ((s', bound), body), bt)
  in

  fun it ->
  if List.mem IT.equal it some_known_facts then bool_ true else
  if List.mem IT.equal (not_ it) some_known_facts then bool_ false else
    let (IT (it_, bt)) = it in
    match it_ with
    | Lit l -> lit l bt
    | Arith_op a -> arith_op a bt
    | Bool_op b -> bool_op b bt
    | Tuple_op t -> tuple_op t bt
    | Struct_op s -> struct_op s bt
    | Pointer_op p -> pointer_op p bt
    | List_op l -> IT (List_op l, bt)
    | Set_op s -> IT (Set_op s, bt)
    | CT_pred c -> ct_pred c bt
    | Map_op a -> map_op a bt
    (* | Option_op o -> option_op o bt *)
    | Let ((s, bound), body) -> letb (s, bound) body bt


let simp ?(some_known_facts = []) struct_decls lcs it = 

  let (values, gen_lcs) = lcs in

  let equalities = 
    List.fold_left (fun equalities c ->
        match c with
        | LC.T it ->
           begin match it with
           | IT (Bool_op (EQ (a, b)), _) ->
              ITPairMap.add (a, b) true equalities
           | IT (Bool_op (Not (IT (Bool_op (EQ (a, b)), _))), _) ->
              ITPairMap.add (a, b) false equalities
           | _ -> 
              equalities
           end
        | _ -> 
           equalities
      ) ITPairMap.empty gen_lcs
  in

  let result = simp struct_decls values equalities some_known_facts it in

  result
  
  



let simp_flatten ?(some_known_facts = []) struct_decls lcs term =
  match simp ~some_known_facts struct_decls lcs term with
  | IT (Lit (Bool true), _) -> []
  | IT (Bool_op (And lcs), _) -> lcs
  | lc -> [lc]



let simp_lc struct_decls lcs lc = 
  match lc with
  | LC.T it -> LC.T (simp struct_decls lcs it)
  | LC.Forall ((q, qbt), body) ->
     let ((q_new, qbt), body) = 
       LC.alpha_rename_forall (Sym.fresh ()) ((q, qbt), body)
     in
     let body = simp struct_decls lcs body in
     let ((q, qbt), body) = LC.alpha_rename_forall q ((q_new, qbt), body) in
     begin match body with
     | IT (Lit (Bool true), _) -> 
        LC.T (bool_ true)
     | IT (Bool_op (EQ (  IT (Map_op (Get (a, i)), _)  ,  
                          IT (Map_op (Get (b, i')), _)  
             )), _) 
           when IT.equal i i' && IT.equal i' (sym_ (q, qbt))
       ->
        LC.T (eq_ (a, b))
     | _ -> LC.Forall ((q, qbt), body)
     end
  | _ -> lc


let simp_lc_flatten struct_decls lcs lc = 
  match lc with
  | LC.T it -> List.map LC.t_ (simp_flatten struct_decls lcs it)
  | _ -> [simp_lc struct_decls lcs lc]
