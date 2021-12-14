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



let rec simp struct_decls values equalities some_known_facts =

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
       | _, IT (Lit (Z i2), _) when Z.equal i2 (Z.of_int 1) ->
          a
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
       | _, IT (Lit (Z b), _) when Z.equal b (Z.of_int 1) -> 
          a
       | _ ->
          IT (Arith_op (Div (a, b)), bt) 
       end
    | Exp (a, b) ->
       IT (Arith_op (Exp (aux a, aux b)), bt) 
    | Rem (a, b) ->
       let a = aux a in
       let b = aux b in 
       begin match a, b with
       | IT (Lit (Z a), _), _ when Z.equal a (Z.zero) -> 
          int_ 0
       | _, IT (Lit (Z b), _) when Z.equal b (Z.of_int 1) -> 
          int_ 0
       | _ ->
          IT (Arith_op (Rem (a, b)), bt) 
       end
    | Mod (a, b) ->
       let a = aux a in
       let b = aux b in
       IT (Arith_op (Mod (a, b)), bt) 
    | LT (a, b) -> 
      let a = aux a in
      let b = aux b in
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
      begin match a, b with
      | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
         IT (Lit (Bool (Z.leq z1 z2)), bt)
      | IT (Lit (Q q1), _), IT (Lit (Q q2), _) ->
         IT (Lit (Bool (Q.leq q1 q2)), bt)
      | _, _ when IT.equal a b ->
         bool_ true
      | IT (Arith_op (Rem (_, IT (Lit (Z z1), _))), _), 
        IT (Lit (Z z2), _) when
             Z.gt z1 Z.zero &&
               Z.gt z2 Z.zero &&
                 Z.leq z1 (Z.add z2 (Z.of_int 1)) ->
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
            | _ -> and_ acc
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
            | _ -> or_ acc
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
       begin match a, b with
       | _ when IT.equal a b ->
         IT (Lit (Bool true), bt) 
       | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
          bool_ (Z.equal z1 z2)
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
       IT (Pointer_op (LTPointer (aux a, aux b)), bt)
    | LEPointer (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _ -> 
          IT (Pointer_op (LEPointer (a, b)), bt)
       end
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
       IT (Pointer_op (MemberOffset (tag, member)), bt)
    | ArrayOffset (ct, t) ->
       aux (mul_ (int_ (Memory.size_of_ctype ct), t))
    | CellPointer c ->
       IT (Pointer_op (CellPointer {
                           base = aux c.base;
                           step = aux c.step;
                           starti = aux c.starti;
                           endi = aux c.endi;
                           p = aux c.p;
             }), bt)
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
  
  let option_op o bt = 
    match o with
    | Nothing vbt -> 
       IT (Option_op (Nothing vbt), bt)
    | Something t -> 
       let t = aux t in
       IT (Option_op (Something t), bt)
    | Is_nothing t ->
       let t = aux t in
       IT (Option_op (Is_nothing t), bt)
    | Is_something t ->
       let t = aux t in
       IT (Option_op (Is_something t), bt)
    | Get_some_value t ->
       let t = aux t in
       IT (Option_op (Get_some_value t), bt)
  in

  let letb (s, bound) body bt =
    let bound = aux bound in
    let s' = Sym.fresh_same s in
    let body = IndexTerms.subst (make_subst [(s, sym_ (s', IT.bt bound))]) body in
    let body = aux body in
    IT (Let ((s', bound), body), bt)
  in

  fun it ->
  if List.mem IT.equal it some_known_facts then bool_ true 
  else
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
    | Option_op o -> option_op o bt
    | Let ((s, bound), body) -> letb (s, bound) body bt


let simp ?(some_known_facts = []) struct_decls lcs it = 

  let values = 
    List.fold_right (fun c values ->
        match c with
        | LC.T (IT (Bool_op (EQ (IT (Lit (Sym sym), bt), 
                                 it')), _)) 
             when Option.is_some (is_lit it') ->
             SymMap.add sym it' values
        | LC.T (IT (Bool_op (EQ (IT (Lit (Sym sym), bt), 
                                 (IT (Map_op (Def _),_) as it'))), _)) ->
             SymMap.add sym it' values
        | _ ->
           values
      ) lcs SymMap.empty
  in
  
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
      ) ITPairMap.empty lcs
  in

  let result = simp struct_decls values equalities some_known_facts it in

  result
  
  



let simp_flatten struct_decls lcs term =
  match simp struct_decls lcs term with
  | IT (Lit (Bool true), _) -> []
  | IT (Bool_op (And lcs), _) -> lcs
  | lc -> [lc]



let simp_lc struct_decls lcs lc = 
  match lc with
  | LC.T it -> LC.T (simp struct_decls lcs it)
  | _ -> lc


let simp_lc_flatten struct_decls lcs lc = 
  match lc with
  | LC.T it -> List.map LC.t_ (simp_flatten struct_decls lcs it)
  | _ -> [lc]
