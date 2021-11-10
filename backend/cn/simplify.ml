module LC = LogicalConstraints
module IT = IndexTerms
open IndexTerms

module SymPair = struct
  type t = Sym.t * Sym.t
  let compare (s1,s2) (s1',s2') =
    let c1 = Sym.compare s1 s1' in
    if c1 <> 0 then c1 else Sym.compare s2 s2'
end


module SymPairMap = Map.Make(SymPair)


let simp struct_decls (lcs : LC.t list) =


  let values = 
    List.fold_right (fun c values ->
        match c with
        | LC.T (IT (Bool_op (EQ (IT (Lit (Sym sym), _), 
                                 it')), _)) ->
           (* when IT.size it' <= 10 -> *)
             SymMap.add sym it' values
        | _ ->
           values
      ) lcs SymMap.empty
  in
  
  let equalities =
    List.fold_right (fun c equalities ->
        match c with
        | LC.T it ->
           begin match it with
           | IT (Bool_op (EQ (IT (Lit (Sym sym), _), 
                              IT (Lit (Sym sym'), _))), _) ->
              SymPairMap.add (sym, sym') true equalities
           | IT (Bool_op (Not (IT (Bool_op (EQ (IT (Lit (Sym sym), _), 
                                                IT (Lit (Sym sym'), _))), _))), _) ->
              SymPairMap.add (sym, sym') false equalities
           | IT (Bool_op (NE (IT (Lit (Sym sym), _), 
                              IT (Lit (Sym sym'), _))), _) ->
              SymPairMap.add (sym, sym') false equalities
           | _ -> equalities
           end
        | _ -> equalities
      ) lcs SymPairMap.empty
  in
  
  let rec aux (IT (it, bt)) =
    match it with
    | Lit it -> lit it bt
    | Arith_op it -> arith_op it bt
    | Bool_op it -> bool_op it bt
    | Tuple_op it -> tuple_op it bt
    | Struct_op it -> struct_op it bt
    | Pointer_op it -> pointer_op it bt
    | List_op it -> IT (List_op it, bt)
    | Set_op it -> IT (Set_op it, bt)
    | CT_pred it -> ct_pred it bt
    | Array_op it -> array_op it bt
  
  and lit it bt = 
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
  
  and arith_op it bt = 
    match it with
    | Add (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Lit (Z i1), _), IT (Lit (Z i2), _) ->
          IT (Lit (Z (Z.add i1 i2)), bt)
       | IT (Lit (Q q1), _), IT (Lit (Q q2), _) ->
          IT (Lit (Q (Q.add q1 q2)), bt) 
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
      | _, _ when equal a b ->
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
  
  and bool_op it bt = 
    match it with
    | And its ->
       let its = List.map aux its in
       begin match its with
       | [a; b] when 
              (* let open Pp in
               * print stdout (item "a" (IT.pp a));
               * print stdout (item "b" (IT.pp b)); *)
              IT.equal (not_ a) b ->
          bool_ false
       | [a; b] when IT.equal a (not_ b) ->
          bool_ false
       | _ ->
          if List.exists is_false its then 
            IT (Lit (Bool false), bt)
          else if List.for_all is_true its then
            IT (Lit (Bool true), bt)
          else
            IT (Bool_op (And its), bt)
       end
    | Or its ->
       let its = List.map aux its in
       if List.exists is_true its then
         IT (Lit (Bool true), bt)
       else if List.for_all is_false its then
         IT (Lit (Bool false), bt)
       else
         IT (Bool_op (Or its), bt)
    | Impl (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a with
       | IT (Lit (Bool true), _) ->
          b
       | IT (Lit (Bool false), _) ->
          IT (Lit (Bool true), bt) 
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
       let b = aux b in
       let c = aux c in
       begin match a with
       | IT (Lit (Bool true), _) -> b
       | IT (Lit (Bool false), _) -> c
       | _ when equal b c -> b
       | _ -> IT (Bool_op (ITE (a, b, c)), bt)
       end
    | EQ (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _ when equal a b ->
         IT (Lit (Bool true), bt) 
       | IT (Lit (Sym s), _), IT (Lit (Sym s'), _) ->
          begin match SymPairMap.find_opt (s,s') equalities with
          | Some bool -> bool_ bool
          | _ -> eq_ (a, b)
          end
       | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
          bool_ (Z.equal z1 z2)
       | IT (Tuple_op (Tuple items1), _), 
         IT (Tuple_op (Tuple items2), _)  ->
          and_ (List.map2 eq__ items1 items2)
       | _, _ ->
          eq_ (a, b)
       end
    | NE (a, b) ->
       let a = aux a in
       let b = aux b in
       IT (Bool_op (NE (a, b)), BT.Bool)
    | EachI ((i1, s, i2), t) ->
       let s' = Sym.fresh_same s in 
       let t = IndexTerms.subst (make_subst [(s, sym_ (s', bt))]) t in
       let t = aux t in
       IT (Bool_op (EachI ((i1, s', i2), t)), bt)


  and tuple_op it bt = 
    match it with
    | Tuple its ->
       let its = List.map aux its in
       IT (Tuple_op (Tuple its), bt)
    | NthTuple (n, it) ->
       let it = aux it in
       IT (Tuple_op (NthTuple (n, it)), bt)
  
  
  and struct_op it bt = 
    match it with
    | IT.Struct (tag, members) ->
       let members = 
         List.map (fun (member, it) ->
             (member, aux it)
           ) members
       in
       IT (Struct_op (IT.Struct (tag, members)), bt)
    | IT.StructMember (it, member) ->
       let it = aux it in
       match it with
       | IT (Struct_op (Struct (_, members)), _) ->
          List.assoc Id.equal member members
       | _ ->
          IT (Struct_op (IT.StructMember (it, member)), bt)
  
  (* revisit when memory model changes *)
  and pointer_op it bt = 
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
       IT (Pointer_op (IntegerToPointerCast a), bt)
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
  
  and ct_pred it bt = 
    match it with
    | _ ->
       IT (CT_pred it, bt)

  and array_op it bt = 
    match it with
    | Const (index_bt, t) ->
       let t = aux t in
       IT (Array_op (Const (index_bt, t)), bt)
    | Set (t1, t2, t3) ->
       let t1 = aux t1 in
       let t2 = aux t2 in
       let t3 = aux t3 in
       IT (Array_op (Set (t1, t2, t3)), bt)
    | Get (array, index) ->
       let array = aux array in
       let index = aux index in
       begin match array with
       | IT (Array_op (Def ((s, abt), body)), _) ->
          assert (BT.equal abt (IT.bt index));
          aux (IT.subst (IT.make_subst [(s, index)]) body)
       | IT (Bool_op (ITE (cond, array1, array2)), bt') ->
          (* (if cond then array1 else array2)[index] -->
           * if cond then array1[index] else array2[index] *)
          assert (BT.equal bt bt');
          ite_ (cond, 
                aux (get_ array1 index), 
                aux (get_ array2 index))
       | _ ->
          IT (Array_op (Get (array, index)), bt)
       end

    | Def ((s, abt), body) ->
       let s' = Sym.fresh_same s in 
       let body = IndexTerms.subst (make_subst [(s, sym_ (s', abt))]) body in
       let body = aux body in
       IT (Array_op (Def ((s', abt), body)), bt)
  in
  
  (* fun term -> aux term *)

  fun term -> 
  let result = aux term in
  result

  (* let term = aux term in
   * if with_solver && IT.size term <= 50 then term else
   *   match Solver.simp struct_decls term with
   *   | Some term -> term
   *   | None -> 
   *      let open Pp in
   *      Pp.warn !^"failed to simplify with SMT solver";
   *      term *)


let simp_flatten struct_decls lcs term =
  match simp struct_decls lcs term with
  | IT (Bool_op (And lcs), _) -> lcs
  | lc -> [lc]




let simp_lc struct_decls lcs lc = 
  match lc with
  | LC.T it -> 
     LC.T (simp struct_decls lcs it)
  | LC.Forall ((s, bt), it) -> 
     let s' = Sym.fresh_same s in 
     let it = IndexTerms.subst (make_subst [(s, sym_ (s', bt))]) it in
     (* let trigger = Option.map (LC.subst_trigger [(s, sym_ (s', bt))]) trigger in *)
     let it = simp struct_decls lcs it in
     LC.Forall ((s', bt), it)
  | LC.Pred pred ->
     LC.Pred pred
  | LC.QPred qpred ->
     LC.QPred qpred


let simp_lc_flatten struct_decls lcs c = 
  match c with
  | LC.T it ->
     List.map (fun c -> LC.T c) (simp_flatten struct_decls lcs it)
  | LC.Forall ((s, bt), it) -> 
     let s' = Sym.fresh_same s in 
     let it = IndexTerms.subst (make_subst [(s, sym_ (s', bt))]) it in
     (* let trigger = Option.map (LC.subst_trigger [(s, sym_ (s', bt))]) trigger in *)
     let it = simp struct_decls lcs it in
     [LC.Forall ((s', bt), it)]
  | LC.Pred pred ->
     [LC.Pred pred]
  | LC.QPred qpred ->
     [LC.QPred qpred]
