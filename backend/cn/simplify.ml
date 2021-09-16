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


let rec simp (lcs : LC.t list) term =

  let values = 
    List.fold_right (fun c values ->
        match c with
        | LC.T (IT (it, bt)) ->
           begin match it with
           | Bool_op (EQ (it, it')) ->
              begin match is_sym it with
              | Some (sym, _) -> SymMap.add sym it' values
              | None -> values
              end
           | _ -> values
           end
        | Forall _ ->
           values
      ) lcs SymMap.empty
  in
  
  let equalities =
    List.fold_right (fun c equalities ->
        match c with
        | LC.T it ->
           begin match it with
           | IT (Bool_op (EQ (it, it')), _) ->
              begin match is_sym it, is_sym it' with
              | Some (sym, _), Some (sym', _) -> 
                 SymPairMap.add (sym, sym') true equalities
              | _ -> equalities
              end
           | IT (Bool_op (Not (IT (Bool_op (EQ (it, it')), _))), _) ->
              begin match is_sym it, is_sym it' with
              | Some (sym, _), Some (sym', _) -> 
                 SymPairMap.add (sym, sym') false equalities
              | _ -> equalities
              end
           | _ -> equalities
           end
        | _ -> equalities
      ) lcs SymPairMap.empty
  in
  
  (* fix later *)
  let rec simp_q (i,j) = 
    if i = 0 then 
      q_ (0, 1) 
    else if i mod 2 = 0 && j mod 2 = 0 then
      simp_q (i/2,j/2) 
    else
      q_ (i,j) 
  in
  
  let rec aux (IT (it, bt)) =
    match it with
    | Lit it -> lit it bt
    | Arith_op it -> arith_op it bt
    | Bool_op it -> bool_op it bt
    | Cmp_op it -> cmp_op it bt
    | Tuple_op it -> tuple_op it bt
    | Struct_op it -> struct_op it bt
    | Pointer_op it -> pointer_op it bt
    | List_op it -> IT (List_op it, bt)
    | Set_op it -> IT (Set_op it, bt)
    | CT_pred it -> IT (CT_pred it, bt)
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
    | Q (i1, i2) ->
       IT (Lit (Q (i1, i2)), bt)
    | Pointer z ->
       IT (Lit (Pointer z), bt)
    | Bool b ->
       IT (Lit (Bool b), bt)
    | Unit ->
       IT (Lit Unit, bt)
    | Default bt' -> 
       IT (Lit (Default bt'), bt)
  
  and arith_op it bt = 
    match it with
    | Add (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Lit (Z i1), _), IT (Lit (Z i2), _) ->
          IT (Lit (Z (Z.add i1 i2)), bt)
       | IT (Lit (Q (i1, j1)), _), IT (Lit (Q (i2, j2)), _) ->
          simp_q (i1 * j2 + i2 * j1, j1 * j2)
       | _, IT (Lit (Q (0, _)), _) -> 
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
       | IT (Lit (Q (i1, j1)), _), IT (Lit (Q (i2, j2)), _), _ ->
          simp_q (i1 * j2 - i2 * j1, j1 * j2)
       | _, IT (Lit (Q (0, _)), _), _ -> 
          a
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
  
  and bool_op it bt = 
    match it with
    | And its ->
       let its = List.map aux its in
       if List.exists is_false its then 
         IT (Lit (Bool false), bt)
       else if List.for_all is_true its then
         IT (Lit (Bool true), bt)
       else
         IT (Bool_op (And its), bt)
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
       let b = simp (LC.T a :: lcs) b in
       let c = simp (LC.T (not_ a) :: lcs) c in
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
       | IT (Pointer_op (AddPointer (b1,o1)), _), 
         IT (Pointer_op (AddPointer (b2,o2)), _) 
            when equal b1 b2 ->
          aux (eq_ (o1, o2))
       | IT (Tuple_op (Tuple items1), _), 
         IT (Tuple_op (Tuple items2), _)  ->
          and_ (List.map2 eq__ items1 items2)
       | _, _ ->
          eq_ (a, b)
       end
  
        
  
  and cmp_op it bt = 
    match it with
    | LT (a, b) -> 
      let a = aux a in
      let b = aux b in
      begin match a, b with
      | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
         IT (Lit (Bool (Z.lt z1 z2)), bt)
      | IT (Lit (Q (i1, j1)), _), IT (Lit (Q (i2, j2)), _) ->
         IT (Lit (Bool ((i1*j2) < (i2*j1))), bt)
      | _, _ ->
         IT (Cmp_op (LT (a, b)), bt)
      end
    | LE (a, b) -> 
      let a = aux a in
      let b = aux b in
       match a, b with
       | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
          IT (Lit (Bool (Z.leq z1 z2)), bt)
       | IT (Lit (Q (i1, j1)), _), IT (Lit (Q (i2, j2)), _) ->
          IT (Lit (Bool ((i1*j2) <= (i2*j1))), bt)
       | _, _ when equal a b ->
          bool_ true
       | IT (Arith_op (Rem (_, IT (Lit (Z z1), _))), _), 
         IT (Lit (Z z2), _) when
              Z.gt z1 Z.zero &&
              Z.gt z2 Z.zero &&
              Z.leq z1 (Z.add z2 (Z.of_int 1)) ->
          bool_ true
       | _, _ ->
          IT (Cmp_op (LE (a, b)), bt)
  
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
    | Null -> 
       IT (Pointer_op Null, bt)
    | AddPointer (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _, IT (Lit (Z offset), _) when Z.equal Z.zero offset ->
          a
       | IT (Pointer_op (AddPointer (aa, IT (Lit (Z i), _))), _), 
         IT (Lit (Pointer j), _) ->
          IT (Pointer_op (AddPointer (aa, IT (Lit (Pointer (Z.add i j)), Integer))), bt)
       | _ ->
          IT (Pointer_op (AddPointer (a, b)), bt)
       end
    | SubPointer (a, b) ->
       IT (Pointer_op (SubPointer (aux a, aux b)), bt)
    | MulPointer (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | _, IT (Lit (Z i2), _) when Z.equal i2 Z.zero ->
          pointer_ (Z.of_int 0)
       | _, IT (Lit (Z i2), _) when Z.equal i2 (Z.of_int 1) ->
          a
       | _ ->
          IT (Pointer_op (MulPointer (a, b)), bt)
       end
    | LTPointer (a, b) ->
       IT (Pointer_op (LTPointer (aux a, aux b)), bt)
    | LEPointer (a, b) ->
       let a = aux a in
       let b = aux b in
       begin match a, b with
       | IT (Pointer_op (AddPointer (base1, IT (Lit (Z offset1), _))), _),  
         IT (Pointer_op (AddPointer (base2, IT (Lit (Z offset2), _))), _) when
              equal base1 base2 ->
          if Z.leq offset1 offset2 then 
            IT (Lit (Bool true), bt)
          else
            IT (Lit (Bool false), bt)
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
    | Get (it, arg) ->
       let it = aux it in
       let arg = aux arg in
       IT (Array_op (Get (it, arg)), bt)
    | Def ((s, abt), body) ->
       let s' = Sym.fresh_same s in 
       let body = IndexTerms.subst [(s, sym_ (s', abt))] body in
       let body = simp lcs body in
       IT (Array_op (Def ((s', abt), body)), bt)


  in
  
  aux term


let simp_flatten lcs term =
  match simp lcs term with
  | IT (Bool_op (And lcs), _) -> lcs
  | lc -> [lc]




let simp_lc lcs lc = 
  match lc with
  | LC.T it -> 
     LC.T (simp lcs it)
  | LC.Forall ((s, bt), it) -> 
     let s' = Sym.fresh_same s in 
     let it = IndexTerms.subst [(s, sym_ (s', bt))] it in
     (* let trigger = Option.map (LC.subst_trigger [(s, sym_ (s', bt))]) trigger in *)
     let it = simp lcs it in
     LC.Forall ((s', bt), it)


let simp_lc_flatten lcs c = 
  match c with
  | LC.T it ->
     List.map (fun c -> LC.T c) (simp_flatten lcs it)
  | LC.Forall ((s, bt), it) -> 
     let s' = Sym.fresh_same s in 
     let it = IndexTerms.subst [(s, sym_ (s', bt))] it in
     (* let trigger = Option.map (LC.subst_trigger [(s, sym_ (s', bt))]) trigger in *)
     let it = simp lcs it in
     [LC.Forall ((s', bt), it)]
