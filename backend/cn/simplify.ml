module IT = IndexTerms
open IndexTerms

module SymPair = struct
  type t = Sym.t * Sym.t
  let compare (s1,s2) (s1',s2') =
    let c1 = Sym.compare s1 s1' in
    if c1 <> 0 then c1 else Sym.compare s2 s2'
end


module SymPairMap = Map.Make(SymPair)


let simp (lcs : t list) term = 

  let values = 
    List.fold_right (fun (IT (it, bt)) values ->
        match it with
        | Bool_op (EQ (it, it')) ->
           begin match is_sym it with
           | Some (sym, _) -> SymMap.add sym it' values
           | None -> values
           end
        | _ -> values
      ) lcs SymMap.empty
  in

  let equalities =
    List.fold_right (fun it equalities ->
        match it with
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
      ) lcs SymPairMap.empty
  in

  let is_true = function
    | IT (Lit (Bool true), _) -> true
    | _ -> false
  in

  let is_false = function
    | IT (Lit (Bool false), _) -> true
    | _ -> false
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
    | Array_op it -> IT (Array_op it, bt)
    | CT_pred it -> IT (CT_pred it, bt)
    | Option_op it -> option_op it bt

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
          IT (Lit (Z (Z.add_big_int i1 i2)), bt)
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
          IT (Lit (Z (Z.sub_big_int i1 i2)), bt)
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
       | _, IT (Lit (Z b), _) when Z.equal b (Z.of_int 1) -> 
          a
       | _ ->
          IT (Arith_op (Div (a, b)), bt) 
       end
    | Exp (a, b) ->
       IT (Arith_op (Exp (aux a, aux b)), bt) 
    | Rem_t (a, b) ->
       let a = aux a in
       let b = aux b in 
       begin match a, b with
       | _, IT (Lit (Z b), _) when Z.equal b (Z.of_int 1) -> 
          IT (Lit (Z Z.zero), bt)
       | _ ->
          IT (Arith_op (Rem_t (a, b)), bt) 
       end
    | Rem_f (a, b) ->
       let a = aux a in
       let b = aux b in 
       begin match a, b with
       | _, IT (Lit (Z b), _) when Z.equal b (Z.of_int 1) -> 
          IT (Lit (Z Z.zero), bt)
       | _ ->
          IT (Arith_op (Rem_f (a, b)), bt) 
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
       match a, b with
       | _ when equal a b ->
         IT (Lit (Bool true), bt) 
       | IT (Lit (Z i1), _), IT (Lit (Z i2), _) ->
          bool_ (Z.equal i1 i2)
       | IT (Pointer_op (AddPointer (b1,o1)), _), 
         IT (Pointer_op (AddPointer (b2,o2)), _) 
            when equal b1 b2 ->
          aux (eq_ (o1, o2))
       | IT (Lit (Sym s), _), IT (Lit (Sym s'), _) ->
          begin match SymPairMap.find_opt (s,s') equalities with
          | Some bool -> bool_ bool
          | _ -> eq_ (a, b)
          end
       | _, _ ->
          eq_ (a, b)
        

  and cmp_op it bt = 
    let cmp_rule mk z_op int_op a b =
      let a = aux a in
      let b = aux b in
       match a, b with
       | IT (Lit (Z z1), _), IT (Lit (Z z2), _) ->
          IT (Lit (Bool (z_op z1 z2)), bt)
       | IT (Lit (Q (i1, j1)), _), IT (Lit (Q (i2, j2)), _) ->
          IT (Lit (Bool (int_op (i1*j2) (i2*j1))), bt)
       | _, _ ->
          IT (Cmp_op (mk (a, b)), bt)
    in
    match it with
    | LT (a, b) -> cmp_rule (fun (a, b) -> LT (a, b)) Z.lt_big_int (<) a b
    | LE (a, b) -> cmp_rule (fun (a, b) -> LE (a, b)) Z.le_big_int (<=) a b

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
    | IT.StructMember (tag, it, member) ->
       let it = aux it in
       IT (Struct_op (IT.StructMember (tag, it, member)), bt)

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
          IT (Pointer_op (AddPointer (aa, IT (Lit (Pointer (Z.add_big_int i j)), Integer))), bt)
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
          if Z.le_big_int offset1 offset2 then 
            IT (Lit (Bool true), bt)
          else if Z.gt_big_int offset1 offset2 then
            IT (Lit (Bool false), bt)
          else
            IT (Pointer_op (LEPointer (a, b)), bt)
       | _ -> 
          IT (Pointer_op (LEPointer (a, b)), bt)
       end
    | IntegerToPointerCast a ->
       IT (Pointer_op (IntegerToPointerCast (aux a)), bt)
    | PointerToIntegerCast a ->
       IT (Pointer_op (PointerToIntegerCast (aux a)), bt)       


  and option_op it bt =
    match it with
    | Something it -> IT (Option_op (Something (aux it)), bt)
    | Nothing bt' -> IT (Option_op (Nothing bt'), bt)
    | Is_some it -> IT (Option_op (Is_some (aux it)), bt)
    | Value_of_some it -> IT (Option_op (Value_of_some (aux it)), bt)
  in


  aux term
