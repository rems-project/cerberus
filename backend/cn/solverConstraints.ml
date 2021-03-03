open IndexTerms
open BaseTypes
open LogicalSorts
module IT = IndexTerms
module SymMap=Map.Make(Sym)



let of_index_term (global: Global.t) (it: IT.t) =

  let open Global in

  let context = global.solver_context in

  let rec bt_name = function
    | Unit -> "void"
    | Bool -> "bool"
    | Integer -> "integer"
    | Loc -> "pointer"
    | List bt -> "list("^bt_name bt^")"
    | Tuple bts -> "list("^String.concat "," (List.map bt_name bts)^")"
    | Struct sym -> "struct "^Sym.pp_string sym
    | Set bt -> "set("^bt_name bt^")"
    | Map bt -> "map("^bt_name bt^")"
  in
  let bt_symbol bt = Z3.Symbol.mk_string context (bt_name bt) in

  let tuple_field_name i = "comp" ^ string_of_int i in
  let tuple_field_symbol i = Z3.Symbol.mk_string context (tuple_field_name i) in

  let member_name id = Id.s id in
  let member_symbol id = Z3.Symbol.mk_string context (member_name id) in

  let rec sort_of_bt = function
    | Unit ->
       Z3.Sort.mk_uninterpreted_s context "unit"
    | Bool ->
       Z3.Boolean.mk_sort context
    | Integer ->
       Z3.Arithmetic.Integer.mk_sort context
    | Loc ->
       Z3.Arithmetic.Integer.mk_sort context
    | List bt ->
       Z3.Z3List.mk_sort context (bt_symbol bt) (sort_of_bt bt) 
    | Tuple bts ->
       let field_symbols = List.mapi (fun i _ -> tuple_field_symbol i) bts in
       let sorts = List.map sort_of_bt bts in
       Z3.Tuple.mk_sort context (bt_symbol (Tuple bts)) field_symbols sorts
    | Struct tag ->
       let decl = SymMap.find tag global.struct_decls in
       let members = Global.member_types decl.layout in
       let member_symbols = List.map (fun (id,_) -> member_symbol id) members in
       let member_sorts = 
         List.map (fun (_, sct) -> 
             sort_of_bt (BT.of_sct sct)
           ) members 
       in
       Z3.Tuple.mk_sort context (bt_symbol (Struct tag)) member_symbols member_sorts
    | Set bt ->
       Z3.Set.mk_sort context (sort_of_bt bt)
    | Map bt ->
       Z3.Z3Array.mk_sort context 
         (sort_of_bt Integer) (sort_of_bt bt)
  in



  let _sort_of_ls (Base bt) = sort_of_bt bt in


  let rec term = function
    | Lit t -> lit t
    | Arith_op t -> arith_op t
    | Bool_op t -> bool_op t
    | Cmp_op t -> cmp_op t
    | Tuple_op t -> tuple_op t
    | Pointer_op t -> pointer_op t
    | List_op t -> list_op t
    | Set_op t -> set_op t 
    | Array_op t -> array_op t
    | CT_pred t -> ct_pred t

  and lit = function
    | Sym (bt, s) -> 
       let sym = Z3.Symbol.mk_string context (Sym.pp_string s) in
       Z3.Expr.mk_const context sym (sort_of_bt bt)
    | Num z ->
       Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
    | Pointer z ->
       Z3.Arithmetic.Integer.mk_numeral_s context (Z.to_string z)
    | Bool true ->
       Z3.Boolean.mk_true context
    | Bool false ->
       Z3.Boolean.mk_false context
    | Unit ->
       Z3.Expr.mk_fresh_const context "unit" (sort_of_bt Unit)
       

  (* fix rem_t vs rem_f *)
  and arith_op = function
    | Add (t1, t2) ->
       Z3.Arithmetic.mk_add context [term t1; term t2]
    | Sub (t1, t2) ->
       Z3.Arithmetic.mk_sub context [term t1; term t2]
    | Mul (t1, t2) ->
       Z3.Arithmetic.mk_mul context [term t1; term t2]
    | Div (t1, t2) ->
       Z3.Arithmetic.mk_div context (term t1) (term t2)
    | Exp (t1, t2) ->
       Z3.Arithmetic.mk_power context (term t1) (term t2)
    | Rem_t (t1, t2) ->
       Z3.Arithmetic.Integer.mk_rem context (term t1) (term t2)
    | Rem_f (t1, t2) ->
       Z3.Arithmetic.Integer.mk_rem context (term t1) (term t2)
    | Min (t1, t2) ->
       term (ite_ (le_ (t1, t2), t1, t2))
    | Max (t1, t2) ->
       term (ite_ (ge_ (t1, t2), t1, t2))

  and bool_op = function
    | And ts -> 
       Z3.Boolean.mk_and context (List.map term ts)
    | Or ts -> 
       Z3.Boolean.mk_or context (List.map term ts)
    | Impl (t1, t2) -> 
       Z3.Boolean.mk_implies context (term t1) (term t2)
    | Not t ->
       Z3.Boolean.mk_not context (term t)
    | ITE (t1, t2, t3) ->
       Z3.Boolean.mk_ite context (term t1) (term t2) (term t3)

  and cmp_op = function
    | EQ (t1, t2) ->
       Z3.Boolean.mk_eq context (term t1) (term t2)
    | NE (t1, t2) ->
       Z3.Boolean.mk_distinct context [term t1; term t2]
    | LT (t1, t2) ->
       Z3.Arithmetic.mk_lt context (term t1) (term t2)
    | GT (t1, t2) ->
       Z3.Arithmetic.mk_gt context (term t1) (term t2)
    | LE (t1, t2) ->
       Z3.Arithmetic.mk_le context (term t1) (term t2)
    | GE (t1, t2) ->
       Z3.Arithmetic.mk_ge context (term t1) (term t2)

  and tuple_op = function 
    | Tuple (bts, ts) ->
       let constructor = Z3.Tuple.get_mk_decl (sort_of_bt (Tuple bts)) in
       Z3.Expr.mk_app context constructor (List.map term ts)
    | NthTuple (tuple_bt, n, t) ->
       let destructors = Z3.Tuple.get_field_decls (sort_of_bt tuple_bt) in
       Z3.Expr.mk_app context (List.nth destructors n) [term t]
    | Struct (tag, mts) ->
       let constructor = Z3.Tuple.get_mk_decl (sort_of_bt (Struct tag)) in
       Z3.Expr.mk_app context constructor (List.map (fun (_, t) -> term t) mts)
    | StructMember (tag, t, member) ->
       let decl = SymMap.find tag global.struct_decls in
       let members = List.map fst (Global.member_types decl.layout) in
       let destructors = Z3.Tuple.get_field_decls (sort_of_bt (Struct tag)) in
       let member_destructors = List.combine members destructors in
       let destructor = List.assoc Id.equal member member_destructors in
       Z3.Expr.mk_app context destructor [term t]       
    | StructMemberOffset (tag, t, member) ->
       let offset = Memory.member_offset tag member in
       Z3.Arithmetic.mk_add context [term t; term (num_ offset)]

  and pointer_op = function
    | Null t ->
       term (eq_ (t, num_ Z.zero))
    | AllocationSize t ->
       Debug_ocaml.error "todo: SMT mapping for AllocationSize"
    | AddPointer (t1, t2) ->
       Z3.Arithmetic.mk_add context [term t1; term t2]
    | SubPointer (t1, t2) ->
       Z3.Arithmetic.mk_sub context [term t1; term t2]
    | MulPointer (t1, t2) ->
       Z3.Arithmetic.mk_mul context [term t1; term t2]
    | LTPointer (t1, t2) ->
       Z3.Arithmetic.mk_lt context (term t1) (term t2)
    | LEPointer (t1, t2) ->
       Z3.Arithmetic.mk_le context (term t1) (term t2)
    | Disjoint ((p1, s1), (p2, s2)) ->
       let p1notin = or_ [lt_ (p1, p2); ge_ (p1, addPointer_ (p2, s2))] in
       let p2notin = or_ [lt_ (p2, p1); ge_ (p2, addPointer_ (p1, s1))] in
       let disjoint = and_ [p1notin; p2notin] in
       term disjoint
    | IntegerToPointerCast t ->
       term t
    | PointerToIntegerCast t ->
       term t
  and list_op _ = 
    Debug_ocaml.error "todo: SMT mapping for list operations"

  and set_op = function
    | SetMember (t1, t2) ->
        Z3.Set.mk_membership context (term t1) (term t2)
    | SetUnion ts ->
        Z3.Set.mk_union context (List.map term (List1.to_list ts))
    | SetIntersection ts ->
        Z3.Set.mk_intersection context (List.map term (List1.to_list ts))
    | SetDifference (t1, t2) ->
       Z3.Set.mk_difference context (term t1) (term t2)
    | Subset (t1, t2) ->
       Z3.Set.mk_subset context (term t1) (term t2)

  and array_op = function
    | ConstArray (t, bt) ->
       Z3.Z3Array.mk_const_array context (sort_of_bt bt) (term t)
    | ArrayGet (t1, t2) ->
       Z3.Z3Array.mk_select context (term t1) (term t2)
    | ArraySet (t1, t2, t3) ->
       Z3.Z3Array.mk_store context (term t1) (term t2) (term t3)
    | ArrayEqualOnRange (at1, at2, it1, it2) ->
       let a1, a2 = term at1, term at2 in
       let i1, i2 = term it1, term it2 in
       let straight_equality = Z3.Boolean.mk_eq context a1 a2 in
       let restricted_equality = 
         let i = Z3.Expr.mk_fresh_const context "i" (sort_of_bt Integer) in
         let body = 
           let in_range = 
             Z3.Boolean.mk_and context [
                 Z3.Arithmetic.mk_le context i1 i;
                 Z3.Arithmetic.mk_le context i i2;
               ] 
           in
           let select_a1 = Z3.Z3Array.mk_select context a1 i in
           let select_a2 = Z3.Z3Array.mk_select context a2 i in
           let select_equal = Z3.Boolean.mk_eq context select_a1 select_a2 in
           Z3.Boolean.mk_implies context in_range select_equal 
         in
         let q = Z3.Quantifier.mk_forall_const context [i] body None [] [] None None in
         Z3.Quantifier.expr_of_quantifier q
       in
       Z3.Boolean.mk_or context [straight_equality; restricted_equality]
    | ArraySelectAfter _ ->
       Debug_ocaml.error "todo: SMT mapping for ArraySelectAfter"
    | ArrayIndexShiftRight _ ->
       Debug_ocaml.error "todo: SMT mapping for ArrayIndexShiftRight"

  and ct_pred = function
    | MinInteger it ->
       term (num_ (Memory.min_integer_type it))
    | MaxInteger it ->
       term (num_ (Memory.max_integer_type it))
    | Representable (ct, t) ->
       let (LC it) = Memory.representable_ctype global.struct_decls ct t in
       term it
    | AlignedI (t1, t2) ->
       term (eq_ (rem_t_ (t2, t1), num_ Z.zero))
    | Aligned (ct, t) ->
       term (eq_ (rem_t_ (t, num_ (Memory.align_of_ctype ct)), num_ Z.zero))
  in

  term it

