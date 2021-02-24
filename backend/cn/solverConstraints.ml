open Global
open List
open Pp
open LogicalSorts

(* copying bits and pieces from https://github.com/alastairreid/asl-interpreter/blob/master/libASL/tcheck.ml and 
https://github.com/Z3Prover/z3/blob/master/examples/ml/ml_example.ml *)
(* and the bmc backend *)


let rem_t_warned = ref false
let rem_f_warned = ref false



(*** mapping to Z3 ************************************************************)

let sym_to_symbol ctxt sym =
  let open Cerb_frontend.Symbol in
  let (Symbol (_digest, num, _mstring)) = sym in
  Z3.Symbol.mk_int ctxt num

let bt_name bt = 
  plain (BT.pp bt)

let tuple_component_name bt i =
  bt_name bt ^ "__" ^ string_of_int i

let struct_member_name bt member =
  bt_name bt ^ "__" ^ Pp.plain (Id.pp member)

let member_sort ctxt = 
  Z3.Sort.mk_uninterpreted_s ctxt "member"


(* maybe fix Loc *)
let rec bt_to_sort global bt = 
  let ctxt = global.solver_context in
  let open BaseTypes in
  let btname = bt_name bt in
  let sort = match bt with
    | Unit -> Z3.Sort.mk_uninterpreted_s ctxt btname
    | Bool -> Z3.Boolean.mk_sort ctxt
    | Integer -> Z3.Arithmetic.Integer.mk_sort ctxt
    | Loc -> Z3.Arithmetic.Integer.mk_sort ctxt
    (* | Loc -> return (Z3.Sort.mk_uninterpreted_s ctxt btname) *)
    | Tuple bts ->
       let names = mapi (fun i _ -> Z3.Symbol.mk_string ctxt (tuple_component_name bt i)) bts in
       let sorts = List.map (bt_to_sort global) bts in
       Z3.Tuple.mk_sort ctxt (Z3.Symbol.mk_string ctxt btname) names sorts
    | Struct tag ->
       let decl = SymMap.find tag global.struct_decls in
       let rec aux = function
         | [] -> ([],[])
         | (member, sct) :: members ->
            let (names,sorts) = aux members in
            let sort = bt_to_sort global (BT.of_sct sct) in
            let names = Z3.Symbol.mk_string ctxt (struct_member_name bt member) :: names in
            let sorts = sort :: sorts in
            (names,sorts)
       in
       let (names,sorts) = aux (Global.member_types decl.layout) in
       let name = Z3.Symbol.mk_string ctxt btname in
       let sort = Z3.Tuple.mk_sort ctxt name names sorts in
       sort
    | Array ->
       Z3.Sort.mk_uninterpreted_s ctxt btname
    | List _ ->
       Z3.Sort.mk_uninterpreted_s ctxt btname
    | Set bt ->
       Z3.Set.mk_sort ctxt (bt_to_sort global bt)
    | Map (bt1,bt2) ->
       Z3.Z3Array.mk_sort ctxt (bt_to_sort global bt1) (bt_to_sort global bt2)
  in
  sort

let ls_to_sort global (LS.Base bt) =
  bt_to_sort global bt


let rec of_index_term global it = 
  let ctxt = global.solver_context in
  let open Pp in
  let open IndexTerms in
  let nth_to_fundecl bt i = 
    let sort = ls_to_sort global (Base bt) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    List.nth member_fun_decls i
  in
  let member_to_fundecl tag member = 
    let decl = SymMap.find tag global.struct_decls in
    let sort = ls_to_sort global (Base (Struct tag)) in
    let member_fun_decls = Z3.Tuple.get_field_decls sort in
    let member_names = 
      map (fun (member, _) -> member)
        (Global.member_types decl.layout)
    in
    let member_funs = combine member_names member_fun_decls in
    assoc Id.equal member member_funs
  in
  match it with
  (* literals *)
  | S (bt, s) -> 
     let sym = sym_to_symbol ctxt s in
     let sort = bt_to_sort global bt in
     Z3.Expr.mk_const ctxt sym sort
  | Num n -> 
     let nstr = Nat_big_num.to_string n in
     Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr
  | Pointer n -> 
     let nstr = Nat_big_num.to_string n in
     Z3.Arithmetic.Integer.mk_numeral_s ctxt nstr
  | Bool true -> 
     Z3.Boolean.mk_true ctxt
  | Bool false -> 
     Z3.Boolean.mk_false ctxt
  | Unit ->
     let unitsort = ls_to_sort global (Base Unit) in
     Z3.Expr.mk_const_s ctxt "unit" unitsort
  (* arithmetic *)
  | Add (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_add ctxt [a;a']
  | Sub (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_sub ctxt [a;a']
  | Mul (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_mul ctxt [a; a']
  | Div (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_div ctxt a a'
  | Exp (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_power ctxt a a'
  | Rem_t (it,it') -> 
     if not (!Debug_ocaml.debug_level > 0) && !rem_t_warned then
       (rem_t_warned := true; Pp.warn !^"Rem_t constraint");
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.Integer.mk_rem ctxt a a'
  | Rem_f (it,it') -> 
     if not (!Debug_ocaml.debug_level > 0) && !rem_f_warned then
       (rem_f_warned := true; Pp.warn !^"Rem_f constraint");
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.Integer.mk_rem ctxt a a'
  | Min (it,it') -> 
     let it_elab = ITE (it %< it', it, it') in
     of_index_term global it_elab 
  | Max (it,it') -> 
     let it_elab = ITE (it %> it', it, it') in
     of_index_term global it_elab 
  (* comparisons *)
  | EQ (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Boolean.mk_eq ctxt a a'
  | NE (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Boolean.mk_distinct ctxt [a; a']
  | LT (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_lt ctxt a a'
  | GT (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_gt ctxt a a'
  | LE (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_le ctxt a a'
  | GE (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_ge ctxt a a'
  (* booleans *)
  | And its -> 
     let ts = List.map (of_index_term global) its in
     Z3.Boolean.mk_and ctxt ts
  | Or its -> 
     let ts = List.map (of_index_term global) its in
     Z3.Boolean.mk_or ctxt ts
  | Impl (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Boolean.mk_implies ctxt a a'
  | Not it -> 
     let a = of_index_term global it in
     Z3.Boolean.mk_not ctxt a
  | ITE (it,it',it'') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     let a'' = of_index_term global it'' in
     Z3.Boolean.mk_ite ctxt a a' a''
  (* tuples *)
  | Tuple (bts, ts) ->
     let sort = bt_to_sort global (Tuple bts) in
     let constructor = Z3.Tuple.get_mk_decl sort in
     let components = 
       List.map (fun it ->
           of_index_term global it
         ) ts
     in
     Z3.Expr.mk_app ctxt constructor components
  | NthTuple (bt,i,t) ->
     let a = of_index_term global t in
     let fundecl = nth_to_fundecl bt i in
     Z3.Expr.mk_app ctxt fundecl [a]
  | Struct (tag,members) ->
     let sort = bt_to_sort global (Struct tag) in
     let constructor = Z3.Tuple.get_mk_decl sort in
     let member_vals = 
       List.map (fun (_member,it) ->
           of_index_term global it
         ) members
     in
     Z3.Expr.mk_app ctxt constructor member_vals
  | StructMember (tag, t, member) ->
     let a = of_index_term global t in
     let fundecl = member_to_fundecl tag member in
     Z3.Expr.mk_app ctxt fundecl [a]
  | StructMemberOffset (tag, t, member) ->
     let a = of_index_term global t in
     let offset = Memory.member_offset tag member in
     let offset_s = Nat_big_num.to_string offset in
     let offset_n = Z3.Arithmetic.Integer.mk_numeral_s ctxt offset_s in
     Z3.Arithmetic.mk_add ctxt [a;offset_n]
  (* pointers *)
  | Null t -> 
     let locsort = ls_to_sort global (Base Loc) in
     let boolsort = ls_to_sort global (Base Bool) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "null" [locsort] boolsort in
     let a = of_index_term global t in
     let is_null = Z3.Expr.mk_app ctxt fundecl [a] in
     let zero_str = Nat_big_num.to_string Z.zero in
     let zero_expr = Z3.Arithmetic.Integer.mk_numeral_s ctxt zero_str in
     let is_zero = Z3.Boolean.mk_eq ctxt a zero_expr in
     Z3.Boolean.mk_and ctxt [is_null; is_zero]
  | AllocationSize t ->
     let locsort = ls_to_sort global (Base Loc) in
     let intsort = ls_to_sort global (Base Integer) in
     let fundecl = Z3.FuncDecl.mk_func_decl_s ctxt "allocationSize" [locsort] intsort in
     let a = of_index_term global t in
     Z3.Expr.mk_app ctxt fundecl [a]
  | AddPointer (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_add ctxt [a;a']
  | SubPointer (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_sub ctxt [a;a']
  | MulPointer (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_mul ctxt [a;a']
  | LTPointer (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_lt ctxt a a'
  | LEPointer (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Arithmetic.mk_le ctxt a a'
  | Disjoint ((it,s),(it',s')) ->
     let fp1_before_fp2 = IT.LTPointer (AddPointer (AddPointer (it, s), IT.int (-1)), it') in
     let fp2_before_fp1 = IT.LTPointer (AddPointer (AddPointer (it', s'), IT.int (-1)), it) in
     let t = Or [fp1_before_fp2; fp2_before_fp1] in
     of_index_term global t
  | Aligned (st,it') -> 
     let align = Memory.align_of_stored_type st in
     let a = of_index_term global (Num align) in
     let a' = of_index_term global it' in
     Z3.Boolean.mk_eq ctxt
       (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
       (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
  | AlignedI (it,it') -> 
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Boolean.mk_eq ctxt
       (Z3.Arithmetic.Integer.mk_mod ctxt a' a)
       (Z3.Arithmetic.Integer.mk_numeral_s ctxt "0")
  | IntegerToPointerCast it ->
     (* identity, at the moment *)
     of_index_term global it
  | PointerToIntegerCast it ->
     (* identity, at the moment *)
     of_index_term global it
  (* representability *)
  | MinInteger it ->
     of_index_term global 
       (Num (Memory.min_integer_type it))
  | MaxInteger it ->
     of_index_term global 
       (Num (Memory.max_integer_type it))
  | Representable (st, t) ->
     let rangef = Memory.representable_stored_type global.struct_decls st in
     of_index_term global (LC.unpack (rangef t))
  (* lists *)
  | Nil _ ->
     Debug_ocaml.error "todo: Z3: Nil"
  | Cons _ ->
     Debug_ocaml.error "todo: Z3: Cons"
  | Head t ->
     Debug_ocaml.error "todo: Z3: Head"
  | Tail t ->
     Debug_ocaml.error "todo: Z3: Tail"
  | List (ts,bt) ->
     Debug_ocaml.error "todo: Z3: List"
  | NthList (i,it) ->
     Debug_ocaml.error "todo: Z3: NthList"
  (* sets *)
  | SetMember (it,it') ->
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Set.mk_membership ctxt a a'
  | SetUnion its ->
     let ts = List.map (of_index_term global) 
                (List1.to_list its) in
     Z3.Set.mk_union ctxt ts
  | SetIntersection its ->
     let ts = List.map (of_index_term global) 
                (List1.to_list its) in
     Z3.Set.mk_intersection ctxt ts
  | SetDifference (it, it') ->
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Set.mk_difference ctxt a a'
  | Subset (it, it') ->
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Set.mk_subset ctxt a a'
  | ConstArray (it, bt) ->
     let sort = bt_to_sort global bt in
     let a = of_index_term global it in
     Z3.Z3Array.mk_const_array ctxt sort a
  | ArrayGet (it,it') ->
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     Z3.Z3Array.mk_select ctxt a a'
  | ArraySet (it,it',it'') ->
     let a = of_index_term global it in
     let a' = of_index_term global it' in
     let a'' = of_index_term global it'' in
     Z3.Z3Array.mk_store ctxt a a' a''
  | ArrayEqualOnRange(array1,array2,i_from,i_to) ->
     let array1 = of_index_term global array1 in
     let array2 = of_index_term global array2 in
     let i_from = of_index_term global i_from in
     let i_to = of_index_term global i_to in
     let i = 
       Z3.Expr.mk_const ctxt 
         (sym_to_symbol ctxt (Sym.fresh ()))
         (bt_to_sort global Integer) 
     in
     let in_range = 
       Z3.Boolean.mk_and ctxt [
           Z3.Arithmetic.mk_le ctxt i_from i;
           Z3.Arithmetic.mk_le ctxt i i_to;
         ]
     in
     let select_equal = 
       Z3.Boolean.mk_eq ctxt
         (Z3.Z3Array.mk_select ctxt array1 i)
         (Z3.Z3Array.mk_select ctxt array2 i)
     in
     let body = Z3.Boolean.mk_implies ctxt in_range select_equal in
     let subrange_equal = 
       Z3.Quantifier.expr_of_quantifier 
         (Z3.Quantifier.mk_forall_const 
            ctxt [i] body None [] (* pattern list *)
            [] None None)
     in
     Z3.Boolean.mk_or ctxt [
         Z3.Boolean.mk_eq ctxt array1 array2;
         subrange_equal
       ]
  | ArraySelectAfter ((t1,t2), t3) ->
     Debug_ocaml.error "Z3 mapping for ArraySelectAfter"
  | ArrayIndexShiftRight (t1, t2) ->
     Debug_ocaml.error "Z3 mapping for ArrayIndexShiftRight"
