open Resultat
module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors
module L = Local
module RE = Resources.RE

open Global
open TE
open Pp



module Make (G : sig val global : Global.t end) = struct
  module Solver = Solver.Make(G)
  module Explain = Explain.Make(G)

  let check_bound loc (names : Explain.naming) local kind s = 
    if L.bound s kind local then return ()
    else fail loc (TE.Unbound_name (Sym s))


  let ensure_integer_or_real_type loc names local context it bt = 
    let open BT in
    match bt with
    | Integer -> 
       return Integer
    | Real -> 
       return Real
    | _ -> 
       let (context, it) = Explain.index_terms names local (context, it) in
       let err = 
         !^"Illtyped index term" ^^^ context ^^ dot ^^^
           !^"Expected" ^^^ it ^^^ !^"to have integer or real type" ^^^ 
             !^"but has type" ^^^ BT.pp bt
       in
       fail loc (Generic err)

  let ensure_set_type loc names local context it bt = 
    let open BT in
    match bt with
    | Set bt -> return bt
    | _ -> 
       let (context, it) = Explain.index_terms names local (context, it) in
       let err = 
         !^"Illtyped index term" ^^^ context ^^ dot ^^^
           !^"Expected" ^^^ it ^^^ !^"to have set type" ^^ comma ^^^
             !^"but has type" ^^^ BT.pp bt
       in
       fail loc (Generic err)

  let ensure_list_type loc names local context it bt = 
    let open BT in
    match bt with
    | List bt -> return bt
    | _ -> 
       let (context, it) = Explain.index_terms names local (context, it) in
       let err = 
         !^"Illtyped index term" ^^^ context ^^ dot ^^^
           !^"Expected" ^^^ it ^^^ !^"to have list type" ^^^ 
             !^"but has type" ^^^ BT.pp bt
       in
       fail loc (Generic err)

  let ensure_param_type loc names local context it bt = 
    let open BT in
    match bt with
    | Param (abt,rbt) -> return (abt, rbt)
    | _ -> 
       let (context, it) = Explain.index_terms names local (context, it) in
       let err = 
         !^"Illtyped index term" ^^^ context ^^ dot ^^^
           !^"Expected" ^^^ it ^^^ !^"to have integer map type" ^^ comma ^^^
             !^"but has type" ^^^ BT.pp bt
       in
       fail loc (Generic err)

  let ensure_option_type loc names local context it bt = 
    let open BT in
    match bt with
    | Option bt -> return bt
    | _ -> 
       let (context, it) = Explain.index_terms names local (context, it) in
       let err = 
         !^"Illtyped index term" ^^^ context ^^ dot ^^^
           !^"Expected" ^^^ it ^^^ !^"to have option type" ^^ comma ^^^
             !^"but has type" ^^^ BT.pp bt
       in
       fail loc (Generic err)
  

  module WIT = struct

    open BaseTypes
    open LogicalSorts
    open IndexTerms

    type t = IndexTerms.t

    let check_or_infer loc names local ols it = 

      let context = it in

      let get_struct_decl tag = 
        match SymMap.find_opt tag G.global.struct_decls with
        | Some decl -> return decl
        | None -> fail loc (Missing_struct tag)
      in

      let get_member_type decl_members member it =
        match List.assoc_opt Id.equal member decl_members with
        | Some sct -> return (BT.of_sct sct)
        | None -> 
           let (context, it) = Explain.index_terms names local (context, it) in
           let err = 
             !^"Illtyped index term" ^^^ context ^^ dot ^^^
               it ^^^ !^"does not have member" ^^^ Id.pp member
           in
           fail loc (Generic err)
      in
      

      let rec infer : 'bt. Loc.t -> L.t -> 'bt IT.term -> (LogicalSorts.t * IT.t, type_error) m =

        let lit local = function
          | Sym s ->
             let@ () = check_bound loc names local KLogical s in
             return (L.get_l s local, Sym s)
          | Z z -> 
             return (Integer, Z z)
          | Q (n,n') -> 
             return (Real, Q (n,n'))
          | Pointer p -> 
             return (Loc, Pointer p)
          | Bool b -> 
             return (BT.Bool, Bool b)
          | Unit -> 
             return (BT.Unit, Unit)
          | Default bt -> 
             return (bt, Default bt)
        in

        let arith_op local = function
          | Add (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (bt, Add (t, t'))
          | Sub (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (bt, Sub (t, t'))
          | Mul (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (bt, Mul (t, t'))
          | Div (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (bt, Div (t, t'))
          | Exp (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (bt, Exp (t, t'))
          | Rem (t,t') ->
             let@ t = check loc local Integer t in
             let@ t' = check loc local Integer t' in
             return (Integer, Rem (t, t'))
        in

        let cmp_op local = function
          | LT (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (BT.Bool, LT (t, t'))
          | LE (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc local t in
             let@ t' = check loc local bt t' in
             return (BT.Bool, LE (t, t'))
        in

        let bool_op local = function
          | And ts ->
             let@ ts = ListM.mapM (check loc local Bool) ts in
             return (BT.Bool, And ts)
          | Or ts ->
             let@ ts = ListM.mapM (check loc local Bool) ts in
             return (BT.Bool, Or ts)
          | Impl (t,t') ->
             let@ t = check loc local Bool t in
             let@ t' = check loc local Bool t' in
             return (BT.Bool, Impl (t, t'))
          | Not t ->
             let@ t = check loc local Bool t in
             return (BT.Bool, Not t)
          | ITE (t,t',t'') ->
             let@ t = check loc local Bool t in
             let@ (ls, t') = infer loc local t' in
             let@ t'' = check loc local ls t'' in
             return (ls, ITE (t, t', t''))
          | EQ (t,t') ->
             let@ (ls,t) = infer loc local t in
             let@ t' = check loc local ls t' in
             return (BT.Bool, EQ (t,t')) 
        in

        let tuple_op local = function
          | Tuple ts ->
             let@ bts_ts = ListM.mapM (infer loc local) ts in
             let (bts,ts) = List.split bts_ts in
             return (BT.Tuple bts, Tuple ts)
          | NthTuple (n, t') ->
             let@ (tuple_bt,t') = infer loc local t' in
             let@ item_bt = match tuple_bt with
               | Tuple bts ->
                  begin match List.nth_opt bts n with
                  | Some t -> return t
                  | None -> 
                     let (context, t') = Explain.index_terms names local (context, t') in
                     let err = 
                       !^"Illtyped index term" ^^^ context ^^ dot ^^^
                         !^"Expected" ^^^ t' ^^^ !^"to be tuple with at least" ^^^ !^(string_of_int n) ^^^
                           !^"components, but has type" ^^^ BT.pp (Tuple bts)
                     in
                     fail loc (Generic err)
                  end
               | _ -> 
                  let (context, t') = Explain.index_terms names local (context, t') in
                  let err = 
                    !^"Illtyped index term" ^^^ context ^^ dot ^^^
                      !^"Expected" ^^^ t' ^^^ !^"to have tuple type, but has type" ^^^
                        BT.pp tuple_bt
                  in
                  fail loc (Generic err)
             in
             return (item_bt, NthTuple (n, t'))
        in
        
        let struct_op local = function
          | Struct (tag, members) ->
             let@ layout = get_struct_decl tag in
             let decl_members = Memory.member_types layout in
             let@ () = 
               let has = List.length members in
               let expect = List.length decl_members in
               if has = expect then return ()
               else fail loc (Number_members {has; expect})
             in
             let@ members = 
               ListM.mapM (fun (member,t) ->
                   let@ bt = get_member_type decl_members member it in
                   let@ t = check loc local bt t in
                   return (member, t)
                 ) members
             in
             return (BT.Struct tag, Struct (tag, members))
          | StructMember (t, member) ->
             let@ (bt, t) = infer loc local t in
             let@ tag = match bt with
               | Struct tag -> return tag
               | _ -> 
                  let (context, t) = Explain.index_terms names local (context, t) in
                  let err = 
                    !^"Illtyped index term" ^^^ context ^^ dot ^^^
                      !^"Expected" ^^^ t ^^^ !^"to have struct type" ^^^ 
                        !^"but has type" ^^^ BT.pp bt
                  in
                  fail loc (Generic err)
             in
             let@ layout = get_struct_decl tag in
             let decl_members = Memory.member_types layout in
             let@ bt = get_member_type decl_members member t in
             return (bt, StructMember (t, member))
        in

        let pointer_op local = function
          | Null ->
             return (BT.Loc, Null)
          | AddPointer (t, t') ->
             let@ t = check loc local Loc t in
             let@ t' = check loc local Integer t' in
             return (Loc, AddPointer (t, t'))
          | SubPointer (t, t') ->
             let@ t = check loc local Loc t in
             let@ t' = check loc local Integer t' in
             return (Loc, SubPointer (t, t'))
          | MulPointer (t, t') ->
             let@ t = check loc local Loc t in
             let@ t' = check loc local Integer t' in
             return (Loc, MulPointer (t, t'))
          | LTPointer (t, t') ->
             let@ t = check loc local Loc t in
             let@ t' = check loc local Loc t' in
             return (BT.Bool, LTPointer (t, t'))
          | LEPointer (t, t') ->
             let@ t = check loc local Loc t in
             let@ t' = check loc local Loc t' in
             return (BT.Bool, LEPointer (t, t'))
          (* | Disjoint ((t,s), (t',s')) ->
           *    let@ t = check loc (Base Loc) t in
           *    let@ t' = check loc (Base Loc) t' in
           *    let@ s = check loc (Base Integer) s in
           *    let@ s' = check loc (Base Integer) s' in
           *    return (Base Bool, Disjoint ((t,s), (t',s'))) *)
          | IntegerToPointerCast t ->
             let@ t = check loc local Integer t in
             return (Loc, IntegerToPointerCast t)
          | PointerToIntegerCast t ->
             let@ t = check loc local Loc t in
             return (Integer, PointerToIntegerCast t)
          | MemberOffset (tag, member) ->
             return (Integer, MemberOffset (tag, member))
          | ArrayOffset (ct, t) ->
             let@ t = check loc local Integer t in
             return (Integer, ArrayOffset (ct, t))
        in

        let ct_pred local = function
          | AlignedI t ->
             let@ t_t = check loc local Loc t.t in
             let@ t_align = check loc local Integer t.align in
             return (BT.Bool, AlignedI {t = t_t; align=t_align})
          | Aligned (t, ct) ->
             let@ t = check loc local Loc t in
             return (BT.Bool, Aligned (t, ct))
          | Representable (ct, t) ->
             let@ t = check loc local (BT.of_sct ct) t in
             return (BT.Bool, Representable (ct, t))
        in

        let list_op local = function
          | Nil -> 
             fail loc (Polymorphic_it context)
          | Cons (t1,t2) ->
             let@ (item_bt, t1) = infer loc local t1 in
             let@ t2 = check loc local (List item_bt) t2 in
             return (BT.List item_bt, Cons (t1, t2))
          | List [] ->
             fail loc (Polymorphic_it context)
          | List (t :: ts) ->
             let@ (bt, t) = infer loc local t in
             let@ ts = ListM.mapM (check loc local bt) ts in
             return (BT.List bt, List (t :: ts))
          | Head t ->
             let@ (bt,t) = infer_list_type loc local t in
             return (bt, Head t)
          | Tail t ->
             let@ (bt,t) = infer_list_type loc local t in
             return (BT.List bt, Tail t)
          | NthList (i, t) ->
             let@ (bt,t) = infer_list_type loc local t in
             return (bt, NthList (i, t))
        in

        let set_op local = function
          | SetMember (t,t') ->
             let@ (bt, t) = infer loc local t in
             let@ t' = check loc local (Set bt) t' in
             return (BT.Bool, SetMember (t, t'))
          | SetUnion its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc local t in
             let@ ts = ListM.mapM (check loc local (Set itembt)) ts in
             return (Set itembt, SetUnion (List1.make (t, ts)))
          | SetIntersection its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc local t in
             let@ ts = ListM.mapM (check loc local (Set itembt)) ts in
             return (Set itembt, SetIntersection (List1.make (t, ts)))
          | SetDifference (t, t') ->
             let@ (itembt, t)  = infer_set_type loc local t in
             let@ t' = check loc local (Set itembt) t' in
             return (Set itembt, SetDifference (t, t'))
          | Subset (t, t') ->
             let@ (bt, t) = infer_set_type loc local t in
             let@ t' = check loc local (Set bt) t' in
             return (BT.Bool, Subset (t,t'))
        in

        let option_op local = function
          | Something it ->
             let@ (bt, it) = infer loc local it in
             let mbt = BT.Option bt in
             return (mbt, Something it)
          | Nothing bt ->
             let mbt = BT.Option bt in
             return (mbt, Nothing bt)
          | Is_some it ->
             let@ (_, it) = infer_option_type loc local it in
             return (BT.Bool, Is_some it)
          | Value_of_some it ->
             let@ (bt, it) = infer_option_type loc local it in
             return (bt, Value_of_some it)
        in

        let param_op local = function
          | Const it ->
             let@ (bt, it) = infer loc local it in
             return (BT.Param (BT.Integer, bt), Const it)
          | Mod (it1, it2, it3) ->
             let@ (bt2, it2) = infer loc local it2 in
             let@ (bt3, it3) = infer loc local it3 in
             let bt = BT.Param (bt2, bt3) in
             let@ it1 = check loc local bt it1 in
             return (bt, Mod (it1, it2, it3))
          | Param ((sym, abt), it) -> 
             let local = L.add_l sym abt local in
             let@ (bt, it) = infer loc local it in
             return (BT.Param (abt, bt), Param ((sym, abt), it))
          | App (it, arg) -> 
             let@ (fbt, it) = infer loc local it in
             begin match fbt with
             | BT.Param (abt, bt) (* when List.length bts = List.length args *) -> 
                let@ arg = check loc local abt arg in
                return (bt, App (it, arg))
             | bt -> 
                let (context, it) = Explain.index_terms names local (context, it) in
                let err = 
                  !^"Illtyped index term" ^^^ context ^^ dot ^^^
                    !^"Expected" ^^^ it ^^^ !^"to have parameterised type" ^^^ 
                      !^"but has type" ^^^ BT.pp bt
                in
                fail loc (Generic err)
             end               
        in

        fun loc local (IT (it, _)) ->
        match it with
        | Lit it ->
           let@ (bt, it) = lit local it in
           return (bt, IT (Lit it, bt))
        | Arith_op it ->
           let@ (bt, it) = arith_op local it in
           return (bt, IT (Arith_op it, bt))
        | Cmp_op it ->
           let@ (bt, it) = cmp_op local it in
           return (bt, IT (Cmp_op it, bt))
        | Bool_op it ->
           let@ (bt, it) = bool_op local it in
           return (bt, IT (Bool_op it, bt))
        | Tuple_op it ->
           let@ (bt, it) = tuple_op local it in
           return (bt, IT (Tuple_op it, bt))
        | Struct_op it ->
           let@ (bt, it) = struct_op local it in
           return (bt, IT (Struct_op it, bt))
        | Pointer_op it ->
           let@ (bt, it) = pointer_op local it in
           return (bt, IT (Pointer_op it, bt))
        | CT_pred it ->
           let@ (bt, it) = ct_pred local it in
           return (bt, IT (CT_pred it, bt))
        | List_op it ->
           let@ (bt, it) = list_op local it in
           return (bt, IT (List_op it, bt))
        | Set_op it ->
           let@ (bt, it) = set_op local it in
           return (bt, IT (Set_op it, bt))
        (* | Array_op it ->
         *    let@ (bt, array_op) = array_op local it in
         *    return (bt, IT (Array_op array_op, bt)) *)
        | Option_op it ->
           let@ (bt, option_op) = option_op local it in
           return (bt, IT (Option_op option_op, bt))
        | Param_op it -> 
           let@ (bt, param_op) = param_op local it in
           return (bt, IT (Param_op param_op, bt))
           
           


      and check : 'bt. Loc.t -> L.t -> LS.t -> 'bt IT.term -> (IT.t, type_error) m =
        fun loc local ls it ->
        match it, ls with
        | IT (List_op Nil, _), List bt ->
           return (IT (List_op Nil, BT.List bt))
        | _, _ ->
           let@ (ls',it) = infer loc local it in
           if LS.equal ls ls' then
             return it
           else
             let (context, it) = Explain.index_terms names local (context, it) in
             fail loc (Illtyped_it {context; it; has = ls'; expected = ls})

      and infer_list_type : 'bt. Loc.t -> L.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc local it ->
        let@ (bt,it) = infer loc local it in
        let@ bt = ensure_list_type loc names local context it bt in
        return (bt, it)

      and infer_integer_or_real_type : 'bt. Loc.t -> L.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc local it ->
        let@ (bt,it) = infer loc local it in
        let@ bt = ensure_integer_or_real_type loc names local context it bt in
        return (bt, it)

      and infer_set_type : 'bt. Loc.t -> L.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc local it ->
        let@ (bt, it) = infer loc local it in
        let@ bt = ensure_set_type loc names local context it bt in
        return (bt, it)


      and infer_option_type : 'bt. Loc.t -> L.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc local it ->
        let@ (bt, it) = infer loc local it in
        let@ bt = ensure_option_type loc names local context it bt in
        return (bt, it)
    
      in  

      match ols with
      | Some ls -> 
         let@ it = check loc local ls it in
         return (ls, it)
      | None -> infer loc local it




    let welltyped loc (names : Explain.naming) local ls it = 
      let@ _ = check_or_infer loc names local (Some ls) it in
      return ()


  end


  module WRE = struct

    open Resources.RE

    let welltyped loc (names : Explain.naming) local = 

      let get_predicate_def name = 
        match Global.get_predicate_def G.global name, name with
        | Some def, _ -> return def
        | None, Ctype ct -> fail loc (Missing_ctype_predicate ct)
        | None, Id id -> fail loc (Missing_predicate id)
      in
      
      let ensure_same_argument_number input_output has ~expect =
        if has = expect then return () else 
          match input_output with
          | `Input -> fail loc (Number_input_arguments {has; expect})
          | `Output -> fail loc (Number_input_arguments {has; expect})
      in

      function
      | Point b -> 
         let@ () = WIT.welltyped loc names local BT.Loc b.pointer in
         let@ _ = WIT.check_or_infer loc names local None b.value in
         let@ _ = WIT.check_or_infer loc names local (Some BT.Bool) b.init in
         let@ _ = WIT.check_or_infer loc names local (Some BT.Real) b.permission in
         return ()
      | QPoint b -> 
         let local = L.add_l b.qpointer Loc local in
         let@ _ = WIT.check_or_infer loc names local None b.value in
         let@ _ = WIT.check_or_infer loc names local (Some BT.Bool) b.init in
         let@ _ = WIT.check_or_infer loc names local (Some BT.Real) b.permission in
         return ()
      | Predicate p -> 
         let@ def = get_predicate_def p.name in
         let has_iargs, expect_iargs = List.length p.iargs, List.length def.iargs in
         let has_oargs, expect_oargs = List.length p.oargs, List.length def.oargs in
         let@ () = ensure_same_argument_number `Input has_iargs ~expect:expect_iargs in
         let@ () = ensure_same_argument_number `Output has_oargs ~expect:expect_oargs in
         let@ () = WIT.welltyped loc names local BT.Loc p.pointer in
         let@ () = 
           ListM.iterM (fun (arg, expected_sort) ->
               WIT.welltyped loc names local expected_sort arg
             ) (List.combine (p.iargs @ p.oargs) 
               (List.map snd def.iargs @ List.map snd def.oargs))
         in
         return ()
      | QPredicate p -> 
         let@ () = WIT.welltyped loc names local BT.Loc p.pointer in
         let@ () = WIT.welltyped loc names local BT.Integer p.element_size in
         let@ () = WIT.welltyped loc names local BT.Integer p.istart in
         let@ () = WIT.welltyped loc names local BT.Integer p.iend in
         let@ () = 
           ListM.iterM (fun it ->
               WIT.welltyped loc names local BT.Loc it
             ) p.moved
         in
         let@ def = get_predicate_def p.name in
         let local = L.add_l p.i Integer local in
         let has_iargs, expect_iargs = List.length p.iargs, List.length def.iargs in
         let has_oargs, expect_oargs = List.length p.oargs, List.length def.oargs in
         let@ () = ensure_same_argument_number `Input has_iargs ~expect:expect_iargs in
         let@ () = ensure_same_argument_number `Output has_oargs ~expect:expect_oargs in
         let@ () = 
           ListM.iterM (fun (arg, (_, expected_sort)) ->
               WIT.welltyped loc names local expected_sort arg
             ) (List.combine p.iargs def.iargs)
         in
         let@ () = 
           ListM.iterM (fun (arg, (_, expected_sort)) ->
               WIT.welltyped loc names local expected_sort arg
             ) (List.combine p.oargs def.oargs)
         in
         return ()
  end


  let resource_inputs_outputs_ok loc resource determined = 
    let bound = SymSet.of_list (List.map fst (RE.quantified resource)) in
    let free = IT.free_vars_list (RE.inputs resource) in
    let undetermined = SymSet.diff free (SymSet.union determined bound) in
    let@ () = match SymSet.is_empty undetermined with
      | true -> return ()
      | false ->
         let bad = List.hd (SymSet.elements undetermined) in
         fail loc (Unconstrained_logical_variable bad)
    in
    let@ fixed = 
      ListM.fold_leftM (fun fixed output ->
         let undetermined = 
           SymSet.diff (IT.free_vars output) 
             (SymSet.union determined bound) 
         in
         match SymSet.is_empty undetermined, IT.unifiable output with
         (* if the logical variables in tht outputs are already determined, ok *)
         | true, _ -> return fixed
         (* if the output is an (unresolved) logical variable, then it can be
            resolved by unification *)       
         | false, Some sym -> return (SymSet.add sym fixed)
         (* otherwise, fail *)
         | false, _ ->
            let bad = List.hd (SymSet.elements undetermined) in
            fail loc (Logical_variable_not_good_for_unification bad)
        ) SymSet.empty (RE.outputs resource)
    in
    return fixed

  module WLC = struct
    type t = LogicalConstraints.t

    (* let welltyped_trigger loc names local trigger = 
     *   match trigger with
     *   | LC.T_Term it -> 
     *      let@ (_, bt) = WIT.check_or_infer loc names local None it in
     *      return bt
     *   | LC.T_App (t, t') ->
     *      let@ fbt = welltyped_trigger loc names local t in
     *      let (abt, rbt) = ensure_param_type loca names local (app_ (t, t')) t fbt in *)
         

         

    let welltyped loc names local lc =
      match lc with
      | LC.T it -> 
         WIT.welltyped loc names local BT.Bool it
      | LC.Forall ((s,bt), trigger, it) ->
         let local = L.add_l s bt local in
         let@ () = WIT.welltyped loc names local BT.Bool it in
         match trigger with
         | None -> return ()
         | Some trigger -> 
            (* let@ _ = WIT.check_or_infer loc names local None trigger in *)
            return ()
  end

  module WLRT = struct

    open LogicalReturnTypes
    type t = LogicalReturnTypes.t

    let rec check loc names local lrt = 
      match lrt with
      | Logical ((s,ls), lrt) -> 
         let lname = Sym.fresh_same s in
         let local = L.add_l lname ls local in
         let lrt = subst_var Subst.{before = s; after = lname} lrt in
         check loc names local lrt
      | Resource (re, lrt) -> 
         let@ () = WRE.welltyped loc names local re in
         let local = L.add_r re local in
         check loc names local lrt
      | Constraint (lc, lrt) ->
         let@ () = WLC.welltyped loc names local lc in
         let local = L.add_c lc local in
         check loc names local lrt
      | I -> 
         return ()

    let wellpolarised loc determined lrt = 
      let open Resultat in
      let rec aux determined undetermined lrt = 
      match lrt with
      | Logical ((s, _), lrt) ->
         aux determined (SymSet.add s undetermined) lrt
      | Resource (re, lrt) ->
         let@ fixed = resource_inputs_outputs_ok loc re determined in
         let determined = SymSet.union determined fixed in
         let undetermined = SymSet.diff undetermined fixed in
         aux determined undetermined lrt
      | Constraint (_, lrt) ->
         aux determined undetermined lrt
      | I ->
         match SymSet.elements undetermined with
         | [] -> return ()
         | s :: _ ->  fail loc (Unconstrained_logical_variable s)
      in
      aux determined SymSet.empty lrt

    let welltyped loc names local lrt = 
      let@ () = check loc names local lrt in
      wellpolarised loc (SymSet.of_list (L.all_names local)) lrt

  end


  module WRT = struct

    open ReturnTypes
    type t = ReturnTypes.t

    let check loc names local rt = 
      match rt with 
      | Computational ((name,bt), lrt) ->
         let name' = Sym.fresh_same name in
         let lname = Sym.fresh () in
         let local = L.add_l lname bt local in
         let local = L.add_a name' (bt, lname) local in
         let lrt = LRT.subst_var Subst.{before = name; after = lname} lrt in
         WLRT.check loc names local lrt

    let wellpolarised loc determined rt = 
      match rt with
      | Computational ((s, _), lrt) ->
         WLRT.wellpolarised loc (SymSet.add s determined) lrt

    let welltyped loc names local at = 
      let@ () = check loc names local at in
      wellpolarised loc (SymSet.of_list (L.all_names local)) at


  end



  module WFalse = struct
    type t = False.t
    let check _ _ _ _ = return ()
    let wellpolarised _ _ _ = return ()
    let welltyped _ _ _ _ = return ()
  end

  module type WOutputSpec = sig val name_bts : (string * LS.t) list end
  module WOutputDef (Spec : WOutputSpec) = struct
    type t = OutputDef.t
    let check loc names local assignment =
      let name_bts = List.sort (fun (s, _) (s', _) -> String.compare s s') Spec.name_bts in
      let assignment = List.sort (fun (s, _) (s', _) -> String.compare s s') assignment in
      let rec aux name_bts assignment =
        match name_bts, assignment with
        | [], [] -> return ()
        | (name, bt) :: name_bts, (name', it) :: assignment when String.equal name name' ->
           let@ () = WIT.welltyped loc names local bt it in
           aux name_bts assignment
        | (name, _) :: _, _ -> fail loc (Generic !^("missing output argument " ^ name))
        | _, (name, _) :: _ -> fail loc (Generic !^("surplus output argument " ^ name))
      in
      aux name_bts assignment
    let wellpolarised _ _ _ = return ()
    let welltyped loc names local assignment = 
      check loc names local assignment
  end


  module type WI_Sig = sig
    type t
    val check : Loc.t -> Explain.naming -> L.t -> t -> (unit,type_error) m
    val wellpolarised : Loc.t -> SymSet.t -> t -> (unit,type_error) m
    val welltyped : Loc.t -> Explain.naming -> L.t -> t -> (unit,type_error) m
  end



  module WAT (I: ArgumentTypes.I_Sig) (WI: WI_Sig with type t = I.t) = struct

    module T = ArgumentTypes.Make(I)

    type t = T.t

    let rec check loc names local (at : T.t) : (unit, type_error) m = 
      let open Resultat in
      match at with
      | T.Computational ((name,bt), at) ->
         let name' = Sym.fresh_same name in
         let lname = Sym.fresh () in
         let local = L.add_l lname bt local in
         let local = L.add_a name' (bt, lname) local in
         let at = T.subst_var Subst.{before = name; after = lname} at in
         check loc names local at
      | T.Logical ((s,ls), at) -> 
         let lname = Sym.fresh_same s in
         let local = L.add_l lname ls local in
         let at = T.subst_var Subst.{before = s; after = lname} at in
         check loc names local at
      | T.Resource (re, at) -> 
         let@ () = WRE.welltyped loc names local re in
         let local = L.add_r re local in
         check loc names local at
      | T.Constraint (lc, at) ->
         let@ () = WLC.welltyped loc names local lc in
         let local = L.add_c lc local in
         check loc names local at
      | T.I i -> 
         WI.check loc names local i


    let wellpolarised loc determined ft = 
      let open Resultat in
      let rec aux determined undetermined ft = 
      match ft with
      | T.Computational ((s, _), ft) ->
         aux (SymSet.add s determined) undetermined ft
      | T.Logical ((s, _), ft) ->
         aux determined (SymSet.add s undetermined) ft
      | T.Resource (re, ft) ->
         let@ fixed = resource_inputs_outputs_ok loc re determined in
         let determined = SymSet.union determined fixed in
         let undetermined = SymSet.diff undetermined fixed in
         aux determined undetermined ft
      | T.Constraint (_, ft) ->
         aux determined undetermined ft
      | T.I rt ->
         match SymSet.elements undetermined with
         | [] -> WI.wellpolarised loc determined rt
         | s :: _ ->  fail loc (Unconstrained_logical_variable s)
      in
      aux determined SymSet.empty ft

    let welltyped loc names local at = 
      let@ () = check loc names local at in
      wellpolarised loc (SymSet.of_list (L.all_names local)) at

  end


  module WFT = WAT(ReturnTypes)(WRT)
  module WLT = WAT(False)(WFalse)
  module WPackingFT(Spec : WOutputSpec) = WAT(OutputDef)(WOutputDef(Spec))

  module WPD = struct
    
    let welltyped names local pd = 
      let open Predicates in
      let local = L.add_l pd.pointer BT.Loc local in
      let local, names = 
        List.fold_left (fun (local, names) (s, ls) -> 
            let local = L.add_l s ls local in
            let names = match Sym.name s with
              | Some name -> 
                 (s, Ast.Var {label = None; v = name }) :: names
              | None -> names 
            in
            (local, names)
          ) (local, names) pd.iargs
      in
      let module WPackingFT = WPackingFT(struct let name_bts = pd.oargs end)  in
      ListM.iterM (fun (loc, clause) ->
          let@ () = WPackingFT.welltyped pd.loc names local clause in
          let lrt, _ = PackingFT.logical_arguments_and_return clause in
          let local = Binding.bind_logical local lrt  in
          if Solver.provably_inconsistent local 
          then fail loc (Generic !^"this clause makes inconsistent assumptions")
          else return ()
        ) pd.clauses
  end


end
