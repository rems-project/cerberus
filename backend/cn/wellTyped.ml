open Resultat
module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors
module L = Local

open Global
open TE



module Make (G : sig val global : Global.t end) = struct
  module Explain = Explain.Make(G)

  let check_bound loc (names : Explain.naming) local kind s = 
    if L.bound s kind local then return ()
    else fail loc (TE.Unbound_name (Sym s))


  module WIT = struct

    open BaseTypes
    open LogicalSorts
    open IndexTerms
    open Pp

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
      

      let rec infer : 'bt. Loc.t -> 'bt IT.term -> (LogicalSorts.t * IT.t, type_error) m =

        let lit = function
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

        let arith_op = function
          | Add (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Add (t, t'))
          | Sub (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Sub (t, t'))
          | Mul (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Mul (t, t'))
          | Div (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Div (t, t'))
          | Exp (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Exp (t, t'))
          | Rem_t (t,t') ->
             let@ t = check loc Integer t in
             let@ t' = check loc Integer t' in
             return (Integer, Rem_t (t, t'))
          | Rem_f (t,t') ->
             let@ t = check loc Integer t in
             let@ t' = check loc Integer t' in
             return (Integer, Rem_f (t, t'))
          | Min (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Min (t, t'))
          | Max (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (bt, Max (t, t'))
        in

        let cmp_op = function
          | LT (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (BT.Bool, LT (t, t'))
          | GT (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (BT.Bool, GT (t, t'))
          | LE (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (BT.Bool, LE (t, t'))
          | GE (t,t') ->
             let@ (bt, t) = infer_integer_or_real_type loc t in
             let@ t' = check loc bt t' in
             return (BT.Bool, GE (t, t'))
        in

        let bool_op = function
          | And ts ->
             let@ ts = ListM.mapM (check loc Bool) ts in
             return (BT.Bool, And ts)
          | Or ts ->
             let@ ts = ListM.mapM (check loc Bool) ts in
             return (BT.Bool, Or ts)
          | Impl (t,t') ->
             let@ t = check loc Bool t in
             let@ t' = check loc Bool t' in
             return (BT.Bool, Impl (t, t'))
          | Not t ->
             let@ t = check loc Bool t in
             return (BT.Bool, Not t)
          | ITE (t,t',t'') ->
             let@ t = check loc Bool t in
             let@ (ls, t') = infer loc t' in
             let@ t'' = check loc ls t'' in
             return (ls, ITE (t, t', t''))
          | EQ (t,t') ->
             let@ (ls,t) = infer loc t in
             let@ t' = check loc ls t' in
             return (BT.Bool, EQ (t,t')) 
          | NE (t,t') ->
             let@ (ls,t) = infer loc t in
             let@ t' = check loc ls t' in
             return (BT.Bool, NE (t,t'))
        in

        let tuple_op = function
          | Tuple ts ->
             let@ bts_ts = ListM.mapM (infer loc) ts in
             let (bts,ts) = List.split bts_ts in
             return (BT.Tuple bts, Tuple ts)
          | NthTuple (n, t') ->
             let@ (tuple_bt,t') = infer loc t' in
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
        
        let struct_op = function
          | Struct (tag, members) ->
             let@ decl = get_struct_decl tag in
             let decl_members = Global.member_types decl.layout in
             let@ () = 
               let has = List.length members in
               let expect = List.length decl_members in
               if has = expect then return ()
               else fail loc (Number_members {has; expect})
             in
             let@ members = 
               ListM.mapM (fun (member,t) ->
                   let@ bt = get_member_type decl_members member it in
                   let@ t = check loc bt t in
                   return (member, t)
                 ) members
             in
             return (BT.Struct tag, Struct (tag, members))
          | StructMember (tag, t, member) ->
             let@ t = check loc (Struct tag) t in
             let@ decl = get_struct_decl tag in
             let decl_members = Global.member_types decl.layout in
             let@ bt = get_member_type decl_members member t in
             return (bt, StructMember (tag, t, member))
          | StructMemberOffset (tag, t, member) ->
             let@ t = check loc Loc t in
             let@ decl = get_struct_decl tag in
             let decl_members = Global.member_types decl.layout in
             let@ _ = get_member_type decl_members member t in
             return (Loc, StructMemberOffset (tag, t, member))
        in

        let pointer_op = function
          | Null ->
             return (BT.Loc, Null)
          | AddPointer (t, t') ->
             let@ t = check loc Loc t in
             let@ t' = check loc Integer t' in
             return (Loc, AddPointer (t, t'))
          | SubPointer (t, t') ->
             let@ t = check loc Loc t in
             let@ t' = check loc Integer t' in
             return (Loc, SubPointer (t, t'))
          | MulPointer (t, t') ->
             let@ t = check loc Loc t in
             let@ t' = check loc Integer t' in
             return (Loc, MulPointer (t, t'))
          | LTPointer (t, t') ->
             let@ t = check loc Loc t in
             let@ t' = check loc Loc t' in
             return (BT.Bool, LTPointer (t, t'))
          | LEPointer (t, t') ->
             let@ t = check loc Loc t in
             let@ t' = check loc Loc t' in
             return (BT.Bool, LEPointer (t, t'))
          (* | Disjoint ((t,s), (t',s')) ->
           *    let@ t = check loc (Base Loc) t in
           *    let@ t' = check loc (Base Loc) t' in
           *    let@ s = check loc (Base Integer) s in
           *    let@ s' = check loc (Base Integer) s' in
           *    return (Base Bool, Disjoint ((t,s), (t',s'))) *)
          | IntegerToPointerCast t ->
             let@ t = check loc Integer t in
             return (Loc, IntegerToPointerCast t)
          | PointerToIntegerCast t ->
             let@ t = check loc Loc t in
             return (Integer, PointerToIntegerCast t)
        in

        let ct_pred = function
          | AlignedI (t, t') ->
             let@ t = check loc Integer t in
             let@ t' = check loc Loc t' in
             return (BT.Bool, AlignedI (t, t'))
          | Aligned (st, t) ->
             let@ t = check loc Loc t in
             return (BT.Bool, Aligned (st, t))
          | MinInteger it ->
             return (BT.Integer, MinInteger it)
          | MaxInteger it ->
             return (BT.Integer, MaxInteger it)
          | Representable (ct, t) ->
             let@ t = check loc (BT.of_sct ct) t in
             return (BT.Bool, Representable (ct, t))
        in

        let list_op = function
          | Nil -> 
             fail loc (Polymorphic_it context)
          | Cons (t1,t2) ->
             let@ (item_bt, t1) = infer loc t1 in
             let@ t2 = check loc (List item_bt) t2 in
             return (BT.List item_bt, Cons (t1, t2))
          | List [] ->
             fail loc (Polymorphic_it context)
          | List (t :: ts) ->
             let@ (bt, t) = infer loc t in
             let@ ts = ListM.mapM (check loc bt) ts in
             return (BT.List bt, List (t :: ts))
          | Head t ->
             let@ (bt,t) = infer_list_type loc t in
             return (bt, Head t)
          | Tail t ->
             let@ (bt,t) = infer_list_type loc t in
             return (BT.List bt, Tail t)
          | NthList (i, t) ->
             let@ (bt,t) = infer_list_type loc t in
             return (bt, NthList (i, t))
        in

        let set_op = function
          | SetMember (t,t') ->
             let@ (bt, t) = infer loc t in
             let@ t' = check loc (Set bt) t' in
             return (BT.Bool, SetMember (t, t'))
          | SetUnion its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc t in
             let@ ts = ListM.mapM (check loc (Set itembt)) ts in
             return (Set itembt, SetUnion (List1.make (t, ts)))
          | SetIntersection its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc t in
             let@ ts = ListM.mapM (check loc (Set itembt)) ts in
             return (Set itembt, SetIntersection (List1.make (t, ts)))
          | SetDifference (t, t') ->
             let@ (itembt, t)  = infer_set_type loc t in
             let@ t' = check loc (Set itembt) t' in
             return (Set itembt, SetDifference (t, t'))
          | Subset (t, t') ->
             let@ (bt, t) = infer_set_type loc t in
             let@ t' = check loc (Set bt) t' in
             return (BT.Bool, Subset (t,t'))
        in

        let array_op = function
          | ConstArray it ->
             let@ (bt, it) = infer loc it in
             let mbt = BT.Array bt in
             return (mbt, ConstArray it)
          | ArrayGet (it,it') ->
             let@ (bt, it) = infer_array_type loc it in
             let@ it' = check loc Integer it' in
             return (bt, ArrayGet (it, it'))
          | ArraySet (it,it',it'') ->
             let@ (bt, it) = infer_array_type loc it in
             let@ it' = check loc Integer it' in
             let@ it'' = check loc bt it'' in
             return (Array bt, ArraySet (it, it', it''))
          | ArrayEqualOnRange (it,it',it'',it''') ->
             let@ (bt, it) = infer_array_type loc it in
             let@ it' = check loc (Array bt) it' in
             let@ it'' = check loc Integer it'' in
             let@ it''' = check loc Integer it''' in
             return (BT.Bool, ArrayEqualOnRange (it, it', it'', it'''))
        in

        fun loc (IT (it, _)) ->
        match it with
        | Lit it ->
           let@ (bt, it) = lit it in
           return (bt, IT (Lit it, bt))
        | Arith_op it ->
           let@ (bt, it) = arith_op it in
           return (bt, IT (Arith_op it, bt))
        | Cmp_op it ->
           let@ (bt, it) = cmp_op it in
           return (bt, IT (Cmp_op it, bt))
        | Bool_op it ->
           let@ (bt, it) = bool_op it in
           return (bt, IT (Bool_op it, bt))
        | Tuple_op it ->
           let@ (bt, it) = tuple_op it in
           return (bt, IT (Tuple_op it, bt))
        | Struct_op it ->
           let@ (bt, it) = struct_op it in
           return (bt, IT (Struct_op it, bt))
        | Pointer_op it ->
           let@ (bt, it) = pointer_op it  in
           return (bt, IT (Pointer_op it, bt))
        | CT_pred it ->
           let@ (bt, it) = ct_pred it in
           return (bt, IT (CT_pred it, bt))
        | List_op it ->
           let@ (bt, it) = list_op it in
           return (bt, IT (List_op it, bt))
        | Set_op it ->
           let@ (bt, it) = set_op it in
           return (bt, IT (Set_op it, bt))
        | Array_op it ->
           let@ (bt, array_op) = array_op it in
           return (bt, IT (Array_op array_op, bt))


      and check : 'bt. Loc.t -> LS.t -> 'bt IT.term -> (IT.t, type_error) m =
        fun loc ls it ->
        match it, ls with
        | IT (List_op Nil, _), List bt ->
           return (IT (List_op Nil, BT.List bt))
        | _, _ ->
           let@ (ls',it) = infer loc it in
           if LS.equal ls ls' then
             return it
           else
             let (context, it) = Explain.index_terms names local (context, it) in
             fail loc (Illtyped_it {context; it; has = ls'; expected = ls})

      and infer_list_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls,it) = infer loc it in
        let@ bt = match ls with
          | List bt -> return bt
          | ls -> 
             let (context, it) = Explain.index_terms names local (context, it) in
             let err = 
               !^"Illtyped index term" ^^^ context ^^ dot ^^^
                 !^"Expected" ^^^ it ^^^ !^"to have list type" ^^^ 
                   !^"but has type" ^^^ LS.pp ls
             in
             fail loc (Generic err)
        in
        return (bt, it)

      and infer_integer_or_real_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls,it) = infer loc it in
        let@ bt = match ls with
          | Integer -> return Integer
          | Real -> return Real
          | ls -> 
             let (context, it) = Explain.index_terms names local (context, it) in
             let err = 
               !^"Illtyped index term" ^^^ context ^^ dot ^^^
                 !^"Expected" ^^^ it ^^^ !^"to have integer or real type" ^^^ 
                   !^"but has type" ^^^ LS.pp ls
             in
             fail loc (Generic err)
        in
        return (bt, it)


      and infer_set_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls, t) = infer loc it in
        let@ bt = match ls with
          | Set bt -> return bt
          | _ -> 
             let (context, it) = Explain.index_terms names local (context, it) in
             let err = 
               !^"Illtyped index term" ^^^ context ^^ dot ^^^
                 !^"Expected" ^^^ it ^^^ !^"to have set type" ^^ comma ^^^
                   !^"but has type" ^^^ LS.pp ls
             in
             fail loc (Generic err)
        in
        return (bt, t)

      and infer_array_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls, it) = infer loc it in
        let@ bt = match ls with
          | Array bt -> return bt
          | _ -> 
             let (context, it) = Explain.index_terms names local (context, it) in
             let err = 
               !^"Illtyped index term" ^^^ context ^^ dot ^^^
                 !^"Expected" ^^^ it ^^^ !^"to have integer map type" ^^ comma ^^^
                   !^"but has type" ^^^ LS.pp ls
             in
             fail loc (Generic err)

        in
        return (bt, it)
    
      in  

      match ols with
      | Some ls -> 
         let@ it = check loc ls it in
         return (ls, it)
      | None -> infer loc it




    let welltyped loc (names : Explain.naming) local ls it = 
      let@ _ = check_or_infer loc names local (Some ls) it in
      return ()


  end


  module WRE = struct
    open Resources
    type t = Resources.t
    let welltyped loc (names : Explain.naming) local = function
      | Point b -> 
         let@ () = WIT.welltyped loc names local BT.Loc b.pointer in
         let@ _ = WIT.check_or_infer loc names local (Some BT.Real) b.permission in
         begin match b.content with
         | Block _ -> return ()
         | Value v -> 
            (* points is "polymorphic" in the pointee *)
            let@ _ = WIT.check_or_infer loc names local None v in
            return ()
         end
      | IteratedStar b -> 
         let local' = L.add_l b.qpointer Loc local in
         let@ _ = WIT.check_or_infer loc names local' (Some BT.Real) b.permission in
         begin match b.content with
         | Block _ -> return ()
         | Value v -> 
            (* iterated star is "polymorphic" in the pointee *)
            let@ _ = WIT.check_or_infer loc names local' None v in
            return ()
         end
      | Predicate p -> 
         let@ def = match Global.get_predicate_def G.global p.name, p.name with
           | Some def, _ -> return def
           | None, Tag tag -> fail loc (Missing_struct tag)
           | None, Id id -> fail loc (Missing_predicate id)
         in
         let@ () = 
           let has = List.length def.iargs in
           let expect = List.length p.iargs in
           if has = expect then return ()
           else fail loc (Number_arguments {has; expect})
         in
         let@ () = 
           ListM.iterM (fun (arg, expected_sort) ->
               WIT.welltyped loc names local expected_sort arg
             ) (List.combine p.iargs (List.map snd def.iargs))
         in
         let@ () = 
           let has = List.length def.oargs in
           let expect = List.length p.oargs in
           if has = expect then return ()
           else fail loc (Number_arguments {has; expect})
         in
         let@ () = 
           ListM.iterM (fun (arg, expected_sort) ->
               WIT.welltyped loc names local expected_sort arg
             ) (List.combine p.oargs (List.map snd def.oargs))
         in
         let@ _ = 
           ListM.fold_leftM (fun i arg ->
               match arg with
               | IT.IT (Lit (Sym _), _) -> return (i + 1)
               | _ ->
                  let (resource, _) = Explain.resource names local (Predicate p) None in
                  let open Pp in
                  let err = 
                    !^("output argument " ^ string_of_int i ^ " of resource") ^^^ resource ^^^
                      !^"not a symbol"
                  in
                  fail loc (Generic err)
             ) 0 p.oargs
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
         match SymSet.is_empty undetermined, IT.is_sym output with
         (* if the logical variables in tht outputs are already determined, ok *)
         | true, _ -> return fixed
         (* if the output is an (unresolved) logical variable, then it can be
            resolved by unification *)       
         | false, Some (sym, _) -> return (SymSet.add sym fixed)
         (* otherwise, fail *)
         | false, _ ->
            let bad = List.hd (SymSet.elements undetermined) in
            fail loc (Logical_variable_not_good_for_unification bad)
        ) SymSet.empty (RE.outputs resource)
    in
    return fixed

  module WLC = struct
    type t = LogicalConstraints.t
    let welltyped loc names env lc =
      WIT.welltyped loc names env BT.Bool lc
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


  module type WI_Sig = sig
    type t
    val check : Loc.t -> Explain.naming -> (L.t) -> t -> (unit,type_error) m
    val wellpolarised : Loc.t -> SymSet.t -> t -> (unit,type_error) m
    val welltyped : Loc.t -> Explain.naming -> (L.t) -> t -> (unit,type_error) m
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

end
