open Resultat
module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors

open Global
open TE


module Make (G : sig val global : Global.t end) = struct

  module L = Local.Make(G)
  module Explain = Explain.Make(G)

  let check_bound loc (names : Explain.naming) local kind s = 
    match L.kind s local with
    | Some kind' when kind' = kind -> 
       return ()
    | Some kind' -> 
       fail loc (TE.Kind_mismatch {expect = KResource; has = kind'})
    | None ->  
       fail loc (TE.Unbound_name (Sym s))


  module WIT = struct

    open BaseTypes
    open LogicalSorts
    open IndexTerms
    open Pp

    type t = IndexTerms.t

    let check_and_type_annot loc names local ls it = 

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
          | Sym (_, s) ->
             let@ () = check_bound loc names local KLogical s in
             let (Base bt) = L.get_l s local in
             return (Base bt, Sym (bt, s))
          | Num n -> 
             return (Base Integer, Num n)
          | Pointer p -> 
             return (Base Loc, Pointer p)
          | Bool b -> 
             return (Base Bool, Bool b)
          | Unit -> 
             return (Base Unit, Unit)
        in

        let arith_op = function
          | Add (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Add (t, t'))
          | Sub (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Sub (t, t'))
          | Mul (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Mul (t, t'))
          | Div (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Div (t, t'))
          | Exp (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Exp (t, t'))
          | Rem_t (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Rem_t (t, t'))
          | Rem_f (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Rem_f (t, t'))
          | Min (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Min (t, t'))
          | Max (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Integer, Max (t, t'))
        in

        let cmp_op = function
          | LT (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Bool, LT (t, t'))
          | GT (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Bool, GT (t, t'))
          | LE (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Bool, LE (t, t'))
          | GE (t,t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Bool, GE (t, t'))
          | EQ (t,t') ->
             let@ (ls,t) = infer loc t in
             let@ t' = check_aux loc ls t' in
             return (Base Bool, EQ (t,t')) 
          | NE (t,t') ->
             let@ (ls,t) = infer loc t in
             let@ t' = check_aux loc ls t' in
             return (Base Bool, NE (t,t'))
        in

        let bool_op = function
          | And ts ->
             let@ ts = ListM.mapM (check_aux loc (Base Bool)) ts in
             return (Base Bool, And ts)
          | Or ts ->
             let@ ts = ListM.mapM (check_aux loc (Base Bool)) ts in
             return (Base Bool, Or ts)
          | Impl (t,t') ->
             let@ t = check_aux loc (Base Bool) t in
             let@ t' = check_aux loc (Base Bool) t' in
             return (Base Bool, Impl (t, t'))
          | Not t ->
             let@ t = check_aux loc (Base Bool) t in
             return (Base Bool, Not t)
          | ITE (t,t',t'') ->
             let@ t = check_aux loc (Base Bool) t in
             let@ (ls, t') = infer loc t' in
             let@ t'' = check_aux loc (Base Integer) t'' in
             return (ls, ITE (t, t', t''))
        in

        let tuple_op = function
          | Tuple (_, ts) ->
             let@ bts_ts = 
               ListM.mapM (fun it -> 
                   let@ (Base bt, t) = infer loc it in
                   return (bt, t)
                 ) ts 
             in
             let (bts,ts) = List.split bts_ts in
             return (Base (BT.Tuple bts), Tuple (bts, ts))
          | NthTuple (_, n, t') ->
             let@ (ls,t') = infer loc t' in
             let@ tuple_bt, item_bt = match ls with
               | Base (Tuple bts) ->
                  begin match List.nth_opt bts n with
                  | Some t -> return (BT.Tuple bts, t)
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
                        LS.pp ls
                  in
                  fail loc (Generic err)
             in
             return (Base item_bt, NthTuple (tuple_bt, n, t'))
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
                   let@ t = check_aux loc (Base bt) t in
                   return (member, t)
                 ) members
             in
             return (Base (Struct tag), Struct (tag, members))
          | StructMember (tag, t, member) ->
             let@ t = check_aux loc (Base (Struct tag)) t in
             let@ decl = get_struct_decl tag in
             let decl_members = Global.member_types decl.layout in
             let@ bt = get_member_type decl_members member t in
             return (Base bt, StructMember (tag, t, member))
          | StructMemberOffset (tag, t, member) ->
             let@ t = check_aux loc (Base Loc) t in
             let@ decl = get_struct_decl tag in
             let decl_members = Global.member_types decl.layout in
             let@ _ = get_member_type decl_members member t in
             return (Base Loc, StructMemberOffset (tag, t, member))
        in

        let pointer_op = function
          | Null t ->
             let@ t = check_aux loc (Base Loc) t in
             return (Base Bool, Null t)
          | AllocationSize t ->
             let@ t = check_aux loc (Base Loc) t in
             return (Base Integer, AllocationSize t)
          | AddPointer (t, t') ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Loc, AddPointer (t, t'))
          | SubPointer (t, t') ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Loc, SubPointer (t, t'))
          | MulPointer (t, t') ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Integer) t' in
             return (Base Loc, MulPointer (t, t'))
          | LTPointer (t, t') ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Loc) t' in
             return (Base Bool, LTPointer (t, t'))
          | LEPointer (t, t') ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Loc) t' in
             return (Base Bool, LEPointer (t, t'))
          | Disjoint ((t,s), (t',s')) ->
             let@ t = check_aux loc (Base Loc) t in
             let@ t' = check_aux loc (Base Loc) t' in
             let@ s = check_aux loc (Base Integer) s in
             let@ s' = check_aux loc (Base Integer) s' in
             return (Base Bool, Disjoint ((t,s), (t',s')))
          | IntegerToPointerCast t ->
             let@ t = check_aux loc (Base Integer) t in
             return (Base Loc, IntegerToPointerCast t)
          | PointerToIntegerCast t ->
             let@ t = check_aux loc (Base Loc) t in
             return (Base Integer, PointerToIntegerCast t)
        in

        let ct_pred = function
          | AlignedI (t, t') ->
             let@ t = check_aux loc (Base Integer) t in
             let@ t' = check_aux loc (Base Loc) t' in
             return (Base Bool, AlignedI (t, t'))
          | Aligned (st, t) ->
             let@ t = check_aux loc (Base Loc) t in
             return (Base Bool, Aligned (st, t))
          | MinInteger it ->
             return (Base BT.Integer, MinInteger it)
          | MaxInteger it ->
             return (Base BT.Integer, MaxInteger it)
          | Representable (ct, t) ->
             let@ t = check_aux loc (Base (BT.of_sct ct)) t in
             return (Base BT.Bool, Representable (ct, t))
        in

        let list_op = function
          | Nil _ -> 
             fail loc (Polymorphic_it context)
          | Cons (t1,t2) ->
             let@ (Base item_bt, t1) = infer loc t1 in
             let@ t2 = check_aux loc (Base (List item_bt)) t2 in
             return (Base (List item_bt), Cons (t1, t2))
          | List ([],_) ->
             fail loc (Polymorphic_it context)
          | List (t :: ts,_) ->
             let@ (Base bt, t) = infer loc t in
             let@ ts = ListM.mapM (check_aux loc (Base bt)) ts in
             return (Base (List bt), List (t :: ts, bt))
          | Head t ->
             let@ (bt,t) = infer_list_type loc t in
             return (Base bt, Head t)
          | Tail t ->
             let@ (bt,t) = infer_list_type loc t in
             return (Base (List bt), Tail t)
          | NthList (i, t) ->
             let@ (bt,t) = infer_list_type loc t in
             return (Base bt, NthList (i, t))
        in

        let set_op = function
          | SetMember (t,t') ->
             let@ (Base bt, t) = infer loc t in
             let@ t' = check_aux loc (Base (Set bt)) t' in
             return (Base BT.Bool, SetMember (t, t'))
          | SetUnion its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc t in
             let@ ts = ListM.mapM (check_aux loc (Base (Set itembt))) ts in
             return (Base (Set itembt), SetUnion (List1.make (t, ts)))
          | SetIntersection its ->
             let (t, ts) = List1.dest its in
             let@ (itembt, t) = infer_set_type loc t in
             let@ ts = ListM.mapM (check_aux loc (Base (Set itembt))) ts in
             return (Base (Set itembt), SetIntersection (List1.make (t, ts)))
          | SetDifference (t, t') ->
             let@ (itembt, t)  = infer_set_type loc t in
             let@ t' = check_aux loc (Base (Set itembt)) t' in
             return (Base (Set itembt), SetDifference (t, t'))
          | Subset (t, t') ->
             let@ (bt, t) = infer_set_type loc t in
             let@ t' = check_aux loc (Base (Set bt)) t' in
             return (Base Bool, Subset (t,t'))
        in

        let array_op = function
          | ConstArray (it, _) ->
             let@ (Base bt, it) = infer loc it in
             let mbt = BT.Map bt in
             return (Base (mbt), ConstArray (it, mbt))
          | ArrayGet (it,it') ->
             let@ (bt, it) = infer_integer_map_type loc it in
             let@ it' = check_aux loc (Base Integer) it' in
             return (Base bt, ArrayGet (it, it'))
          | ArraySet (it,it',it'') ->
             let@ (bt, it) = infer_integer_map_type loc it in
             let@ it' = check_aux loc (Base Integer) it' in
             let@ it'' = check_aux loc (Base bt) it'' in
             return (Base (Map bt), ArraySet (it, it', it''))
          | ArrayEqualOnRange (it,it',it'',it''') ->
             let@ (bt, it) = infer_integer_map_type loc it in
             let@ it' = check_aux loc (Base (Map bt)) it' in
             let@ it'' = check_aux loc (Base Integer) it'' in
             let@ it''' = check_aux loc (Base Integer) it''' in
             return (Base Bool, ArrayEqualOnRange (it, it', it'', it'''))
          | ArraySelectAfter ((it,it'), it'') ->
             let@ (bt, it) = infer_integer_map_type loc it in
             let@ it' = check_aux loc (Base Integer) it' in
             let@ it'' = check_aux loc (Base (Map bt)) it'' in
             return (Base (Map bt), ArraySelectAfter ((it, it'), it''))
          | ArrayIndexShiftRight (it, it') ->
             let@ (bt, it) = infer_integer_map_type loc it in
             let@ it' = check_aux loc (Base Integer) it' in
             return (Base (Map bt), ArrayIndexShiftRight (it, it'))
        in

        fun loc it ->
        match it with
        | Lit it ->
           let@ (ls, it) = lit it in
           return (ls, Lit it)
        | Arith_op it ->
           let@ (ls, it) = arith_op it in
           return (ls, Arith_op it)
        | Cmp_op it ->
           let@ (ls, it) = cmp_op it in
           return (ls, Cmp_op it)
        | Bool_op it ->
           let@ (ls, it) = bool_op it in
           return (ls, Bool_op it)
        | Tuple_op it ->
           let@ (ls, it) = tuple_op it in
           return (ls, Tuple_op it)
        | Pointer_op it ->
           let@ (ls, it) = pointer_op it  in
           return (ls, Pointer_op it)
        | CT_pred it ->
           let@ (ls, it) = ct_pred it in
           return (ls, CT_pred it)
        | List_op it ->
           let@ (ls, it) = list_op it in
           return (ls, List_op it)
        | Set_op it ->
           let@ (ls, it) = set_op it in
           return (ls, Set_op it)
        | Array_op it ->
           let@ (ls, array_op) = array_op it in
           return (ls, Array_op array_op)
    
      and check_aux : 'bt. Loc.t -> LS.t -> 'bt IT.term -> (IT.t, type_error) m =
        fun loc ls it ->
        match it, ls with
        | List_op (Nil _), Base (List bt) ->
           return (List_op (Nil bt))
        | _, _ ->
           let@ (ls',it) = infer loc it in
           if LS.equal ls ls' then
             let (Base bt) = ls in
             return it
           else
             let (context, it) = Explain.index_terms names local (context, it) in
             fail loc (Illtyped_it {context; it; has = ls'; expected = ls})

      and infer_list_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls,it) = infer loc it in
        let@ bt = match ls with
          | Base (List bt) -> return bt
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


      and infer_set_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls, t) = infer loc it in
        let@ bt = match ls with
          | Base (Set bt) -> return bt
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

      and infer_integer_map_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
        fun loc it ->
        let@ (ls, it) = infer loc it in
        let@ bt = match ls with
          | Base (Map bt) -> return bt
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
      check_aux loc ls it




    let welltyped loc (names : Explain.naming) local ls it = 
      let@ _ = check_and_type_annot loc names local ls it in
      return ()


  end


  module WRE = struct
    open Resources
    type t = Resources.t
    let welltyped loc (names : Explain.naming) local = function
      | Point b -> 
         let@ () = WIT.welltyped loc names local (LS.Base BT.Loc) b.pointer in
         begin match b.content with
         | Block _ -> return ()
         | Value v -> 
            (* points is "polymorphic" in the pointee *)
            check_bound loc names local KLogical v
         end
      | Region r -> 
         let@ () = WIT.welltyped loc names local (LS.Base BT.Loc) r.pointer in
         WIT.welltyped loc names local (LS.Base BT.Integer) r.size
      | Array a -> 
         let@ () = WIT.welltyped loc names local (LS.Base BT.Loc) a.pointer in
         let@ () = WIT.welltyped loc names local (LS.Base BT.Integer) a.length in
         (* array is "polymorphic" in the content type *)
         let@ () = check_bound loc names local KLogical a.content in
         let content_t = L.get_l a.content local in
         begin match content_t with
         | Base (Map _) -> return ()
         | _ ->
            let err = 
              let open Pp in
              !^"Array content argument not a map:" ^^^ LS.pp content_t in
            fail loc (Generic err)
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
               let@ () = check_bound loc names local KLogical arg in
               let has_sort = L.get_l arg local in
               if LS.equal has_sort expected_sort then return ()
               else fail loc (Mismatch { has = has_sort; expect = expected_sort; })
             ) (List.combine p.oargs (List.map snd def.oargs))
         in
         return ()
  end


  module WLC = struct
    open LogicalConstraints
    type t = LogicalConstraints.t
    let welltyped loc names env = function
      | LC it -> WIT.welltyped loc names env (LS.Base BT.Bool) it
  end

  module WLRT = struct

    open LogicalReturnTypes
    type t = LogicalReturnTypes.t

    let rec welltyped loc names local lrt = 
      match lrt with
      | Logical ((s,ls), lrt) -> 
         let lname = Sym.fresh_same s in
         let local = L.add_l lname ls local in
         let lrt = subst_var Subst.{before = s; after = lname} lrt in
         welltyped loc names local lrt
      | Resource (re, lrt) -> 
         let@ () = WRE.welltyped loc names local re in
         let local = L.add_ur re local in
         welltyped loc names local lrt
      | Constraint (lc, lrt) ->
         let@ () = WLC.welltyped loc names local lc in
         let local = L.add_uc lc local in
         welltyped loc names local lrt
      | I -> 
         return ()

  end


  module WRT = struct

    open ReturnTypes
    type t = ReturnTypes.t

    let welltyped loc names local rt = 
      match rt with 
      | Computational ((name,bt), lrt) ->
         let name' = Sym.fresh_same name in
         let lname = Sym.fresh () in
         let local = L.add_l lname (LS.Base bt) local in
         let local = L.add_a name' (bt, lname) local in
         let lrt = LRT.subst_var Subst.{before = name; after = lname} lrt in
         WLRT.welltyped loc names local lrt

  end



  module WFalse = struct
    type t = False.t
    let welltyped _ _ _ _ = return ()
  end


  module type WI_Sig = sig
    type t
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
         let local = L.add_l lname (LS.Base bt) local in
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
         let local = L.add_ur re local in
         check loc names local at
      | T.Constraint (lc, at) ->
         let@ () = WLC.welltyped loc names local lc in
         let local = L.add_uc lc local in
         check loc names local at
      | T.I i -> 
         WI.welltyped loc names local i


    let wellpolarised loc determined ft = 
      let open Resultat in
      let rec aux determined undetermined ft = 
      match ft with
      | T.Computational ((s, _), ft) ->
         aux (SymSet.add s determined) undetermined ft
      | T.Logical ((s, _), ft) ->
         aux determined (SymSet.add s undetermined) ft
      | T.Resource (re, ft) ->
         begin match SymSet.elements (SymSet.diff (RE.input re) determined) with
         | [] ->
            let fixed = RE.output re in
            let determined = SymSet.union determined fixed in
            let undetermined = SymSet.diff undetermined fixed in
            aux determined undetermined ft
         | s :: _ -> 
            fail loc (Unconstrained_logical_variable s)
         end
      | T.Constraint (_, ft) ->
         aux determined undetermined ft
      | T.I _ ->
         match SymSet.elements undetermined with
         | [] -> return ()
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
