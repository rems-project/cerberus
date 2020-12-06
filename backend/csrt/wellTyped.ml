open Resultat
open Environment
module E = Environment
module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors

open TE

let check_bound loc local kind s = 
  match Local.kind s local with
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

  type t = IndexTerms.t

  let check_and_type_annot loc {local;global} ls it = 

    let context = it in

    let rec infer : 'bt. Loc.t -> 'bt IT.term -> (LogicalSorts.t * IT.t, type_error) m =
      fun loc it ->
      (* let () = Pp.print stderr (Local.pp local) in *)
      match it with
      | Num n -> 
         return (Base Integer, Num n)
      | Pointer p -> 
         return (Base Loc, Pointer p)
      | Bool b -> 
         return (Base Bool, Bool b)
      | Unit -> 
         return (Base Unit, Unit)
      | Add (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Add (t, t'))
      | Sub (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Sub (t, t'))
      | Mul (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Mul (t, t'))
      | Div (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Div (t, t'))
      | Exp (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Exp (t, t'))
      | Rem_t (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Rem_t (t, t'))
      | Rem_f (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Rem_f (t, t'))
      | Min (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Min (t, t'))
      | Max (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Integer, Max (t, t'))
      | LT (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Bool, LT (t, t'))
      | GT (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Bool, GT (t, t'))
      | LE (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Bool, LE (t, t'))
      | GE (t,t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Bool, GE (t, t'))
      | EQ (t,t') ->
         let* (ls,t) = infer loc t in
         let* t' = check_aux loc ls t' in
         return (Base Bool, EQ (t,t')) 
      | NE (t,t') ->
         let* (ls,t) = infer loc t in
         let* t' = check_aux loc ls t' in
         return (Base Bool, NE (t,t'))
      | Null t ->
         let* t = check_aux loc (Base Loc) t in
         return (Base Bool, Null t)
      | And ts ->
         let* ts = ListM.mapM (check_aux loc (Base Bool)) ts in
         return (Base Bool, And ts)
      | Or ts ->
         let* ts = ListM.mapM (check_aux loc (Base Bool)) ts in
         return (Base Bool, Or ts)
      | Impl (t,t') ->
         let* t = check_aux loc (Base Bool) t in
         let* t' = check_aux loc (Base Bool) t' in
         return (Base Bool, Impl (t, t'))
      | Not t ->
         let* t = check_aux loc (Base Bool) t in
         return (Base Bool, Not t)
      | ITE (t,t',t'') ->
         let* t = check_aux loc (Base Bool) t in
         let* t' = check_aux loc (Base Integer) t' in
         let* t'' = check_aux loc (Base Integer) t'' in
         return (ls, ITE (t, t', t''))
      | Tuple ts ->
         let* bts_ts = 
           ListM.mapM (fun it -> 
               let* (Base bt, t) = infer loc it in
               return (bt, t)
             ) ts 
         in
         let (bts,ts) = List.split bts_ts in
         return (Base (BT.Tuple bts), Tuple ts)
      | Nth (_, n, t') ->
         let* (ls,t') = infer loc t' in
         let* tuple_bt, item_bt = match ls with
           | Base (Tuple bts) ->
              begin match List.nth_opt bts n with
              | Some t -> return (BT.Tuple bts, t)
              | None -> fail loc (Illtyped_it context)
              end
           | _ -> fail loc (Illtyped_it context)
       in
       return (Base item_bt, Nth (tuple_bt, n, t'))
      | Struct (tag, members) ->
         let* decl = match SymMap.find_opt tag global.struct_decls with
           | Some decl -> return decl
           | None -> fail loc (Missing_struct tag)
         in
         let decl_members = Global.member_types decl.layout in
         let* () = 
           let has = List.length members in
           let expect = List.length decl_members in
           if has = expect then return ()
           else fail loc (Number_members {has; expect})
         in
         let* members = 
           ListM.mapM (fun (member,t) ->
               let* sct = assoc_err loc Id.equal member decl_members (Illtyped_it context) in
               let* t = check_aux loc (Base (BT.of_sct sct)) t in
               return (member, t)
             ) members
         in
         return (Base (Struct tag), Struct (tag, members))
      | StructMember (tag, t, member) ->
         let* t = check_aux loc (Base (Struct tag)) t in
         let* decl = match SymMap.find_opt tag global.struct_decls with
           | Some decl -> return decl
           | None -> fail loc (Missing_struct tag)
         in
         let decl_members = Global.member_types decl.layout in
         let* sct = assoc_err loc Id.equal member decl_members (Illtyped_it context) in
         return (Base (BT.of_sct sct), StructMember (tag, t, member))
      | StructMemberOffset (tag, t, member) ->
         let* t = check_aux loc (Base Loc) t in
         let* decl = match SymMap.find_opt tag global.struct_decls with
           | Some decl -> return decl
           | None -> fail loc (Missing_struct tag)
         in
         let decl_members = Global.member_types decl.layout in
         let* _ = assoc_err loc Id.equal member decl_members (Illtyped_it context) in
         return (Base Loc, StructMemberOffset (tag, t, member))
      | AllocationSize t ->
         let* t = check_aux loc (Base Loc) t in
         return (Base Integer, AllocationSize t)
      | Offset (t, t') ->
         let* t = check_aux loc (Base Loc) t in
         let* t' = check_aux loc (Base Integer) t' in
         return (Base Loc, Offset (t, t'))
      | LocLT (t, t') ->
         let* t = check_aux loc (Base Loc) t in
         let* t' = check_aux loc (Base Loc) t' in
         return (Base Bool, LocLT (t, t'))
      | LocLE (t, t') ->
         let* t = check_aux loc (Base Loc) t in
         let* t' = check_aux loc (Base Loc) t' in
         return (Base Bool, LocLT (t, t'))
      | Disjoint ((t,s), (t',s')) ->
         let* t = check_aux loc (Base Loc) t in
         let* t' = check_aux loc (Base Loc) t' in
         return (Base Bool, Disjoint ((t,s), (t',s')))
      | Nil _ -> 
         fail loc (Polymorphic_it context)
      | Cons (t1,t2) ->
         let* (Base item_bt, t1) = infer loc t1 in
         let* t2 = check_aux loc (Base (List item_bt)) t2 in
         return (Base (List item_bt), Cons (t1, t2))
      | List ([],_) ->
         fail loc (Polymorphic_it context)
      | List (t :: ts,_) ->
         let* (Base bt, t) = infer loc t in
         let* ts = ListM.mapM (check_aux loc (Base bt)) ts in
         return (Base (List bt), List (t :: ts, bt))
      | Head t ->
         let* (ls,t) = infer loc t in
         let* bt = match ls with
           | Base (List bt) -> return (Base bt)
           | _ -> fail loc (Illtyped_it context)
         in
         return (bt, Head t)
      | Tail t ->
         let* (ls, t) = infer loc t in
         let* () = match ls with
           | Base (List bt) -> return ()
           | _ -> fail loc (Illtyped_it context)
         in
         return (ls, Tail t)
      | AlignedI (t, t') ->
         let* t = check_aux loc (Base Integer) t in
         let* t' = check_aux loc (Base Loc) t' in
         return (Base Bool, AlignedI (t, t'))
      | Aligned (st, t) ->
         let* t = check_aux loc (Base Loc) t in
         return (Base Bool, Aligned (st, t))
      | Representable (st, t) ->
         let* t = check_aux loc (Base (ST.to_bt st)) t in
         return (Base BT.Bool, Representable (st, t))
      | MinInteger it ->
         return (Base BT.Integer, MinInteger it)
      | MaxInteger it ->
         return (Base BT.Integer, MaxInteger it)
      | SetMember (t,t') ->
         let* (Base bt, t) = infer loc t in
         let* t' = check_aux loc (Base (Set bt)) t' in
         return (Base BT.Bool, SetMember (t, t'))
      | SetAdd (t,t') ->
         let* (Base bt, t) = infer loc t in
         let* t' = check_aux loc (Base (Set bt)) t' in
         return (Base (Set bt), SetAdd (t, t'))
      | SetRemove (t,t') ->
         let* (Base bt, t) = infer loc t in
         let* t' = check_aux loc (Base (Set bt)) t' in
         return (Base (Set bt), SetRemove (t, t'))
      | SetUnion its
      | SetIntersection its ->
         let (t, ts) = List1.dest its in
         let* (itembt, t) = infer_set_type loc t in
         let* ts = ListM.mapM (check_aux loc (Base (Set itembt))) ts in
         return (Base (Set itembt), SetIntersection (List1.make (t, ts)))
      | SetDifference (t, t') ->
         let* (itembt, t)  = infer_set_type loc t in
         let* t' = check_aux loc (Base (Set itembt)) t' in
         return (Base (Set itembt), SetDifference (t, t'))
      | Subset (t, t') ->
         let* (bt, t) = infer_set_type loc t in
         let* t' = check_aux loc (Base (Set bt)) t' in
         return (Base Bool, Subset (t,t'))
      | S s ->
         let* () = check_bound loc local KLogical s in
         return (Local.get_l s local, S s)

    and check_aux : 'bt. Loc.t -> LS.t -> 'bt IT.term -> (IT.t, type_error) m =
      fun loc ls it ->
      match it, ls with
      | Nil _, Base (List bt) ->
         return (Nil bt)
      | _, _ ->
         let* (ls',it) = infer loc it in
         if not (LS.equal ls ls')
         then fail loc (Illtyped_it context)
         else 
           let (Base bt) = ls in
           return it

    and infer_set_type : 'bt. Loc.t -> 'bt IT.term -> (BT.t * IT.t, type_error) m =
      fun loc it ->
      let* (ls, t) = infer loc it in
      let* bt = match ls with
        | Base (Set bt) -> return bt
        | _ -> fail loc (Illtyped_it context)
      in
      return (bt, t)
    in

    check_aux loc ls it

  let welltyped loc env ls it = 
    let* _ = check_and_type_annot loc env ls it in
    return ()
    

end


module WRE = struct
  open Resources
  type t = Resources.t
  let welltyped loc {local; global} = function
    | Block b -> 
       WIT.welltyped loc {local; global} (LS.Base BT.Loc) b.pointer
    | Points p -> 
       (* points is "polymorphic" in the pointee *)
       let* () = check_bound loc local KLogical p.pointee in
       WIT.welltyped loc {local; global} (LS.Base BT.Loc) p.pointer
    | Predicate p -> 
       let* () = WIT.welltyped loc {local; global} (LS.Base BT.Loc) p.pointer in
       let* def = match Global.get_predicate_def loc global p.name, p.name with
         | Some def, _ -> return def
         | None, Tag tag -> fail loc (Missing_struct tag)
         | None, Id id -> fail loc (Missing_predicate id)
       in
       let* () = 
         let has = List.length def.arguments in
         let expect = List.length p.args in
         if has = expect then return ()
         else fail loc (Number_arguments {has; expect})
       in
       ListM.iterM (fun (arg, expected_sort) ->
           let* () = check_bound loc local KLogical arg in
           let has_sort = Local.get_l arg local in
           if LS.equal has_sort expected_sort then return ()
           else fail loc (Mismatch { has = has_sort; expect = expected_sort; })
         ) (List.combine p.args def.arguments)
end


module WLC = struct
  open LogicalConstraints
  type t = LogicalConstraints.t
  let welltyped loc env = function
    | LC it -> WIT.welltyped loc env (LS.Base BT.Bool) it
end

module WLRT = struct

  open LogicalReturnTypes
  type t = LogicalReturnTypes.t

  let rec welltyped loc {local; global} lrt = 
    match lrt with
    | Logical ((s,ls), lrt) -> 
       let lname = Sym.fresh_same s in
       let local = Local.add_l lname ls local in
       let lrt = subst_var Subst.{before = s; after = lname} lrt in
       welltyped loc {local; global} lrt
    | Resource (re, lrt) -> 
       let* () = WRE.welltyped loc {local; global} re in
       let local = Local.add_ur re local in
       welltyped loc {local; global} lrt
    | Constraint (lc, lrt) ->
       let* () = WLC.welltyped loc {local; global} lc in
       let local = Local.add_uc lc local in
       welltyped loc {local; global} lrt
    | I -> 
       return ()

end


module WRT = struct

  open ReturnTypes
  type t = ReturnTypes.t

  let welltyped loc {local; global} rt = 
    match rt with 
    | Computational ((name,bt), lrt) ->
       let name' = Sym.fresh_same name in
       let lname = Sym.fresh_relative name' (fun s -> s ^ "_l") in
       let local = Local.add_l lname (LS.Base bt) local in
       let local = Local.add_a name' (bt, lname) local in
       let lrt = LRT.subst_var Subst.{before = name; after = lname} lrt in
       WLRT.welltyped loc {local; global} lrt

end



module WFalse = struct
  type t = False.t
  let welltyped _ _ _ = return ()
end


module type WI_Sig = sig
  type t
  val welltyped : Loc.t -> E.t_pure -> t -> (unit,type_error) m
end


module WAT (I: ArgumentTypes.I_Sig) (WI: WI_Sig with type t = I.t) = struct

  module T = ArgumentTypes.Make(I)

  type t = T.t

  let rec check loc {local; global} (at : T.t) : (unit, type_error) m = 
    let open Resultat in
    match at with
    | T.Computational ((name,bt), at) ->
       let name' = Sym.fresh_same name in
       let lname = Sym.fresh_relative name' (fun s -> s ^ "_l") in
       let local = Local.add_l lname (LS.Base bt) local in
       let local = Local.add_a name' (bt, lname) local in
       let at = T.subst_var Subst.{before = name; after = lname} at in
       check loc {local; global} at
    | T.Logical ((s,ls), at) -> 
       let lname = Sym.fresh_same s in
       let local = Local.add_l lname ls local in
       let at = T.subst_var Subst.{before = s; after = lname} at in
       check loc {local; global} at
    | T.Resource (re, at) -> 
       let* () = WRE.welltyped loc {local; global} re in
       let local = Local.add_ur re local in
       check loc {local; global} at
    | T.Constraint (lc, at) ->
       let* () = WLC.welltyped loc {local; global} lc in
       let local = Local.add_uc lc local in
       check loc {local; global} at
    | T.I i -> 
       WI.welltyped loc {local; global} i


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

  let welltyped loc {local; global} at = 
    let* () = check loc {local; global} at in
    wellpolarised loc (SymSet.of_list (Local.all_names local)) at

end


module WFT = WAT(ReturnTypes)(WRT)
module WLT = WAT(False)(WFalse)

