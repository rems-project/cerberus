module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors
module RE = Resources.RE
module AT = ArgumentTypes

open Global
open TE
open Pp
open Locations


open Typing
open Effectful.Make(Typing)


let check_consistency = ref true

module WIT = struct


  let check_bound_l loc s = 
    let@ is_bound = bound_l s in
    if is_bound then return ()
    else fail (fun _ -> {loc; msg = TE.Unknown_variable s})


  let illtyped_index_term (loc: loc) context it has expected ctxt =
    {loc = loc; msg = TypeErrors.Illtyped_it {context; it; has; expected; ctxt}}


  let ensure_integer_or_real_type (loc : loc) context it = 
    let open BT in
    match IT.bt it with
    | (Integer | Real) -> return ()
    | _ -> 
       let expect = "integer or real type" in
       fail (illtyped_index_term loc context it (IT.bt it) expect)

  let ensure_set_type loc context it = 
    let open BT in
    match IT.bt it with
    | Set bt -> return bt
    | _ -> fail (illtyped_index_term loc context it (IT.bt it) "set type")

  (* let ensure_option_type loc context it =  *)
  (*   let open BT in *)
  (*   match IT.bt it with *)
  (*   | Option bt -> return bt *)
  (*   | _ -> fail (illtyped_index_term loc context it (IT.bt it) "option type") *)

  let ensure_list_type loc context it = 
    let open BT in
    match IT.bt it with
    | List bt -> return bt
    | _ -> fail (illtyped_index_term loc context it (IT.bt it) "list type")

  let ensure_map_type loc context it = 
    let open BT in
    match IT.bt it with
    | Map (abt, rbt) -> return (abt, rbt)
    | _ -> fail (illtyped_index_term loc context it (IT.bt it) "map/array type")

  let get_struct_decl loc tag = 
    let@ global = get_global () in
    match SymMap.find_opt tag global.struct_decls with
    | Some decl -> return decl
    | None -> fail (fun _ -> {loc; msg = Unknown_struct tag})

  let ensure_same_argument_number loc input_output has ~expect =
    if has = expect then return () else 
      match input_output with
      | `General -> fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
      | `Input -> fail (fun _ -> {loc; msg = Number_input_arguments {has; expect}})
      | `Output -> fail (fun _ -> {loc; msg = Number_output_arguments {has; expect}})

  open BaseTypes
  open LogicalSorts
  open IndexTerms

  type t = IndexTerms.t


  let rec infer : 'bt. Loc.t -> context:(BT.t IT.term) -> 'bt IT.term -> (IT.t, type_error) m =
      fun loc ~context (IT (it, _)) ->
      match it with
      | Lit lit ->
         let@ (bt, lit) = match lit with
           | Sym s ->
              let@ () = check_bound_l loc s in
              let@ bt = get_l s in
              return (bt, Sym s)
           | Z z -> 
              return (Integer, Z z)
           | Q q -> 
              return (Real, Q q)
           | Pointer p -> 
              return (Loc, Pointer p)
           | Bool b -> 
              return (BT.Bool, Bool b)
           | Unit -> 
              return (BT.Unit, Unit)
           | Default bt -> 
              return (bt, Default bt)
           | Null ->
              return (BT.Loc, Null)
         in
         return (IT (Lit lit, bt))
      | Arith_op arith_op ->
         begin match arith_op with
         | Add (t,t') ->
            let@ t = infer loc ~context t in
            let@ () = ensure_integer_or_real_type loc context t in
            let@ t' = check loc ~context (IT.bt t) t' in
            return (IT (Arith_op (Add (t, t')), IT.bt t))
         | Sub (t,t') ->
            let@ t = infer loc ~context t in
            let@ () = ensure_integer_or_real_type loc context t in
            let@ t' = check loc ~context (IT.bt t) t' in
            return (IT (Arith_op (Sub (t, t')), IT.bt t))
         | Mul (t,t') ->
            let@ t = infer loc ~context t in
            let@ () = ensure_integer_or_real_type loc context t in
            let@ t' = check loc ~context (IT.bt t) t' in
            let@ () = 
              if Option.is_some (is_lit t) || Option.is_some (is_lit t') then return () else
                let hint = "Only multiplication by constants is allowed" in
                fail (fun ctxt -> {loc; msg = NIA {context; it = IT.mul_ (t, t'); ctxt; hint}})
            in
            return (IT (Arith_op (Mul (t, t')), IT.bt t))
         | Div (t,t') ->
            let@ t = infer loc ~context t in
            let@ () = ensure_integer_or_real_type loc context t in
            let@ t' = check loc ~context (IT.bt t) t' in
            let@ () = 
              if Option.is_some (is_lit t') then return () else 
                let hint = "Only division by constants is allowed" in
                fail (fun ctxt -> {loc; msg = NIA {context; it = div_ (t, t'); ctxt; hint}})
            in
            return (IT (Arith_op (Div (t, t')), IT.bt t))
         | Exp (t,t') ->
            let@ t = infer loc ~context t in
            let@ () = ensure_integer_or_real_type loc context t in
            let@ t' = check loc ~context (IT.bt t) t' in
            begin match is_z t, is_z t' with
            | Some z, Some z' -> 
               if Z.lt z' Z.zero then
                 fail (fun ctxt -> {loc; msg = NegativeExponent {context; it = exp_ (t, t'); ctxt}})
               else if Z.fits_int32 z' then
                 return (z_ (Z.pow z (Z.to_int z')))
               else 
                 fail (fun ctxt -> {loc; msg = TooBigExponent {context; it = exp_ (t, t'); ctxt}})
            | _ ->
               let hint = "Only exponentiation of two constants is allowed" in
               fail (fun ctxt -> {loc; msg = NIA {context; it = exp_ (t, t'); ctxt; hint}})
            end
           | Rem (t,t') ->
              let@ t = check loc ~context Integer t in
              let@ t' = check loc ~context Integer t' in
              let@ () = 
                if Option.is_some (is_lit t') then return () else 
                  let hint = "Only division by constants is allowed" in
                  fail (fun ctxt -> {loc; msg = NIA {context; it = rem_ (t, t'); ctxt; hint}})
              in
              return (IT (Arith_op (Rem (t, t')), Integer))
           | Mod (t,t') ->
              let@ t = check loc ~context Integer t in
              let@ t' = check loc ~context Integer t' in
              let@ () = 
                if Option.is_some (is_lit t') then return () else 
                  let hint = "Only division by constants is allowed" in
                  fail (fun ctxt -> {loc; msg = NIA {context; it = mod_ (t, t'); ctxt; hint}})
              in
              return (IT (Arith_op (Mod (t, t')), Integer))
           | Divisible (t, t') ->
              let@ t = check loc ~context Integer t in
              let@ t' = check loc ~context Integer t' in
              let@ () = 
                if Option.is_some (is_lit t') then return () else 
                  let hint = "Only division by constants is allowed" in
                  fail (fun ctxt -> {loc; msg = NIA {context; it = divisible_ (t, t'); ctxt; hint}})
              in
              return (IT (Arith_op (Divisible (t, t')), BT.Bool))
           | LT (t,t') ->
              let@ t = infer loc ~context t in
              let@ () = ensure_integer_or_real_type loc context t in
              let@ t' = check loc ~context (IT.bt t) t' in
              return (IT (Arith_op (LT (t, t')), BT.Bool))
           | LE (t,t') ->
              let@ t = infer loc ~context t in
              let@ () = ensure_integer_or_real_type loc context t in
              let@ t' = check loc ~context (IT.bt t) t' in
              return (IT (Arith_op (LE (t, t')), BT.Bool))
           | Min (t,t') ->
              let@ t = infer loc ~context t in
              let@ () = ensure_integer_or_real_type loc context t in
              let@ t' = check loc ~context (IT.bt t) t' in
              return (IT (Arith_op (Min (t, t')), IT.bt t))
           | Max (t,t') ->
              let@ t = infer loc ~context t in
              let@ () = ensure_integer_or_real_type loc context t in
              let@ t' = check loc ~context (IT.bt t) t' in
              return (IT (Arith_op (Max (t, t')), IT.bt t))
           | IntToReal t ->
              let@ t = check loc ~context Integer t in
              return (IT (Arith_op (IntToReal t), BT.Real))
           | RealToInt t ->
              let@ t = check loc ~context Real t in
              return (IT (Arith_op (IntToReal t), BT.Integer))
           | XOR (ity, t, t') ->
              let@ t = check loc ~context Integer t in
              let@ t' = check loc ~context Integer t' in
              return (IT (Arith_op (XOR (ity, t, t')), BT.Integer))
         end
      | Bool_op bool_op ->
         let@ (bt, bool_op) = match bool_op with
           | And ts ->
              let@ ts = ListM.mapM (check loc ~context Bool) ts in
              return (BT.Bool, And ts)
           | Or ts ->
              let@ ts = ListM.mapM (check loc ~context Bool) ts in
              return (BT.Bool, Or ts)
           | Impl (t,t') ->
              let@ t = check loc ~context Bool t in
              let@ t' = check loc ~context Bool t' in
              return (BT.Bool, Impl (t, t'))
           | Not t ->
              let@ t = check loc ~context Bool t in
              return (BT.Bool, Not t)
           | ITE (t,t',t'') ->
              let@ t = check loc ~context Bool t in
              let@ t' = infer loc ~context t' in
              let@ t'' = check loc ~context (IT.bt t') t'' in
              return (IT.bt t', ITE (t, t', t''))
           | EQ (t,t') ->
              let@ t = infer loc ~context t in
              let@ t' = check loc ~context (IT.bt t) t' in
              return (BT.Bool, EQ (t,t')) 
           | EachI ((i1, s, i2), t) ->
              pure begin 
                  let@ () = add_l s Integer in
                  let@ t = check loc ~context Bool t in
                  return (BT.Bool, EachI ((i1, s, i2), t))
                end
         in
         return (IT (Bool_op bool_op, bt))
      | Tuple_op tuple_op ->
         let@ (bt, tuple_op) = match tuple_op with
           | Tuple ts ->
              let@ ts = ListM.mapM (infer loc ~context) ts in
              let bts = List.map IT.bt ts in
              return (BT.Tuple bts, Tuple ts)
           | NthTuple (n, t') ->
              let@ t' = infer loc ~context t' in
              let@ item_bt = match IT.bt t' with
                | Tuple bts ->
                   begin match List.nth_opt bts n with
                   | Some t -> return t
                   | None -> 
                      let expected = "tuple with at least " ^ string_of_int n ^ "components" in
                      fail (illtyped_index_term loc context t' (Tuple bts) expected)
                   end
                | has -> 
                   fail (illtyped_index_term loc context t' has "tuple")
              in
              return (item_bt, NthTuple (n, t'))
         in
         return (IT (Tuple_op tuple_op, bt))
      | Struct_op struct_op ->
         let@ (bt, struct_op) = match struct_op with
           | Struct (tag, members) ->
              let@ layout = get_struct_decl loc tag in
              let decl_members = Memory.member_types layout in
              let@ () = 
                let has = List.length members in
                let expect = List.length decl_members in
                if has = expect then return ()
                else fail (fun _ -> {loc; msg = Number_members {has; expect}})
              in
              let@ members = 
                ListM.mapM (fun (member,t) ->
                    let@ bt = match List.assoc_opt Id.equal member decl_members with
                      | Some sct -> return (BT.of_sct sct)
                      | None -> fail (fun _ -> {loc; msg = Unknown_member (tag, member)})
                    in
                    let@ t = check loc ~context bt t in
                    return (member, t)
                  ) members
              in
              return (BT.Struct tag, Struct (tag, members))
           | StructMember (t, member) ->
              let@ t = infer loc ~context t in
              let@ tag = match IT.bt t with
                | Struct tag -> return tag
                | has -> fail (illtyped_index_term loc context t has "struct")
              in
              let@ layout = get_struct_decl loc tag in
              let decl_members = Memory.member_types layout in
              let@ bt = match List.assoc_opt Id.equal member decl_members with
                | Some sct -> return (BT.of_sct sct)
                | None -> 
                   let expected = "struct with member " ^ Id.s member in
                   fail (illtyped_index_term loc context t (Struct tag) expected)
              in
              return (bt, StructMember (t, member))
         in
         return (IT (Struct_op struct_op, bt))
      | Pointer_op pointer_op ->
         let@ (bt, pointer_op) = match pointer_op with 
           | LTPointer (t, t') ->
              let@ t = check loc ~context Loc t in
              let@ t' = check loc ~context Loc t' in
              return (BT.Bool, LTPointer (t, t'))
           | LEPointer (t, t') ->
              let@ t = check loc ~context Loc t in
              let@ t' = check loc ~context Loc t' in
              return (BT.Bool, LEPointer (t, t'))
           | IntegerToPointerCast t ->
              let@ t = check loc ~context Integer t in
              return (Loc, IntegerToPointerCast t)
           | PointerToIntegerCast t ->
              let@ t = check loc ~context Loc t in
              return (Integer, PointerToIntegerCast t)
           | MemberOffset (tag, member) ->
              return (Integer, MemberOffset (tag, member))
           | ArrayOffset (ct, t) ->
              let@ t = check loc ~context Integer t in
              return (Integer, ArrayOffset (ct, t))
         in
         return (IT (Pointer_op pointer_op, bt))
      | CT_pred ct_pred ->
         let@ (bt, ct_pred) = match ct_pred with
           | AlignedI t ->
              let@ t_t = check loc ~context Loc t.t in
              let@ t_align = check loc ~context Integer t.align in
              return (BT.Bool, AlignedI {t = t_t; align=t_align})
           | Aligned (t, ct) ->
              let@ t = check loc ~context Loc t in
              return (BT.Bool, Aligned (t, ct))
           | Representable (ct, t) ->
              let@ t = check loc ~context (BT.of_sct ct) t in
              return (BT.Bool, Representable (ct, t))
           | Good (ct, t) ->
              let@ t = check loc ~context (BT.of_sct ct) t in
              return (BT.Bool, Good (ct, t))
         in
         return (IT (CT_pred ct_pred, bt))
      | List_op list_op ->
         let@ (bt, list_op) = match list_op with
           | Nil -> 
              fail (fun _ -> {loc; msg = Polymorphic_it context})
           | Cons (t1,t2) ->
              let@ t1 = infer loc ~context t1 in
              let@ t2 = check loc ~context (List (IT.bt t1)) t2 in
              return (BT.List (IT.bt t1), Cons (t1, t2))
           | List [] ->
              fail (fun _ -> {loc; msg = Polymorphic_it context})
           | List (t :: ts) ->
              let@ t = infer loc ~context t in
              let@ ts = ListM.mapM (check loc ~context (IT.bt t)) ts in
              return (BT.List (IT.bt t), List (t :: ts))
           | Head t ->
              let@ t = infer loc ~context t in
              let@ bt = ensure_list_type loc context t in
              return (bt, Head t)
           | Tail t ->
              let@ t = infer loc ~context t in
              let@ bt = ensure_list_type loc context t in
              return (BT.List bt, Tail t)
           | NthList (i, t) ->
              let@ t = infer loc ~context t in
              let@ bt = ensure_list_type loc context t in
              return (bt, NthList (i, t))
         in
         return (IT (List_op list_op, bt))
      | Set_op set_op ->
         let@ (bt, set_op) = match set_op with
           | SetMember (t,t') ->
              let@ t = infer loc ~context t in
              let@ t' = check loc ~context (Set (IT.bt t)) t' in
              return (BT.Bool, SetMember (t, t'))
           | SetUnion its ->
              let@ (t, ts) = match its with
                | t :: ts -> return (t, ts)
                | _ -> fail (fun _ -> {loc; msg = Polymorphic_it context})
              in
              let@ t = infer loc ~context t in
              let@ itembt = ensure_set_type loc context t in
              let@ ts = ListM.mapM (check loc ~context (Set itembt)) ts in
              return (BT.Set itembt, SetUnion (t :: ts))
           | SetIntersection its ->
              let@ (t, ts) = match its with
                | t :: ts -> return (t, ts)
                | _ -> fail (fun _ -> {loc; msg = Polymorphic_it context})
              in
              let@ t = infer loc ~context t in
              let@ itembt = ensure_set_type loc context t in
              let@ ts = ListM.mapM (check loc ~context (Set itembt)) ts in
              return (BT.Set itembt, SetIntersection (t :: ts))
           | SetDifference (t, t') ->
              let@ t  = infer loc ~context t in
              let@ itembt = ensure_set_type loc context t in
              let@ t' = check loc ~context (Set itembt) t' in
              return (BT.Set itembt, SetDifference (t, t'))
           | Subset (t, t') ->
              let@ t = infer loc ~context t in
              let@ itembt = ensure_set_type loc context t in
              let@ t' = check loc ~context (Set itembt) t' in
              return (BT.Bool, Subset (t,t'))
         in
         return (IT (Set_op set_op, bt))
      | Map_op map_op -> 
         let@ (bt, map_op) = match map_op with
           | Const (index_bt, t) ->
              let@ t = infer loc ~context t in
              return (BT.Map (index_bt, IT.bt t), Const (index_bt, t))
           | Set (t1, t2, t3) ->
              let@ t1 = infer loc ~context t1 in
              let@ (abt, rbt) = ensure_map_type loc context t1 in
              let@ t2 = check loc ~context abt t2 in
              let@ t3 = check loc ~context rbt t3 in
              return (IT.bt t1, Set (t1, t2, t3))
           | Get (t, arg) -> 
              let@ t = infer loc ~context t in
              let@ (abt, bt) = ensure_map_type loc context t in
              let@ arg = check loc ~context abt arg in
              return (bt, Get (t, arg))
           | Def ((s, abt), body) ->
              pure begin
                  let@ () = add_l s abt in
                  let@ body = infer loc ~context body in
                  return (Map (abt, IT.bt body), Def ((s, abt), body))
                end
         in
         return (IT (Map_op map_op, bt))
      | Pred (name, args) ->
         let@ def = Typing.get_logical_predicate_def loc name in
         let has_args, expect_args = List.length args, List.length def.args in
         let@ () = ensure_same_argument_number loc `General has_args ~expect:expect_args in
         let@ args = 
           ListM.map2M (fun has_arg (_, def_arg_bt) ->
               check loc ~context def_arg_bt has_arg
             ) args def.args
         in
         return (IT (Pred (name, args), def.return_bt))
         
         


    and check : 'bt. Loc.t -> context:(BT.t IT.term) -> LS.t -> 'bt IT.term -> (IT.t, type_error) m =
      fun loc ~context ls it ->
      match it, ls with
      | IT (List_op Nil, _), List bt ->
         return (IT (List_op Nil, BT.List bt))
      | _, _ ->
         let@ it = infer loc ~context it in
         if LS.equal ls (IT.bt it) then
           return it
         else
           let expected = Pp.plain (LS.pp ls) in
           fail (illtyped_index_term loc context it (IT.bt it) expected)

  let infer loc it = infer loc ~context:it it
  let check loc ls it = check loc ~context:it ls it



end





let unconstrained_lvar loc infos lvar = 
  let (loc, odescr) = SymMap.find lvar infos in
  fail (fun _ -> {loc; msg = Unconstrained_logical_variable (lvar, odescr)})




module WRE = struct

  open Resources.RE

  let welltyped loc resource = 
    begin match resource with
    | Point b -> 
       let@ _ = WIT.check loc BT.Loc b.pointer in
       let@ _ = WIT.check loc BT.Bool b.permission in
       let@ _ = WIT.check loc (BT.of_sct b.ct) b.value in
       let@ _ = WIT.check loc BT.Bool b.init in
       return ()
    | QPoint b -> 
       let@ _ = WIT.check loc BT.Loc b.pointer in
       pure begin 
           let@ () = add_l b.q Integer in
           let@ _ = WIT.check loc BT.Bool b.permission in
           let@ _ = WIT.check loc (BT.of_sct b.ct) b.value in
           let@ _ = WIT.check loc BT.Bool b.init in
           return ()
         end
    | Predicate p -> 
       let@ def = Typing.get_resource_predicate_def loc p.name in
       let@ _ = WIT.check loc BT.Loc p.pointer in
       let@ _ = WIT.check loc BT.Bool p.permission in
       let has_iargs, expect_iargs = List.length p.iargs, List.length def.iargs in
       let has_oargs, expect_oargs = List.length p.oargs, List.length def.oargs in
       (* +1 because of pointer argument *)
       let@ () = WIT.ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs) in
       let@ () = WIT.ensure_same_argument_number loc `Output has_oargs ~expect:expect_oargs in
       let@ _ = 
         ListM.mapM (fun (arg, expected_sort) ->
             WIT.check loc expected_sort arg
           ) (List.combine (p.iargs @ p.oargs) 
             (List.map snd def.iargs @ List.map snd def.oargs))
       in
       return ()
    | QPredicate p -> 
       let@ def = Typing.get_resource_predicate_def loc p.name in
       let@ _ = WIT.check loc BT.Loc p.pointer in
       pure begin 
           let@ () = add_l p.q Integer in
           let@ _ = WIT.check loc BT.Bool p.permission in
           let has_iargs, expect_iargs = List.length p.iargs, List.length def.iargs in
           let has_oargs, expect_oargs = List.length p.oargs, List.length def.oargs in
           (* +1 because of pointer argument *)
           let@ () = WIT.ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs) in
           let@ () = WIT.ensure_same_argument_number loc `Output has_oargs ~expect:expect_oargs in
           let@ _ = 
             ListM.mapM (fun (arg, expected_sort) ->
                 WIT.check loc expected_sort arg
               ) (List.combine (p.iargs @ p.oargs) 
                 (List.map snd def.iargs @ List.map snd def.oargs))
           in
           return ()
         end
    end

  let mode_check loc ~infos ~undetermined resource = 
    (* check inputs *)
    let undetermined_input_vars = SymSet.inter (RE.free_input_vars resource) undetermined in
    let@ () = match SymSet.choose_opt undetermined_input_vars with
      | None -> return ()
      | Some lvar -> unconstrained_lvar loc infos lvar 
    in
    (* check outputs *)
    (* NOTE: The following line is ok because the quantifier is bound
       in all the outputs. In principle, this is not necessary,
       however. *)
    let undetermined = SymSet.diff undetermined (RE.bound resource) in
    let@ fixed = 
      ListM.mapM (fun output ->
          let undetermined_output = SymSet.inter undetermined (IT.free_vars output) in
          if SymSet.is_empty undetermined_output then 
            (* If the logical variables in the output term are already
               determined, ok. *)
            return SymSet.empty
          else
            (* otherwise, check that there is a single unification
               variable that can be resolved by unification *)
            match RE.quantifier resource, output with
            | None, 
              IT (Lit (Sym s), _) -> 
               return (SymSet.singleton s)
            | Some (q, _), 
              IT (Map_op (Get (IT (Lit (Sym map_s), _), 
                               IT (Lit (Sym arg_s), _))), _)
                 when Sym.equal arg_s q ->
               return (SymSet.singleton map_s)
            (* otherwise, fail *)
            | _ ->
               let u = SymSet.choose undetermined_output in
               let (loc, odescr) = SymMap.find u infos in
               fail (fun _ -> {loc; msg = Logical_variable_not_good_for_unification (u, odescr)})
        ) (RE.outputs resource)
    in
    return (List.fold_left SymSet.union SymSet.empty fixed)

end

module WLC = struct
  type t = LogicalConstraints.t

  let welltyped loc lc =
    match lc with
    | LC.T it -> 
       let@ _ = WIT.check loc BT.Bool it in
       return ()
    | LC.Forall ((s,bt), it) ->
       pure begin
           let@ () = add_l s bt in
           let@ _ = WIT.check loc BT.Bool it in
           return ()
       end

end

module WLRT = struct

  module LRT = LogicalReturnTypes
  open LRT
  type t = LogicalReturnTypes.t

  let welltyped loc lrt = 
    let rec aux = function
      | Logical ((s,ls), info, lrt) -> 
         let s' = Sym.fresh_same s in
         let@ () = add_l s' ls in
         let lrt = subst (IT.make_subst [(s, IT.sym_ (s', ls))]) lrt in
         aux lrt
      | Define ((s, it), info, lrt) ->
         let@ it = WIT.infer loc it in
         let s' = Sym.fresh_same s in
         let bt = IT.bt it in
         let@ () = add_l s' bt in
         let@ () = add_c (LC.t_ (IT.def_ s' it)) in
         let lrt = subst (IT.make_subst [(s, IT.sym_ (s', bt))]) lrt in
         aux lrt
      | Resource (re, info, lrt) -> 
         let@ () = WRE.welltyped (fst info) re in
         let@ () = add_r None re in
         aux lrt
      | Constraint (lc, info, lrt) ->
         let@ () = WLC.welltyped (fst info) lc in
         let@ () = add_c lc in
         aux lrt
      | I -> 
         return ()
    in
    pure (aux lrt)

  let mode_check loc ~infos lrt = 
    let rec aux ~infos ~undetermined constraints lrt = 
      match lrt with
      | Logical ((s, ls), info, lrt) ->
         let s' = Sym.fresh_same s in
         let lrt = LRT.subst (IT.make_subst [(s, IT.sym_ (s', ls))]) lrt in
         let undetermined = SymSet.add s' undetermined in
         let infos = SymMap.add s' info infos in
         aux ~infos ~undetermined constraints lrt
      | Define ((s, it), info, lrt) ->
         let@ () = match SymSet.choose_opt (SymSet.inter (IT.free_vars it) undetermined) with
           | None -> return ()
           | Some lvar -> unconstrained_lvar loc infos lvar 
         in
         let s' = Sym.fresh_same s in
         let bt = IT.bt it in
         let lrt = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) lrt in
         let infos = SymMap.add s' info infos in
         aux ~infos ~undetermined constraints lrt
      | Resource (re, info, lrt) ->
         let@ fixed = WRE.mode_check (fst info) ~infos ~undetermined re in
         let undetermined = SymSet.diff undetermined fixed in
         aux ~infos ~undetermined constraints lrt
      | Constraint (lc, info, lrt) ->
         aux ~infos ~undetermined ((lc, info) :: constraints) lrt
      | I ->
         let@ () = match SymSet.choose_opt undetermined with
           | Some s -> 
              let (loc, odescr) = SymMap.find s infos in
              fail (fun _ -> {loc; msg = Unconstrained_logical_variable (s, odescr)})
           | None -> return ()
         in
         return ()
    in
    aux ~infos ~undetermined:SymSet.empty [] lrt

  let good loc lrt = 
    let@ () = welltyped loc lrt in
    let@ () = 
      let infos = SymMap.empty in
      mode_check loc ~infos lrt
    in
    return ()

end


module WRT = struct

  include ReturnTypes
  type t = ReturnTypes.t

  let welltyped loc rt = 
    pure begin match rt with 
      | Computational ((name,bt), _info, lrt) ->
         let name' = Sym.fresh_same name in
         let lname = Sym.fresh () in
         let@ () = add_l lname bt in
         let@ () = add_a name' (bt, lname) in
         let lrt = LRT.subst (IT.make_subst [(name, IT.sym_ (lname, bt))]) lrt in
         WLRT.welltyped loc lrt
      end

  let mode_check loc ~infos rt = 
    match rt with
    | Computational ((s, bt), _info, lrt) ->
       let s' = Sym.fresh_same s in
       let lrt = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) lrt in
       WLRT.mode_check loc ~infos lrt


  let good loc rt =
    let@ () = welltyped loc rt in
    let@ () = 
      let infos = SymMap.empty in
      mode_check loc ~infos rt
    in
    return ()

end



module WFalse = struct
  include False
  type t = False.t
  let welltyped _ _ = return ()
  let mode_check _ ~infos:_ _ = return ()
end

module type WOutputSpec = sig val name_bts : (Sym.t * LS.t) list end
module WOutputDef (Spec : WOutputSpec) = struct
  include OutputDef
  type t = OutputDef.t
  let check loc assignment =
    let rec aux name_bts assignment =
      match name_bts, assignment with
      | [], [] -> 
         return ()
      | (name, bt) :: name_bts, {loc; name = name'; value = it} :: assignment 
           when Sym.equal name name' ->
         let@ _ = WIT.check loc bt it in
         aux name_bts assignment
      | (name, _) :: _, _ -> 
         fail (fun _ -> {loc; msg = Generic (!^"expected output argument" ^^^ Sym.pp name)})
      | _, {loc = loc'; name = name'; _} :: _ -> 
         fail (fun _ -> {loc; msg = Generic (!^"unexpected output argument" ^^^ Sym.pp name')})
    in
    aux Spec.name_bts assignment

  let mode_check loc ~infos assignment = 
    return ()

  let welltyped loc assignment = 
    check loc assignment

end


module type WI_Sig = sig

  type t

  val subst : IndexTerms.t Subst.t -> t -> t

  val pp : t -> Pp.document

  val mode_check : 
    Loc.t -> 
    infos:(Loc.info SymMap.t) -> 
    t -> 
    (unit, type_error) m

  val welltyped : 
    Loc.t -> 
    t -> 
    (unit, type_error) m
end




module WAT (WI: WI_Sig) = struct


  type t = WI.t AT.t

  let welltyped kind loc (at : t) : (unit, type_error) m = 
    let rec aux = function
      | AT.Computational ((name,bt), _info, at) ->
         let name' = Sym.fresh_same name in
         let lname = Sym.fresh () in
         let@ () = add_l lname bt in
         let@ () = add_a name' (bt, lname) in
         let at = AT.subst WI.subst (IT.make_subst [(name, IT.sym_ (lname, bt))]) at in
         aux at
      | AT.Logical ((s,ls), _info, at) -> 
         let lname = Sym.fresh_same s in
         let@ () = add_l lname ls in
         let at = AT.subst WI.subst (IT.make_subst [(s, IT.sym_ (lname, ls))]) at in
         aux at
      | AT.Define ((s, it), info, at) ->
         let@ it = WIT.infer loc it in
         let s' = Sym.fresh_same s in
         let bt = IT.bt it in
         let@ () = add_l s' bt in
         let@ () = add_c (LC.t_ (IT.def_ s' it)) in
         let at = AT.subst WI.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) at in
         aux at
      | AT.Resource (re, info, at) -> 
         let@ () = WRE.welltyped (fst info) re in
         let@ () = add_r None re in
         aux at
      | AT.Constraint (lc, info, at) ->
         let@ () = WLC.welltyped (fst info) lc in
         let@ () = add_c lc in
         aux at
      | AT.I i -> 
         let@ provable = provable loc in
         let@ () = 
           if !check_consistency then
             match provable (LC.t_ (IT.bool_ false)) with
             | `True -> fail (fun _ -> {loc; msg = Generic !^("this "^kind^" makes inconsistent assumptions")})
             | `False -> return ()
           else return ()
         in
         let@ () = WI.welltyped loc i in
         return ()
    in
    pure (aux at)


  let mode_check loc ~infos ft = 
    let rec aux ~infos ~undetermined constraints ft = 
      match ft with
      | AT.Computational ((s, bt), _info, ft) ->
         let s' = Sym.fresh_same s in
         let ft = AT.subst WI.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) ft in
         aux ~infos ~undetermined constraints ft
      | Logical ((s, ls), info, ft) ->
         let s' = Sym.fresh_same s in
         let ft = AT.subst WI.subst (IT.make_subst [(s, IT.sym_ (s', ls))]) ft in
         let undetermined = SymSet.add s' undetermined in
         let infos = SymMap.add s' info infos in
         aux ~infos ~undetermined constraints ft
      | AT.Define ((s, it), info, ft) ->
         let@ () = match SymSet.choose_opt (SymSet.inter (IT.free_vars it) undetermined) with
           | None -> return ()
           | Some lvar -> unconstrained_lvar loc infos lvar 
         in
         let s' = Sym.fresh_same s in
         let bt = IT.bt it in
         let ft = AT.subst WI.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) ft in
         let infos = SymMap.add s' info infos in
         aux ~infos ~undetermined constraints ft
      | AT.Resource (re, info, ft) ->
         let@ fixed = WRE.mode_check (fst info) ~infos ~undetermined re in
         let undetermined = SymSet.diff undetermined fixed in
         aux ~infos ~undetermined constraints ft
      | AT.Constraint (lc, info, ft) ->
         let constraints = (lc, info) :: constraints in
         aux ~infos ~undetermined constraints ft
      | AT.I rt ->
         let@ () = match SymSet.choose_opt undetermined with
           | Some s -> 
              let (loc, odescr) = SymMap.find s infos in
              fail (fun _ -> {loc; msg = Unconstrained_logical_variable (s, odescr)})
           | None -> return ()
         in 
         WI.mode_check loc ~infos rt
    in
    aux ~infos ~undetermined:SymSet.empty [] ft


  let good kind loc ft = 
    let () = Debug_ocaml.begin_csv_timing "WAT.good" in
    let () = Debug_ocaml.begin_csv_timing "WAT.welltyped" in
    let@ () = welltyped kind loc ft in
    let () = Debug_ocaml.end_csv_timing "WAT.welltyped" in
    let () = Debug_ocaml.begin_csv_timing "WAT.mode_and_bad_value_check" in
    let@ () = 
      let infos = SymMap.empty in
      mode_check loc ~infos ft 
    in
    let () = Debug_ocaml.end_csv_timing "WAT.mode_and_bad_value_check" in
    let () = Debug_ocaml.end_csv_timing "WAT.good" in
    return ()

end


module WFT = WAT(WRT)
module WLT = WAT(WFalse)
module WPackingFT(Spec : WOutputSpec) = WAT(WOutputDef(Spec))

module WRPD = struct

  let welltyped pd = 
    pure begin
        let open ResourcePredicates in
        let@ () = add_l pd.pointer BT.Loc in
        let@ () = ListM.iterM (fun (s, ls) -> add_l s ls) pd.iargs in
        let module WPackingFT = WPackingFT(struct let name_bts = pd.oargs end)  in
        ListM.iterM (fun {loc; guard; packing_ft} ->
            let@ _ = WIT.check loc BT.Bool guard in
            WPackingFT.welltyped "clause" pd.loc packing_ft
          ) pd.clauses
      end

  let mode_check loc ~infos pd = 
    let open ResourcePredicates in
    let module WPackingFT = WPackingFT(struct let name_bts = pd.oargs end)  in
    ListM.iterM (fun {loc; guard; packing_ft} ->
        WPackingFT.mode_check loc ~infos packing_ft
      ) pd.clauses

  let good pd =
    let () = Debug_ocaml.begin_csv_timing "WPD.good" in
    let@ () = welltyped pd in
    let@ () = 
      let infos = SymMap.empty in
      mode_check pd.loc ~infos pd 
    in
    let () = Debug_ocaml.end_csv_timing "WPD.good" in
    return ()

end



module WLPD = struct

  let welltyped (pd : LogicalPredicates.definition) = 
    pure begin
        let@ () = add_ls pd.args in
        match pd.definition with
        | Def body -> 
           let@ _ = WIT.check pd.loc pd.return_bt body in
           return ()
        | Uninterp -> 
           return ()
      end


  let good pd =
    welltyped pd

end



