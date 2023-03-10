module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make(Sym)
module TE = TypeErrors
module RE = Resources
module RET = ResourceTypes
module LRT = LogicalReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module Mu = Mucore

open Global
open TE
open Pp
open Locations


open Typing
open Effectful.Make(Typing)





let ensure_logical_sort (loc : loc) ~(expect : LS.t) (has : LS.t) : (unit, type_error) m =
  if LS.equal has expect 
  then return () 
  else fail (fun _ -> {loc; msg = Mismatch {has = BT.pp has; expect = BT.pp expect}})

let ensure_base_type (loc : loc) ~(expect : BT.t) (has : BT.t) : (unit, type_error) m =
  ensure_logical_sort loc ~expect has


(* let check_bound_l loc s =  *)
(*   let@ is_bound = bound_l s in *)
(*   if is_bound then return () *)
(*   else fail (fun _ -> {loc; msg = TE.Unknown_variable s}) *)


let illtyped_index_term (loc: loc) it has expected ctxt =
  {loc = loc; msg = TypeErrors.Illtyped_it {it = IT.pp it; has = BT.pp has; expected; o_ctxt = Some ctxt}}


let ensure_integer_or_real_type (loc : loc) it = 
  let open BT in
  match IT.bt it with
  | (Integer | Real) -> return ()
  | _ -> 
     let expect = "integer or real type" in
     fail (illtyped_index_term loc it (IT.bt it) expect)

let ensure_set_type loc it = 
  let open BT in
  match IT.bt it with
  | Set bt -> return bt
  | _ -> fail (illtyped_index_term loc it (IT.bt it) "set type")

let ensure_list_type loc it = 
  let open BT in
  match IT.bt it with
  | List bt -> return bt
  | _ -> fail (illtyped_index_term loc it (IT.bt it) "list type")

let ensure_map_type loc it = 
  let open BT in
  match IT.bt it with
  | Map (abt, rbt) -> return (abt, rbt)
  | _ -> fail (illtyped_index_term loc it (IT.bt it) "map/array type")

let ensure_same_argument_number loc input_output has ~expect =
  if has = expect then return () else 
    match input_output with
    | `General -> fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
    | `Input -> fail (fun _ -> {loc; msg = Number_input_arguments {has; expect}})
    | `Output -> fail (fun _ -> {loc; msg = Number_output_arguments {has; expect}})


module WBT = struct

  open BT
  let is_bt loc = 
    let rec aux = function
      | Unit -> return ()
      | Bool -> return ()
      | Integer -> return ()
      | Real -> return ()
      | Loc -> return ()
      | Struct tag -> let@ _struct_decl = get_struct_decl loc tag in return ()
      | Datatype tag -> let@ _datatype = get_datatype loc tag in return ()
      | Record members -> ListM.iterM (fun (_, bt) -> aux bt) members
      | Map (abt, rbt) -> ListM.iterM aux [abt; rbt]
      | List bt -> aux bt
      | Tuple bts -> ListM.iterM aux bts
      | Set bt -> aux bt
    in
    fun bt -> aux bt
[@@deriving eq, ord]

end


module WLS = struct

  let is_ls loc ls = WBT.is_bt loc ls

end


module WCT = struct

  open Sctypes

  let is_ct loc = 
    let rec aux = function
      | Void -> return ()
      | Integer _ -> return ()
      | Array (ct, _) -> aux ct
      | Pointer ct -> aux ct
      | Struct tag -> let@ _struct_decl = get_struct_decl loc tag in return ()
      | Function ((_, rct), args, _) -> ListM.iterM aux (rct :: List.map fst args)
    in
    fun ct -> aux ct

end


module WIT = struct


  open BaseTypes
  open IndexTerms

  type t = IndexTerms.t

  let eval = Simplify.IndexTerms.eval

  let rec infer =
      fun loc ((IT (it, _)) as it_) ->
      match it with
      | Lit lit ->
         let@ (bt, lit) = match lit with
           | Sym s ->
              let@ is_a = bound_a s in
              let@ is_l = bound_l s in
              let@ bt = match () with
                | () when is_a -> get_a s
                | () when is_l -> get_l s
                | () -> fail (fun _ -> {loc; msg = TE.Unknown_variable s})
              in
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
              let@ () = WBT.is_bt loc bt in
              return (bt, Default bt)
           | Null ->
              return (BT.Loc, Null)
         in
         return (IT (Lit lit, bt))
      | Arith_op arith_op ->
         begin match arith_op with
         | Add (t,t') ->
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Arith_op (Add (t, t')), IT.bt t))
         | Sub (t,t') ->
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Arith_op (Sub (t, t')), IT.bt t))
         | Mul (t,t') ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            begin match (IT.bt t), (eval simp_ctxt t), (eval simp_ctxt t') with
            | Real, _, _ -> 
               return (IT (Arith_op (Mul (t, t')), IT.bt t))
            | Integer, simp_t, _ when Option.is_some (is_lit simp_t) ->
               return (IT (Arith_op (Mul (simp_t, t')), IT.bt t))
            | Integer, _, simp_t' when Option.is_some (is_lit simp_t') ->
               return (IT (Arith_op (Mul (t, simp_t')), IT.bt t))
            | _ ->
               let hint = "Integer multiplication only allowed when argument is constant" in
               fail (fun ctxt -> {loc; msg = NIA {it = IT.mul_ (t, t'); ctxt; hint}})
            end
         | MulNoSMT (t,t') ->
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Arith_op (MulNoSMT (t, t')), IT.bt t))
         | Div (t,t') ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            begin match IT.bt t, eval simp_ctxt t' with
            | Real, _ ->
               return (IT (Arith_op (Div (t, t')), IT.bt t))
            | Integer, simp_t' when Option.is_some (is_lit simp_t') ->
               return (IT (Arith_op (Div (t, simp_t')), IT.bt t))
            | _ ->
               let hint = "Integer division only allowed when divisor is constant" in
               fail (fun ctxt -> {loc; msg = NIA {it = div_ (t, t'); ctxt; hint}})
            end
         | DivNoSMT (t,t') ->
            let@ t = infer loc t in
            let@ () = ensure_integer_or_real_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Arith_op (DivNoSMT (t, t')), IT.bt t))
         | Exp (t,t') ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = check loc Integer t in
            let@ t' = check loc Integer t' in
            begin match is_z (eval simp_ctxt t), is_z (eval simp_ctxt t') with
            | Some _, Some z' when Z.lt z' Z.zero ->
               fail (fun ctxt -> {loc; msg = NegativeExponent {it = exp_ (t, t'); ctxt}})
            | Some _, Some z' when not (Z.fits_int32 z') ->
               fail (fun ctxt -> {loc; msg = TooBigExponent {it = exp_ (t, t'); ctxt}})
            | Some z, Some z' ->
               return (IT (Arith_op (Exp (z_ z, z_ z')), Integer))
            | _ ->
               let hint = "Only exponentiation of two constants is allowed" in
               fail (fun ctxt -> {loc; msg = NIA {it = exp_ (t, t'); ctxt; hint}})
            end
           | ExpNoSMT (t,t') ->
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              return (exp_no_smt_ (t, t'))
           | Rem (t,t') ->
              let@ simp_ctxt = simp_ctxt () in
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              begin match is_z (eval simp_ctxt t') with
              | None ->
                 let hint = "Only division (rem) by constants is allowed" in
                 fail (fun ctxt -> {loc; msg = NIA {it = rem_ (t, t'); ctxt; hint}})
              | Some z' ->
                 return (IT (Arith_op (Rem (t, z_ z')), Integer))
              end
           | RemNoSMT (t,t') ->
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              return (IT (Arith_op (RemNoSMT (t, t')), Integer))
           | Mod (t,t') ->
              let@ simp_ctxt = simp_ctxt () in
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              begin match is_z (eval simp_ctxt t') with
              | None ->
                 let hint = "Only division (mod) by constants is allowed" in
                 fail (fun ctxt -> {loc; msg = NIA {it = mod_ (t, t'); ctxt; hint}})
              | Some z' ->
                 return (IT (Arith_op (Mod (t, z_ z')), Integer))
              end
           | ModNoSMT (t,t') ->
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              return (IT (Arith_op (ModNoSMT (t, t')), Integer))
           | LT (t,t') ->
              let@ t = infer loc t in
              let@ () = ensure_integer_or_real_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Arith_op (LT (t, t')), BT.Bool))
           | LE (t,t') ->
              let@ t = infer loc t in
              let@ () = ensure_integer_or_real_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Arith_op (LE (t, t')), BT.Bool))
           | Min (t,t') ->
              let@ t = infer loc t in
              let@ () = ensure_integer_or_real_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Arith_op (Min (t, t')), IT.bt t))
           | Max (t,t') ->
              let@ t = infer loc t in
              let@ () = ensure_integer_or_real_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Arith_op (Max (t, t')), IT.bt t))
           | IntToReal t ->
              let@ t = check loc Integer t in
              return (IT (Arith_op (IntToReal t), BT.Real))
           | RealToInt t ->
              let@ t = check loc Real t in
              return (IT (Arith_op (IntToReal t), BT.Integer))
           | XORNoSMT (t, t') ->
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              return (IT (Arith_op (XORNoSMT (t, t')), BT.Integer))
         end
      | Bool_op bool_op ->
         let@ (bt, bool_op) = match bool_op with
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
              let@ t' = infer loc t' in
              let@ t'' = check loc (IT.bt t') t'' in
              return (IT.bt t', ITE (t, t', t''))
           | EQ (t,t') ->
              let@ t = infer loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (BT.Bool, EQ (t,t')) 
           | EachI ((i1, s, i2), t) ->
              (* no need to alpha-rename, because context.ml ensures
                 there's no name clashes *)
              (* let s, t = IT.alpha_rename (s, BT.Integer) t in *)
              pure begin 
                  let@ () = add_l s Integer (loc, lazy (Pp.string "forall-var")) in
                  let@ t = check loc Bool t in
                  return (BT.Bool, EachI ((i1, s, i2), t))
                end
         in
         return (IT (Bool_op bool_op, bt))
      | Tuple_op tuple_op ->
         let@ (bt, tuple_op) = match tuple_op with
           | Tuple ts ->
              let@ ts = ListM.mapM (infer loc) ts in
              let bts = List.map IT.bt ts in
              return (BT.Tuple bts, Tuple ts)
           | NthTuple (n, t') ->
              let@ t' = infer loc t' in
              let@ item_bt = match IT.bt t' with
                | Tuple bts ->
                   begin match List.nth_opt bts n with
                   | Some t -> return t
                   | None -> 
                      let expected = "tuple with at least " ^ string_of_int n ^ "components" in
                      fail (illtyped_index_term loc t' (Tuple bts) expected)
                   end
                | has -> 
                   fail (illtyped_index_term loc t' has "tuple")
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
                    let@ t = check loc bt t in
                    return (member, t)
                  ) members
              in
              return (BT.Struct tag, Struct (tag, members))
           | StructMember (t, member) ->
              let@ t = infer loc t in
              let@ tag = match IT.bt t with
                | Struct tag -> return tag
                | has -> fail (illtyped_index_term loc t has "struct")
              in
              let@ field_ct = get_struct_member_type loc tag member in
              return (BT.of_sct field_ct, StructMember (t, member))
           | StructUpdate ((t, member), v) ->
              let@ t = infer loc t in
              let@ tag = match IT.bt t with
                | Struct tag -> return tag
                | has -> fail (illtyped_index_term loc t has "struct")
              in
              let@ field_ct = get_struct_member_type loc tag member in
              let@ v = check loc (BT.of_sct field_ct) v in
              return (BT.Struct tag, StructUpdate ((t, member), v))
         in
         return (IT (Struct_op struct_op, bt))
      | Record_op record_op ->
         let@ (bt, record_op) = match record_op with
           | Record members ->
              let@ members = 
                ListM.mapM (fun (member,t) ->
                    let@ t = infer loc t in
                    return (member, t)
                  ) members
              in
              let member_types = 
                List.map (fun (member, t) -> (member, IT.bt t)
                  ) members
              in
              return (BT.Record member_types, IT.Record members)
           | RecordMember (t, member) ->
              let@ t = infer loc t in
              let@ members = match IT.bt t with
                | Record members -> return members
                | has -> fail (illtyped_index_term loc t has "struct")
              in
              let@ bt = match List.assoc_opt Sym.equal member members with
                | Some bt -> return bt
                | None -> 
                   let expected = "struct with member " ^ Sym.pp_string member in
                   fail (illtyped_index_term loc t (IT.bt t) expected)
              in
              return (bt, RecordMember (t, member))
           | RecordUpdate ((t, member), v) ->
              let@ t = infer loc t in
              let@ members = match IT.bt t with
                | Record members -> return members
                | has -> fail (illtyped_index_term loc t has "struct")
              in
              let@ bt = match List.assoc_opt Sym.equal member members with
                | Some bt -> return bt
                | None -> 
                   let expected = "struct with member " ^ Sym.pp_string member in
                   fail (illtyped_index_term loc t (IT.bt t) expected)
              in
              let@ v = check loc bt v in
              return (IT.bt t, RecordUpdate ((t, member), v))
         in
         return (IT (Record_op record_op, bt))
      | Datatype_op datatype_op ->
         let@ (bt, datatype_op) = match datatype_op with
           | DatatypeCons (nm, member_rec) ->
             let@ info = get_datatype_constr loc nm in
             let (arg_ty, res_ty) = BT.cons_dom_rng info in
             let@ member_rec = check loc arg_ty member_rec in
             return (res_ty, DatatypeCons (nm, member_rec))
           | DatatypeMember (t, member) ->
             let@ t = infer loc t in
             let@ info = match IT.bt t with
               | Datatype tag -> get_datatype loc tag
               | has -> fail (illtyped_index_term loc t has "record")
             in
             let@ bt = match List.assoc_opt Sym.equal member info.dt_all_params with
               | Some bt -> return bt
               | None ->
                   let expected = "datatype with member " ^ Sym.pp_string member in
                   fail (illtyped_index_term loc t (IT.bt t) expected)
             in
             return (bt, DatatypeMember (t, member))
           | DatatypeIsCons (nm, t) ->
             let@ info = get_datatype_constr loc nm in
             let (_, res_ty) = BT.cons_dom_rng info in
             let@ t = check loc res_ty t in
             return (BT.Bool, DatatypeIsCons (nm, t))
         in
         return (IT (Datatype_op datatype_op, bt))
       | Pointer_op pointer_op ->
         let@ (bt, pointer_op) = match pointer_op with 
           | LTPointer (t, t') ->
              let@ t = check loc Loc t in
              let@ t' = check loc Loc t' in
              return (BT.Bool, LTPointer (t, t'))
           | LEPointer (t, t') ->
              let@ t = check loc Loc t in
              let@ t' = check loc Loc t' in
              return (BT.Bool, LEPointer (t, t'))
           | IntegerToPointerCast t ->
              let@ t = check loc Integer t in
              return (Loc, IntegerToPointerCast t)
           | PointerToIntegerCast t ->
              let@ t = check loc Loc t in
              return (Integer, PointerToIntegerCast t)
           | MemberOffset (tag, member) ->
              let@ layout = get_struct_decl loc tag in
              let decl_members = Memory.member_types layout in
              let@ () = match List.assoc_opt Id.equal member decl_members with
                | Some _ -> return ()
                | None -> fail (fun _ -> {loc; msg = Unknown_member (tag, member)})
              in
              return (Integer, MemberOffset (tag, member))
           | ArrayOffset (ct, t) ->
              let@ () = WCT.is_ct loc ct in
              let@ t = check loc Integer t in
              return (Integer, ArrayOffset (ct, t))
         in
         return (IT (Pointer_op pointer_op, bt))
      | CT_pred ct_pred ->
         let@ (bt, ct_pred) = match ct_pred with
           | AlignedI t ->
              let@ t_t = check loc Loc t.t in
              let@ t_align = check loc Integer t.align in
              return (BT.Bool, AlignedI {t = t_t; align=t_align})
           | Aligned (t, ct) ->
              let@ () = WCT.is_ct loc ct in
              let@ t = check loc Loc t in
              return (BT.Bool, Aligned (t, ct))
           | Representable (ct, t) ->
              let@ () = WCT.is_ct loc ct in
              let@ t = check loc (BT.of_sct ct) t in
              return (BT.Bool, Representable (ct, t))
           | Good (ct, t) ->
              let@ () = WCT.is_ct loc ct in
              let@ t = check loc (BT.of_sct ct) t in
              return (BT.Bool, Good (ct, t))
         in
         return (IT (CT_pred ct_pred, bt))
      | List_op list_op ->
         let@ (bt, list_op) = match list_op with
           | Nil -> 
              fail (fun _ -> {loc; msg = Polymorphic_it it_})
           | Cons (t1,t2) ->
              let@ t1 = infer loc t1 in
              let@ t2 = check loc (List (IT.bt t1)) t2 in
              return (BT.List (IT.bt t1), Cons (t1, t2))
           | List [] ->
              fail (fun _ -> {loc; msg = Polymorphic_it it_})
           | List (t :: ts) ->
              let@ t = infer loc t in
              let@ ts = ListM.mapM (check loc (IT.bt t)) ts in
              return (BT.List (IT.bt t), List (t :: ts))
           | Head t ->
              let@ t = infer loc t in
              let@ bt = ensure_list_type loc t in
              return (bt, Head t)
           | Tail t ->
              let@ t = infer loc t in
              let@ bt = ensure_list_type loc t in
              return (BT.List bt, Tail t)
           | NthList (i, xs, d) ->
              let@ i = check loc Integer i in
              let@ xs = infer loc xs in
              let@ bt = ensure_list_type loc xs in
              let@ d = check loc bt d in
              return (bt, NthList (i, xs, d))
           | ArrayToList (arr, i, len) ->
              let@ i = check loc Integer i in
              let@ len = check loc Integer len in
              let@ arr = infer loc arr in
              let@ (_, bt) = ensure_map_type loc arr in
              return (BT.List bt, ArrayToList (arr, i, len))
         in
         return (IT (List_op list_op, bt))
      | Set_op set_op ->
         let@ (bt, set_op) = match set_op with
           | SetMember (t,t') ->
              let@ t = infer loc t in
              let@ t' = check loc (Set (IT.bt t)) t' in
              return (BT.Bool, SetMember (t, t'))
           | SetUnion its ->
              let@ (t, ts) = match its with
                | t :: ts -> return (t, ts)
                | _ -> fail (fun _ -> {loc; msg = Polymorphic_it it_})
              in
              let@ t = infer loc t in
              let@ itembt = ensure_set_type loc t in
              let@ ts = ListM.mapM (check loc (Set itembt)) ts in
              return (BT.Set itembt, SetUnion (t :: ts))
           | SetIntersection its ->
              let@ (t, ts) = match its with
                | t :: ts -> return (t, ts)
                | _ -> fail (fun _ -> {loc; msg = Polymorphic_it it_})
              in
              let@ t = infer loc t in
              let@ itembt = ensure_set_type loc t in
              let@ ts = ListM.mapM (check loc (Set itembt)) ts in
              return (BT.Set itembt, SetIntersection (t :: ts))
           | SetDifference (t, t') ->
              let@ t  = infer loc t in
              let@ itembt = ensure_set_type loc t in
              let@ t' = check loc (Set itembt) t' in
              return (BT.Set itembt, SetDifference (t, t'))
           | Subset (t, t') ->
              let@ t = infer loc t in
              let@ itembt = ensure_set_type loc t in
              let@ t' = check loc (Set itembt) t' in
              return (BT.Bool, Subset (t,t'))
         in
         return (IT (Set_op set_op, bt))
      | Map_op map_op -> 
         let@ (bt, map_op) = match map_op with
           | Const (index_bt, t) ->
              let@ () = WBT.is_bt loc index_bt in
              let@ t = infer loc t in
              return (BT.Map (index_bt, IT.bt t), Const (index_bt, t))
           | Set (t1, t2, t3) ->
              let@ t1 = infer loc t1 in
              let@ (abt, rbt) = ensure_map_type loc t1 in
              let@ t2 = check loc abt t2 in
              let@ t3 = check loc rbt t3 in
              return (IT.bt t1, Set (t1, t2, t3))
           | Get (t, arg) -> 
              let@ t = infer loc t in
              let@ (abt, bt) = ensure_map_type loc t in
              let@ arg = check loc abt arg in
              return (bt, Get (t, arg))
           | Def ((s, abt), body) ->
              (* no need to alpha-rename, because context.ml ensures
                 there's no name clashes *)
              (* let s, body = IT.alpha_rename (s, abt) body in *)
              let@ () = WBT.is_bt loc abt in
              pure begin
                  let@ () = add_l s abt (loc, lazy (Pp.string "map-def-var")) in
                  let@ body = infer loc body in
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
               check loc def_arg_bt has_arg
             ) args def.args
         in
         return (IT (Pred (name, args), def.return_bt))
         

    and check =
      fun loc ls it ->
      let@ () = WLS.is_ls loc ls in
      match it, ls with
      | IT (List_op Nil, _), List bt ->
         return (IT (List_op Nil, BT.List bt))
      | _, _ ->
         let@ it = infer loc it in
         if LS.equal ls (IT.bt it) then
           return it
         else
           let expected = Pp.plain (LS.pp ls) in
           fail (illtyped_index_term loc it (IT.bt it) expected)



end








module WRET = struct

  open IndexTerms

  let welltyped loc r = 
    let@ spec_iargs = match RET.predicate_name r with
      | Block _ ->
         return (Resources.block_iargs)
      | Owned ct ->
         return (Resources.owned_iargs ct)
      | PName name -> 
         let@ def = Typing.get_resource_predicate_def loc name in
         return def.iargs
    in
    match r with
    | P p -> 
       let@ pointer = WIT.check loc BT.Loc p.pointer in
       let@ permission = WIT.check loc BT.Bool p.permission in
       let has_iargs, expect_iargs = List.length p.iargs, List.length spec_iargs in
       (* +1 because of pointer argument *)
       let@ () = ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs) in
       let@ iargs = ListM.map2M (fun (_, expected) arg -> WIT.check loc expected arg) spec_iargs p.iargs in
       return (RET.P {name = p.name; pointer; permission; iargs})
    | Q p ->
       (* no need to alpha-rename, because context.ml ensures
          there's no name clashes *)
       (* let p = RET.alpha_rename_qpredicate_type p in *)
       let@ pointer = WIT.check loc BT.Loc p.pointer in
       let@ step = WIT.check loc BT.Integer p.step in
       let@ simp_ctxt = simp_ctxt () in
       let@ step = match IT.is_z (Simplify.IndexTerms.eval simp_ctxt step) with
         | Some z -> return (IT.z_ z) 
         | None ->
           let hint = "Only constant iteration steps are allowed" in
           fail (fun ctxt -> {loc; msg = NIA {it = p.step; ctxt; hint}})
       in
       let@ () = match p.name with
         | Owned ct ->
           let sz = Memory.size_of_ctype ct in
           if IT.equal step (IT.int_ sz) then return ()
           else fail (fun _ -> {loc; msg = Generic
             (!^"Iteration step" ^^^ IT.pp p.step ^^^ !^ "different to sizeof" ^^^
                 Sctypes.pp ct ^^^ parens (!^ (Int.to_string sz)))})
         | _ -> return ()
       in
       let@ permission, iargs = 
         pure begin 
             let@ () = add_l p.q Integer (loc, lazy (Pp.string "forall-var")) in
             let@ permission = WIT.check loc BT.Bool p.permission in
             let@ provable = provable loc in
             let only_nonnegative_indices =
               LC.forall_ (p.q, Integer) 
                 (impl_ (p.permission, ge_ (sym_ (p.q, BT.Integer), int_ 0)))
             in
             let@ () = match provable only_nonnegative_indices with
               | `True ->
                  return ()
               | `False ->
                  let model = Solver.model () in
                  let msg = "Iterated resource gives ownership to negative indices." in
                  fail (fun ctxt -> {loc; msg = Generic_with_model {err= !^msg; ctxt; model}})
             in
             let has_iargs, expect_iargs = List.length p.iargs, List.length spec_iargs in
             (* +1 because of pointer argument *)
             let@ () = ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs) in
             let@ iargs = ListM.map2M (fun (_, expected) arg -> WIT.check loc expected arg) spec_iargs p.iargs in
             return (permission, iargs)
           end  
       in
       return (RET.Q {name = p.name; pointer; q = p.q; step; permission; iargs})
end



let oargs_spec loc = function
  | RET.P {name = Block _; _} -> 
     return (Resources.block_oargs)
  | RET.P {name = Owned ct; _} -> 
     return (Resources.owned_oargs ct)
  | RET.P {name = PName pn; _} ->
     let@ def = Typing.get_resource_predicate_def loc pn in
         return (BT.Record def.oargs)
  | RET.Q {name = Block _; _} -> 
     return (Resources.q_block_oargs)
  | RET.Q {name = Owned ct; _} -> 
     return (Resources.q_owned_oargs ct)
  | RET.Q {name = PName pn; _} ->
     let@ def = Typing.get_resource_predicate_def loc pn in
     return (BT.Record (List.map_snd (BT.make_map_bt Integer) def.oargs))






module WRS = struct

  let welltyped loc (resource, bt) = 
    let@ resource = WRET.welltyped loc resource in
    let@ () = WBT.is_bt loc bt in
    let@ oargs_spec = oargs_spec loc resource in
    let@ () = ensure_base_type loc ~expect:oargs_spec bt in
    return (resource, bt)

end




module WLC = struct
  type t = LogicalConstraints.t

  let welltyped loc lc =
    match lc with
    | LC.T it -> 
       let@ it = WIT.check loc BT.Bool it in
       return (LC.T it)
    | LC.Forall ((s, bt), it) ->
       (* no need to alpha-rename, because context.ml ensures
          there's no name clashes *)
       (* let s, it = IT.alpha_rename (s,bt) it in *)
       let@ () = WBT.is_bt loc bt in
       pure begin
           let@ () = add_l s bt (loc, lazy (Pp.string "forall-var")) in
           let@ it = WIT.check loc BT.Bool it in
           return (LC.Forall ((s, bt), it))
       end

end

module WLRT = struct

  module LRT = LogicalReturnTypes
  open LRT
  type t = LogicalReturnTypes.t

  let welltyped loc lrt = 
    let rec aux = function
      | Define ((s, it), info, lrt) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, lrt = LRT.alpha_rename (s, IT.bt it) lrt in *)
         let@ it = WIT.infer loc it in
         let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
         let@ () = add_c (LC.t_ (IT.def_ s it)) in
         let@ lrt = aux lrt in
         return (Define ((s, it), info, lrt))
      | Resource ((s, (re, re_oa_spec)), info, lrt) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, lrt = LRT.alpha_rename (s, re_oa_spec) lrt in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ lrt = aux lrt in
         return (Resource ((s, (re, re_oa_spec)), info, lrt))
      | Constraint (lc, info, lrt) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c lc in
         let@ lrt = aux lrt in
         return (Constraint (lc, info, lrt))
      | I -> 
         return I
    in
    pure (aux lrt)


end


module WRT = struct

  type t = ReturnTypes.t
  let subst = ReturnTypes.subst
  let pp = ReturnTypes.pp

  let welltyped loc rt = 
    pure begin match rt with 
      | RT.Computational ((name,bt), info, lrt) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let name, lrt = LRT.alpha_rename (name, bt) lrt in *)
         let@ () = WBT.is_bt (fst info) bt in
         let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
         let@ lrt = WLRT.welltyped loc lrt in
         return (RT.Computational ((name, bt), info, lrt))
      end

end








module WFalse = struct
  type t = False.t
  let subst = False.subst
  let pp = False.pp
  let welltyped _ False.False = 
    return False.False
end

module WOutputDef = struct
  open OutputDef
  type t = OutputDef.t
  let subst = OutputDef.subst
  let pp = OutputDef.pp
  let welltyped spec_name_bts loc assignment =
    let rec aux name_bts assignment =
      match name_bts, assignment with
      | [], 
        [] -> 
         return []
      | (name, bt) :: name_bts, 
        a :: assignment when Sym.equal name a.name ->
         let@ value = WIT.check a.loc bt a.value in
         let@ assignment = aux name_bts assignment in
         return ({loc = a.loc; name = a.name; value} :: assignment)
      | (name, bt) :: name_bts, 
        {loc; name = name'; value = it} :: _ ->
         fail (fun _ -> {loc; msg = Generic (!^"expected output argument" ^^^ Sym.pp name ^^^ !^"but found" ^^^ Sym.pp name')})
      | (name, _) :: _, 
        _ -> 
         fail (fun _ -> {loc; msg = Generic (!^"expected output argument" ^^^ Sym.pp name)})
      | _, 
        {loc = loc'; name = name'; _} :: _ -> 
         fail (fun _ -> {loc; msg = Generic (!^"unexpected output argument" ^^^ Sym.pp name')})
    in
    aux spec_name_bts assignment

end


module WLAT = struct

  let welltyped i_subst i_welltyped kind loc (at : 'i LAT.t) : ('i LAT.t, type_error) m = 
    let rec aux = function
      | LAT.Define ((s, it), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, IT.bt it) at in *)
         let@ it = WIT.infer loc it in
         let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
         let@ () = add_c (LC.t_ (IT.def_ s it)) in
         let@ at = aux at in
         return (LAT.Define ((s, it), info, at))
      | LAT.Resource ((s, (re, re_oa_spec)), info, at) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, re_oa_spec) at in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ at = aux at in
         return (LAT.Resource ((s, (re, re_oa_spec)), info, at))
      | LAT.Constraint (lc, info, at) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c lc in
         let@ at = aux at in
         return (LAT.Constraint (lc, info, at))
      | LAT.I i -> 
         let@ provable = provable loc in
         let@ () = match provable (LC.t_ (IT.bool_ false)) with
           | `True -> fail (fun _ -> {loc; msg = Generic !^("this "^kind^" makes inconsistent assumptions")})
           | `False -> return ()
         in
         let@ i = i_welltyped loc i in
         return (LAT.I i)
    in
    pure (aux at)



end



module WAT = struct

  let welltyped i_subst i_welltyped kind loc (at : 'i AT.t) : ('i AT.t, type_error) m = 
    let rec aux = function
      | AT.Computational ((name,bt), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let name, at = AT.alpha_rename i_subst (name, bt) at in *)
         let@ () = WBT.is_bt (fst info) bt in
         let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
         let@ at = aux at in
         return (AT.Computational ((name, bt), info, at))
      | AT.L at ->
         let@ at = WLAT.welltyped i_subst i_welltyped kind loc at in
         return (AT.L at)
    in
    pure (aux at)



end










module WFT = struct 
  let welltyped = WAT.welltyped WRT.subst WRT.welltyped
end

module WLT = struct
  let welltyped = WAT.welltyped WFalse.subst WFalse.welltyped
end

(* module WPackingFT(struct let name_bts = pd.oargs end) = 
   WLAT(WOutputDef.welltyped (pd.oargs)) *)








module WLArgs = struct

  let welltyped 
        (i_welltyped : Loc.t -> 'i -> ('i * 'it, type_error) m)
        kind
        loc
        (at : 'i Mu.mu_arguments_l)
      : ('i Mu.mu_arguments_l * 'it LAT.t, type_error) m = 
    let rec aux = function
      | Mu.M_Define ((s, it), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, IT.bt it) at in *)
         let@ it = WIT.infer loc it in
         let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
         let@ () = add_c (LC.t_ (IT.def_ s it)) in
         let@ at, typ = aux at in
         return (Mu.M_Define ((s, it), info, at), 
                 LAT.Define ((s, it), info, typ))
      | Mu.M_Resource ((s, (re, re_oa_spec)), info, at) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, re_oa_spec) at in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ at, typ = aux at in
         return (Mu.M_Resource ((s, (re, re_oa_spec)), info, at),
                 LAT.Resource ((s, (re, re_oa_spec)), info, typ))
      | Mu.M_Constraint (lc, info, at) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c lc in
         let@ at, typ = aux at in
         return (Mu.M_Constraint (lc, info, at),
                 LAT.Constraint (lc, info, typ))
      | Mu.M_I i -> 
         let@ provable = provable loc in
         let@ () = match provable (LC.t_ (IT.bool_ false)) with
           | `True -> fail (fun _ -> {loc; msg = Generic !^("this "^kind^" makes inconsistent assumptions")})
           | `False -> return ()
         in
         let@ i, it = i_welltyped loc i in
         return (Mu.M_I i, 
                 LAT.I it)
    in
    pure (aux at)



end



module WArgs = struct

  let welltyped 
        (i_welltyped : Loc.t -> 'i -> ('i * 'it, type_error) m) 
        kind 
        loc
        (at : 'i Mu.mu_arguments) 
      : ('i Mu.mu_arguments * 'it AT.t, type_error) m = 
    let rec aux = function
      | Mu.M_Computational ((name,bt), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let name, at = AT.alpha_rename i_subst (name, bt) at in *)
         let@ () = WBT.is_bt (fst info) bt in
         let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
         let@ at, typ = aux at in
         return (Mu.M_Computational ((name, bt), info, at),
                 AT.Computational ((name, bt), info, typ))
      | Mu.M_L at ->
         let@ at, typ = WLArgs.welltyped i_welltyped kind loc at in
         return (Mu.M_L at, AT.L typ)
    in
    pure (aux at)

end




module WProc = struct 
  let welltyped (loc : Loc.t) (at : _ Mu.mu_proc_args_and_body)
      : (_ Mu.mu_proc_args_and_body * AT.ft, type_error) m 
    =
    WArgs.welltyped (fun loc (body, labels, rt) ->
        let@ rt = WRT.welltyped loc rt in
        return ((body, labels, rt), rt)
      ) "function" loc at
end

module WLabel = struct
  open Mu
  let welltyped (loc : Loc.t) (lt : _ mu_expr mu_arguments)
      : (_ mu_expr mu_arguments * AT.lt, type_error) m 
    =
    WArgs.welltyped (fun loc body -> 
        return (body, False.False)
      ) "loop/label" loc lt
end


module WRPD = struct

  open ResourcePredicates 

  let welltyped pd = 
    (* no need to alpha-rename, because context.ml ensures
       there's no name clashes *)
    (* let pd = ResourcePredicates.alpha_rename_definition pd in *)
    pure begin
        let@ () = add_l pd.pointer BT.Loc (pd.loc, lazy (Pp.string "ptr-var")) in
        let@ () = 
          ListM.iterM (fun (s, ls) -> 
              let@ () = WLS.is_ls pd.loc ls in
              add_l s ls (pd.loc, lazy (Pp.string "input-var"))
            ) pd.iargs 
        in
        let@ () = ListM.iterM (WLS.is_ls pd.loc) (List.map snd pd.oargs) in
        let@ clauses = match pd.clauses with
          | None -> return None
          | Some clauses ->
             let@ clauses = 
               ListM.fold_leftM (fun acc {loc; guard; packing_ft} ->
                   let@ guard = WIT.check loc BT.Bool guard in
                   let negated_guards = List.map (fun clause -> IT.not_ clause.guard) acc in
                   pure begin 
                       let@ () = add_c (LC.t_ guard) in
                       let@ () = add_c (LC.t_ (IT.and_ negated_guards)) in
                       let@ packing_ft = 
                         WLAT.welltyped WOutputDef.subst (WOutputDef.welltyped (pd.oargs))
                           "clause" loc packing_ft
                       in
                       return (acc @ [{loc; guard; packing_ft}])
                     end
                 ) [] clauses
             in
             return (Some clauses)
        in
        return { pd with clauses }
      end

end



module WLPD = struct

  open LogicalPredicates

  let rec welltyped_body loc return_bt body =
    pure begin
      match body with
      | Body.Case (it, cases) ->
         let@ it = WIT.infer loc it in
         let@ cases = 
           ListM.mapM (fun (ctor, case_body) ->
               pure begin
                   let@ info = get_datatype_constr loc ctor in
                   let@ () = ensure_base_type loc ~expect:(IT.bt it)
                               (Datatype info.c_datatype_tag) in
                   let@ case_body = welltyped_body loc return_bt case_body in
                   return (ctor, case_body)
                 end
             ) cases
         in
         return (Body.Case (it, cases))
      | Body.Let ((s, it), t) ->
         let@ it = WIT.infer loc it in
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, t = Body.alpha_rename (s, IT.bt it) t in *)
         let@ () = add_l s (IT.bt it) (loc, lazy (Sym.pp s)) in
         let@ () = add_c (LC.t_ (IT.def_ s it)) in
         let@ t = welltyped_body loc return_bt t in
         return (Body.Let ((s, it), t))
      | Body.Term t -> 
         let@ t = WIT.check loc return_bt t in
         return (Body.Term t)
      end


  let welltyped (pd : LogicalPredicates.definition) = 
    (* no need to alpha-rename, because context.ml ensures
       there's no name clashes *)
    (* let pd = LogicalPredicates.alpha_rename_definition pd in *)
    pure begin
        let@ () = ListM.iterM (WLS.is_ls pd.loc) (List.map snd pd.args) in
        let info = (pd.loc, lazy (Pp.string "arg-var")) in
        let@ () = add_ls (List.map (fun (s,bt) -> (s, bt, info)) pd.args) in
        let@ () = WBT.is_bt pd.loc pd.return_bt in
        let@ definition = match pd.definition with
          | Def body -> 
             let@ body = welltyped_body pd.loc pd.return_bt body in
             return (Def body)
          | Rec_Def body -> 
             let@ body = welltyped_body pd.loc pd.return_bt body in
             return (Rec_Def body)
          | Uninterp -> 
             return Uninterp
        in
        return {
            loc = pd.loc; 
            args = pd.args; 
            return_bt = pd.return_bt;
            definition = definition;
          }
      end

end




