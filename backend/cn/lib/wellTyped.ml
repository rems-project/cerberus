module CF = Cerb_frontend
module LS = LogicalSorts
module BT = BaseTypes
module SymSet = Set.Make (Sym)
module TE = TypeErrors
module RE = Resources
module RET = ResourceTypes
module LRT = LogicalReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module Mu = Mucore
module IdSet = Set.Make (Id)
open Context
open Global
open TE
open Pp
open Typing

open Effectful.Make (Typing)

let use_ity = ref true

let ensure_base_type = Typing.ensure_base_type

let illtyped_index_term (loc : Locations.t) it has ~expected ~reason (_ctxt, _log) =
  let reason =
    match reason with
    | Either.Left reason ->
      let head, pos = Locations.head_pos_of_location reason in
      head ^ "\n" ^ pos
    | Either.Right reason -> reason
  in
  { loc;
    msg = TypeErrors.Illtyped_it { it = IT.pp it; has = BT.pp has; expected; reason }
  }


let ensure_bits_type (loc : Loc.t) (has : BT.t) =
  match has with
  | BT.Bits (_sign, _n) -> return ()
  | has ->
    fail (fun _ -> { loc; msg = Mismatch { has = BT.pp has; expect = !^"bitvector" } })


let ensure_z_fits_bits_type loc (sign, n) v =
  if BT.fits_range (sign, n) v then
    return ()
  else (
    let err = !^"Value" ^^^ Pp.z v ^^^ !^"does not fit" ^^^ BT.pp (Bits (sign, n)) in
    fail (fun _ -> { loc; msg = Generic err }))


let ensure_arith_type ~reason it =
  let open BT in
  match IT.bt it with
  | Integer | Real | Bits _ -> return ()
  | _ ->
    let expected = "integer, real or bitvector type" in
    fail
      (illtyped_index_term
         (IT.loc it)
         it
         (IT.bt it)
         ~expected
         ~reason:(Either.Left reason))


let ensure_set_type ~reason it =
  let open BT in
  match IT.bt it with
  | Set bt -> return bt
  | _ ->
    let expected = "set" in
    fail
      (illtyped_index_term
         (IT.loc it)
         it
         (IT.bt it)
         ~expected
         ~reason:(Either.Left reason))


let ensure_list_type ~reason it =
  let open BT in
  match IT.bt it with
  | List bt -> return bt
  | _ ->
    let expected = "list" in
    fail
      (illtyped_index_term
         (IT.loc it)
         it
         (IT.bt it)
         ~expected
         ~reason:(Either.Left reason))


let ensure_map_type ~reason it =
  let open BT in
  match IT.bt it with
  | Map (abt, rbt) -> return (abt, rbt)
  | _ ->
    let expected = "map/array" in
    fail
      (illtyped_index_term
         (IT.loc it)
         it
         (IT.bt it)
         ~expected
         ~reason:(Either.Left reason))


let ensure_same_argument_number loc input_output has ~expect =
  if has = expect then
    return ()
  else (
    match input_output with
    | `General -> fail (fun _ -> { loc; msg = Number_arguments { has; expect } })
    | `Input -> fail (fun _ -> { loc; msg = Number_input_arguments { has; expect } })
    | `Output -> fail (fun _ -> { loc; msg = Number_output_arguments { has; expect } }))


let compare_by_fst_id (x, _) (y, _) = Id.compare x y

let correct_members loc (spec : (Id.t * 'a) list) (have : (Id.t * 'b) list) =
  let needed = IdSet.of_list (List.map fst spec) in
  let@ needed =
    ListM.fold_leftM
      (fun needed (id, _) ->
        if IdSet.mem id needed then
          return (IdSet.remove id needed)
        else
          fail (fun _ -> { loc; msg = Unexpected_member (List.map fst spec, id) }))
      needed
      have
  in
  match IdSet.elements needed with
  | [] -> return ()
  | missing :: _ -> fail (fun _ -> { loc; msg = Missing_member missing })


let correct_members_sorted_annotated loc spec have =
  let@ () = correct_members loc spec have in
  let have = List.sort compare_by_fst_id have in
  let have_annotated =
    List.map2
      (fun (id, bt) (id', x) ->
        assert (Id.equal id id');
        (bt, (id', x)))
      spec
      have
  in
  return have_annotated


module WBT = struct
  open BT

  let is_bt loc =
    let rec aux = function
      | Unit -> return Unit
      | Bool -> return Bool
      | Integer -> return Integer
      | Bits (sign, n) -> return (Bits (sign, n))
      | Real -> return Real
      | Alloc_id -> return Alloc_id
      | Loc () -> return (Loc ())
      | CType -> return CType
      | Struct tag ->
        let@ _struct_decl = get_struct_decl loc tag in
        return (Struct tag)
      | Datatype tag ->
        let@ _datatype = get_datatype loc tag in
        return (Datatype tag)
      | Record members ->
        let@ members =
          ListM.mapM
            (fun (id, bt) ->
              let@ bt = aux bt in
              return (id, bt))
            members
        in
        assert (List.sorted_and_unique compare_by_fst_id members);
        return (Record members)
      | Map (abt, rbt) ->
        let@ abt = aux abt in
        let@ rbt = aux rbt in
        return (Map (abt, rbt))
      | List bt ->
        let@ bt = aux bt in
        return (List bt)
      | Tuple bts ->
        let@ bts = ListM.mapM aux bts in
        return (Tuple bts)
      | Set bt ->
        let@ bt = aux bt in
        return (Set bt)
    in
    fun bt -> aux bt


  let pick_integer_encoding_type loc z =
    match BT.pick_integer_encoding_type z with
    | Some bt -> return bt
    | None ->
      fail (fun _ ->
        { loc; msg = Generic (Pp.item "no standard encoding type for constant" (Pp.z z)) })
end

module WLS = struct
  let is_ls = WBT.is_bt
end

module WCT = struct
  open Sctypes

  let is_ct loc =
    let rec aux = function
      | Void -> return ()
      | Integer _ -> return ()
      | Array (ct, _) -> aux ct
      | Pointer ct -> aux ct
      | Struct tag ->
        let@ _struct_decl = get_struct_decl loc tag in
        return ()
      | Function ((_, rct), args, _) -> ListM.iterM aux (rct :: List.map fst args)
    in
    fun ct -> aux ct
end

module WIT = struct
  open BaseTypes
  open IndexTerms

  type t = IndexTerms.t

  (* let rec check_and_bind_pattern loc bt pat =  *)
  (*   match pat with *)
  (*   | PSym s ->  *)

  let rec check_and_bind_pattern bt (Pat (pat_, _, loc)) =
    match pat_ with
    | PSym s ->
      let@ () = add_l s bt (loc, lazy (Sym.pp s)) in
      return (Pat (PSym s, bt, loc))
    | PWild -> return (Pat (PWild, bt, loc))
    | PConstructor (s, args) ->
      let@ info = get_datatype_constr loc s in
      let@ () = ensure_base_type loc ~expect:bt (Datatype info.datatype_tag) in
      let@ args_annotated = correct_members_sorted_annotated loc info.params args in
      let@ args =
        ListM.mapM
          (fun (bt', (id', pat')) ->
            let@ pat' = check_and_bind_pattern bt' pat' in
            return (id', pat'))
          args_annotated
      in
      return (Pat (PConstructor (s, args), bt, loc))


  let leading_sym_or_wild = function
    | [] -> assert false
    | Pat (pat_, _, _) :: _ ->
      (match pat_ with PSym _ -> true | PWild -> true | PConstructor _ -> false)


  let expand_constr (constr, (constr_info : BT.constr_info)) (case : BT.t pattern list) =
    match case with
    | Pat (PWild, _, loc) :: pats | Pat (PSym _, _, loc) :: pats ->
      Some (List.map (fun (_m, bt) -> Pat (PWild, bt, loc)) constr_info.params @ pats)
    | Pat (PConstructor (constr', args), _, _) :: pats when Sym.equal constr constr' ->
      assert (List.for_all2 (fun (m, _) (m', _) -> Id.equal m m') constr_info.params args);
      Some (List.map snd args @ pats)
    | Pat (PConstructor (_constr', _args), _, _) :: _pats -> None
    | [] -> assert false


  (* copying and adjusting Neel Krishnaswami's pattern.ml code *)
  let rec cases_complete loc (bts : BT.t list) (cases : BT.t pattern list list) =
    match bts with
    | [] ->
      assert (List.for_all (function [] -> true | _ -> false) cases);
      (match cases with
       | [] -> fail (fun _ -> { loc; msg = Generic !^"Incomplete pattern" })
       | _ -> return ())
      (* | [_(\*[]*\)] -> return () *)
      (* | _::_::_ -> fail (fun _ -> {loc; msg = Generic !^"Duplicate pattern"}) *)
    | bt :: bts ->
      if List.for_all leading_sym_or_wild cases then
        cases_complete loc bts (List.map List.tl cases)
      else (
        match bt with
        | Unit | Bool | Integer | Bits _ | Real | Alloc_id
        | Loc ()
        | CType | Struct _ | Record _ | Map _ | List _ | Tuple _ | Set _ ->
          failwith "revisit for extended pattern language"
        | Datatype s ->
          let@ dt_info = get_datatype loc s in
          ListM.iterM
            (fun constr ->
              let@ constr_info = get_datatype_constr loc constr in
              let relevant_cases =
                List.filter_map (expand_constr (constr, constr_info)) cases
              in
              let member_bts = List.map snd constr_info.params in
              cases_complete loc (member_bts @ bts) relevant_cases)
            dt_info.constrs)


  let cases_necessary pats =
    (* checking no case is covered by previous cases (not whether a case is covered by a
       collection of previous cases, that's more work to do *)
    let rec covers p1 p2 =
      match (p1, p2) with
      | Pat (PWild, _, _), _ -> true
      | Pat (PSym _, _, _), _ -> true
      | Pat (PConstructor (s1, ps1), _, _), Pat (PConstructor (s2, ps2), _, _)
        when Sym.equal s1 s2 && List.equal Id.equal (List.map fst ps1) (List.map fst ps2)
        ->
        List.for_all2 covers (List.map snd ps1) (List.map snd ps2)
      | _, _ -> false
    in
    let@ _ =
      ListM.fold_leftM
        (fun prev (Pat (_, _, pat_loc) as pat) ->
          match List.find_opt (fun p1 -> covers p1 pat) prev with
          | None -> return (pat :: prev)
          | Some (Pat (case, _, p1_loc)) ->
            let prev_head, prev_pos = Locations.head_pos_of_location p1_loc in
            let case, sym =
              match case with
              | PWild -> ("wildcard", None)
              | PSym sym -> ("variable", Some sym)
              | PConstructor _ -> ("constructor", None)
            in
            let suggestion =
              Option.(
                value ~default:""
                @@ map
                     (fun sym ->
                       let str = Sym.pp_string sym in
                       let first_letter = String.unsafe_get str 0 in
                       let first_upper =
                         Char.(equal (uppercase_ascii first_letter) first_letter)
                       in
                       if first_upper then
                         "\nIf this is meant to be an nullary constructor, write `"
                         ^ str
                         ^ " {}` instead"
                       else
                         "")
                     sym)
            in
            let err =
              !^"covered by previous"
              ^^^ !^case
              ^^^ !^"at"
              ^^^ !^prev_head
              ^/^ !^prev_pos
              ^^ !^suggestion
            in
            fail (fun _ -> { loc = pat_loc; msg = Redundant_pattern err }))
        []
        pats
    in
    return ()


  let rec get_location_for_type = function
    | IT (Apply (name, _args), _, loc) ->
      let@ def = Typing.get_logical_function_def loc name in
      return def.loc
    | IT ((MapSet (t, _, _) | Let (_, t)), _, _) -> get_location_for_type t
    | IT (Cons (it, _), _, _) | it -> return @@ IT.loc it


  (* NOTE: This cannot _check_ what the root type of term is (the type is
     universally quantified) and so is not suitable for catching incorrect
     type annotations. *)
  let rec infer : 'bt. 'bt annot -> IT.t m =
    fun it ->
    Pp.debug 22 (lazy (Pp.item "Welltyped.WIT.infer" (IT.pp it)));
    let (IT (it, _, loc)) = it in
    let@ result =
      match it with
      | Sym s ->
        let@ is_a = bound_a s in
        let@ is_l = bound_l s in
        let@ binding =
          match () with
          | () when is_a -> get_a s
          | () when is_l -> get_l s
          | () -> fail (fun _ -> { loc; msg = TE.Unknown_variable s })
        in
        (match binding with
         | BaseType bt -> return (IT (Sym s, bt, loc))
         | Value it -> return it)
      | Const (Z z) -> return (IT (Const (Z z), Integer, loc))
      | Const (Bits ((sign, n), v) as c) ->
        let@ () = ensure_z_fits_bits_type loc (sign, n) v in
        return (IT (Const c, BT.Bits (sign, n), loc))
      | Const (Q q) -> return (IT (Const (Q q), Real, loc))
      | Const (Pointer p) ->
        let rs = Option.get (BT.is_bits_bt Memory.uintptr_bt) in
        let@ () = ensure_z_fits_bits_type loc rs p.addr in
        return (IT (Const (Pointer p), Loc (), loc))
      | Const (Alloc_id p) -> return (IT (Const (Alloc_id p), BT.Alloc_id, loc))
      | Const (Bool b) -> return (IT (Const (Bool b), BT.Bool, loc))
      | Const Unit -> return (IT (Const Unit, BT.Unit, loc))
      | Const (Default bt) ->
        let@ bt = WBT.is_bt loc bt in
        return (IT (Const (Default bt), bt, loc))
      | Const Null -> return (IT (Const Null, BT.Loc (), loc))
      | Const (CType_const ct) -> return (IT (Const (CType_const ct), BT.CType, loc))
      | Unop (unop, t) ->
        let@ t, ret_bt =
          match unop with
          | Not ->
            let@ t = check loc BT.Bool t in
            return (t, BT.Bool)
          | Negate ->
            let@ t = infer t in
            let@ () = ensure_arith_type ~reason:loc t in
            return (t, IT.bt t)
          | BW_CLZ_NoSMT | BW_CTZ_NoSMT | BW_FFS_NoSMT | BW_FLS_NoSMT | BW_Compl ->
            let@ t = infer t in
            let@ () = ensure_bits_type (IT.loc t) (IT.bt t) in
            return (t, IT.bt t)
        in
        return (IT (Unop (unop, t), ret_bt, loc))
      | Binop (arith_op, t, t') ->
        (match arith_op with
         | Add ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (Add, t, t'), IT.bt t, loc))
         | Sub ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (Sub, t, t'), IT.bt t, loc))
         | Mul ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           (match (IT.bt t, is_const t, is_const t') with
            | Integer, None, None ->
              let msg =
                !^"Both sides of the integer multiplication"
                ^^^ squotes (IT.pp (mul_ (t, t') loc))
                ^^^ !^"are not constants."
                ^^^ !^"treating the term as uninterpreted."
              in
              warn loc msg;
              return (IT (Binop (MulNoSMT, t, t'), IT.bt t, loc))
            | _ -> return (IT (Binop (Mul, t, t'), IT.bt t, loc)))
         | MulNoSMT ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (MulNoSMT, t, t'), IT.bt t, loc))
         | Div ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           (match (IT.bt t, is_const t') with
            | Integer, Some (Z z', _) when Z.leq z' Z.zero ->
              let msg =
                !^"Division"
                ^^^ squotes (IT.pp (div_ (t, t') loc))
                ^^^ !^"does not have positive right-hand argument."
                ^^^ !^"Treating as uninterpreted."
              in
              warn loc msg;
              return (IT (Binop (DivNoSMT, t, t'), IT.bt t, loc))
            | Integer, None ->
              let msg =
                !^"Division"
                ^^^ squotes (IT.pp (div_ (t, t') loc))
                ^^^ !^"does not have constant as right-hand argument."
                ^^^ !^"Treating as uninterpreted."
              in
              warn loc msg;
              return (IT (Binop (DivNoSMT, t, t'), IT.bt t, loc))
            | _ ->
              (* TODO: check for a zero divisor *)
              return (IT (Binop (Div, t, t'), IT.bt t, loc)))
         | DivNoSMT ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (DivNoSMT, t, t'), IT.bt t, loc))
         | Exp ->
           let@ t = infer t in
           let@ () = ensure_bits_type loc (IT.bt t) in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           let msg =
             !^"Treating exponentiation"
             ^^^ squotes (IT.pp (exp_ (t, t') loc))
             ^^^ !^"as uninterpreted."
           in
           warn loc msg;
           return (IT (Binop (ExpNoSMT, t, t'), IT.bt t, loc))
         | ExpNoSMT | RemNoSMT | ModNoSMT | BW_Xor | BW_And | BW_Or | ShiftLeft
         | ShiftRight | Rem | Mod ->
           let@ t = infer t in
           let@ () = ensure_bits_type loc (IT.bt t) in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (arith_op, t, t'), IT.bt t, loc))
         | LT ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (LT, t, t'), BT.Bool, loc))
         | LE ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (LE, t, t'), BT.Bool, loc))
         | Min ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (Min, t, t'), IT.bt t, loc))
         | Max ->
           let@ t = infer t in
           let@ () = ensure_arith_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (Max, t, t'), IT.bt t, loc))
         | EQ ->
           let@ t = infer t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (EQ, t, t'), BT.Bool, loc))
         | LTPointer ->
           let@ t = check loc (Loc ()) t in
           let@ t' = check loc (Loc ()) t' in
           return (IT (Binop (LTPointer, t, t'), BT.Bool, loc))
         | LEPointer ->
           let@ t = check loc (Loc ()) t in
           let@ t' = check loc (Loc ()) t' in
           return (IT (Binop (LEPointer, t, t'), BT.Bool, loc))
         | SetMember ->
           let@ t = infer t in
           let@ t' = check loc (Set (IT.bt t)) t' in
           return (IT (Binop (SetMember, t, t'), BT.Bool, loc))
         | SetUnion ->
           let@ t = infer t in
           let@ _itembt = ensure_set_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (SetUnion, t, t'), IT.bt t, loc))
         | SetIntersection ->
           let@ t = infer t in
           let@ _itembt = ensure_set_type ~reason:loc t in
           let@ t' = check (IT.loc t) (IT.bt t) t' in
           return (IT (Binop (SetIntersection, t, t'), IT.bt t, loc))
         | SetDifference ->
           let@ t = infer t in
           let@ itembt = ensure_set_type ~reason:loc t in
           let@ t' = check loc (Set itembt) t' in
           return (IT (Binop (SetDifference, t, t'), BT.Set itembt, loc))
         | Subset ->
           let@ t = infer t in
           let@ itembt = ensure_set_type ~reason:loc t in
           let@ t' = check (IT.loc t) (Set itembt) t' in
           return (IT (Binop (Subset, t, t'), BT.Bool, loc))
         | And ->
           let@ t = check loc Bool t in
           let@ t' = check loc Bool t' in
           return (IT (Binop (And, t, t'), Bool, loc))
         | Or ->
           let@ t = check loc Bool t in
           let@ t' = check loc Bool t' in
           return (IT (Binop (Or, t, t'), Bool, loc))
         | Implies ->
           let@ t = check loc Bool t in
           let@ t' = check loc Bool t' in
           return (IT (Binop (Implies, t, t'), Bool, loc)))
      | ITE (t, t', t'') ->
        let@ t = check loc Bool t in
        let@ t' = infer t' in
        let@ t'' = check (IT.loc t') (IT.bt t') t'' in
        return (IT (ITE (t, t', t''), IT.bt t', loc))
      | EachI ((i1, (s, bt), i2), t) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        pure
          (let@ bt = WBT.is_bt loc bt in
           let@ () = ensure_bits_type loc bt in
           let rs = Option.get (BT.is_bits_bt bt) in
           let@ () = ensure_z_fits_bits_type loc rs (Z.of_int i1) in
           let@ () = ensure_z_fits_bits_type loc rs (Z.of_int i2) in
           let@ () = add_l s bt (loc, lazy (Pp.string "forall-var")) in
           let@ t = check loc Bool t in
           return (IT (EachI ((i1, (s, bt), i2), t), BT.Bool, loc)))
      | Tuple ts ->
        let@ ts = ListM.mapM infer ts in
        let bts = List.map IT.bt ts in
        return (IT (Tuple ts, BT.Tuple bts, loc))
      | NthTuple (n, t') ->
        let@ t' = infer t' in
        let@ item_bt =
          match IT.bt t' with
          | Tuple bts ->
            (match List.nth_opt bts n with
             | Some t -> return t
             | None ->
               let expected = string_of_int n ^ "-tuple" in
               fail
                 (illtyped_index_term
                    loc
                    t'
                    (Tuple bts)
                    ~expected
                    ~reason:(Either.Left loc)))
          | has ->
            fail
              (illtyped_index_term
                 loc
                 t'
                 has
                 ~expected:"tuple"
                 ~reason:(Either.Right "not a tuple"))
        in
        return (IT (NthTuple (n, t'), item_bt, loc))
      | Struct (tag, members) ->
        let@ layout = get_struct_decl loc tag in
        let decl_members = Memory.member_types layout in
        let@ () = correct_members loc decl_members members in
        (* "sort" according to declaration *)
        let@ members_sorted =
          ListM.mapM
            (fun (id, ct) ->
              let@ t = check loc (Memory.bt_of_sct ct) (List.assoc Id.equal id members) in
              return (id, t))
            decl_members
        in
        assert (List.length members_sorted = List.length members);
        return (IT (Struct (tag, members_sorted), BT.Struct tag, loc))
      | StructMember (t, member) ->
        let@ t = infer t in
        let@ tag =
          match IT.bt t with
          | Struct tag -> return tag
          | has ->
            let expected = "struct" in
            let reason = Either.Left loc in
            fail (illtyped_index_term loc t has ~expected ~reason)
        in
        let@ field_ct = get_struct_member_type loc tag member in
        return (IT (StructMember (t, member), Memory.bt_of_sct field_ct, loc))
      | StructUpdate ((t, member), v) ->
        let@ t = infer t in
        let@ tag =
          match IT.bt t with
          | Struct tag -> return tag
          | has ->
            (* this case should have been caught by compile.ml *)
            let expected = "struct" in
            let reason = Either.Left (IT.loc t) in
            fail (illtyped_index_term loc t has ~expected ~reason)
        in
        let@ field_ct = get_struct_member_type loc tag member in
        let@ v = check (IT.loc t) (Memory.bt_of_sct field_ct) v in
        return (IT (StructUpdate ((t, member), v), BT.Struct tag, loc))
      | Record members ->
        assert (List.sorted_and_unique compare_by_fst_id members);
        let@ members =
          ListM.mapM
            (fun (id, t) ->
              let@ t = infer t in
              return (id, t))
            members
        in
        let member_types = List.map (fun (id, t) -> (id, IT.bt t)) members in
        return (IT (IT.Record members, BT.Record member_types, loc))
      | RecordMember (t, member) ->
        let@ t = infer t in
        let@ members =
          match IT.bt t with
          | Record members -> return members
          | has ->
            let expected = "struct" in
            let reason = Either.Left loc in
            fail (illtyped_index_term loc t has ~expected ~reason)
        in
        let@ bt =
          match List.assoc_opt Id.equal member members with
          | Some bt -> return bt
          | None ->
            let expected = "struct with member " ^ Id.pp_string member in
            let reason = Either.Left loc in
            fail (illtyped_index_term loc t (IT.bt t) ~expected ~reason)
        in
        return (IT (RecordMember (t, member), bt, loc))
      | RecordUpdate ((t, member), v) ->
        let@ t = infer t in
        let@ members =
          match IT.bt t with
          | Record members -> return members
          | has ->
            let expected = "struct" in
            let reason = Either.Left loc in
            fail (illtyped_index_term loc t has ~expected ~reason)
        in
        let@ bt =
          match List.assoc_opt Id.equal member members with
          | Some bt -> return bt
          | None ->
            let expected = "struct with member " ^ Id.pp_string member in
            let reason = Either.Left loc in
            fail (illtyped_index_term loc t (IT.bt t) ~expected ~reason)
        in
        let@ v = check (IT.loc t) bt v in
        return (IT (RecordUpdate ((t, member), v), IT.bt t, loc))
      | Cast (cbt, t) ->
        let@ cbt = WBT.is_bt loc cbt in
        let@ t = infer t in
        let@ () =
          match (IT.bt t, cbt) with
          | Integer, Loc () ->
            fail (fun _ ->
              { loc;
                msg = Generic !^"cast from integer not allowed in bitvector version"
              })
          | Loc (), Alloc_id -> return ()
          | Integer, Real -> return ()
          | Real, Integer -> return ()
          | Bits (_sign, _n), Bits (_sign', _n')
          (* FIXME: seems too restrictive when not (equal_sign sign sign' ) && n = n' *)
            ->
            return ()
          | Bits _, Loc () -> return ()
          | Loc (), Bits _ -> return ()
          | source, target ->
            let msg =
              !^"Unsupported cast from"
              ^^^ BT.pp source
              ^^^ !^"to"
              ^^^ BT.pp target
              ^^ dot
            in
            fail (fun _ -> { loc; msg = Generic msg })
        in
        return (IT (Cast (cbt, t), cbt, loc))
      | MemberShift (t, tag, member) ->
        let@ _ty = get_struct_member_type loc tag member in
        let@ t = check loc (Loc ()) t in
        let@ decl = get_struct_decl loc tag in
        let o = Option.get (Memory.member_offset decl member) in
        let rs = Option.get (BT.is_bits_bt Memory.uintptr_bt) in
        let@ () = ensure_z_fits_bits_type loc rs (Z.of_int o) in
        (* looking at solver mapping *)
        return (IT (MemberShift (t, tag, member), BT.Loc (), loc))
      | ArrayShift { base; ct; index } ->
        let@ () = WCT.is_ct loc ct in
        let@ base = check loc (Loc ()) base in
        let@ index = infer index in
        let@ () = ensure_bits_type loc (IT.bt index) in
        return (IT (ArrayShift { base; ct; index }, BT.Loc (), loc))
      | CopyAllocId { addr; loc = ptr } ->
        let@ addr = check loc Memory.uintptr_bt addr in
        let@ ptr = check loc (Loc ()) ptr in
        return (IT (CopyAllocId { addr; loc = ptr }, BT.Loc (), loc))
      | HasAllocId ptr ->
        let@ ptr = check loc (Loc ()) ptr in
        return (IT (HasAllocId ptr, BT.Bool, loc))
      | SizeOf ct ->
        let@ () = WCT.is_ct loc ct in
        let sz = Memory.size_of_ctype ct in
        let rs = Option.get (BT.is_bits_bt Memory.size_bt) in
        let@ () = ensure_z_fits_bits_type loc rs (Z.of_int sz) in
        return (IT (SizeOf ct, Memory.size_bt, loc))
      | OffsetOf (tag, member) ->
        let@ _ty = get_struct_member_type loc tag member in
        let@ decl = get_struct_decl loc tag in
        let o = Option.get (Memory.member_offset decl member) in
        let rs = Option.get (BT.is_bits_bt Memory.sint_bt) in
        let@ () = ensure_z_fits_bits_type loc rs (Z.of_int o) in
        return (IT (OffsetOf (tag, member), Memory.sint_bt, loc))
      | Aligned t ->
        let@ t_t = check loc (Loc ()) t.t in
        let@ t_align = check loc Memory.uintptr_bt t.align in
        return (IT (Aligned { t = t_t; align = t_align }, BT.Bool, loc))
      | Representable (ct, t) ->
        let@ () = WCT.is_ct loc ct in
        let@ t = check loc (Memory.bt_of_sct ct) t in
        return (IT (Representable (ct, t), BT.Bool, loc))
      | Good (ct, t) ->
        let@ () = WCT.is_ct loc ct in
        let@ t = check loc (Memory.bt_of_sct ct) t in
        return (IT (Good (ct, t), BT.Bool, loc))
      | WrapI (ity, t) ->
        let@ () = WCT.is_ct loc (Integer ity) in
        let@ t = infer t in
        return (IT (WrapI (ity, t), Memory.bt_of_sct (Integer ity), loc))
      | Nil bt ->
        let@ bt = WBT.is_bt loc bt in
        return (IT (Nil bt, BT.List bt, loc))
      | Cons (t1, t2) ->
        let@ t1 = infer t1 in
        let t1_loc = IT.loc t1 in
        let t1_bt = IT.bt t1 in
        (* This is all a little more complicated than ideal because we use the type of the
           first element of a list literal (currently always non-empty) is used to
           annotate the (Nil bt), and so _its_ location is the one which must be passed to
           `check` - not that of the nearest (Cons _). Without all of this, we would get
           this: ``` tests/cn/repeat.c:12:16: error: Type error [true,false,3] ^
           Expression 'nil<bool>' has type 'list<bool>'. I expected it to have type
           'list<integer>' because of tests/cn/repeat.c:12:14: [true,false,3] ^ ``` *)
        let rest, last =
          let rec to_list = function
            | IT (Cons (elem, tl), _, loc) ->
              let rest, last = to_list tl in
              ((elem, loc) :: rest, last)
            | it -> ([], it)
          in
          to_list t2
        in
        let@ rest =
          let check_elem (elem, loc) =
            let@ elem = check t1_loc t1_bt elem in
            return (elem, loc)
          in
          ListM.mapM check_elem rest
        in
        let@ last = check t1_loc (List t1_bt) last in
        let cons (hd, loc) tl = IT (Cons (hd, tl), BT.List t1_bt, loc) in
        return (List.fold_right cons ((t1, loc) :: rest) last)
      | Head t ->
        let@ t = infer t in
        let@ bt = ensure_list_type t ~reason:loc in
        return (IT (Head t, bt, loc))
      | Tail t ->
        let@ t = infer t in
        let@ bt = ensure_list_type t ~reason:loc in
        return (IT (Tail t, BT.List bt, loc))
      | NthList (i, xs, d) ->
        let@ i = infer i in
        let@ () = ensure_bits_type loc (IT.bt i) in
        let@ xs = infer xs in
        let@ bt = ensure_list_type xs ~reason:loc in
        let@ d = check (IT.loc xs) bt d in
        return (IT (NthList (i, xs, d), bt, loc))
      | ArrayToList (arr, i, len) ->
        let@ i = infer i in
        let@ () = ensure_bits_type loc (IT.bt i) in
        let@ len = check (IT.loc i) (IT.bt i) len in
        let@ arr = infer arr in
        let@ ix_bt, bt = ensure_map_type ~reason:loc arr in
        let@ () =
          if BT.equal ix_bt (IT.bt i) then
            return ()
          else
            fail (fun _ ->
              { loc;
                msg =
                  Generic
                    (Pp.item
                       "array_to_list: index type disagreement"
                       (Pp.list IT.pp_with_typ [ i; arr ]))
              })
        in
        return (IT (ArrayToList (arr, i, len), BT.List bt, loc))
      | MapConst (index_bt, t) ->
        let@ index_bt = WBT.is_bt loc index_bt in
        let@ t = infer t in
        return (IT (MapConst (index_bt, t), BT.Map (index_bt, IT.bt t), loc))
      | MapSet (t1, t2, t3) ->
        let@ t1 = infer t1 in
        let@ abt, rbt = ensure_map_type ~reason:loc t1 in
        let@ t2 = check (IT.loc t1) abt t2 in
        let@ t3 = check (IT.loc t1) rbt t3 in
        return (IT (MapSet (t1, t2, t3), IT.bt t1, loc))
      | MapGet (t, arg) ->
        let@ t = infer t in
        let@ abt, bt = ensure_map_type ~reason:loc t in
        let@ arg = check (IT.loc t) abt arg in
        return (IT (MapGet (t, arg), bt, loc))
      | MapDef ((s, abt), body) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ abt = WBT.is_bt loc abt in
        pure
          (let@ () = add_l s abt (loc, lazy (Pp.string "map-def-var")) in
           let@ body = infer body in
           return (IT (MapDef ((s, abt), body), Map (abt, IT.bt body), loc)))
      | Apply (name, args) ->
        let@ def = Typing.get_logical_function_def loc name in
        let has_args, expect_args = (List.length args, List.length def.args) in
        let@ () = ensure_same_argument_number loc `General has_args ~expect:expect_args in
        let@ args =
          ListM.map2M
            (fun has_arg (_, def_arg_bt) ->
              (* TODO - add location information to binders *)
              check def.loc def_arg_bt has_arg)
            args
            def.args
        in
        return (IT (Apply (name, args), def.return_bt, loc))
      | Let ((name, t1), t2) ->
        let@ t1 = infer t1 in
        pure
          (let@ () = add_l name (IT.bt t1) (loc, lazy (Pp.string "let-var")) in
           let@ () = add_c loc (LC.t_ (IT.def_ name t1 loc)) in
           let@ t2 = infer t2 in
           return (IT (Let ((name, t1), t2), IT.bt t2, loc)))
      | Constructor (s, args) ->
        let@ info = get_datatype_constr loc s in
        let@ args_annotated = correct_members_sorted_annotated loc info.params args in
        let@ args =
          ListM.mapM
            (fun (bt', (id', t')) ->
              (* TODO - add location information to binders *)
              let@ t' = check loc bt' t' in
              return (id', t'))
            args_annotated
        in
        return (IT (Constructor (s, args), Datatype info.datatype_tag, loc))
      | Match (e, cases) ->
        let@ e = infer e in
        let@ rbt, cases =
          ListM.fold_leftM
            (fun (rbt, acc) (pat, body) ->
              pure
                (let@ pat = check_and_bind_pattern (IT.bt e) pat in
                 let@ body =
                   match rbt with None -> infer body | Some rbt -> check loc rbt body
                 in
                 return (Some (IT.bt body), acc @ [ (pat, body) ])))
            (None, [])
            cases
        in
        let@ () =
          cases_complete loc [ IT.bt e ] (List.map (fun (pat, _) -> [ pat ]) cases)
        in
        let@ () = cases_necessary (List.map (fun (pat, _) -> pat) cases) in
        let@ rbt =
          match rbt with
          | None -> fail (fun _ -> { loc; msg = Empty_pattern })
          | Some rbt -> return rbt
        in
        return (IT (Match (e, cases), rbt, loc))
    in
    Pp.debug 22 (lazy (Pp.item "Welltyped.WIT.infer: inferred" (IT.pp_with_typ result)));
    return result


  and check expect_loc expect_ls it =
    let@ ls = WLS.is_ls expect_loc expect_ls in
    let@ it = infer it in
    let@ loc = get_location_for_type it in
    if LS.equal ls (IT.bt it) then
      return it
    else (
      let expected = Pp.plain @@ LS.pp ls in
      let reason = Either.Left expect_loc in
      fail (illtyped_index_term loc it (IT.bt it) ~expected ~reason))
end

module WRET = struct
  open IndexTerms

  let welltyped loc r =
    Pp.debug 22 (lazy (Pp.item "WRET: checking" (RET.pp r)));
    let@ spec_iargs =
      match RET.predicate_name r with
      | Owned (_ct, _init) -> return []
      | PName name ->
        let@ def = Typing.get_resource_predicate_def loc name in
        return def.iargs
    in
    match r with
    | P p ->
      let@ pointer = WIT.check loc (BT.Loc ()) p.pointer in
      let has_iargs, expect_iargs = (List.length p.iargs, List.length spec_iargs) in
      (* +1 because of pointer argument *)
      let@ () =
        ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs)
      in
      let@ iargs =
        ListM.map2M
          (fun (_, expected) arg -> WIT.check loc expected arg)
          spec_iargs
          p.iargs
      in
      return (RET.P { name = p.name; pointer; iargs })
    | Q p ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ pointer = WIT.check loc (BT.Loc ()) p.pointer in
      let@ qbt = WBT.is_bt loc (snd p.q) in
      let@ () = ensure_bits_type loc qbt in
      assert (BT.equal (snd p.q) qbt);
      (*normalisation does not change bit types. If this assertion fails, we have to
        adjust the later code to use qbt.*)
      let@ step = WIT.check loc (snd p.q) p.step in
      let@ step =
        match step with
        | IT (Const (Bits (_bits_bt, z)), _, _) ->
          if Z.lt Z.zero z then
            return step
          else
            fail (fun _ ->
              { loc;
                msg =
                  Generic (!^"Iteration step" ^^^ IT.pp p.step ^^^ !^"must be positive")
              })
        | IT (SizeOf _, _, _) -> return step
        | IT (Cast (_, IT (SizeOf _, _, _)), _, _) -> return step
        | _ ->
          let hint = "Only constant iteration steps are allowed." in
          fail (fun _ -> { loc; msg = NIA { it = p.step; hint } })
      in
      (*let@ () = match p.name with | (Owned (ct, _init)) -> let sz = Memory.size_of_ctype
        ct in if IT.equal step (IT.int_lit_ sz (snd p.q)) then return () else fail (fun _
        -> {loc; msg = Generic (!^"Iteration step" ^^^ IT.pp p.step ^^^ parens (IT.pp
        step) ^^^ !^ "different to sizeof" ^^^ Sctypes.pp ct ^^^ parens (!^ (Int.to_string
        sz)))}) | _ -> return () in*)
      let@ permission, iargs =
        pure
          (let@ () = add_l (fst p.q) (snd p.q) (loc, lazy (Pp.string "forall-var")) in
           let@ permission = WIT.check loc BT.Bool p.permission in
           (* let@ provable = provable loc in *)
           (* let here = Locations.other __FUNCTION__ in *)
           (* let only_nonnegative_indices = *)
           (*   (\* It is important to use `permission` here and NOT `p.permission`. *)
           (* If there is a record involved, `permission` is normalised but the
              `p.permission` is not *)
           (*      If there is a subsitution in `provable` then a type check *)
           (*      assertion may fail if the non-normalised form is used *\) *)
           (*   let sym_args = (fst p.q, snd p.q, p.q_loc) in *)
           (* LC.forall_ p.q (impl_ (permission, ge_ (sym_ sym_args, int_lit_ 0 (snd p.q)
              here) here) here) *)
           (* in *)
           (* let@ () = match provable only_nonnegative_indices with *)
           (*   | `True -> *)
           (*      return () *)
           (*   | `False -> *)
           (*      let model = Solver.model () in *)
           (*      let msg = "Iterated resource gives ownership to negative indices." in *)
           (*      fail (fun ctxt -> {loc; msg = Generic_with_model {err= !^msg; ctxt; model}}) *)
           (* in *)
           let has_iargs, expect_iargs = (List.length p.iargs, List.length spec_iargs) in
           (* +1 because of pointer argument *)
           let@ () =
             ensure_same_argument_number
               loc
               `Input
               (1 + has_iargs)
               ~expect:(1 + expect_iargs)
           in
           let@ iargs =
             ListM.map2M
               (fun (_, expected) arg -> WIT.check loc expected arg)
               spec_iargs
               p.iargs
           in
           return (permission, iargs))
      in
      return
        (RET.Q
           { name = p.name; pointer; q = p.q; q_loc = p.q_loc; step; permission; iargs })
end

let oarg_bt_of_pred loc = function
  | RET.Owned (ct, _init) -> return (Memory.bt_of_sct ct)
  | RET.PName pn ->
    let@ def = Typing.get_resource_predicate_def loc pn in
    return def.oarg_bt


let oarg_bt loc = function
  | RET.P pred -> oarg_bt_of_pred loc pred.name
  | RET.Q pred ->
    let@ item_bt = oarg_bt_of_pred loc pred.name in
    return (BT.make_map_bt (snd pred.q) item_bt)


module WRS = struct
  let welltyped loc (resource, bt) =
    Pp.(debug 6 (lazy !^__FUNCTION__));
    let@ resource = WRET.welltyped loc resource in
    let@ bt = WBT.is_bt loc bt in
    let@ oarg_bt = oarg_bt loc resource in
    let@ () = ensure_base_type loc ~expect:oarg_bt bt in
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
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ bt = WBT.is_bt loc bt in
      pure
        (let@ () = add_l s bt (loc, lazy (Pp.string "forall-var")) in
         let@ it = WIT.check loc BT.Bool it in
         return (LC.Forall ((s, bt), it)))
end

module WLRT = struct
  module LRT = LogicalReturnTypes
  open LRT

  type t = LogicalReturnTypes.t

  let welltyped loc lrt =
    let rec aux =
      let here = Locations.other __FUNCTION__ in
      function
      | Define ((s, it), ((loc, _) as info), lrt) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ it = WIT.infer it in
        let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
        let@ () = add_c (fst info) (LC.t_ (IT.def_ s it here)) in
        let@ lrt = aux lrt in
        return (Define ((s, it), info, lrt))
      | Resource ((s, (re, re_oa_spec)), ((loc, _) as info), lrt) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ re, re_oa_spec = WRS.welltyped loc (re, re_oa_spec) in
        let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
        let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
        let@ lrt = aux lrt in
        return (Resource ((s, (re, re_oa_spec)), info, lrt))
      | Constraint (lc, info, lrt) ->
        let@ lc = WLC.welltyped (fst info) lc in
        let@ () = add_c (fst info) lc in
        let@ lrt = aux lrt in
        return (Constraint (lc, info, lrt))
      | I ->
        let@ provable = provable loc in
        let here = Locations.other __FUNCTION__ in
        let@ () =
          match provable (LC.t_ (IT.bool_ false here)) with
          | `True ->
            fail (fun ctxt_log ->
              { loc; msg = Inconsistent_assumptions ("return type", ctxt_log) })
          | `False -> return ()
        in
        return I
    in
    pure (aux lrt)
end

module WRT = struct
  type t = ReturnTypes.t

  let subst = ReturnTypes.subst

  let pp = ReturnTypes.pp

  let welltyped loc rt =
    Pp.(debug 6 (lazy !^__FUNCTION__));
    pure
      (match rt with
       | RT.Computational ((name, bt), info, lrt) ->
         (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
         let@ bt = WBT.is_bt (fst info) bt in
         let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
         let@ lrt = WLRT.welltyped loc lrt in
         return (RT.Computational ((name, bt), info, lrt)))
end

(* module WFalse = struct *)
(*   type t = False.t *)

(*   let subst = False.subst *)

(*   let pp = False.pp *)

(*   let welltyped _ False.False = return False.False *)
(* end *)

let pure_and_no_initial_resources loc m =
  pure
    (let@ (), _ = map_and_fold_resources loc (fun _re () -> (Deleted, ())) () in
     m)


module WLAT = struct
  let welltyped i_welltyped i_pp kind loc (at : 'i LAT.t) : 'i LAT.t m =
    debug
      12
      (lazy
        (item ("checking wf of " ^ kind ^ " at " ^ Loc.to_string loc) (LAT.pp i_pp at)));
    let rec aux =
      let here = Locations.other __FUNCTION__ in
      function
      | LAT.Define ((s, it), info, at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ it = WIT.infer it in
        let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
        let@ () = add_c (fst info) (LC.t_ (IT.def_ s it here)) in
        let@ at = aux at in
        return (LAT.Define ((s, it), info, at))
      | LAT.Resource ((s, (re, re_oa_spec)), ((loc, _) as info), at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ re, re_oa_spec = WRS.welltyped (fst info) (re, re_oa_spec) in
        let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
        let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
        let@ at = aux at in
        return (LAT.Resource ((s, (re, re_oa_spec)), info, at))
      | LAT.Constraint (lc, info, at) ->
        let@ lc = WLC.welltyped (fst info) lc in
        let@ () = add_c (fst info) lc in
        let@ at = aux at in
        return (LAT.Constraint (lc, info, at))
      | LAT.I i ->
        let@ provable = provable loc in
        let here = Locations.other __FUNCTION__ in
        let@ () =
          match provable (LC.t_ (IT.bool_ false here)) with
          | `True ->
            fail (fun ctxt_log ->
              { loc; msg = Inconsistent_assumptions (kind, ctxt_log) })
          | `False -> return ()
        in
        let@ i = i_welltyped loc i in
        return (LAT.I i)
    in
    pure (aux at)
end

module WAT = struct
  let welltyped i_welltyped i_pp kind loc (at : 'i AT.t) : 'i AT.t m =
    debug
      12
      (lazy
        (item ("checking wf of " ^ kind ^ " at " ^ Loc.to_string loc) (AT.pp i_pp at)));
    let rec aux = function
      | AT.Computational ((name, bt), info, at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ bt = WBT.is_bt (fst info) bt in
        let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
        let@ at = aux at in
        return (AT.Computational ((name, bt), info, at))
      | AT.L at ->
        let@ at = WLAT.welltyped i_welltyped i_pp kind loc at in
        return (AT.L at)
    in
    pure (aux at)
end

module WFT = struct
  let welltyped =
    WAT.welltyped
      (fun loc rt -> pure_and_no_initial_resources loc (WRT.welltyped loc rt))
      WRT.pp
end

module WLT = struct
  open False

  let welltyped = WAT.welltyped (fun _loc False -> return False) False.pp
end

(* module WPackingFT(struct let name_bts = pd.oargs end) = WLAT(WOutputDef.welltyped
   (pd.oargs)) *)

module WLArgs = struct
  let rec typ ityp = function
    | Mu.M_Define (bound, info, lat) -> LAT.Define (bound, info, typ ityp lat)
    | Mu.M_Resource (bound, info, lat) -> LAT.Resource (bound, info, typ ityp lat)
    | Mu.M_Constraint (lc, info, lat) -> LAT.Constraint (lc, info, typ ityp lat)
    | Mu.M_I i -> LAT.I (ityp i)


  let welltyped (i_welltyped : Loc.t -> 'i -> 'j m) kind loc (at : 'i Mu.mu_arguments_l)
    : 'j Mu.mu_arguments_l m
    =
    let rec aux =
      let here = Locations.other __FUNCTION__ in
      Pp.(debug 6 (lazy !^__FUNCTION__));
      function
      | Mu.M_Define ((s, it), ((loc, _) as info), at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ it = WIT.infer it in
        let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
        let@ () = add_c (fst info) (LC.t_ (IT.def_ s it here)) in
        let@ at = aux at in
        return (Mu.M_Define ((s, it), info, at))
      | Mu.M_Resource ((s, (re, re_oa_spec)), ((loc, _) as info), at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ re, re_oa_spec = WRS.welltyped (fst info) (re, re_oa_spec) in
        let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
        let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
        let@ at = aux at in
        return (Mu.M_Resource ((s, (re, re_oa_spec)), info, at))
      | Mu.M_Constraint (lc, info, at) ->
        let@ lc = WLC.welltyped (fst info) lc in
        let@ () = add_c (fst info) lc in
        let@ at = aux at in
        return (Mu.M_Constraint (lc, info, at))
      | Mu.M_I i ->
        let@ provable = provable loc in
        let here = Locations.other __FUNCTION__ in
        let@ () =
          match provable (LC.t_ (IT.bool_ false here)) with
          | `True ->
            fail (fun ctxt_log ->
              { loc; msg = Inconsistent_assumptions (kind, ctxt_log) })
          | `False -> return ()
        in
        let@ i = i_welltyped loc i in
        return (Mu.M_I i)
    in
    pure (aux at)
end

module WArgs = struct
  let rec typ ityp = function
    | Mu.M_Computational (bound, info, at) -> AT.Computational (bound, info, typ ityp at)
    | Mu.M_L lat -> AT.L (WLArgs.typ ityp lat)


  let welltyped
    : 'i 'j.
    (Loc.t -> 'i -> 'j m) -> string -> Loc.t -> 'i Mu.mu_arguments -> 'j Mu.mu_arguments m
    =
    fun (i_welltyped : Loc.t -> 'i -> 'j m) kind loc (at : 'i Mu.mu_arguments) ->
    debug 6 (lazy !^__FUNCTION__);
    debug
      12
      (lazy
        (item
           ("checking wf of " ^ kind ^ " at " ^ Loc.to_string loc)
           (CF.Pp_ast.pp_doc_tree
              (Mucore.dtree_of_mu_arguments (fun _i -> Dleaf !^"...") at))));
    let rec aux = function
      | Mu.M_Computational ((name, bt), info, at) ->
        (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
        let@ bt = WBT.is_bt (fst info) bt in
        let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
        let@ at = aux at in
        return (Mu.M_Computational ((name, bt), info, at))
      | Mu.M_L at ->
        let@ at = WLArgs.welltyped i_welltyped kind loc at in
        return (Mu.M_L at)
    in
    pure (aux at)
end

module BaseTyping = struct
  open Mucore
  open Typing
  open TypeErrors
  module SymMap = Map.Make (Sym)
  module BT = BaseTypes
  module RT = ReturnTypes
  module AT = ArgumentTypes
  open BT

  type label_context = (AT.lt * label_kind * Locations.t) SymMap.t

  let check_against_core_bt loc msg2 cbt bt =
    Typing.embed_resultat
      (CoreTypeChecks.check_against_core_bt
         (fun msg -> Resultat.fail { loc; msg = Generic (msg ^^ Pp.hardline ^^ msg2) })
         cbt
         bt)


  let rec check_and_bind_pattern bt = function
    | M_Pattern (loc, anns, _, p_) ->
      let@ p_ = check_and_bind_pattern_ bt loc p_ in
      return (M_Pattern (loc, anns, bt, p_))


  and check_and_bind_pattern_ bt loc = function
    | M_CaseBase (sym_opt, cbt) ->
      let@ () =
        match sym_opt with
        | Some nm ->
          let@ () =
            check_against_core_bt loc (!^"  checking pattern-var:" ^^^ Sym.pp nm) cbt bt
          in
          add_a nm bt (loc, lazy (Pp.string "pattern-match var"))
        | None ->
          let@ () = check_against_core_bt loc !^"  checking _ pattern-var" cbt bt in
          return ()
      in
      return (M_CaseBase (sym_opt, cbt))
    | M_CaseCtor (ctor, pats) ->
      let get_item_bt bt =
        match BT.is_list_bt bt with
        | Some bt -> return bt
        | None ->
          fail (fun _ ->
            { loc; msg = Generic (Pp.item "list pattern match against" (BT.pp bt)) })
      in
      let@ ctor, pats =
        match (ctor, pats) with
        | M_Cnil cbt, [] ->
          let@ _item_bt = get_item_bt bt in
          return (M_Cnil cbt, [])
        | M_Cnil _, _ ->
          fail (fun _ ->
            { loc; msg = Number_arguments { has = List.length pats; expect = 0 } })
        | M_Ccons, [ p1; p2 ] ->
          let@ item_bt = get_item_bt bt in
          let@ p1 = check_and_bind_pattern item_bt p1 in
          let@ p2 = check_and_bind_pattern bt p2 in
          return (M_Ccons, [ p1; p2 ])
        | M_Ccons, _ ->
          fail (fun _ ->
            { loc; msg = Number_arguments { has = List.length pats; expect = 2 } })
        | M_Ctuple, pats ->
          let@ bts =
            match BT.is_tuple_bt bt with
            | Some bts when List.length bts == List.length pats -> return bts
            | _ ->
              fail (fun _ ->
                { loc;
                  msg =
                    Generic
                      (Pp.item
                         (Int.to_string (List.length pats)
                          ^ "-length tuple pattern match against")
                         (BT.pp bt))
                })
          in
          let@ pats = ListM.map2M check_and_bind_pattern bts pats in
          return (M_Ctuple, pats)
        | M_Carray, _ -> Cerb_debug.error "todo: array types"
      in
      return (M_CaseCtor (ctor, pats))


  let rec infer_object_value
    : 'TY. Locations.t -> 'TY mu_object_value -> BT.t mu_object_value m
    =
    fun loc (M_OV (_, ov) as ov_original) ->
    let todo () =
      failwith
        ("TODO: WellTyped infer_object_value: "
         ^ Pp.plain
             (CF.Pp_ast.pp_doc_tree (Pp_mucore_ast.PP.dtree_of_object_value ov_original))
        )
    in
    let@ bt, ov =
      match ov with
      | M_OVinteger iv ->
        let z = Memory.z_of_ival iv in
        let@ bt = WBT.pick_integer_encoding_type loc z in
        Pp.debug
          2
          (lazy
            (Loc.pp loc
             ^^ colon
             ^^^ !^"no type-annotation for integer literal, picking"
             ^^^ squotes (BT.pp bt)));
        return (bt, M_OVinteger iv)
      | M_OVfloating fv -> return (Real, M_OVfloating fv)
      | M_OVpointer pv -> return (Loc (), M_OVpointer pv)
      | M_OVarray xs ->
        let@ _bt_xs = ListM.mapM (infer_object_value loc) xs in
        todo ()
      | M_OVstruct (nm, xs) -> return (Struct nm, M_OVstruct (nm, xs))
      | M_OVunion _ -> todo ()
    in
    return (M_OV (bt, ov))


  let check_object_value
    : 'TY. Locations.t -> BT.t -> 'TY mu_object_value -> BT.t mu_object_value m
    =
    fun loc bt (M_OV (_, ov) as ov_original) ->
    match ov with
    | M_OVinteger iv ->
      let z = Memory.z_of_ival iv in
      let@ () = ensure_bits_type loc bt in
      if BT.fits_range (Option.get (BT.is_bits_bt bt)) z then
        return (M_OV (bt, M_OVinteger iv))
      else
        fail (fun _ ->
          { loc;
            msg =
              Generic
                (!^"Value " ^^^ Pp.z z ^^^ !^"does not fit in expected type" ^^^ BT.pp bt)
          })
    | _ ->
      let@ ov = infer_object_value loc ov_original in
      let@ () = ensure_base_type loc ~expect:bt (bt_of_object_value ov) in
      return ov


  let rec infer_value : 'TY. Locations.t -> 'TY mu_value -> BT.t mu_value m =
    fun loc (M_V (_, v)) ->
    let@ bt, v =
      match v with
      | M_Vobject ov ->
        let@ ov = infer_object_value loc ov in
        return (bt_of_object_value ov, M_Vobject ov)
      | M_Vctype ct -> return (CType, M_Vctype ct)
      | M_Vunit -> return (Unit, M_Vunit)
      | M_Vtrue -> return (Bool, M_Vtrue)
      | M_Vfalse -> return (Bool, M_Vfalse)
      | M_Vfunction_addr sym -> return (Loc (), M_Vfunction_addr sym)
      | M_Vlist (item_cbt, vals) ->
        let@ vals = ListM.mapM (infer_value loc) vals in
        let item_bt = bt_of_value (List.hd vals) in
        return (List item_bt, M_Vlist (item_cbt, vals))
      | M_Vtuple vals ->
        let@ vals = ListM.mapM (infer_value loc) vals in
        let bt = Tuple (List.map bt_of_value vals) in
        return (bt, M_Vtuple vals)
    in
    return (M_V (bt, v))


  let check_value : 'TY. Locations.t -> BT.t -> 'TY mu_value -> BT.t mu_value m =
    fun loc expect (M_V (_, v) as orig_v) ->
    match v with
    | M_Vobject ov ->
      let@ ov = check_object_value loc expect ov in
      return (M_V (expect, M_Vobject ov))
    | _ ->
      let@ v = infer_value loc orig_v in
      let@ () = ensure_base_type loc ~expect (bt_of_value v) in
      return v


  let is_integer_annot = function CF.Annot.Avalue (Ainteger ity) -> Some ity | _ -> None

  let integer_annot annots =
    match
      List.sort_uniq
        CF.IntegerType.setElemCompare_integerType
        (List.filter_map is_integer_annot annots)
    with
    | [] -> None
    | [ ity ] -> Some ity
    | _ -> assert false


  let remove_integer_annot annots =
    List.filter (fun a -> Option.is_none (is_integer_annot a)) annots


  let remove_integer_annot_expr (M_Expr (loc, annots, bty, e_)) =
    M_Expr (loc, remove_integer_annot annots, bty, e_)


  let remove_integer_annot_pexpr (M_Pexpr (loc, annots, bty, e_)) =
    M_Pexpr (loc, remove_integer_annot annots, bty, e_)


  let rec infer_pexpr : 'TY. 'TY mu_pexpr -> BT.t mu_pexpr m =
    fun pe ->
    Pp.debug
      22
      (lazy (Pp.item "WellTyped.BaseTyping.infer_pexpr" (Pp_mucore_ast.pp_pexpr pe)));
    let (M_Pexpr (loc, annots, _, pe_)) = pe in
    match integer_annot annots with
    | Some ity when !use_ity ->
      check_pexpr (Memory.bt_of_sct (Integer ity)) (remove_integer_annot_pexpr pe)
    | _ ->
      let todo () =
        Pp.error loc !^"TODO: WellTyped infer_pexpr" [ Pp_mucore_ast.pp_pexpr pe ];
        failwith "TODO: WellTyped infer_pexpr"
      in
      let@ bty, pe_ =
        match pe_ with
        | M_PEsym sym ->
          let@ l_elem = get_a sym in
          return (Context.bt_of l_elem, M_PEsym sym)
        | M_PEval v ->
          let@ v = infer_value loc v in
          let bt = bt_of_value v in
          return (bt, M_PEval v)
        | M_PElet (pat, pe1, pe2) ->
          let@ pe1 = infer_pexpr pe1 in
          pure
            (let@ pat = check_and_bind_pattern (bt_of_pexpr pe1) pat in
             let@ pe2 = infer_pexpr pe2 in
             return (bt_of_pexpr pe2, M_PElet (pat, pe1, pe2)))
        | M_PEop (op, pe1, pe2) ->
          let@ pe1 = infer_pexpr pe1 in
          (* Core binops are either ('a -> 'a -> bool) or ('a -> 'a -> 'a) *)
          let@ pe2 = check_pexpr (bt_of_pexpr pe1) pe2 in
          let casts_to_bool =
            match op with OpEq | OpGt | OpLt | OpGe | OpLe -> true | _ -> false
          in
          let bt = if casts_to_bool then Bool else bt_of_pexpr pe1 in
          return (bt, M_PEop (op, pe1, pe2))
        | M_PEbounded_binop (bk, op, pe1, pe2) ->
          let@ pe1 = infer_pexpr pe1 in
          (* Core i-binops are all ('a -> 'a -> 'a), except shifts which promote the
             rhs *)
          let promotes_rhs = match op with IOpShl | IOpShr -> true | _ -> false in
          let@ pe2 =
            if promotes_rhs then
              let@ pe2 = infer_pexpr pe2 in
              let@ () = ensure_bits_type (loc_of_pexpr pe2) (bt_of_pexpr pe2) in
              return pe2
            else
              check_pexpr (bt_of_pexpr pe1) pe2
          in
          return
            (Memory.bt_of_sct (bound_kind_act bk).ct, M_PEbounded_binop (bk, op, pe1, pe2))
        | M_PEbitwise_unop (unop, pe) ->
          (* all the supported unops do arithmetic in the one (bitwise) type *)
          let@ pe = infer_pexpr pe in
          let bt = bt_of_pexpr pe in
          let@ () = ensure_bits_type (loc_of_pexpr pe) bt in
          return (bt, M_PEbitwise_unop (unop, pe))
        | M_PEbitwise_binop (binop, pe1, pe2) ->
          (* all the supported binops do arithmetic in the one (bitwise) type *)
          let@ pe1 = infer_pexpr pe1 in
          let bt = bt_of_pexpr pe1 in
          let@ () = ensure_bits_type (loc_of_pexpr pe1) bt in
          let@ pe2 = check_pexpr bt pe2 in
          return (bt, M_PEbitwise_binop (binop, pe1, pe2))
        | M_PEif (c_pe, pe1, pe2) ->
          let@ c_pe = check_pexpr Bool c_pe in
          let@ bt, pe1, pe2 =
            if is_undef_or_error_pexpr pe1 then
              let@ pe2 = infer_pexpr pe2 in
              let bt = bt_of_pexpr pe2 in
              let@ pe1 = check_pexpr bt pe1 in
              return (bt, pe1, pe2)
            else
              let@ pe1 = infer_pexpr pe1 in
              let bt = bt_of_pexpr pe1 in
              let@ pe2 = check_pexpr bt pe2 in
              return (bt, pe1, pe2)
          in
          return (bt, M_PEif (c_pe, pe1, pe2))
        | M_PEarray_shift (pe1, ct, pe2) ->
          let@ pe1 = infer_pexpr pe1 in
          let@ pe2 = infer_pexpr pe2 in
          return (Loc (), M_PEarray_shift (pe1, ct, pe2))
        | M_PEmember_shift (pe, tag, member) ->
          let@ pe = infer_pexpr pe in
          return (Loc (), M_PEmember_shift (pe, tag, member))
        | M_PEconv_int (M_Pexpr (l2, a2, _, M_PEval (M_V (_, M_Vctype ct))), pe) ->
          let ct_pe = M_Pexpr (l2, a2, CType, M_PEval (M_V (CType, M_Vctype ct))) in
          let@ pe = infer_pexpr pe in
          return
            (Memory.bt_of_sct (Sctypes.of_ctype_unsafe loc ct), M_PEconv_int (ct_pe, pe))
        | M_PEconv_loaded_int (M_Pexpr (l2, a2, _, M_PEval (M_V (_, M_Vctype ct))), pe) ->
          let ct_pe = M_Pexpr (l2, a2, CType, M_PEval (M_V (CType, M_Vctype ct))) in
          let@ pe = infer_pexpr pe in
          return
            ( Memory.bt_of_sct (Sctypes.of_ctype_unsafe loc ct),
              M_PEconv_loaded_int (ct_pe, pe) )
        | M_PEcatch_exceptional_condition (act, pe) ->
          let@ pe = infer_pexpr pe in
          return (bt_of_pexpr pe, M_PEcatch_exceptional_condition (act, pe))
        | M_PEwrapI (act, pe) ->
          let@ pe = infer_pexpr pe in
          return (Memory.bt_of_sct act.ct, M_PEwrapI (act, pe))
        | M_PEis_representable_integer (pe, act) ->
          let@ pe = infer_pexpr pe in
          return (Bool, M_PEis_representable_integer (pe, act))
        | M_PEbool_to_integer pe ->
          let@ pe = infer_pexpr pe in
          (* FIXME: replace this with something derived from a ctype when that info is
             available *)
          let ity = Sctypes.(IntegerTypes.Signed IntegerBaseTypes.Int_) in
          let bt = Memory.bt_of_sct (Sctypes.Integer ity) in
          return (bt, M_PEbool_to_integer pe)
        | M_PEnot pe ->
          let@ pe = infer_pexpr pe in
          return (Bool, M_PEnot pe)
        | M_PEctor (ctor, pes) ->
          let@ pes = ListM.mapM infer_pexpr pes in
          let@ bt =
            match ctor with
            | M_Cnil _ -> todo ()
            | M_Ccons ->
              (match pes with
               | [ x; xs ] ->
                 let ibt = bt_of_pexpr x in
                 let@ () = ensure_base_type loc ~expect:(List ibt) (bt_of_pexpr xs) in
                 return (bt_of_pexpr xs)
               | _ ->
                 fail (fun _ ->
                   { loc; msg = Number_arguments { has = List.length pes; expect = 2 } }))
            | M_Ctuple -> return (BT.Tuple (List.map bt_of_pexpr pes))
            | M_Carray ->
              let ibt = bt_of_pexpr (List.hd pes) in
              let@ () =
                ListM.iterM
                  (fun pe -> ensure_base_type loc ~expect:ibt (bt_of_pexpr pe))
                  pes
              in
              return (Map (Memory.uintptr_bt, ibt))
          in
          return (bt, M_PEctor (ctor, pes))
        | M_PEcfunction pe ->
          let@ pe = infer_pexpr pe in
          return (Tuple [ CType; List CType; Bool; Bool ], M_PEcfunction pe)
        | M_PEstruct (nm, nm_pes) ->
          let@ nm_pes =
            ListM.mapM
              (fun (nm, pe) ->
                let@ pe = infer_pexpr pe in
                return (nm, pe))
              nm_pes
          in
          return (Struct nm, M_PEstruct (nm, nm_pes))
        | M_PEapply_fun (fname, pes) ->
          let@ bt, pes = check_infer_apply_fun None fname pes pe in
          return (bt, M_PEapply_fun (fname, pes))
        | M_PEconstrained _ | M_Cfvfromint _
        | M_Civfromfloat (_, _)
        | M_PEunion (_, _, _)
        | M_PEmemberof (_, _, _)
        | M_PEconv_int (_, _)
        | M_PEconv_loaded_int (_, _)
        (* reaching these cases should be prevented by the `is_unreachable` used in
           inferring types of M_PEif *)
        | M_PEerror (_, _)
        | M_PEundef (_, _) ->
          todo ()
      in
      return (M_Pexpr (loc, annots, bty, pe_))


  and check_pexpr (expect : BT.t) expr =
    let (M_Pexpr (loc, annots, _, pe_)) = expr in
    let@ () =
      match integer_annot annots with
      | Some ity when !use_ity ->
        ensure_base_type loc ~expect (Memory.bt_of_sct (Integer ity))
      | _ -> return ()
    in
    let annot bt pe_ = M_Pexpr (loc, annots, bt, pe_) in
    match pe_ with
    | M_PEundef (a, b) -> return (annot expect (M_PEundef (a, b)))
    | M_PEerror (err, pe) ->
      let@ pe = infer_pexpr pe in
      return (annot expect (M_PEerror (err, pe)))
    | M_PEval v ->
      let@ v = check_value loc expect v in
      return (annot expect (M_PEval v))
    | M_PEapply_fun (fname, pes) ->
      let@ _bt, pes = check_infer_apply_fun (Some expect) fname pes expr in
      return (annot expect (M_PEapply_fun (fname, pes)))
    | _ ->
      let@ expr = infer_pexpr expr in
      (match bt_of_pexpr expr with
       | Integer ->
         Pp.debug
           1
           (lazy (Pp.item "warning: inferred integer bt" (Pp_mucore_ast.pp_pexpr expr)))
       | _ -> ());
      let@ () = ensure_base_type (loc_of_pexpr expr) ~expect (bt_of_pexpr expr) in
      return expr


  and check_infer_apply_fun (expect : BT.t option) fname pexps orig_pe =
    let (M_Pexpr (loc, _annots, _, _)) = orig_pe in
    let param_tys = Mucore.mu_fun_param_types fname in
    let@ () =
      ensure_same_argument_number
        loc
        `Input
        (List.length pexps)
        ~expect:(List.length param_tys)
    in
    let@ pexps = ListM.map2M check_pexpr param_tys pexps in
    let@ bt =
      match (Mucore.mu_fun_return_type fname pexps, expect) with
      | Some (`Returns_BT bt), _ -> return bt
      | Some `Returns_Integer, Some bt ->
        let@ () = ensure_bits_type loc bt in
        return bt
      | None, _ ->
        fail (fun _ ->
          { loc;
            msg =
              Generic
                (Pp.item "untypeable mucore function" (Pp_mucore_ast.pp_pexpr orig_pe))
          })
      | Some `Returns_Integer, None ->
        fail (fun _ ->
          { loc;
            msg =
              Generic
                (Pp.item
                   "mucore function requires type-annotation"
                   (Pp_mucore_ast.pp_pexpr orig_pe))
          })
    in
    return (bt, pexps)


  let check_cn_statement loc stmt =
    let open Cnprog in
    Pp.debug
      22
      (lazy
        (Pp.item
           "WellTyped.check_cn_statement"
           (CF.Pp_ast.pp_doc_tree (dtree_of_cn_statement stmt))));
    match stmt with
    | M_CN_pack_unpack (pack_unpack, pt) ->
      let@ p_pt = WRET.welltyped loc (P pt) in
      let[@warning "-8"] (RET.P pt) = p_pt in
      return (M_CN_pack_unpack (pack_unpack, pt))
    | M_CN_have lc ->
      let@ lc = WLC.welltyped loc lc in
      return (M_CN_have lc)
    | M_CN_instantiate (to_instantiate, it) ->
      let@ () =
        match to_instantiate with
        | I_Function f ->
          let@ _ = get_logical_function_def loc f in
          return ()
        | I_Good ct -> WCT.is_ct loc ct
        | I_Everything -> return ()
      in
      let@ it = WIT.infer it in
      return (M_CN_instantiate (to_instantiate, it))
    | M_CN_extract (attrs, to_extract, it) ->
      let@ () =
        match to_extract with
        | E_Pred (CN_owned None) -> return ()
        | E_Pred (CN_owned (Some ct)) -> WCT.is_ct loc ct
        | E_Pred (CN_block None) -> return ()
        | E_Pred (CN_block (Some ct)) -> WCT.is_ct loc ct
        | E_Pred (CN_named p) ->
          let@ _ = get_resource_predicate_def loc p in
          return ()
        | E_Everything -> return ()
      in
      let@ it = WIT.infer it in
      return (M_CN_extract (attrs, to_extract, it))
    | M_CN_unfold (f, its) ->
      let@ def = get_logical_function_def loc f in
      if LogicalFunctions.is_recursive def then
        ()
      else
        Pp.warn loc (Pp.item "unfold of function not marked [rec] (no effect)" (Sym.pp f));
      let@ () =
        ensure_same_argument_number
          loc
          `General
          (List.length its)
          ~expect:(List.length def.args)
      in
      let@ its = ListM.map2M (fun (_, bt) it -> WIT.check loc bt it) def.args its in
      return (M_CN_unfold (f, its))
    | M_CN_apply (l, its) ->
      let@ _lemma_loc, lemma_typ = get_lemma loc l in
      let@ its =
        let wrong_number_arguments () =
          let has = List.length its in
          let expect = AT.count_computational lemma_typ in
          fail (fun _ -> { loc; msg = Number_arguments { has; expect } })
        in
        let rec check_args lemma_typ its =
          match (lemma_typ, its) with
          | AT.Computational ((_s, bt), _info, lemma_typ'), it :: its' ->
            let@ it = WIT.check loc bt it in
            let@ its' = check_args lemma_typ' its' in
            return (it :: its')
          | AT.L _, [] -> return []
          | _ -> wrong_number_arguments ()
        in
        check_args lemma_typ its
      in
      return (M_CN_apply (l, its))
    | M_CN_assert lc ->
      let@ lc = WLC.welltyped loc lc in
      return (M_CN_assert lc)
    | M_CN_inline fs ->
      let@ _ = ListM.mapM (get_fun_decl loc) fs in
      return (M_CN_inline fs)
    | M_CN_print it ->
      let@ it = WIT.infer it in
      return (M_CN_print it)
    | M_CN_split_case lc ->
      let@ lc = WLC.welltyped loc lc in
      return (M_CN_split_case lc)


  let check_cnprog p =
    let open Cnprog in
    let rec aux = function
      | M_CN_let (loc, (s, { ct; pointer }), p') ->
        let@ () = WCT.is_ct loc ct in
        let@ pointer = WIT.check loc (Loc ()) pointer in
        let@ () = add_l s (Memory.bt_of_sct ct) (loc, lazy (Sym.pp s)) in
        let@ p' = aux p' in
        return (M_CN_let (loc, (s, { ct; pointer }), p'))
      | M_CN_statement (loc, stmt) ->
        let@ stmt = check_cn_statement loc stmt in
        return (M_CN_statement (loc, stmt))
    in
    pure (aux p)


  let signed_int_ty = Memory.bt_of_sct Sctypes.(Integer (Signed Int_))

  let rec infer_expr : 'TY. label_context -> 'TY mu_expr -> BT.t mu_expr m =
    fun label_context e ->
    Pp.debug
      22
      (lazy (Pp.item "WellTyped.BaseTyping.infer_expr" (Pp_mucore_ast.pp_expr e)));
    let (M_Expr (loc, annots, _, e_)) = e in
    match integer_annot annots with
    | Some ity when !use_ity ->
      check_expr
        label_context
        (Memory.bt_of_sct (Integer ity))
        (remove_integer_annot_expr e)
    | _ ->
      let todo () =
        Pp.error loc !^"TODO: WellTyped infer_expr" [ Pp_mucore_ast.pp_expr e ];
        failwith "TODO: WellTyped infer_expr"
      in
      let@ bty, e_ =
        match e_ with
        | M_Epure pe ->
          let@ pe = infer_pexpr pe in
          return (bt_of_pexpr pe, M_Epure pe)
        | M_Ememop (M_PtrEq (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrEq (pe1, pe2)))
        | M_Ememop (M_PtrNe (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrNe (pe1, pe2)))
        | M_Ememop (M_PtrLt (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrLt (pe1, pe2)))
        | M_Ememop (M_PtrGt (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrGt (pe1, pe2)))
        | M_Ememop (M_PtrLe (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrLe (pe1, pe2)))
        | M_Ememop (M_PtrGe (pe1, pe2)) ->
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          return (Bool, M_Ememop (M_PtrGe (pe1, pe2)))
        | M_Ememop (M_Ptrdiff (act, pe1, pe2)) ->
          let@ () = WCT.is_ct act.loc act.ct in
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = check_pexpr (Loc ()) pe2 in
          let bty = Memory.bt_of_sct (Integer Ptrdiff_t) in
          return (bty, M_Ememop (M_Ptrdiff (act, pe1, pe2)))
        | M_Ememop (M_IntFromPtr (act_from, act_to, pe)) ->
          let@ () = WCT.is_ct act_from.loc act_from.ct in
          let@ () = WCT.is_ct act_to.loc act_to.ct in
          let@ pe = check_pexpr (Loc ()) pe in
          let bty = Memory.bt_of_sct act_to.ct in
          return (bty, M_Ememop (M_IntFromPtr (act_from, act_to, pe)))
        | M_Ememop (M_PtrFromInt (act_from, act_to, pe)) ->
          let@ () = WCT.is_ct act_from.loc act_from.ct in
          let@ () = WCT.is_ct act_to.loc act_to.ct in
          let from_bt = Memory.bt_of_sct act_from.ct in
          let@ pe = check_pexpr from_bt pe in
          let@ () = ensure_bits_type (loc_of_pexpr pe) from_bt in
          return (Loc (), M_Ememop (M_PtrFromInt (act_from, act_to, pe)))
        | M_Ememop (M_PtrValidForDeref (act, pe)) ->
          let@ () = WCT.is_ct act.loc act.ct in
          let@ pe = check_pexpr (Loc ()) pe in
          return (Bool, M_Ememop (M_PtrValidForDeref (act, pe)))
        | M_Ememop (M_PtrWellAligned (act, pe)) ->
          let@ () = WCT.is_ct act.loc act.ct in
          let@ pe = check_pexpr (Loc ()) pe in
          return (Bool, M_Ememop (M_PtrWellAligned (act, pe)))
        | M_Ememop (M_PtrArrayShift (pe1, act, pe2)) ->
          let@ () = WCT.is_ct act.loc act.ct in
          let@ pe1 = check_pexpr (Loc ()) pe1 in
          let@ pe2 = infer_pexpr pe2 in
          let@ () = ensure_bits_type (loc_of_pexpr pe2) (bt_of_pexpr pe2) in
          return (Loc (), M_Ememop (M_PtrArrayShift (pe1, act, pe2)))
        | M_Ememop (M_PtrMemberShift (tag_sym, memb_ident, pe)) ->
          let@ _ = get_struct_member_type loc tag_sym memb_ident in
          let@ pe = check_pexpr (Loc ()) pe in
          return (Loc (), M_Ememop (M_PtrMemberShift (tag_sym, memb_ident, pe)))
        | M_Ememop (M_Memcpy _) (* (asym 'bty * asym 'bty * asym 'bty) *) -> todo ()
        | M_Ememop (M_Memcmp _) (* (asym 'bty * asym 'bty * asym 'bty) *) -> todo ()
        | M_Ememop (M_Realloc _) (* (asym 'bty * asym 'bty * asym 'bty) *) -> todo ()
        | M_Ememop (M_Va_start _) (* (asym 'bty * asym 'bty) *) -> todo ()
        | M_Ememop (M_Va_copy _) (* (asym 'bty) *) -> todo ()
        | M_Ememop (M_Va_arg _) (* (asym 'bty * actype 'bty) *) -> todo ()
        | M_Ememop (M_Va_end _) (* (asym 'bty) *) -> todo ()
        | M_Ememop (M_CopyAllocId (pe1, pe2)) ->
          let@ pe1 = check_pexpr Memory.uintptr_bt pe1 in
          let@ pe2 = check_pexpr BT.(Loc ()) pe2 in
          return (Loc (), M_Ememop (M_CopyAllocId (pe1, pe2)))
        | M_Eaction (M_Paction (pol, M_Action (aloc, action_))) ->
          let@ bTy, action_ =
            match action_ with
            | M_Create (pe, act, prefix) ->
              let@ () = WCT.is_ct act.loc act.ct in
              let@ pe = check_pexpr signed_int_ty pe in
              let@ () = ensure_bits_type (loc_of_pexpr pe) (bt_of_pexpr pe) in
              return (Loc (), M_Create (pe, act, prefix))
            | M_Kill (k, pe) ->
              let@ () =
                match k with M_Dynamic -> return () | M_Static ct -> WCT.is_ct loc ct
              in
              let@ pe = check_pexpr (Loc ()) pe in
              return (Unit, M_Kill (k, pe))
            | M_Store (is_locking, act, p_pe, v_pe, mo) ->
              let@ () = WCT.is_ct act.loc act.ct in
              let@ p_pe = check_pexpr (Loc ()) p_pe in
              let@ v_pe = check_pexpr (Memory.bt_of_sct act.ct) v_pe in
              return (Unit, M_Store (is_locking, act, p_pe, v_pe, mo))
            | M_Load (act, p_pe, mo) ->
              let@ () = WCT.is_ct act.loc act.ct in
              let@ p_pe = check_pexpr (Loc ()) p_pe in
              return (Memory.bt_of_sct act.ct, M_Load (act, p_pe, mo))
            | _ -> todo ()
          in
          return (bTy, M_Eaction (M_Paction (pol, M_Action (aloc, action_))))
        | M_Eskip -> return (Unit, M_Eskip)
        | M_Eccall (act, f_pe, pes) ->
          let@ () = WCT.is_ct act.loc act.ct in
          let@ ret_ct, arg_cts =
            match act.ct with
            | Sctypes.(Pointer (Function (ret_v_ct, arg_r_cts, is_variadic))) ->
              assert (not is_variadic);
              return (snd ret_v_ct, List.map fst arg_r_cts)
            | _ ->
              fail (fun _ ->
                { loc;
                  msg =
                    Generic
                      (Pp.item "not a function pointer at call-site" (Sctypes.pp act.ct))
                })
          in
          let@ f_pe = check_pexpr (Loc ()) f_pe in
          (* TODO: we'd have to check the arguments against the function type, but we
             can't when f_pe is dynamic *)
          let arg_bt_specs = List.map (fun ct -> Memory.bt_of_sct ct) arg_cts in
          let@ pes = ListM.map2M check_pexpr arg_bt_specs pes in
          return (Memory.bt_of_sct ret_ct, M_Eccall (act, f_pe, pes))
        | M_Eif (c_pe, e1, e2) ->
          let@ c_pe = check_pexpr Bool c_pe in
          let@ bt, e1, e2 =
            if is_undef_or_error_expr e1 then
              let@ e2 = infer_expr label_context e2 in
              let bt = bt_of_expr e2 in
              let@ e1 = check_expr label_context bt e1 in
              return (bt, e1, e2)
            else
              let@ e1 = infer_expr label_context e1 in
              let bt = bt_of_expr e1 in
              let@ e2 = check_expr label_context bt e2 in
              return (bt, e1, e2)
          in
          return (bt, M_Eif (c_pe, e1, e2))
        | M_Ebound e ->
          let@ e = infer_expr label_context e in
          return (bt_of_expr e, M_Ebound e)
        | M_Elet (pat, pe, e) ->
          let@ pe = infer_pexpr pe in
          pure
            (let@ pat = check_and_bind_pattern (bt_of_pexpr pe) pat in
             let@ e = infer_expr label_context e in
             return (bt_of_expr e, M_Elet (pat, pe, e)))
        | M_Esseq (pat, e1, e2) | M_Ewseq (pat, e1, e2) ->
          let@ e1 = infer_expr label_context e1 in
          pure
            (let@ pat = check_and_bind_pattern (bt_of_expr e1) pat in
             let@ e2 = infer_expr label_context e2 in
             let e_ =
               match e_ with
               | M_Esseq _ -> M_Esseq (pat, e1, e2)
               | _ -> M_Ewseq (pat, e1, e2)
             in
             return (bt_of_expr e2, e_))
        | M_Eunseq es ->
          let@ es = ListM.mapM (infer_expr label_context) es in
          let bts = List.map bt_of_expr es in
          return (Tuple bts, M_Eunseq es)
        | M_Erun (l, pes) ->
          (* copying from check.ml *)
          let@ lt, _lkind =
            match SymMap.find_opt l label_context with
            | None ->
              fail (fun _ ->
                { loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp l) })
            | Some (lt, lkind, _) -> return (lt, lkind)
          in
          let@ pes =
            let wrong_number_arguments () =
              let has = List.length pes in
              let expect = AT.count_computational lt in
              fail (fun _ -> { loc; msg = Number_arguments { has; expect } })
            in
            let rec check_args lt pes =
              match (lt, pes) with
              | AT.Computational ((_s, bt), _info, lt'), pe :: pes' ->
                let@ pe = check_pexpr bt pe in
                let@ pes' = check_args lt' pes' in
                return (pe :: pes')
              | AT.L _lat, [] -> return []
              | _ -> wrong_number_arguments ()
            in
            check_args lt pes
          in
          return (Unit, M_Erun (l, pes))
        | M_CN_progs (surfaceprog, cnprogs) ->
          let@ cnprogs = ListM.mapM check_cnprog cnprogs in
          return (Unit, M_CN_progs (surfaceprog, cnprogs))
        | M_End _ -> todo ()
      in
      return (M_Expr (loc, annots, bty, e_))


  and check_expr label_context (expect : BT.t) expr =
    (* the special-case is needed for pure undef, whose type can't be inferred *)
    let (M_Expr (loc, annots, _, e_)) = expr in
    let@ () =
      match integer_annot annots with
      | Some ity when !use_ity ->
        ensure_base_type loc ~expect (Memory.bt_of_sct (Integer ity))
      | _ -> return ()
    in
    match e_ with
    | M_Epure pe ->
      let@ pe = check_pexpr expect pe in
      return (M_Expr (loc, annots, bt_of_pexpr pe, M_Epure pe))
    | _ ->
      let@ expr = infer_expr label_context expr in
      (match bt_of_expr expr with
       | Integer ->
         Pp.debug
           1
           (lazy (Pp.item "warning: inferred integer bt" (Pp_mucore_ast.pp_expr expr)))
       | _ -> ());
      let@ () = ensure_base_type (loc_of_expr expr) ~expect (bt_of_expr expr) in
      return expr
end

module WLabel = struct
  open Mu

  let typ l = WArgs.typ (fun _body -> False.False) l

  let welltyped (loc : Loc.t) (lt : _ mu_expr mu_arguments) : _ mu_expr mu_arguments m =
    WArgs.welltyped (fun _loc body -> return body) "loop/label" loc lt
end

module WProc = struct
  open Mu

  let label_context function_rt label_defs =
    Pmap.fold
      (fun sym def label_context ->
        let lt, kind, loc =
          match def with
          | M_Return loc ->
            (AT.of_rt function_rt (LAT.I False.False), CF.Annot.LAreturn, loc)
          | M_Label (loc, label_args_and_body, annots, _parsed_spec) ->
            let lt = WLabel.typ label_args_and_body in
            let kind = Option.get (CF.Annot.get_label_annot annots) in
            (lt, kind, loc)
        in
        (*debug 6 (lazy (!^"label type within function" ^^^ Sym.pp fsym)); debug 6 (lazy
          (CF.Pp_ast.pp_doc_tree (AT.dtree False.dtree lt)));*)
        SymMap.add sym (lt, kind, loc) label_context)
      label_defs
      SymMap.empty


  let typ p = WArgs.typ (fun (_body, _labels, rt) -> rt) p

  let welltyped
    :  (*'TY.*) Loc.t -> 'TY Mu.mu_proc_args_and_body ->
    _ (*BT.t*) Mu.mu_proc_args_and_body m
    =
    fun (loc : Loc.t) (at : 'TY1 Mu.mu_proc_args_and_body) ->
    Pp.(debug 6 (lazy !^__FUNCTION__));
    WArgs.welltyped
      (fun loc (body, labels, rt) ->
        let@ rt = pure_and_no_initial_resources loc (WRT.welltyped loc rt) in
        let@ labels =
          PmapM.mapM
            (fun _sym def ->
              match def with
              | M_Return loc -> return (M_Return loc)
              | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
                let@ label_args_and_body =
                  pure_and_no_initial_resources
                    loc
                    (WLabel.welltyped loc label_args_and_body)
                in
                return (M_Label (loc, label_args_and_body, annots, parsed_spec)))
            labels
            Sym.compare
        in
        let label_context = label_context rt labels in
        let@ labels =
          PmapM.mapM
            (fun _sym def ->
              match def with
              | M_Return loc -> return (M_Return loc)
              | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
                let@ label_args_and_body =
                  pure_and_no_initial_resources
                    loc
                    (WArgs.welltyped
                       (fun _loc label_body ->
                         BaseTyping.check_expr label_context Unit label_body)
                       "label"
                       loc
                       label_args_and_body)
                in
                return (M_Label (loc, label_args_and_body, annots, parsed_spec)))
            labels
            Sym.compare
        in
        let@ body = pure (BaseTyping.check_expr label_context Unit body) in
        return (body, labels, rt))
      "function"
      loc
      at
end

module WRPD = struct
  open ResourcePredicates

  let welltyped { loc; pointer; iargs; oarg_bt; clauses } =
    (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
    pure
      (let@ () = add_l pointer BT.(Loc ()) (loc, lazy (Pp.string "ptr-var")) in
       let@ iargs =
         ListM.mapM
           (fun (s, ls) ->
             let@ ls = WLS.is_ls loc ls in
             let@ () = add_l s ls (loc, lazy (Pp.string "input-var")) in
             return (s, ls))
           iargs
       in
       let@ oarg_bt = WBT.is_bt loc oarg_bt in
       let@ clauses =
         match clauses with
         | None -> return None
         | Some clauses ->
           let@ clauses =
             ListM.fold_leftM
               (fun acc { loc; guard; packing_ft } ->
                 let@ guard = WIT.check loc BT.Bool guard in
                 let here = Locations.other __FUNCTION__ in
                 let negated_guards =
                   List.map (fun clause -> IT.not_ clause.guard here) acc
                 in
                 pure
                   (let@ () = add_c loc (LC.t_ guard) in
                    let@ () = add_c loc (LC.t_ (IT.and_ negated_guards here)) in
                    let@ packing_ft =
                      WLAT.welltyped
                        (fun loc it -> WIT.check loc oarg_bt it)
                        IT.pp
                        "clause"
                        loc
                        packing_ft
                    in
                    return (acc @ [ { loc; guard; packing_ft } ])))
               []
               clauses
           in
           return (Some clauses)
       in
       return { loc; pointer; iargs; oarg_bt; clauses })
end

module WLFD = struct
  open LogicalFunctions

  let welltyped
    ({ loc; args; return_bt; emit_coq; definition } : LogicalFunctions.definition)
    =
    (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
    pure
      (let@ args =
         ListM.mapM
           (fun (s, ls) ->
             let@ ls = WLS.is_ls loc ls in
             let@ () = add_l s ls (loc, lazy (Pp.string "arg-var")) in
             return (s, ls))
           args
       in
       let@ return_bt = WBT.is_bt loc return_bt in
       let@ definition =
         match definition with
         | Def body ->
           let@ body = WIT.check loc return_bt body in
           return (Def body)
         | Rec_Def body ->
           let@ body = WIT.check loc return_bt body in
           return (Rec_Def body)
         | Uninterp -> return Uninterp
       in
       return { loc; args; return_bt; emit_coq; definition })
end

module WLemma = struct
  let welltyped loc _lemma_s lemma_typ =
    WAT.welltyped
      (fun loc lrt -> pure_and_no_initial_resources loc (WLRT.welltyped loc lrt))
      LRT.pp
      "lemma"
      loc
      lemma_typ
end

module WDT = struct
  open Mu

  let welltyped (dt_name, { loc; cases }) =
    let@ _ =
      (* all argument members disjoint *)
      ListM.fold_leftM
        (fun already (id, _) ->
          if IdSet.mem id already then
            (* this should have been checked earlier in compile.ml *)
            assert false
          else
            return (IdSet.add id already))
        IdSet.empty
        (List.concat_map snd cases)
    in
    let@ cases =
      ListM.mapM
        (fun (c, args) ->
          let@ args =
            ListM.mapM
              (fun (id, bt) ->
                let@ bt = WBT.is_bt loc bt in
                return (id, bt))
              (List.sort compare_by_fst_id args)
          in
          return (c, args))
        cases
    in
    return (dt_name, { loc; cases })


  module G = Graph.Persistent.Digraph.Concrete (Sym)
  module Components = Graph.Components.Make (G)

  (* Z3 (possibly other solvers, too) does not permit types where in the definition of a
     type t, t is used inside an array, e.g. an integer-t-array. We forbid this here. *)

  let bts_in_dt_constructor_argument (_name, bt) = bt :: BT.contained bt

  let bts_in_dt_case (_constr, args) = List.concat_map bts_in_dt_constructor_argument args

  let bts_in_dt_definition { loc = _; cases } = List.concat_map bts_in_dt_case cases

  let dts_in_dt_definition dt_def =
    List.filter_map BT.is_datatype_bt (bts_in_dt_definition dt_def)


  let check_recursion_ok datatypes =
    let graph = G.empty in
    let graph =
      List.fold_left (fun graph (dt, _) -> G.add_vertex graph dt) graph datatypes
    in
    let graph =
      List.fold_left
        (fun graph (dt, dt_def) ->
          List.fold_left
            (fun graph dt' -> G.add_edge graph dt dt')
            graph
            (dts_in_dt_definition dt_def))
        graph
        datatypes
    in
    let sccs = Components.scc_list graph in
    let@ () =
      ListM.iterM
        (fun scc ->
          let scc_set = SymSet.of_list scc in
          ListM.iterM
            (fun dt ->
              let { loc; cases } = List.assoc Sym.equal dt datatypes in
              ListM.iterM
                (fun (_ctor, args) ->
                  ListM.iterM
                    (fun (id, bt) ->
                      let indirect_deps =
                        SymSet.of_list
                          (List.filter_map BT.is_datatype_bt (BT.contained bt))
                      in
                      let bad = SymSet.inter indirect_deps scc_set in
                      match SymSet.elements bad with
                      | [] -> return ()
                      | dt' :: _ ->
                        let err =
                          !^"Illegal datatype definition."
                          ^/^ !^"Constructor argument"
                          ^^^ squotes (Id.pp id)
                          ^^^ !^"is given type"
                          ^^^ squotes (BT.pp bt)
                          ^^ comma
                          ^^^ !^"which indirectly refers to"
                          ^^^ squotes (BT.pp (Datatype dt'))
                          ^^ dot
                          ^/^ !^"Indirect recursion via map, set, record,"
                          ^^^ !^"or tuple types is not permitted."
                        in
                        fail (fun _ -> { loc; msg = Generic err }))
                    args)
                cases)
            scc)
        sccs
    in
    return sccs
end
