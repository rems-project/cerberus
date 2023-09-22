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
module IdSet = Set.Make(Id)

open Global
open TE
open Pp
open Locations


open Typing
open Effectful.Make(Typing)


let ensure_base_type = Typing.ensure_base_type

let illtyped_index_term (loc: loc) it has expected ctxt =
  {loc = loc; msg = TypeErrors.Illtyped_it {it = IT.pp it; has = BT.pp has; expected; o_ctxt = Some ctxt}}


let ensure_bits_type (loc : loc) (has : BT.t) = 
  match has with
  | BT.Bits (sign,n) -> return ()
  | has -> 
     fail (fun _ -> {loc; msg = Mismatch {has = BT.pp has; expect = !^"bitvector"}})

let ensure_arith_type (loc : loc) it =
  let open BT in
  match IT.bt it with
  | (Integer | Real | Bits _) -> return ()
  | _ ->
     let expect = "integer, real or bitvector type" in
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




let compare_by_member_id (id,_) (id',_) = Id.compare id id'


let no_duplicate_members loc (have : (Id.t * 'a) list) =
  let _already = 
    ListM.fold_leftM (fun already (id, _) ->
        if IdSet.mem id already 
        then fail (fun _ -> {loc; msg = Duplicate_member id})
        else return (IdSet.add id already)
      ) IdSet.empty have
  in
  return ()

let no_duplicate_members_sorted loc have = 
  let@ () = no_duplicate_members loc have in
  return (List.sort compare_by_member_id have)


let correct_members loc (spec : (Id.t * 'a) list) (have : (Id.t * 'b) list) =
  let needed = IdSet.of_list (List.map fst spec) in
  let already = IdSet.empty in
  let@ needed, already =
    ListM.fold_leftM (fun (needed, already) (id, _) ->
        if IdSet.mem id already then
          fail (fun _ -> {loc; msg = Duplicate_member id})
        else if IdSet.mem id needed then
          return (IdSet.remove id needed, IdSet.add id already)
        else
          fail (fun _ -> {loc; msg = Unexpected_member (List.map fst spec, id)})
      ) (needed, already) have
  in
  match IdSet.elements needed with
  | [] -> return ()
  | missing :: _ -> fail (fun _ -> {loc; msg = Missing_member missing})

let correct_members_sorted_annotated loc spec have = 
  let@ () = correct_members loc spec have in
  let have = List.sort compare_by_member_id have in
  let have_annotated = 
    List.map2 (fun (id,bt) (id',x) ->
        assert (Id.equal id id');
        (bt, (id', x))
      ) spec have
  in
  return have_annotated
  




module WBT = struct

  open BT
  let is_bt loc = 
    let rec aux = function
      | Unit -> 
         return Unit
      | Bool -> 
         return Bool
      | Integer -> 
         return Integer
      | Bits (sign, n) ->
         return (Bits (sign, n))
      | Real -> 
         return Real
      | Alloc_id -> 
         return Alloc_id
      | Loc -> 
         return Loc
      | CType -> 
         return CType
      | Struct tag -> 
         let@ _struct_decl = get_struct_decl loc tag in 
         return (Struct tag)
      | Datatype tag -> 
         let@ _datatype = get_datatype loc tag in 
         return (Datatype tag)
      | Record members -> 
         let@ members = 
           ListM.mapM (fun (id, bt) -> 
               let@ bt = aux bt in
               return (id, bt)
             ) members
         in
         let@ members = no_duplicate_members_sorted loc members in
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

  
  (* let rec check_and_bind_pattern loc bt pat =  *)
  (*   match pat with *)
  (*   | PSym s ->  *)
       

  let rec check_and_bind_pattern loc bt (Pat (pat_, _)) =
    match pat_ with
    | PSym s -> 
       let@ () = add_l s bt (loc, lazy (Sym.pp s)) in
       return (Pat (PSym s, bt))
    | PWild ->
       return (Pat (PWild, bt))
    | PConstructor (s, args) ->
       let@ info = get_datatype_constr loc s in
       let@ () = ensure_base_type loc ~expect:bt (Datatype info.c_datatype_tag) in
       let@ args_annotated = correct_members_sorted_annotated loc info.c_params args in
       let@ args = 
         ListM.mapM (fun (bt', (id', pat')) ->
             let@ pat' = check_and_bind_pattern loc bt' pat' in
             return (id', pat')
           ) args_annotated
       in
       return (Pat (PConstructor (s, args), bt))

  let leading_sym_or_wild = function
    | [] -> assert false
    | Pat (pat_, _) :: _ ->
       match pat_ with
       | PSym _ -> true
       | PWild -> true
       | PConstructor _ -> false

  let expand_constr (constr, constr_info) (case : (BT.t pattern) list) = 
    match case with
    | Pat (PWild, _) :: pats
    | Pat (PSym _, _) :: pats ->
       Some (List.map (fun (_m, bt) -> Pat (PWild, bt)) constr_info.c_params @ pats)
    | Pat (PConstructor (constr', args), _) :: pats 
         when Sym.equal constr constr' ->
       assert (List.for_all2 (fun (m,_) (m',_) -> Id.equal m m') constr_info.c_params args);
       Some (List.map snd args @ pats)
    | Pat (PConstructor (constr', args), _) :: pats ->
       None
    | [] ->
       assert false

       

  (* copying and adjusting Neel Krishnaswami's pattern.ml code *)
  let rec cases_complete loc (bts : BT.t list) (cases : ((BT.t pattern) list) list) =
    match bts with
    | [] -> 
       assert (List.for_all (function [] -> true | _ -> false) cases);
       begin match cases with
       | [] -> fail (fun _ -> {loc; msg = Generic !^"Incomplete pattern"})
       | _ -> return ()
       (* | [_(\*[]*\)] -> return () *)
       (* | _::_::_ -> fail (fun _ -> {loc; msg = Generic !^"Duplicate pattern"}) *)
       end
    | bt::bts ->
       if List.for_all leading_sym_or_wild cases then
         cases_complete loc bts (List.map List.tl cases)
       else
         begin match bt with
         | (Unit|Bool|Integer|Bits _|Real|Alloc_id|Loc|CType|Struct _|
            Record _|Map _|List _|Tuple _|Set _) ->
            failwith "revisit for extended pattern language"
         | Datatype s ->
            let@ dt_info = get_datatype loc s in
            ListM.iterM (fun constr ->
                let@ constr_info = get_datatype_constr loc constr  in
                let relevant_cases = 
                  List.filter_map (expand_constr (constr, constr_info)) cases in
                let member_bts = List.map snd constr_info.c_params in
                cases_complete loc (member_bts @ bts) relevant_cases
              ) dt_info.dt_constrs
         end

  let rec infer : 'bt. Loc.t -> 'bt term -> (BT.t term) m =
      fun loc (IT (it, _)) ->
      match it with
      | Sym s ->
         let@ is_a = bound_a s in
         let@ is_l = bound_l s in
         let@ binding = match () with
           | () when is_a -> get_a s
           | () when is_l -> get_l s
           | () -> fail (fun _ -> {loc; msg = TE.Unknown_variable s})
         in
         begin match binding with
         | BaseType bt -> return (IT (Sym s, bt))
         | Value it -> return it
         end
      | Const (Z z) ->
         return (IT (Const (Z z), Integer))
      | Const (Bits ((sign,n),v) as c) ->
         return (IT (Const c, BT.Bits (sign,n)))
      | Const (Q q) ->
         return (IT (Const (Q q), Real))
      | Const (Pointer p) ->
         return (IT (Const (Pointer p), Loc))
      | Const (Alloc_id p) ->
         return (IT (Const (Alloc_id p), BT.Alloc_id))
      | Const (Bool b) ->
         return (IT (Const (Bool b), BT.Bool))
      | Const Unit ->
         return (IT (Const Unit, BT.Unit))
      | Const (Default bt) -> 
         let@ bt = WBT.is_bt loc bt in
         return (IT (Const (Default bt), bt))
      | Const Null ->
         return (IT (Const Null, BT.Loc))
      | Const (CType_const ct) ->
         return (IT (Const (CType_const ct), BT.CType))
      | Unop (unop, t) ->
         let (arg_bt, ret_bt) = match unop with
         | Not -> (BT.Bool, BT.Bool)
         | BWCLZNoSMT
         | BWCTZNoSMT
         | BWFFSNoSMT -> (BT.Integer, BT.Integer)
         in
         let@ t = check loc arg_bt t in
         return (IT (Unop (unop, t), ret_bt))
      | Binop (arith_op, t, t') ->
         begin match arith_op with
         | Add ->
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (Add, t, t'), IT.bt t))
         | Sub ->
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (Sub, t, t'), IT.bt t))
         | Mul ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            begin match (IT.bt t), (eval simp_ctxt t), (eval simp_ctxt t') with
            | Real, _, _ -> 
               return (IT (Binop (Mul, t, t'), IT.bt t))
            | Integer, simp_t, simp_t' when 
                   Option.is_some (is_const simp_t) 
                   || Option.is_some (is_const simp_t') ->
               return (IT (Binop (Mul, simp_t, simp_t'), IT.bt t))
            | _ ->
               let hint = "Integer multiplication only allowed when one of the arguments is a constant" in
               fail (fun ctxt -> {loc; msg = NIA {it = IT.mul_ (t, t'); ctxt; hint}})
            end
         | MulNoSMT ->
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (MulNoSMT, t, t'), IT.bt t))
         | Div ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            begin match IT.bt t, eval simp_ctxt t' with
            | Real, _ ->
               return (IT (Binop (Div, t, t'), IT.bt t))
            | Integer, simp_t' when Option.is_some (is_const simp_t') ->
               let z = Option.get (is_z simp_t') in
               let@ () = if Z.lt Z.zero z then return ()
                 else fail (fun _ -> {loc; msg = Generic
                   (!^"Divisor " ^^^ IT.pp t' ^^^ !^ "must be positive")}) in
               return (IT (Binop (Div, t, simp_t'), IT.bt t))
            | _ ->
               let hint = "Integer division only allowed when divisor is constant" in
               fail (fun ctxt -> {loc; msg = NIA {it = div_ (t, t'); ctxt; hint}})
            end
         | DivNoSMT ->
            let@ t = infer loc t in
            let@ () = ensure_arith_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (DivNoSMT, t, t'), IT.bt t))
         | Exp ->
            let@ simp_ctxt = simp_ctxt () in
            let@ t = check loc Integer t in
            let@ t' = check loc Integer t' in
            begin match is_z (eval simp_ctxt t), is_z (eval simp_ctxt t') with
            | Some _, Some z' when Z.lt z' Z.zero ->
               fail (fun ctxt -> {loc; msg = NegativeExponent {it = exp_ (t, t'); ctxt}})
            | Some _, Some z' when not (Z.fits_int32 z') ->
               fail (fun ctxt -> {loc; msg = TooBigExponent {it = exp_ (t, t'); ctxt}})
            | Some z, Some z' ->
               return (IT (Binop (Exp, z_ z, z_ z'), Integer))
            | _ ->
               let hint = "Only exponentiation of two constants is allowed" in
               fail (fun ctxt -> {loc; msg = NIA {it = exp_ (t, t'); ctxt; hint}})
            end
           | ExpNoSMT
           | RemNoSMT
           | ModNoSMT
           | XORNoSMT
           | BWAndNoSMT
           | BWOrNoSMT ->
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              return (IT (Binop (arith_op, t, t'), Integer))
           | Rem ->
              let@ simp_ctxt = simp_ctxt () in
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              begin match is_z (eval simp_ctxt t') with
              | None ->
                 let hint = "Only division (rem) by constants is allowed" in
                 fail (fun ctxt -> {loc; msg = NIA {it = rem_ (t, t'); ctxt; hint}})
              | Some z' ->
                 return (IT (Binop (Rem, t, z_ z'), Integer))
              end
           | Mod ->
              let@ simp_ctxt = simp_ctxt () in
              let@ t = check loc Integer t in
              let@ t' = check loc Integer t' in
              begin match is_z (eval simp_ctxt t') with
              | None ->
                 let hint = "Only division (mod) by constants is allowed" in
                 fail (fun ctxt -> {loc; msg = NIA {it = mod_ (t, t'); ctxt; hint}})
              | Some z' ->
                 return (IT (Binop (Mod, t, z_ z'), Integer))
              end
           | LT ->
              let@ t = infer loc t in
              let@ () = ensure_arith_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Binop (LT, t, t'), BT.Bool))
           | LE ->
              let@ t = infer loc t in
              let@ () = ensure_arith_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Binop (LE, t, t'), BT.Bool))
           | Min ->
              let@ t = infer loc t in
              let@ () = ensure_arith_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Binop (Min, t, t'), IT.bt t))
           | Max ->
              let@ t = infer loc t in
              let@ () = ensure_arith_type loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Binop (Max, t, t'), IT.bt t))
           | EQ ->
              let@ t = infer loc t in
              let@ t' = check loc (IT.bt t) t' in
              return (IT (Binop (EQ, t,t'),BT.Bool))
           | LTPointer ->
              let@ t = check loc Loc t in
              let@ t' = check loc Loc t' in
              return (IT (Binop (LTPointer, t, t'),BT.Bool))
           | LEPointer ->
              let@ t = check loc Loc t in
              let@ t' = check loc Loc t' in
              return (IT (Binop (LEPointer, t, t'),BT.Bool))
         | SetMember ->
            let@ t = infer loc t in
            let@ t' = check loc (Set (IT.bt t)) t' in
            return (IT (Binop (SetMember, t, t'), BT.Bool))
         | SetUnion ->
            let@ t = infer loc t in
            let@ _itembt = ensure_set_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (SetUnion, t, t'), IT.bt t))
         | SetIntersection ->
            let@ t = infer loc t in
            let@ _itembt = ensure_set_type loc t in
            let@ t' = check loc (IT.bt t) t' in
            return (IT (Binop (SetIntersection, t, t'), IT.bt t))
         | SetDifference ->
            let@ t  = infer loc t in
            let@ itembt = ensure_set_type loc t in
            let@ t' = check loc (Set itembt) t' in
            return (IT (Binop (SetDifference, t, t'), BT.Set itembt))
         | Subset ->
            let@ t = infer loc t in
            let@ itembt = ensure_set_type loc t in
            let@ t' = check loc (Set itembt) t' in
            return (IT (Binop (Subset, t,t'), BT.Bool))
         | And ->
            let@ t = check loc Bool t in
            let@ t' = check loc Bool t' in
            return (IT (Binop (And, t, t'), Bool))
         | Or -> 
            let@ t = check loc Bool t in
            let@ t' = check loc Bool t' in
            return (IT (Binop (Or, t, t'), Bool))
         | Impl ->
            let@ t = check loc Bool t in
            let@ t' = check loc Bool t' in
            return (IT (Binop (Impl, t, t'), Bool))
         end
      | ITE (t,t',t'') ->
         let@ t = check loc Bool t in
         let@ t' = infer loc t' in
         let@ t'' = check loc (IT.bt t') t'' in
         return (IT (ITE (t, t', t''),IT.bt t')) 
      | EachI ((i1, (s, _), i2), t) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, t = IT.alpha_rename (s, BT.Integer) t in *)
         pure begin 
             let@ () = add_l s Integer (loc, lazy (Pp.string "forall-var")) in
             let@ t = check loc Bool t in
             return (IT (EachI ((i1, (s, BT.Integer), i2), t),BT.Bool))
           end
      | Tuple ts ->
         let@ ts = ListM.mapM (infer loc) ts in
         let bts = List.map IT.bt ts in
         return (IT (Tuple ts,BT.Tuple bts))
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
         return (IT (NthTuple (n, t'),item_bt))
      | Struct (tag, members) ->
         let@ layout = get_struct_decl loc tag in
         let decl_members = Memory.member_types layout in
         let@ () = correct_members loc decl_members members in
         (* "sort" according to declaration *)
         let@ members_sorted = 
           ListM.mapM (fun (id, ct) ->
               let@ t = check loc (Memory.bt_of_sct ct) (List.assoc Id.equal id members) in
               return (id, t)
             ) decl_members
         in
         assert (List.length members_sorted = List.length members);
         return (IT (Struct (tag, members_sorted), BT.Struct tag))
      | StructMember (t, member) ->
         let@ t = infer loc t in
         let@ tag = match IT.bt t with
           | Struct tag -> return tag
           | has -> fail (illtyped_index_term loc t has "struct")
         in
         let@ field_ct = get_struct_member_type loc tag member in
         return (IT (StructMember (t, member),Memory.bt_of_sct field_ct))
      | StructUpdate ((t, member), v) ->
         let@ t = infer loc t in
         let@ tag = match IT.bt t with
           | Struct tag -> return tag
           | has -> fail (illtyped_index_term loc t has "struct")
         in
         let@ field_ct = get_struct_member_type loc tag member in
         let@ v = check loc (Memory.bt_of_sct field_ct) v in
         return (IT (StructUpdate ((t, member), v),BT.Struct tag))
      | Record members ->
         let@ members = no_duplicate_members_sorted loc members in
         let@ members = 
           ListM.mapM (fun (id, t) ->
               let@ t = infer loc t in
               return (id, t)
             ) members
         in
         let member_types = List.map (fun (id, t) -> (id, IT.bt t)) members in
         return (IT (IT.Record members,BT.Record member_types))
      | RecordMember (t, member) ->
         let@ t = infer loc t in
         let@ members = match IT.bt t with
           | Record members -> return members
           | has -> fail (illtyped_index_term loc t has "struct")
         in
         let@ bt = match List.assoc_opt Id.equal member members with
           | Some bt -> return bt
           | None -> 
              let expected = "struct with member " ^ Id.pp_string member in
              fail (illtyped_index_term loc t (IT.bt t) expected)
         in
         return (IT (RecordMember (t, member), bt))
      | RecordUpdate ((t, member), v) ->
         let@ t = infer loc t in
         let@ members = match IT.bt t with
           | Record members -> return members
           | has -> fail (illtyped_index_term loc t has "struct")
         in
         let@ bt = match List.assoc_opt Id.equal member members with
           | Some bt -> return bt
           | None -> 
              let expected = "struct with member " ^ Id.pp_string member in
              fail (illtyped_index_term loc t (IT.bt t) expected)
         in
         let@ v = check loc bt v in
         return (IT (RecordUpdate ((t, member), v),IT.bt t))
       | Cast (cbt, t) ->
          let@ cbt = WBT.is_bt loc cbt in
          let@ t = infer loc t in
          let@ () = match IT.bt t, cbt with
            | Integer, Loc ->
              let msg = !^"Deprecated cast from integer to pointer." ^^^
                        !^"Please use copy_alloc_id instead."
              in
              Pp.warn loc msg; return ()
           | Loc, Integer -> return ()
           | Integer, Real -> return ()
           | Real, Integer -> return ()
           | Bits (sign,n), Bits (sign',n') when not (equal_sign sign sign' ) && n = n' -> return ()
           | source, target -> 
             let msg = 
               !^"Unsupported cast from" ^^^ BT.pp source
               ^^^ !^"to" ^^^ BT.pp target ^^ dot
             in
             fail (fun _ -> {loc; msg = Generic msg})
          in
          return (IT (Cast (cbt, t), cbt))
       | MemberOffset (tag, member) ->
          let@ _ty = get_struct_member_type loc tag member in
          return (IT (MemberOffset (tag, member),Integer))
       | ArrayOffset (ct, t) ->
          let@ () = WCT.is_ct loc ct in
          let@ t = check loc Integer t in
          return (IT (ArrayOffset (ct, t), Integer))
       | SizeOf ct ->
          let@ () = WCT.is_ct loc ct in
          return (IT (SizeOf ct, Integer))
       | Aligned t ->
          let@ t_t = check loc Loc t.t in
          let@ t_align = check loc Integer t.align in
          return (IT (Aligned {t = t_t; align=t_align},BT.Bool))
       | Representable (ct, t) ->
          let@ () = WCT.is_ct loc ct in
          let@ t = check loc (Memory.bt_of_sct ct) t in
          return (IT (Representable (ct, t),BT.Bool))
       | Good (ct, t) ->
          let@ () = WCT.is_ct loc ct in
          let@ t = check loc (Memory.bt_of_sct ct) t in
          return (IT (Good (ct, t),BT.Bool))
       | WrapI (ity, t) ->
          let@ () = WCT.is_ct loc (Integer ity) in
          let@ t = check loc Integer t in
          return (IT (WrapI (ity, t), BT.Integer))
       | Nil bt -> 
          let@ bt = WBT.is_bt loc bt in
          return (IT (Nil bt, BT.List bt))
       | Cons (t1,t2) ->
          let@ t1 = infer loc t1 in
          let@ t2 = check loc (List (IT.bt t1)) t2 in
          return (IT (Cons (t1, t2),BT.List (IT.bt t1)))
       | Head t ->
          let@ t = infer loc t in
          let@ bt = ensure_list_type loc t in
          return (IT (Head t,bt))
       | Tail t ->
          let@ t = infer loc t in
          let@ bt = ensure_list_type loc t in
          return (IT (Tail t,BT.List bt))
       | NthList (i, xs, d) ->
          let@ i = check loc Integer i in
          let@ xs = infer loc xs in
          let@ bt = ensure_list_type loc xs in
          let@ d = check loc bt d in
          return (IT (NthList (i, xs, d),bt))
       | ArrayToList (arr, i, len) ->
          let@ i = check loc Integer i in
          let@ len = check loc Integer len in
          let@ arr = infer loc arr in
          let@ (_, bt) = ensure_map_type loc arr in
          return (IT (ArrayToList (arr, i, len), BT.List bt))
      | MapConst (index_bt, t) ->
         let@ index_bt = WBT.is_bt loc index_bt in
         let@ t = infer loc t in
         return (IT (MapConst (index_bt, t), BT.Map (index_bt, IT.bt t)))
      | MapSet (t1, t2, t3) ->
         let@ t1 = infer loc t1 in
         let@ (abt, rbt) = ensure_map_type loc t1 in
         let@ t2 = check loc abt t2 in
         let@ t3 = check loc rbt t3 in
         return (IT (MapSet (t1, t2, t3), IT.bt t1))
      | MapGet (t, arg) -> 
         let@ t = infer loc t in
         let@ (abt, bt) = ensure_map_type loc t in
         let@ arg = check loc abt arg in
         return (IT (MapGet (t, arg),bt))
      | MapDef ((s, abt), body) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, body = IT.alpha_rename (s, abt) body in *)
         let@ abt = WBT.is_bt loc abt in
         pure begin
            let@ () = add_l s abt (loc, lazy (Pp.string "map-def-var")) in
            let@ body = infer loc body in
            return (IT (MapDef ((s, abt), body), Map (abt, IT.bt body)))
            end
      | Apply (name, args) ->
         let@ def = Typing.get_logical_function_def loc name in
         let has_args, expect_args = List.length args, List.length def.args in
         let@ () = ensure_same_argument_number loc `General has_args ~expect:expect_args in
         let@ args = 
           ListM.map2M (fun has_arg (_, def_arg_bt) ->
               check loc def_arg_bt has_arg
             ) args def.args
         in
         return (IT (Apply (name, args), def.return_bt))
      | Let ((name, t1), t2) ->
         let@ t1 = infer loc t1 in
         pure begin
             let@ () = add_l name (IT.bt t1) (loc, lazy (Pp.string "let-var")) in
             let@ () = add_c loc (LC.t_ (IT.def_ name t1)) in
             let@ t2 = infer loc t2 in
             return (IT (Let ((name, t1), t2), IT.bt t2))
           end
      | Constructor (s, args) ->
         let@ info = get_datatype_constr loc s in
         let@ args_annotated = correct_members_sorted_annotated loc info.c_params args in
         let@ args = 
           ListM.mapM (fun (bt', (id', t')) ->
               let@ t' = check loc bt' t' in
               return (id', t')
             ) args_annotated
         in
         return (IT (Constructor (s, args), Datatype info.c_datatype_tag))
      | Match (e, cases) ->
         let@ e = infer loc e in
         let@ rbt, cases = 
           ListM.fold_leftM (fun (rbt, acc) (pat, body) ->
               pure begin
                   let@ pat = check_and_bind_pattern loc (IT.bt e) pat in
                   let@ body = match rbt with
                     | None -> infer loc body 
                     | Some rbt -> check loc rbt body
                   in
                   return (Some (IT.bt body), acc @ [(pat, body)])
                 end
             ) (None, []) cases
         in
         let@ () = cases_complete loc [IT.bt e] (List.map (fun (pat, _) -> [pat]) cases) in
         let@ rbt = match rbt with
           | None -> fail (fun _ -> {loc; msg = Empty_pattern})
           | Some rbt -> return rbt
         in
         return (IT (Match (e, cases), rbt))


    and check loc ls it =
      let@ ls = WLS.is_ls loc ls in
      let@ it = infer loc it in
      if LS.equal ls (IT.bt it) 
      then return it
      else fail (illtyped_index_term loc it (IT.bt it) (Pp.plain (LS.pp ls)))



end








module WRET = struct

  open IndexTerms

  let welltyped loc r = 
    let@ spec_iargs = match RET.predicate_name r with
      | Owned (_ct,_init) ->
         return []
      | PName name -> 
         let@ def = Typing.get_resource_predicate_def loc name in
         return def.iargs
    in
    match r with
    | P p -> 
       let@ pointer = WIT.check loc BT.Loc p.pointer in
       let has_iargs, expect_iargs = List.length p.iargs, List.length spec_iargs in
       (* +1 because of pointer argument *)
       let@ () = ensure_same_argument_number loc `Input (1 + has_iargs) ~expect:(1 + expect_iargs) in
       let@ iargs = ListM.map2M (fun (_, expected) arg -> WIT.check loc expected arg) spec_iargs p.iargs in
       return (RET.P {name = p.name; pointer; iargs})
    | Q p ->
       (* no need to alpha-rename, because context.ml ensures
          there's no name clashes *)
       (* let p = RET.alpha_rename_qpredicate_type p in *)
       let@ pointer = WIT.check loc BT.Loc p.pointer in
       let@ step = WIT.check loc BT.Integer p.step in
       let@ simp_ctxt = simp_ctxt () in
       let@ step = match IT.is_z (Simplify.IndexTerms.eval simp_ctxt step) with
         | Some z ->
           let@ () = if Z.lt Z.zero z then return ()
           else fail (fun _ -> {loc; msg = Generic
             (!^"Iteration step" ^^^ IT.pp p.step ^^^ !^ "must be positive")}) in
           return (IT.z_ z)
         | None ->
           let hint = "Only constant iteration steps are allowed" in
           fail (fun ctxt -> {loc; msg = NIA {it = p.step; ctxt; hint}})
       in
       let@ () = match p.name with
         | (Owned (ct, _init)) ->
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



let oarg_bt_of_pred loc = function
  | RET.Owned (ct,_init) -> 
      return (Memory.bt_of_sct ct)
  | RET.PName pn ->
      let@ def = Typing.get_resource_predicate_def loc pn in
      return def.oarg_bt
      

let oarg_bt loc = function
  | RET.P pred -> 
      oarg_bt_of_pred loc pred.name
  | RET.Q pred ->
      let@ item_bt = oarg_bt_of_pred loc pred.name in
      return (BT.make_map_bt Integer item_bt)






module WRS = struct

  let welltyped loc (resource, bt) = 
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
       (* no need to alpha-rename, because context.ml ensures
          there's no name clashes *)
       let@ bt = WBT.is_bt loc bt in
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
         let@ () = add_c (fst info) (LC.t_ (IT.def_ s it)) in
         let@ lrt = aux lrt in
         return (Define ((s, it), info, lrt))
      | Resource ((s, (re, re_oa_spec)), info, lrt) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, lrt = LRT.alpha_rename (s, re_oa_spec) lrt in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ lrt = aux lrt in
         return (Resource ((s, (re, re_oa_spec)), info, lrt))
      | Constraint (lc, info, lrt) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c (fst info) lc in
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
         let@ bt = WBT.is_bt (fst info) bt in
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


module WLAT = struct

  let welltyped i_subst i_welltyped kind loc (at : 'i LAT.t) : ('i LAT.t) m = 
    let rec aux = function
      | LAT.Define ((s, it), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, IT.bt it) at in *)
         let@ it = WIT.infer loc it in
         let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
         let@ () = add_c (fst info) (LC.t_ (IT.def_ s it)) in
         let@ at = aux at in
         return (LAT.Define ((s, it), info, at))
      | LAT.Resource ((s, (re, re_oa_spec)), info, at) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, re_oa_spec) at in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ at = aux at in
         return (LAT.Resource ((s, (re, re_oa_spec)), info, at))
      | LAT.Constraint (lc, info, at) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c (fst info) lc in
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

  let welltyped i_subst i_welltyped kind loc (at : 'i AT.t) : ('i AT.t) m = 
    let rec aux = function
      | AT.Computational ((name,bt), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let name, at = AT.alpha_rename i_subst (name, bt) at in *)
         let@ bt = WBT.is_bt (fst info) bt in
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

  let rec typ ityp = function
    | Mu.M_Define (bound, info, lat) ->
       LAT.Define (bound, info, typ ityp lat)
    | Mu.M_Resource (bound, info, lat) ->
       LAT.Resource (bound, info, typ ityp lat)
    | Mu.M_Constraint (lc, info, lat) ->
       LAT.Constraint (lc, info, typ ityp lat)
    | Mu.M_I i ->
       LAT.I (ityp i)

  let welltyped 
        (i_welltyped : Loc.t -> 'i -> 'j m)
        kind
        loc
        (at : 'i Mu.mu_arguments_l)
      : ('j Mu.mu_arguments_l) m = 
    let rec aux = function
      | Mu.M_Define ((s, it), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, IT.bt it) at in *)
         let@ it = WIT.infer loc it in
         let@ () = add_l s (IT.bt it) (loc, lazy (Pp.string "let-var")) in
         let@ () = add_c (fst info) (LC.t_ (IT.def_ s it)) in
         let@ at = aux at in
         return (Mu.M_Define ((s, it), info, at))
      | Mu.M_Resource ((s, (re, re_oa_spec)), info, at) -> 
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let s, at = LAT.alpha_rename i_subst (s, re_oa_spec) at in *)
         let@ (re, re_oa_spec) = WRS.welltyped (fst info) (re, re_oa_spec) in
         let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
         let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec))) in
         let@ at = aux at in
         return (Mu.M_Resource ((s, (re, re_oa_spec)), info, at))
      | Mu.M_Constraint (lc, info, at) ->
         let@ lc = WLC.welltyped (fst info) lc in
         let@ () = add_c (fst info) lc in
         let@ at = aux at in
         return (Mu.M_Constraint (lc, info, at))
      | Mu.M_I i -> 
         let@ provable = provable loc in
         let@ () = match provable (LC.t_ (IT.bool_ false)) with
           | `True -> fail (fun _ -> {loc; msg = Generic !^("this "^kind^" makes inconsistent assumptions")})
           | `False -> return ()
         in
         let@ i = i_welltyped loc i in
         return (Mu.M_I i)
    in
    pure (aux at)



end



module WArgs = struct

  let rec typ ityp = function
    | Mu.M_Computational (bound, info, at) -> 
       AT.Computational (bound, info, typ ityp at)
    | Mu.M_L lat ->
       AT.L (WLArgs.typ ityp lat)

  let welltyped : 'i 'j. (Loc.t -> 'i -> 'j m) -> string -> Loc.t -> 'i Mu.mu_arguments -> 'j Mu.mu_arguments m =
    fun (i_welltyped : Loc.t -> 'i -> 'j m) 
        kind 
        loc
        (at : 'i Mu.mu_arguments) ->
    let rec aux = function
      | Mu.M_Computational ((name,bt), info, at) ->
         (* no need to alpha-rename, because context.ml ensures
            there's no name clashes *)
         (* let name, at = AT.alpha_rename i_subst (name, bt) at in *)
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
module SymMap = Map.Make(Sym)
module BT = BaseTypes
module RT = ReturnTypes
module AT = ArgumentTypes
open BT

type label_context = (AT.lt * label_kind) SymMap.t


let bt_of_expr : 'TY. 'TY mu_expr -> 'TY =
  fun (M_Expr (_loc, _annots, bty, _e)) -> bty

let bt_of_pexpr : 'TY. 'TY mu_pexpr -> 'TY =
  fun (M_Pexpr (_loc, _annots, bty, _e)) -> bty

let check_against_core_bt loc cbt bt = Typing.embed_resultat
  (CoreTypeChecks.check_against_core_bt
    (fun msg -> Resultat.fail {loc; msg = Generic msg})
    cbt bt)


let rec check_and_bind_pattern bt = function
  | M_Pattern (loc, anns, _, p_) ->
    let@ p_ = check_and_bind_pattern_ bt loc p_ in
    return (M_Pattern (loc, anns, bt, p_))
  and check_and_bind_pattern_ bt loc = function
  | M_CaseBase (sym_opt, cbt) ->
    let@ () = check_against_core_bt loc cbt bt in
    let@ () = match sym_opt with
      | Some nm -> add_l nm bt (loc, lazy (Pp.string "pattern-match var"))
      | None -> return ()
    in
    return (M_CaseBase (sym_opt, cbt))
  | M_CaseCtor (ctor, pats) ->
    let get_item_bt bt = match BT.is_list_bt bt with
      | Some bt -> return bt
      | None -> fail (fun _ -> {loc; msg = Generic (Pp.item "list pattern match against"
          (BT.pp bt))})
    in
    let@ (ctor, pats) = begin match ctor, pats with
    | M_Cnil cbt, [] -> 
       let@ item_bt = get_item_bt bt in
       return (M_Cnil cbt, [])
    | M_Cnil _, _ ->
       fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 0}})
    | M_Ccons, [p1; p2] ->
       let@ item_bt = get_item_bt bt in
       let@ p1 = check_and_bind_pattern item_bt p1 in
       let@ p2 = check_and_bind_pattern bt p2 in
       return (M_Ccons, [p1; p2])
    | M_Ccons, _ ->
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 2}})
    | M_Ctuple, pats ->
        let@ bts = match BT.is_tuple_bt bt with
          | Some bts when List.length bts == List.length pats -> return bts
          | _ -> fail (fun _ -> {loc; msg = Generic
              (Pp.item (Int.to_string (List.length pats) ^ "-length tuple pattern match against")
                  (BT.pp bt))})
        in
        let@ pats = ListM.map2M check_and_bind_pattern bts pats in
        return (M_Ctuple, pats)
    | M_Carray, _ ->
        Cerb_debug.error "todo: array types"
    end in
    return (M_CaseCtor (ctor, pats))

let rec infer_object_value : 'TY. Locations.t -> 'TY mu_object_value ->
    (BT.t * BT.t mu_object_value) m =
  fun loc ov ->
  let todo () = failwith ("TODO: WellTyped infer_object_value: "
      ^ Pp.plain (CF.Pp_ast.pp_doc_tree (Pp_mucore_ast.PP.dtree_of_object_value ov))) in
  match ov with
  | M_OVinteger iv ->
    let z = Memory.z_of_ival iv in
    let ity = Sctypes.(IntegerTypes.Signed IntegerBaseTypes.Int_) in
    if Z.leq (Memory.min_integer_type ity) z && Z.leq z (Memory.max_integer_type ity)
    then return (Memory.bt_of_sct (Sctypes.Integer ity), M_OVinteger iv)
    else fail (fun _ -> {loc; msg = Generic (Pp.item "infer_object_value: doesn't fit in int"
        (IT.pp (IT.z_ z)))})
  | M_OVfloating fv ->
    return (Real, M_OVfloating fv)
  | M_OVpointer pv ->
    return (Loc, M_OVpointer pv)
  | M_OVarray xs ->
    let@ bt_xs = ListM.mapM (infer_object_value loc) xs in
    todo ()
  | M_OVstruct (nm, xs) ->
    return (Struct nm, M_OVstruct (nm, xs))
  | M_OVunion _ ->
    todo ()

let rec infer_value : 'TY. Locations.t -> 'TY mu_value -> (BT.t * BT.t mu_value) m =
  fun loc v ->
  match v with
  | M_Vobject ov ->
     let@ (bt, ov) = infer_object_value loc ov in
     return (bt, M_Vobject ov)
  | M_Vctype ct ->
     return (CType, M_Vctype ct)
  | M_Vunit ->
     return (Unit, M_Vunit)
  | M_Vtrue ->
     return (Bool, M_Vtrue)
  | M_Vfalse -> 
     return (Bool, M_Vfalse)
  | M_Vfunction_addr sym ->
     return (Loc, M_Vfunction_addr sym)
  | M_Vlist (item_cbt, vals) ->
     let@ res = ListM.mapM (infer_value loc) vals in
     begin match res with
     | [] -> fail (fun _ -> {loc; msg = Generic (!^ "infer_value of empty list")})
     | ((bt, _) :: _) ->
       return (BT.List bt, M_Vlist (item_cbt, List.map snd res))
     end
  | M_Vtuple vals ->
     let@ res = ListM.mapM (infer_value loc) vals in
     return (BT.Tuple (List.map fst res), M_Vtuple (List.map snd res))



let rec infer_pexpr : 'TY. 'TY mu_pexpr -> BT.t mu_pexpr m = 
  fun pe ->
    let (M_Pexpr (loc, annots, _, pe_)) = pe in
    let todo () = failwith ("TODO: WellTyped infer_pexpr: "
        ^ Pp.plain (Pp_mucore_ast.pp_pexpr pe)) in
    let@ bty, pe_ = match pe_ with
     | M_PEsym sym ->
        let@ l_elem = get_l sym in
        return (Context.bt_of l_elem, M_PEsym sym)
     | M_PEval v ->
        let@ (bt, v) = infer_value loc v in
        return (bt, M_PEval v)
     | M_PEop (op, pe1, pe2) ->
        let@ pe1 = infer_pexpr pe1 in
        let@ pe2 = infer_pexpr pe2 in
        let casts_to_bool = match op with
          | OpEq | OpGt | OpLt | OpGe | OpLe
            -> true
          | _ -> false
        in
        let bt = if casts_to_bool then Bool else bt_of_pexpr pe1 in
        return (bt, M_PEop (op, pe1, pe2))
      | _ -> todo ()
    in
    return (M_Pexpr (loc, annots, bty, pe_))

and check_pexpr spec expr =
  let@ expr = infer_pexpr expr in
  let@ () = match spec with
    | `BT expect -> 
       ensure_base_type (loc_of_pexpr expr) ~expect (bt_of_pexpr expr)
    | `BV -> 
       ensure_bits_type (loc_of_pexpr expr) (bt_of_pexpr expr) 
  in
  return expr


let rec infer_expr : 'TY. 'TY mu_expr -> BT.t mu_expr m = 
  fun e ->
    let (M_Expr (loc, annots, _, e_)) = e in
    let todo () = failwith ("TODO: WellTyped infer_expr: " ^ Pp.plain (Pp_mucore_ast.pp_expr e)) in
    let@ bty, e_ = match e_ with
     | M_Epure pe ->
        let@ pe = infer_pexpr pe in
        return (bt_of_pexpr pe, M_Epure pe)
     | M_Ememop (M_PtrEq (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrEq (pe1, pe2)))
     | M_Ememop (M_PtrNe (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrNe (pe1, pe2)))
     | M_Ememop (M_PtrLt (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrLt (pe1, pe2)))
     | M_Ememop (M_PtrGt (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrGt (pe1, pe2)))
     | M_Ememop (M_PtrLe (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrLe (pe1, pe2)))
     | M_Ememop (M_PtrGe (pe1, pe2)) ->
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        return (Bool, M_Ememop (M_PtrGe (pe1, pe2)))
     | M_Ememop (M_Ptrdiff (act, pe1, pe2)) ->
        let@ () = WCT.is_ct act.loc act.ct in
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr (`BT Loc) pe2 in
        let bty = Memory.bt_of_sct (Integer Ptrdiff_t) in
        return (bty, M_Ememop (M_Ptrdiff (act, pe1, pe2)))
     | M_Ememop (M_IntFromPtr (act_from, act_to, pe)) ->
        let@ () = WCT.is_ct act_from.loc act_from.ct in
        let@ () = WCT.is_ct act_to.loc act_to.ct in
        let@ pe = check_pexpr (`BT Loc) pe in
        let bty = Memory.bt_of_sct act_to.ct in
        return (bty, M_Ememop (M_IntFromPtr (act_from, act_to, pe)))
     | M_Ememop (M_PtrFromInt (act_from, act_to, pe)) ->
        let@ () = WCT.is_ct act_from.loc act_from.ct in
        let@ () = WCT.is_ct act_to.loc act_to.ct in
        let@ pe = check_pexpr (`BT (Memory.bt_of_sct act_from.ct)) pe in
        let bty = Memory.bt_of_sct act_to.ct in
        return (bty, M_Ememop (M_PtrFromInt (act_from, act_to, pe)))
     | M_Ememop (M_PtrValidForDeref (act, pe)) ->
        let@ () = WCT.is_ct act.loc act.ct in
        let@ pe = check_pexpr (`BT Loc) pe in
        return (Bool, M_Ememop (M_PtrValidForDeref (act, pe)))
     | M_Ememop (M_PtrWellAligned (act, pe)) ->
        let@ () = WCT.is_ct act.loc act.ct in
        let@ pe = check_pexpr (`BT Loc) pe in
        return (Bool, M_Ememop (M_PtrWellAligned (act, pe)))
     | M_Ememop (M_PtrArrayShift (pe1, act, pe2)) ->
        let@ () = WCT.is_ct act.loc act.ct in
        let@ pe1 = check_pexpr (`BT Loc) pe1 in
        let@ pe2 = check_pexpr `BV pe2 in
        return (Loc, M_Ememop (M_PtrArrayShift (pe1, act, pe2)))
     | M_Ememop (M_PtrMemberShift (tag_sym, memb_ident, pe)) ->
        let@ _ = get_struct_member_type loc tag_sym memb_ident in
        let@ pe = check_pexpr (`BT Loc) pe in
        return (Loc, M_Ememop (M_PtrMemberShift (tag_sym, memb_ident, pe)))
     | M_Ememop (M_Memcpy _) (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        todo ()
     | M_Ememop (M_Memcmp _) (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        todo ()
     | M_Ememop (M_Realloc _) (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        todo ()
     | M_Ememop (M_Va_start _) (* (asym 'bty * asym 'bty) *) ->
        todo ()
     | M_Ememop (M_Va_copy _) (* (asym 'bty) *) ->
        todo ()
     | M_Ememop (M_Va_arg _) (* (asym 'bty * actype 'bty) *) ->
        todo ()
     | M_Ememop (M_Va_end _) (* (asym 'bty) *) ->
        todo ()
     | M_Eaction (M_Paction (pol, M_Action (aloc, action_))) ->
        let@ (bTy, action_) = match action_ with
        | M_Create (pe, act, prefix) ->
           let@ () = WCT.is_ct act.loc act.ct in
           let@ pe = check_pexpr `BV pe in
           return (Loc, M_Create (pe, act, prefix))
        | M_Kill (k, pe) -> 
           let@ () = match k with
             | M_Dynamic -> return ()
             | M_Static ct -> WCT.is_ct loc ct
           in
           let@ pe = check_pexpr (`BT Loc) pe in
           return (Unit, M_Kill (k, pe))
        | M_Store (is_locking, act, p_pe, v_pe, mo) ->
           let@ () = WCT.is_ct act.loc act.ct in
           let@ p_pe = check_pexpr (`BT Loc) p_pe in
           let@ v_pe = check_pexpr (`BT (Memory.bt_of_sct act.ct)) v_pe in
           return (Unit, M_Store (is_locking, act, p_pe, v_pe, mo))
        | M_Load (act, p_pe, mo) ->
           let@ () = WCT.is_ct act.loc act.ct in
           let@ p_pe = check_pexpr (`BT Loc) p_pe in
           return (Memory.bt_of_sct act.ct, M_Load (act, p_pe, mo))
        | _ ->
           todo ()
        in
        return (bTy, M_Eaction (M_Paction (pol, M_Action (aloc, action_))))
     | M_Eskip ->
        return (Unit, M_Eskip)
     | M_Eccall (act, f_pe, pes) ->
        let@ () = WCT.is_ct act.loc act.ct in
        let@ f_pe = check_pexpr (`BT Loc) f_pe in
        (* TODO: we'd have to check the arguments against the function
           type, but we can't when f_pe is dynamic *)
        let@ pes = ListM.mapM infer_pexpr pes in
        return (Memory.bt_of_sct act.ct, M_Eccall (act, f_pe, pes))
     | M_Eif (c_pe, e1, e2) ->
        let@ c_pe = check_pexpr (`BT Bool) c_pe in
        let@ e1 = infer_expr e1 in
        let bt = bt_of_expr e1 in
        let@ e2 = check_expr (`BT bt) e2 in
        return (bt, M_Eif (c_pe, e1, e2))
     | M_Ebound e ->
        let@ e = infer_expr e in
        return (bt_of_expr e, M_Ebound e)
     | M_Elet (pat, pe, e) ->
        let@ pe = infer_pexpr pe in
        pure begin
          let@ pat = check_and_bind_pattern (bt_of_pexpr pe) pat in
          let@ e = infer_expr e in
          return (bt_of_expr e, M_Elet (pat, pe, e))
        end
     | M_Esseq (pat, e1, e2)
     | M_Ewseq (pat, e1, e2) ->
        let@ e1 = infer_expr e1 in
        pure begin
          let@ pat = check_and_bind_pattern (bt_of_expr e1) pat in
          let@ e2 = infer_expr e2 in
          let e_ = match e_ with
            | M_Esseq _ -> M_Esseq (pat, e1, e2)
            | _ -> M_Ewseq (pat, e1, e2)
          in
          return (bt_of_expr e2, e_)
        end
     | _ ->
       todo ()
  in
  return (M_Expr (loc, annots, bty, e_))

and check_expr spec expr =
  let@ expr = infer_expr expr in
  let@ () = match spec with
    | `BT expect -> 
       ensure_base_type (loc_of_expr expr) ~expect (bt_of_expr expr)
    | `BV -> 
       ensure_bits_type (loc_of_expr expr) (bt_of_expr expr) 
  in
  return expr




let infer_glob = function
  | M_GlobalDef (ct, expr) ->
    let@ expr = check_expr (`BT (Memory.bt_of_sct ct)) expr in
    return (M_GlobalDef (ct, expr))
  | M_GlobalDecl ct ->
    return (M_GlobalDecl ct)

let infer_globs gs = ListM.mapM (fun (nm, glob) ->
    let@ glob = infer_glob glob in
    return (nm, glob)
  ) gs

let rec infer_mu_args_l (f : 'i -> 'j m) (x : 'i mu_arguments_l) =
  match x with
  | M_Define ((nm, rhs), info, args) ->
    pure begin
    let@ () = add_l nm (IT.bt rhs) (fst info, lazy (Pp.string "defined-var")) in
    let@ args = infer_mu_args_l f args in
    return (M_Define ((nm, rhs), info, args))
    end
  | M_Resource ((nm, (ret, bt)), info, args) ->
    pure begin
    let@ () = add_l nm bt (fst info, lazy (Pp.string "resource-var")) in
    let@ args = infer_mu_args_l f args in
    return (M_Resource ((nm, (ret, bt)), info, args))
    end
  | M_Constraint (lc, info, args) ->
    let@ args = infer_mu_args_l f args in
    return (M_Constraint (lc, info, args))
  | M_I y ->
    let@ y = f y in
    return (M_I y)

let rec infer_mu_args (f : 'i -> 'j m) (x : 'i mu_arguments) =
  match x with
  | M_Computational ((nm, bt), info, args) ->
    pure begin
    let@ () = add_l nm bt (fst info, lazy (Pp.string "argument")) in
    let@ args = infer_mu_args f args in
    return (M_Computational ((nm, bt), info, args))
    end
  | M_L args_l ->
    let@ args_l = infer_mu_args_l f args_l in
    return (M_L args_l)

let infer_label_def = function
  | M_Return loc -> return (M_Return loc)
  | M_Label (loc, args, annots, spec) ->
    let@ args = infer_mu_args infer_expr args in
    return (M_Label (loc, args, annots, spec))

let infer_fun_map_decl = function
  | M_Proc (loc, args_and_body, trusted, spec) ->
    let f (expr, label_defs, rt) =
      let@ expr = infer_expr expr in
      let@ label_defs = PmapM.mapM (fun sym label_def -> infer_label_def label_def)
          label_defs Sym.compare in
      return (expr, label_defs, rt)
    in
    let@ args_and_body = infer_mu_args f args_and_body in
    return (M_Proc (loc, args_and_body, trusted, spec))
  | M_ProcDecl (loc, spec_opt) ->
    return (M_ProcDecl (loc, spec_opt))

let infer_funs funs = PmapM.mapM (fun sym decl -> infer_fun_map_decl decl) funs Sym.compare

let infer_types_file : 'bt. 'bt mu_file -> BT.t mu_file m =
  fun file ->
  let@ globs = infer_globs file.mu_globs in
  let@ funs = infer_funs file.mu_funs in
  return {
    mu_main = file.mu_main;
    mu_tagDefs = file.mu_tagDefs;
    mu_globs = globs;
    mu_funs = funs;
    mu_extern = file.mu_extern;
    mu_stdlib_syms = file.mu_stdlib_syms;
    mu_resource_predicates = file.mu_resource_predicates;
    mu_logical_predicates = file.mu_logical_predicates;
    mu_datatypes = file.mu_datatypes;
    mu_lemmata = file.mu_lemmata;
    mu_call_funinfo = file.mu_call_funinfo;
  }

end







module WLabel = struct
   open Mu
 
   let typ l = WArgs.typ (fun _body -> False.False) l
 
   let welltyped (loc : Loc.t) (lt : _ mu_expr mu_arguments)
       : (_ mu_expr mu_arguments) m 
     =
     WArgs.welltyped (fun loc body -> 
         return body
       ) "loop/label" loc lt
 end





 
module WProc = struct 
  open Mu
   
   
  let label_context function_rt label_defs =
    Pmap.fold (fun sym def label_context ->
         let lt, kind =
            match def with
            | M_Return loc ->
               (AT.of_rt function_rt (LAT.I False.False), Return)
            | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
               let lt = WLabel.typ label_args_and_body in
               let kind = match CF.Annot.get_label_annot annots with
               | Some (LAloop_body loop_id) -> Loop
               | Some (LAloop_continue loop_id) -> Loop
               | _ -> Other
               in
               (lt, kind)
         in
         (*debug 6 (lazy (!^"label type within function" ^^^ Sym.pp fsym));
         debug 6 (lazy (CF.Pp_ast.pp_doc_tree (AT.dtree False.dtree lt)));*)
         (SymMap.add sym (lt, kind) label_context)
      ) label_defs SymMap.empty


  let typ p = WArgs.typ (fun (_body,_labels,rt) -> rt) p

  let welltyped : (*'TY.*) Loc.t -> 'TY Mu.mu_proc_args_and_body -> (_(*BT.t*) Mu.mu_proc_args_and_body) m =
    fun (loc : Loc.t) (at : 'TY1 Mu.mu_proc_args_and_body) ->
    WArgs.welltyped (fun loc (body, labels, rt) ->
        let@ rt = pure (WRT.welltyped loc rt) in
        let@ labels =
          PmapM.mapM (fun sym def ->
            match def with
            | M_Return loc -> 
               return (M_Return loc)
            | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
               let@ label_args_and_body = pure (WLabel.welltyped loc label_args_and_body) in
               return (M_Label (loc, label_args_and_body, annots, parsed_spec))
            ) labels Sym.compare
        in
        (* let label_context = label_context rt labels in *)
        let@ labels = 
          PmapM.mapM (fun sym def ->
              match def with
              | M_Return loc ->
                 return (M_Return loc)
              | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
                 let@ label_args_and_body = 
                   pure begin
                     WArgs.welltyped (fun loc label_body ->
                        BaseTyping.infer_expr (* label_context *) label_body
                        ) "label" loc label_args_and_body
                     end
                 in
                 return (M_Label (loc, label_args_and_body, annots, parsed_spec))
            ) labels Sym.compare
        in
        let@ body = pure (BaseTyping.infer_expr (* label_context *) body) in
        return (body, labels, rt)
      ) "function" loc at
end




module WRPD = struct

  open ResourcePredicates 

  let welltyped {loc; pointer; iargs; oarg_bt; clauses} = 
    (* no need to alpha-rename, because context.ml ensures
       there's no name clashes *)
    pure begin
        let@ () = add_l pointer BT.Loc (loc, lazy (Pp.string "ptr-var")) in
        let@ iargs = 
          ListM.mapM (fun (s, ls) -> 
              let@ ls = WLS.is_ls loc ls in
              let@ () = add_l s ls (loc, lazy (Pp.string "input-var")) in
              return (s, ls)
            ) iargs 
        in
        let@ oarg_bt = WBT.is_bt loc oarg_bt in
        let@ clauses = match clauses with
          | None -> return None
          | Some clauses ->
             let@ clauses = 
               ListM.fold_leftM (fun acc {loc; guard; packing_ft} ->
                   let@ guard = WIT.check loc BT.Bool guard in
                   let negated_guards = List.map (fun clause -> IT.not_ clause.guard) acc in
                   pure begin 
                       let@ () = add_c loc (LC.t_ guard) in
                       let@ () = add_c loc (LC.t_ (IT.and_ negated_guards)) in
                       let@ packing_ft = 
                         WLAT.welltyped IT.subst (fun loc it -> WIT.check loc oarg_bt it)
                           "clause" loc packing_ft
                       in
                       return (acc @ [{loc; guard; packing_ft}])
                     end
                 ) [] clauses
             in
             return (Some clauses)
        in
        return {loc; pointer; iargs; oarg_bt; clauses}
      end

end



module WLFD = struct

  open LogicalFunctions

  let welltyped ({loc; args; return_bt; emit_coq; definition} : LogicalFunctions.definition) = 
    (* no need to alpha-rename, because context.ml ensures
       there's no name clashes *)
    pure begin
        let@ args = 
          ListM.mapM (fun (s,ls) -> 
              let@ ls = WLS.is_ls loc ls in
              let@ () = add_l s ls (loc, lazy (Pp.string "arg-var")) in
              return (s, ls)
            ) args 
        in
        let@ return_bt = WBT.is_bt loc return_bt in
        let@ definition = match definition with
          | Def body -> 
             let@ body = WIT.check loc return_bt body in
             return (Def body)
          | Rec_Def body -> 
             let@ body = WIT.check loc return_bt body in
             return (Rec_Def body)
          | Uninterp -> 
             return Uninterp
        in
        return {loc; args; return_bt; emit_coq; definition}
      end

end




module WLemma = struct

  let welltyped loc lemma_s lemma_typ = 
    WAT.welltyped LRT.subst WLRT.welltyped "lemma" loc lemma_typ

end


module WDT = struct

  open Mu

  let welltyped (dt_name, {loc; cases}) =
    let@ _ = 
      (* all argument members disjoint *)
      ListM.fold_leftM (fun already (id,_) ->
          if IdSet.mem id already 
          then fail (fun _ -> {loc; msg = Duplicate_member id})
          else return (IdSet.add id already)
        ) IdSet.empty (List.concat_map snd cases)
    in
    let@ cases = 
      ListM.mapM (fun (c, args) ->
          let@ args = 
            ListM.mapM (fun (id,bt) -> 
                let@ bt = WBT.is_bt loc bt in
                return (id, bt)
              ) (List.sort compare_by_member_id args)
          in
          return (c, args)
        ) cases
    in
    return (dt_name, {loc; cases})

end
