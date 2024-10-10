module BT = BaseTypes
module IT = IndexTerms
module SymSet = Set.Make (Sym)

let check_bits_bt (sgn1, sz1) (sgn2, sz2) here : (unit, string) result =
  if not @@ BT.equal_sign sgn1 sgn2 then
    Error ("Mismatched signs at " ^ Locations.simple_location here)
  else if sz1 <> sz2 then
    Error ("Mismatched sizes at " ^ Locations.simple_location here)
  else
    Ok ()


let eval_num_binop
  (eval : IT.t -> (IT.t, string) result)
  (bt : BT.t)
  (here : Locations.t)
  (f : Z.t -> Z.t -> Z.t)
  (it1 : IT.t)
  (it2 : IT.t)
  (loc : string)
  : (IT.t, string) result
  =
  let ( let@ ) = Result.bind in
  let return = Result.ok in
  let@ it1 = eval it1 in
  let@ it2 = eval it2 in
  match (it1, it2) with
  | IT (Const (Z n1), _, _), IT (Const (Z n2), _, _) ->
    return @@ IT.num_lit_ (f n1 n2) bt here
  | IT (Const (Bits ((sgn1, sz1), n1)), _, _), IT (Const (Bits ((sgn2, sz2), n2)), _, _)
    ->
    let@ () = check_bits_bt (sgn1, sz1) (sgn2, sz2) here in
    return @@ IT.num_lit_ (BT.normalise_to_range_bt bt (f n1 n2)) bt here
  | _, IT (Const (Z _), _, _) ->
    Error ("Not constant integer `" ^ Pp.plain (IT.pp it1) ^ "` (" ^ loc ^ ")")
  | _, IT (Const (Bits _), _, _) ->
    Error ("Not constant bitvector `" ^ Pp.plain (IT.pp it1) ^ "` (" ^ loc ^ ")")
  | IT (Const (Z _), _, _), _ ->
    Error ("Not constant integer `" ^ Pp.plain (IT.pp it2) ^ "` (" ^ loc ^ ")")
  | IT (Const (Bits _), _, _), _ ->
    Error ("Not constant bitvector `" ^ Pp.plain (IT.pp it2) ^ "` (" ^ loc ^ ")")
  | _, _ ->
    Error
      ("Not constant integer or bitvector `"
       ^ Pp.plain (IT.pp it1)
       ^ "` and `"
       ^ Pp.plain (IT.pp it2)
       ^ "` ("
       ^ loc
       ^ ")")


let eval_term_generic
  (eval_aux : IT.t -> (IT.t, string) result)
  (prog5 : unit Mucore.mu_file)
  (it : IT.t)
  : (IT.t, string) result
  =
  let ( let@ ) = Result.bind in
  let return = Result.ok in
  let open IT in
  let (IT (t_, bt, here)) = it in
  let eval_num_binop = eval_num_binop eval_aux bt here in
  match t_ with
  | Const _ | Nil _ | MapDef _ -> return it
  | Sym x -> Error (Sym.pp_string x ^ " is free")
  (* Unary ops *)
  | Unop (Not, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bool b), _, _) -> return @@ bool_ (not b) here
     | _ -> Error ("Not constant boolean (" ^ __LOC__ ^ ")"))
  | Unop (Negate, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Z n), _, _) -> return @@ num_lit_ (Z.neg n) bt here
     | IT (Const (Bits ((Signed, _), n)), _, _) ->
       return @@ num_lit_ (BT.normalise_to_range_bt bt (Z.neg n)) bt here
     | IT (Const (Bits ((Unsigned, _), _)), _, _) ->
       Error
         ("Can't negate unsigned integer at "
          ^ Locations.simple_location here
          ^ " ("
          ^ __LOC__
          ^ ")")
     | _ -> Error ("Not constant integer or bitvector (" ^ __LOC__ ^ ")"))
  | Unop (BW_CLZ_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits ((sgn, bits), n)), bt, _) ->
       let open Int64 in
       let reverse_bits (n : Z.t) : Z.t =
         let rec aux (bits : int) (n : int64) (acc : int64) : int64 =
           if bits = 0 then
             acc
           else (
             let acc = logor (shift_left acc 1) (logand n (of_int 1)) in
             aux (bits - 1) (shift_right n 1) acc)
         in
         let to_64, of_64 =
           match sgn with
           | Signed -> (Z.to_int64, Z.of_int64)
           | Unsigned -> (Z.to_int64_unsigned, Z.of_int64_unsigned)
         in
         of_64 (aux bits (to_64 n) (of_int 0))
       in
       let n = BT.normalise_to_range_bt bt (reverse_bits n) in
       eval_aux (arith_unop BW_CTZ_NoSMT (num_lit_ n bt here) here)
     | _ -> Error ("Not constant bitvector (" ^ __LOC__ ^ ")"))
  | Unop (BW_CTZ_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits ((_, sz), n)), _, _) ->
       let res = Z.trailing_zeros n in
       let res = if res = max_int then sz else res in
       return @@ num_lit_ (Z.of_int res) bt here
     | _ -> Error ("Not constant bitvector (" ^ __LOC__ ^ ")"))
  | Unop (BW_FFS_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits (_, n)), _, _) ->
       if Z.equal n Z.zero then
         return @@ num_lit_ Z.zero bt here
       else
         let@ it' = return @@ arith_unop BW_CTZ_NoSMT it' here in
         eval_aux (add_ (it', num_lit_ Z.one bt here) here)
     | _ -> Error ("Not constant bitvector (" ^ __LOC__ ^ ")"))
  | Unop (BW_FLS_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits ((_, sz), n)), bt, _) ->
       if Z.equal n Z.zero then
         return @@ int_lit_ 0 bt here
       else (
         let it' = arith_unop BW_CLZ_NoSMT it' here in
         eval_aux (sub_ (int_lit_ sz bt here, it') here))
     | _ -> Error ("Not constant bitvector (" ^ __LOC__ ^ ")"))
  | Unop (BW_Compl, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits (_, n)), _, _) ->
       return @@ num_lit_ (BT.normalise_to_range_bt bt (Z.lognot n)) bt here
     | _ -> Error ("Not constant bitvector (" ^ __LOC__ ^ ")"))
  (* Binary ops *)
  | Binop (And, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) -> if b1 then eval_aux it2 else return it1
     | _ -> Error ("Not constant boolean (" ^ __LOC__ ^ ")"))
  | Binop (Or, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) -> if b1 then return it1 else eval_aux it2
     | _ -> Error ("Not constant boolean (" ^ __LOC__ ^ ")"))
  | Binop (Implies, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) ->
       if b1 then eval_aux it2 else return @@ bool_ true here
     | _ -> Error ("Not constant boolean (" ^ __LOC__ ^ ")"))
  | Binop (Add, it1, it2) -> eval_num_binop Z.add it1 it2 __LOC__
  | Binop (Sub, it1, it2) -> eval_num_binop Z.sub it1 it2 __LOC__
  | Binop (Mul, it1, it2) | Binop (MulNoSMT, it1, it2) ->
    eval_num_binop Z.mul it1 it2 __LOC__
  | Binop (Div, it1, it2) | Binop (DivNoSMT, it1, it2) ->
    eval_num_binop Z.div it1 it2 __LOC__
  | Binop (Exp, it1, it2) | Binop (ExpNoSMT, it1, it2) ->
    eval_num_binop (fun n1 n2 -> Z.pow n1 (Z.to_int n2)) it1 it2 __LOC__
  | Binop (Rem, it1, it2) | Binop (RemNoSMT, it1, it2) ->
    eval_num_binop Z.rem it1 it2 __LOC__
  | Binop (Mod, it1, it2) | Binop (ModNoSMT, it1, it2) ->
    eval_num_binop Z.( mod ) it1 it2 __LOC__
  | Binop (BW_Xor, it1, it2) -> eval_num_binop Z.logxor it1 it2 __LOC__
  | Binop (BW_And, it1, it2) -> eval_num_binop Z.logand it1 it2 __LOC__
  | Binop (BW_Or, it1, it2) -> eval_num_binop Z.logor it1 it2 __LOC__
  | Binop (ShiftLeft, _it1, _it2) | Binop (ShiftRight, _it1, _it2) ->
    Error "todo: Bits shifts"
  | Binop (LT, it1, it2) ->
    let@ it1 = eval_aux it1 in
    let@ it2 = eval_aux it2 in
    (match (it1, it2) with
     | IT (Const (Z n1), _, _), IT (Const (Z n2), _, _) ->
       return @@ bool_ (Z.lt n1 n2) here
     | IT (Const (Bits ((sgn1, sz1), n1)), _, _), IT (Const (Bits ((sgn2, sz2), n2)), _, _)
       ->
       let@ () = check_bits_bt (sgn1, sz1) (sgn2, sz2) here in
       return @@ bool_ (Z.lt n1 n2) here
     | _ -> Error ("Not constant integer or bitvector (" ^ __LOC__ ^ ")"))
  | Binop (LE, it1, it2) ->
    let@ it1 = eval_aux it1 in
    let@ it2 = eval_aux it2 in
    (match (it1, it2) with
     | IT (Const (Z n1), _, _), IT (Const (Z n2), _, _) ->
       return @@ bool_ (Z.leq n1 n2) here
     | IT (Const (Bits ((sgn1, sz1), n1)), _, _), IT (Const (Bits ((sgn2, sz2), n2)), _, _)
       ->
       let@ () = check_bits_bt (sgn1, sz1) (sgn2, sz2) here in
       return @@ bool_ (Z.leq n1 n2) here
     | _ -> Error ("Not constant integer or bitvector (" ^ __LOC__ ^ ")"))
  | Binop (Min, it1, it2) -> eval_num_binop Z.min it1 it2 __LOC__
  | Binop (Max, it1, it2) -> eval_num_binop Z.max it1 it2 __LOC__
  | Binop (EQ, it1, it2) ->
    let@ it1 = eval_aux it1 in
    let@ it2 = eval_aux it2 in
    (match (it1, it2) with
     | IT (Const c1, _, _), IT (Const c2, _, _) ->
       return @@ bool_ (equal_const c1 c2) here
     | IT (Tuple its1, _, _), IT (Tuple its2, _, _) ->
       eval_aux (and_ (List.map (fun its -> eq_ its here) (List.combine its1 its2)) here)
     | IT (Struct (tag1, xits1), _, _), IT (Struct (tag2, xits2), _, _) ->
       if not (Sym.equal tag1 tag2) then
         Error "Ill-typed"
       else (
         let compare (x1, _) (x2, _) = Id.compare x1 x2 in
         let zipped = List.combine (List.sort compare xits1) (List.sort compare xits2) in
         if List.exists (fun ((x1, _), (x2, _)) -> not (Id.equal x1 x2)) zipped then
           Error "Malformed, different members"
         else
           eval_aux
             (and_
                (List.map (fun ((_, it1), (_, it2)) -> eq_ (it1, it2) here) zipped)
                here))
     | IT (Record xits1, _, _), IT (Record xits2, _, _) ->
       let compare (x1, _) (x2, _) = Id.compare x1 x2 in
       let zipped = List.combine (List.sort compare xits1) (List.sort compare xits2) in
       if List.exists (fun ((x1, _), (x2, _)) -> not (Id.equal x1 x2)) zipped then
         Error "Malformed, different members"
       else
         eval_aux
           (and_ (List.map (fun ((_, it1), (_, it2)) -> eq_ (it1, it2) here) zipped) here)
     | IT (Constructor (constr1, xits1), _, _), IT (Constructor (constr2, xits2), _, _) ->
       if not (Sym.equal constr1 constr2) then
         return @@ IT.bool_ false here
       else (
         let compare (x1, _) (x2, _) = Id.compare x1 x2 in
         let zipped = List.combine (List.sort compare xits1) (List.sort compare xits2) in
         if List.exists (fun ((x1, _), (x2, _)) -> not (Id.equal x1 x2)) zipped then
           Error "Malformed, same constructor, different members"
         else
           eval_aux
             (and_
                (List.map (fun ((_, it1), (_, it2)) -> eq_ (it1, it2) here) zipped)
                here))
     | _ -> Error "Not equal")
  | Binop (LTPointer, _, _) | Binop (LEPointer, _, _) ->
    Error "todo: Pointer inequalities"
  | Binop (SetUnion, _, _)
  | Binop (SetIntersection, _, _)
  | Binop (SetDifference, _, _)
  | Binop (SetMember, _, _)
  | Binop (Subset, _, _) ->
    Error "todo: Sets"
  (* Other ops *)
  | ITE (it_if, it_then, it_else) ->
    let@ it_if = eval_aux it_if in
    (match it_if with
     | IT (Const (Bool b), _, _) -> if b then eval_aux it_then else eval_aux it_else
     | _ -> Error ("Not constant boolean (" ^ __LOC__ ^ ")"))
  | EachI ((i_start, (i_sym, bt'), i_end), it') ->
    let rec loop i =
      if i <= i_end then (
        let su = make_subst [ (i_sym, num_lit_ (Z.of_int i) bt' here) ] in
        let t1 = IT.subst su it' in
        if i = i_end then
          t1
        else
          IT.and2_ (t1, loop (i + 1)) here)
      else
        failwith "unreachable"
    in
    if i_start > i_end then return @@ IT.bool_ true here else eval_aux (loop i_start)
  | NthTuple (i, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Tuple its, _, _) -> return @@ List.nth its i
     | _ -> Error ("Not tuple (" ^ __LOC__ ^ ")"))
  | SizeOf ty ->
    return
    @@ IT
         ( Const
             (Bits
                ( (Unsigned, Memory.size_of_ctype Sctypes.(Integer Size_t)),
                  Z.of_int (Memory.size_of_ctype ty) )),
           BT.of_sct
             Memory.is_signed_integer_type
             Memory.size_of_integer_type
             Sctypes.(Integer Size_t),
           here )
  | OffsetOf (tag, member) ->
    (match Pmap.find tag prog5.mu_tagDefs with
     | M_StructDef st ->
       let n = Z.of_int (Option.get (Memory.member_offset st member)) in
       return @@ num_lit_ n bt here
     | _ -> Error "Invalid OffsetOf")
  | MemberShift _ -> Error "todo: MemberShift"
  | ArrayShift _ -> Error "todo: ArrayShift"
  | CopyAllocId _ -> Error "todo: CopyAllocId"
  | HasAllocId _ -> Error "todo: HasAllocId"
  | Head it' ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Cons (it_head, _), _, _) -> eval_aux it_head
     | _ -> Error ("Not `Cons` (" ^ __LOC__ ^ ")"))
  | Tail it' ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Cons (_, it_tail), _, _) -> eval_aux it_tail
     | _ -> Error ("Not `Cons` (" ^ __LOC__ ^ ")"))
  | NthList _ -> Error "todo: NthList"
  | ArrayToList _ -> Error "todo: ArrayToList"
  | Representable (ty, it') ->
    let struct_decls =
      Pmap.fold
        (fun tag def decls ->
          match def with Mucore.M_StructDef st -> SymMap.add tag st decls | _ -> decls)
        prog5.mu_tagDefs
        SymMap.empty
    in
    eval_aux (representable struct_decls ty it' here)
  | Good (ty, it') ->
    let struct_decls =
      Pmap.fold
        (fun tag def decls ->
          match def with Mucore.M_StructDef st -> SymMap.add tag st decls | _ -> decls)
        prog5.mu_tagDefs
        SymMap.empty
    in
    eval_aux (good_value struct_decls ty it' here)
  | Aligned { t; align } ->
    let addr = addr_ t here in
    if not (BT.equal (IT.bt addr) (IT.bt align)) then
      Error "Mismatched types"
    else
      eval_aux (divisible_ (addr, align) here)
  | Apply (fsym, its) ->
    (match List.assoc_opt Sym.equal fsym prog5.mu_logical_predicates with
     | Some { args; definition = Def it_body; _ }
     | Some { args; definition = Rec_Def it_body; _ } ->
       return @@ IT.subst (IT.make_subst (List.combine (List.map fst args) its)) it_body
     | Some { definition = Uninterp; _ } ->
       Error ("Function " ^ Sym.pp_string fsym ^ " is uninterpreted")
     | None -> Error ("Function " ^ Sym.pp_string fsym ^ " was not found"))
  | Let ((x, it_v), it_rest) -> eval_aux (IT.subst (IT.make_subst [ (x, it_v) ]) it_rest)
  | StructMember (it', member) ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Struct (_, xits), _, _) -> return @@ List.assoc Id.equal member xits
     | _ -> Error ("Not struct (" ^ __LOC__ ^ ")"))
  | StructUpdate ((it_struct, member), it_value) ->
    let@ it_struct = eval_aux it_struct in
    (match it_struct with
     | IT (Struct (tag, xits), _, _) ->
       let xits =
         List.map (fun (x, it) -> (x, if Id.equal x member then it_value else it)) xits
       in
       return @@ struct_ (tag, xits) here
     | _ -> Error ("Not struct (" ^ __LOC__ ^ ")"))
  | RecordMember (it', member) ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Record xits, _, _) -> return @@ List.assoc Id.equal member xits
     | _ -> Error ("Not record (" ^ __LOC__ ^ ")"))
  | RecordUpdate ((it_record, member), it_value) ->
    let@ it_record = eval_aux it_record in
    (match it_record with
     | IT (Record xits, _, _) ->
       let xits =
         List.map (fun (x, it) -> (x, if Id.equal x member then it_value else it)) xits
       in
       return @@ record_ xits here
     | _ -> Error ("Not record (" ^ __LOC__ ^ ")"))
  | Match (it', pits) ->
    let@ it' = eval_aux it' in
    let is_constructor = match it' with IT (Constructor _, _, _) -> true | _ -> false in
    if not is_constructor then
      return @@ IT (Match (it', pits), bt, here)
    else (
      let rec get_match (it_match : IT.t) (p : BT.t pattern)
        : (Sym.sym * IT.t) list option
        =
        let (Pat (p_, _, _)) = p in
        match p_ with
        | PSym x -> Some [ (x, it_match) ]
        | PWild -> Some []
        | PConstructor (constr, xps) ->
          (match it_match with
           | IT (Constructor (constr', xits), _, _) ->
             if not (Sym.equal constr constr') then
               None
             else (
               let compare (x1, _) (x2, _) = Id.compare x1 x2 in
               let zipped =
                 List.combine (List.sort compare xits) (List.sort compare xps)
               in
               Some
                 (List.flatten
                  @@ List.map
                       (fun ((_, it), (_, p)) ->
                         List.flatten @@ Option.to_list @@ get_match it p)
                       zipped))
           | _ -> None)
      in
      let none = "No pattern matched" in
      Option.to_result
        ~none
        (List.find_map
           (fun (p, it_case) ->
             let open Option in
             let@ sub = get_match it' p in
             Some (IT.subst (IT.make_subst sub) it_case))
           pits))
  | WrapI _ -> Error "todo: WrapI"
  | MapGet (it_m, it_k) ->
    let@ it_m = eval_aux it_m in
    let@ it_k = eval_aux it_k in
    let aux (it_m : IT.t) (it_k : IT.t) : (IT.t, string) result =
      match it_m with
      | IT (MapConst (_, it_body), _, _) -> eval_aux it_body
      | IT (MapSet (it_m', it_k', it_v), _, _) ->
        let@ it_k' = eval_aux it_k' in
        (match (get_num_z it_k, get_num_z it_k') with
         | Some n1, Some n2 when Z.equal n1 n2 -> eval_aux it_v
         | Some _, Some _ -> eval_aux (map_get_ it_m' it_k here)
         | _, _ -> Error "not a valid key")
      | IT (MapDef ((k, _), it_body), _, _) ->
        eval_aux (IT.subst (IT.make_subst [ (k, it_k) ]) it_body)
      | _ -> Error "Attempted MapGet on non-map"
    in
    aux it_m it_k
  | Cast _ -> Error "todo: Cast"
  | Tuple _ | Struct _ | Record _ | Constructor _ | Cons _ | MapConst _ | MapSet _ ->
    failwith "unreachable, specific to evaluation mode"


let eval_term_strictly (prog5 : unit Mucore.mu_file) (it : IT.t) : (IT.t, string) result =
  let rec eval_aux (it : IT.t) : (IT.t, string) result =
    let ( let@ ) = Result.bind in
    let return = Result.ok in
    let open IT in
    let (IT (t_, bt, here)) = it in
    match t_ with
    (* Shared *)
    | Const _ | Sym _ | Unop _ | Binop _ | ITE _ | EachI _ | NthTuple _ | StructMember _
    | RecordMember _ | MemberShift _ | ArrayShift _ | CopyAllocId _ | HasAllocId _
    | SizeOf _ | OffsetOf _ | Nil _ | Head _ | Tail _ | NthList _ | ArrayToList _
    | Representable _ | Good _ | Aligned _ | MapGet _ | MapDef _ | Match _ ->
      eval_term_generic eval_aux prog5 it
    (* Strict *)
    | Tuple its ->
      let@ its =
        List.fold_left
          (fun acc it ->
            let@ it = eval_aux it in
            let@ acc in
            Ok (it :: acc))
          (Ok [])
          its
      in
      return @@ tuple_ its here
    | Struct (tag, xits) ->
      let@ xits =
        List.fold_left
          (fun acc (x, it) ->
            let@ it = eval_aux it in
            let@ acc in
            Ok ((x, it) :: acc))
          (Ok [])
          xits
      in
      return @@ struct_ (tag, xits) here
    | StructUpdate ((it_struct, member), it_value) ->
      let@ it_value = eval_aux it_value in
      eval_term_generic
        eval_aux
        prog5
        (IT.IT (StructUpdate ((it_struct, member), it_value), bt, here))
    | Record xits ->
      let@ xits =
        List.fold_left
          (fun acc (x, it) ->
            let@ it = eval_aux it in
            let@ acc in
            Ok ((x, it) :: acc))
          (Ok [])
          xits
      in
      return @@ record_ xits here
    | RecordUpdate ((it_record, member), it_value) ->
      let@ it_value = eval_aux it_value in
      eval_term_generic
        eval_aux
        prog5
        (IT.IT (RecordUpdate ((it_record, member), it_value), bt, here))
    | Constructor (constr, xits) ->
      let@ xits =
        List.fold_left
          (fun acc (x, it) ->
            let@ it = eval_aux it in
            let@ acc in
            Ok ((x, it) :: acc))
          (Ok [])
          xits
      in
      return @@ IT (Constructor (constr, xits), bt, here)
    | Cons (it_head, it_tail) ->
      let@ it_head = eval_aux it_head in
      let@ it_tail = eval_aux it_tail in
      return @@ cons_ (it_head, it_tail) here
    | Apply (fsym, its) ->
      let@ its =
        List.fold_left
          (fun acc it ->
            let@ it = eval_aux it in
            let@ acc in
            Ok (it :: acc))
          (Ok [])
          its
      in
      eval_term_generic eval_aux prog5 (apply_ fsym its bt here)
    | Let ((x, it_v), it_rest) ->
      let@ it_v = eval_aux it_v in
      eval_term_generic eval_aux prog5 (let_ ((x, it_v), it_rest) here)
    | WrapI _ -> Error "todo: WrapI"
    | MapConst (bt, it') ->
      let@ it' = eval_aux it' in
      return @@ const_map_ bt it' here
    | MapSet (it_m, it_k, it_v) ->
      let@ it_m = eval_aux it_m in
      let@ it_k = eval_aux it_k in
      let@ it_v = eval_aux it_v in
      return @@ map_set_ it_m (it_k, it_v) here
    | Cast _ -> Error "todo: Cast"
  in
  eval_aux it


let eval_term_lazily (prog5 : unit Mucore.mu_file) (it : IT.t) : (IT.t, string) result =
  let rec eval_aux (it : IT.t) : (IT.t, string) result =
    let open IT in
    let (IT (t_, _, _)) = it in
    match t_ with
    | Const _ | Sym _ | Unop _ | Binop _ | ITE _ | EachI _ | NthTuple _ | StructMember _
    | StructUpdate _ | RecordMember _ | RecordUpdate _ | SizeOf _ | OffsetOf _
    | MemberShift _ | ArrayShift _ | CopyAllocId _ | HasAllocId _ | Nil _ | Head _
    | Tail _ | NthList _ | ArrayToList _ | Representable _ | Good _ | Aligned _ | MapGet _
    | MapDef _ | Apply _ | Let _ | Match _ ->
      eval_term_generic eval_aux prog5 it
    (* Lazy *)
    | Tuple _ | Struct _ | Record _ | Constructor _ | Cons _ | MapConst _ | MapSet _ ->
      Ok it
    | WrapI _ -> Error "todo: WrapI"
    | Cast _ -> Error "todo: Cast"
  in
  eval_aux it


type eval_mode =
  | Strict
  | Lazy

let empty_mufile : unit Mucore.mu_file =
  { mu_main = None;
    mu_tagDefs = Pmap.empty Sym.compare;
    mu_globs = [];
    mu_funs = Pmap.empty Sym.compare;
    mu_extern = Pmap.empty Id.compare;
    mu_stdlib_syms = SymSet.empty;
    mu_mk_functions = [];
    mu_resource_predicates = [];
    mu_logical_predicates = [];
    mu_datatypes = [];
    mu_lemmata = [];
    mu_call_funinfo = Pmap.empty Sym.compare
  }


let eval ?(mode = Strict) ?(prog5 : unit Mucore.mu_file = empty_mufile) (it : IT.t)
  : (IT.t, string) result
  =
  match mode with
  | Strict -> eval_term_strictly prog5 it
  | Lazy -> eval_term_lazily prog5 it


let partial_eval
  ?(mode = Strict)
  ?(prog5 : unit Mucore.mu_file = empty_mufile)
  (it : IT.t)
  : IT.t
  =
  let f ?(mode = mode) (it : IT.t) : IT.t =
    match eval ~mode ~prog5 it with Ok it' -> it' | Error _ -> it
  in
  let aux (it : IT.t) : IT.t =
    match it with
    | IT (Apply (fsym, _), _, _) ->
      (* If we lazily evaluate every sub-term, all applications will result in a
       * substitution, diverging. As such, we force strict evaluation of recursive calls
       *)
      (match List.assoc_opt Sym.equal fsym prog5.mu_logical_predicates with
       | Some { definition = Def _; _ } -> f it
       | Some { definition = Rec_Def _; _ } -> f ~mode:Strict it
       | Some { definition = Uninterp; _ } | None -> it)
    | _ -> f it
  in
  IT.map_term_post aux it
