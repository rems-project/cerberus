module BT = BaseTypes
module IT = IndexTerms

let check_bits_bt (sgn1, sz1) (sgn2, sz2) here : (unit, string) result =
  if Stdlib.( = ) sgn1 sgn2 then
    Result.error ("Mismatched signs at " ^ Locations.simple_location here)
  else if sz1 <> sz2 then
    Result.error ("Mismatched sizes at " ^ Locations.simple_location here)
  else
    Ok ()


let handle_bounds (sgn, sz) (n : Z.t) : (Z.t, string) result =
  let min, max = BT.bits_range (sgn, sz) in
  match sgn with
  | Unsigned ->
    Ok
      (if Z.gt n max then
         Z.rem n (Z.add max Z.one)
       else if Z.lt n Z.zero then
         Z.add n max
       else
         n)
  | Signed ->
    if Z.lt n min then
      Error "signed underflow"
    else if Z.gt n max then
      Error "signed overflow"
    else
      Ok n


let eval_num_binop
  (eval : IT.t -> (IT.t, string) result)
  (bt : BT.t)
  (here : Locations.t)
  (op : IT.binop)
  (f : Z.t -> Z.t -> Z.t)
  (it1 : IT.t)
  (it2 : IT.t)
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
    (match sgn1 with
     | Unsigned ->
       let@ res = handle_bounds (sgn1, sz1) (f n1 n2) in
       return @@ IT.num_lit_ res bt here
     | Signed ->
       let@ res = handle_bounds (sgn1, sz1) (f n1 n2) in
       return @@ IT.num_lit_ res bt here)
  | _ -> return @@ IT.arith_binop op (it1, it2) here


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
  | Const _ -> return it
  | Sym x -> Result.error (Sym.pp_string x ^ " is free")
  (* Unary ops *)
  | Unop (Not, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bool b), _, _) -> return @@ bool_ (not b) here
     | _ -> return @@ not_ it' here)
  | Unop (Negate, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Z n), _, _) -> return @@ num_lit_ (Z.neg n) bt here
     | IT (Const (Bits ((Signed, sz), n)), _, _) ->
       let@ res = handle_bounds (Signed, sz) (Z.neg n) in
       return @@ num_lit_ res bt here
     | IT (Const (Bits ((Unsigned, _), _)), _, _) ->
       Result.error ("Can't negate unsigned integer at " ^ Locations.simple_location here)
     | _ -> return @@ negate it' here)
  | Unop (BW_CLZ_NoSMT, _) -> failwith "todo: BW_CLZ_NoSMT"
  | Unop (BW_CTZ_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits ((_, sz), n)), _, _) ->
       let res = Z.trailing_zeros n in
       let res = if res = max_int then sz else res in
       return @@ num_lit_ (Z.of_int res) bt here
     | _ -> return @@ arith_unop BW_CTZ_NoSMT it' here)
  | Unop (BW_FFS_NoSMT, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits (_, n)), _, _) ->
       if Z.equal n Z.zero then
         return @@ num_lit_ Z.zero bt here
       else
         let@ it' = return @@ arith_unop BW_CTZ_NoSMT it' here in
         eval_aux (add_ (it', num_lit_ Z.one bt here) here)
     | _ -> return @@ arith_unop BW_FFS_NoSMT it' here)
  | Unop (BW_FLS_NoSMT, _) -> failwith "todo: BW_FLS_NoSMT"
  | Unop (BW_Compl, it') ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Const (Bits (_, n)), _, _) -> return @@ num_lit_ (Z.lognot n) bt here
     | _ -> return @@ arith_unop BW_Compl it' here)
  (* Binary ops *)
  | Binop (And, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) -> if b1 then eval_aux it2 else return it1
     | _ -> return @@ arith_binop And (it1, it2) here)
  | Binop (Or, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) -> if b1 then return it1 else eval_aux it2
     | _ -> return @@ arith_binop Or (it1, it2) here)
  | Binop (Implies, it1, it2) ->
    let@ it1 = eval_aux it1 in
    (match it1 with
     | IT (Const (Bool b1), _, _) ->
       if b1 then eval_aux it2 else return @@ bool_ true here
     | _ -> return @@ arith_binop Implies (it1, it2) here)
  | Binop (Add, it1, it2) -> eval_num_binop Add Z.add it1 it2
  | Binop (Sub, it1, it2) -> eval_num_binop Sub Z.sub it1 it2
  | Binop (Mul, it1, it2) -> eval_num_binop Mul Z.mul it1 it2
  | Binop (MulNoSMT, it1, it2) -> eval_num_binop MulNoSMT Z.mul it1 it2
  | Binop (Div, it1, it2) -> eval_num_binop Div Z.div it1 it2
  | Binop (DivNoSMT, it1, it2) -> eval_num_binop DivNoSMT Z.div it1 it2
  | Binop (Exp, it1, it2) ->
    eval_num_binop Exp (fun n1 n2 -> Z.pow n1 (Z.to_int n2)) it1 it2
  | Binop (ExpNoSMT, it1, it2) ->
    eval_num_binop ExpNoSMT (fun n1 n2 -> Z.pow n1 (Z.to_int n2)) it1 it2
  | Binop (Rem, it1, it2) -> eval_num_binop Rem Z.rem it1 it2
  | Binop (RemNoSMT, it1, it2) -> eval_num_binop RemNoSMT Z.rem it1 it2
  | Binop (Mod, it1, it2) -> eval_num_binop Mod Z.( mod ) it1 it2
  | Binop (ModNoSMT, it1, it2) -> eval_num_binop ModNoSMT Z.( mod ) it1 it2
  | Binop (XORNoSMT, it1, it2) -> eval_num_binop XORNoSMT Z.logxor it1 it2
  | Binop (BW_And, it1, it2) -> eval_num_binop BW_And Z.logand it1 it2
  | Binop (BWOrNoSMT, it1, it2) -> eval_num_binop BWOrNoSMT Z.logor it1 it2
  | Binop (ShiftLeft, _, _) | Binop (ShiftRight, _, _) -> failwith "todo: Bit shifts"
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
     | _ -> return @@ lt_ (it1, it2) here)
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
     | _ -> return @@ le_ (it1, it2) here)
  | Binop (Min, it1, it2) -> eval_num_binop Min Z.min it1 it2
  | Binop (Max, it1, it2) -> eval_num_binop Max Z.max it1 it2
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
         Result.error "Ill-typed"
       else (
         let compare (x1, _) (x2, _) = Id.compare x1 x2 in
         let zipped = List.combine (List.sort compare xits1) (List.sort compare xits2) in
         if List.exists (fun ((x1, _), (x2, _)) -> not (Id.equal x1 x2)) zipped then
           Result.error "Malformed, different members"
         else
           eval_aux
             (and_
                (List.map (fun ((_, it1), (_, it2)) -> eq_ (it1, it2) here) zipped)
                here))
     | IT (Record xits1, _, _), IT (Record xits2, _, _) ->
       let compare (x1, _) (x2, _) = Id.compare x1 x2 in
       let zipped = List.combine (List.sort compare xits1) (List.sort compare xits2) in
       if List.exists (fun ((x1, _), (x2, _)) -> not (Id.equal x1 x2)) zipped then
         Result.error "Malformed, different members"
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
           Result.error "Malformed, same constructor, different members"
         else
           eval_aux
             (and_
                (List.map (fun ((_, it1), (_, it2)) -> eq_ (it1, it2) here) zipped)
                here))
     | _ -> return @@ eq_ (it1, it2) here)
  | Binop (LTPointer, _, _) | Binop (LEPointer, _, _) ->
    failwith "todo: Pointer inequalities"
  | Binop (SetUnion, _, _)
  | Binop (SetIntersection, _, _)
  | Binop (SetDifference, _, _)
  | Binop (SetMember, _, _)
  | Binop (Subset, _, _) ->
    failwith "todo: Sets"
  (* Other ops *)
  | ITE (it_if, it_then, it_else) ->
    let@ it_if = eval_aux it_if in
    (match it_if with
     | IT (Const (Bool b), _, _) -> if b then eval_aux it_then else eval_aux it_else
     | _ -> return @@ ite_ (it_if, it_then, it_else) here)
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
     | _ -> return @@ nthTuple_ ~item_bt:bt (i, it') here)
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
     | _ -> Result.error "Invalid OffsetOf")
  | MemberShift _ -> failwith "todo: MemberShift"
  | ArrayShift _ -> failwith "todo: ArrayShift"
  | CopyAllocId _ -> failwith "todo: CopyAllocId"
  | Head it' ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Cons (it_head, _), _, _) -> eval_aux it_head
     | _ -> return @@ head_ ~item_bt:bt it' here)
  | Tail it' ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Cons (_, it_tail), _, _) -> eval_aux it_tail
     | _ -> return @@ head_ ~item_bt:bt it' here)
  | NthList _ -> failwith "todo: NthList"
  | ArrayToList _ -> failwith "todo: ArrayToList"
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
    let addr = pointerToIntegerCast_ t here in
    if not (BT.equal (IT.bt addr) (IT.bt align)) then
      Result.error "Mismatched types"
    else
      eval_aux (divisible_ (addr, align) here)
  | Apply (fsym, its) ->
    (match List.assoc_opt Sym.equal fsym prog5.mu_logical_predicates with
     | Some { args; definition = Def it_body; _ }
     | Some { args; definition = Rec_Def it_body; _ } ->
       return @@ IT.subst (IT.make_subst (List.combine (List.map fst args) its)) it_body
     | Some { definition = Uninterp; _ } ->
       Result.error ("Function " ^ Sym.pp_string fsym ^ " is uninterpreted")
     | None -> Result.error ("Function " ^ Sym.pp_string fsym ^ " was not found"))
  | Let ((x, it_v), it_rest) -> eval_aux (IT.subst (IT.make_subst [ (x, it_v) ]) it_rest)
  | StructMember (it', member) ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Struct (_, xits), _, _) -> return @@ List.assoc Id.equal member xits
     | _ -> return @@ member_ ~member_bt:bt (it', member) here)
  | StructUpdate ((it_struct, member), it_value) ->
    let@ it_struct = eval_aux it_struct in
    (match it_struct with
     | IT (Struct (tag, xits), _, _) ->
       let xits =
         List.map (fun (x, it) -> (x, if Id.equal x member then it_value else it)) xits
       in
       return @@ struct_ (tag, xits) here
     | _ -> return @@ IT.IT (StructUpdate ((it_struct, member), it_value), bt, here))
  | RecordMember (it', member) ->
    let@ it' = eval_aux it' in
    (match it' with
     | IT (Record xits, _, _) -> return @@ List.assoc Id.equal member xits
     | _ -> return @@ recordMember_ ~member_bt:bt (it', member) here)
  | RecordUpdate ((it_record, member), it_value) ->
    let@ it_record = eval_aux it_record in
    (match it_record with
     | IT (Record xits, _, _) ->
       let xits =
         List.map (fun (x, it) -> (x, if Id.equal x member then it_value else it)) xits
       in
       return @@ record_ xits here
     | _ -> return @@ IT.IT (RecordUpdate ((it_record, member), it_value), bt, here))
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
  | _ -> failwith "todo"


let eval_term_strictly (prog5 : unit Mucore.mu_file) (it : IT.t) : (IT.t, string) result =
  let rec eval_aux (it : IT.t) : (IT.t, string) result =
    let ( let@ ) = Result.bind in
    let return = Result.ok in
    let open IT in
    let (IT (t_, bt, here)) = it in
    match t_ with
    (* Shared *)
    | Const _ | Sym _ | Unop _ | Binop _ | ITE _ | EachI _ | NthTuple _ | SizeOf _
    | OffsetOf _ | MemberShift _ | ArrayShift _ | CopyAllocId _ | Nil _ | Head _ | Tail _
    | NthList _ | ArrayToList _ | Representable _ | Good _ | Aligned _ | StructMember _
    | RecordMember _ | Match _ ->
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
      eval_term_generic eval_aux prog5 (pred_ fsym its bt here)
    | Let ((x, it_v), it_rest) ->
      let@ it_v = eval_aux it_v in
      eval_term_generic eval_aux prog5 (let_ ((x, it_v), it_rest) here)
    | WrapI _ -> failwith "todo: WrapI"
    | MapConst _ -> failwith "todo: MapConst"
    | MapSet _ -> failwith "todo: MapSet"
    | MapGet _ -> failwith "todo: MapGet"
    | MapDef _ -> failwith "todo: MapDef"
    | Cast _ -> failwith "todo: Cast"
  in
  eval_aux it


let eval_term_lazily (prog5 : unit Mucore.mu_file) (it : IT.t) : (IT.t, string) result =
  let rec eval_aux (it : IT.t) : (IT.t, string) result =
    (* let ( let@ ) = Result.bind in *)
    let return = Result.ok in
    let open IT in
    let (IT (t_, _, _)) = it in
    match t_ with
    | Const _ | Sym _ | Unop _ | Binop _ | ITE _ | EachI _ | NthTuple _ | StructMember _
    | StructUpdate _ | RecordMember _ | RecordUpdate _ | SizeOf _ | OffsetOf _
    | MemberShift _ | ArrayShift _ | CopyAllocId _ | Nil _ | Head _ | Tail _ | NthList _
    | ArrayToList _ | Representable _ | Good _ | Aligned _ | Apply _ | Let _ | Match _ ->
      eval_term_generic eval_aux prog5 it
    (* Lazy *)
    | Tuple _ | Struct _ | Record _ | Constructor _ | Cons _ -> return it
    | WrapI _ -> failwith "todo: WrapI"
    | MapConst _ -> failwith "todo: MapConst"
    | MapSet _ -> failwith "todo: MapSet"
    | MapGet _ -> failwith "todo: MapGet"
    | MapDef _ -> failwith "todo: MapDef"
    | Cast _ -> failwith "todo: Cast"
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
    mu_stdlib_syms = Mucore.SymSet.empty;
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
  let aux ?(mode = mode) (it : IT.t) : IT.t =
    match eval ~mode ~prog5 it with Ok it -> it | Error _ -> it
  in
  let rec loop (it : IT.t) : IT.t =
    let (IT (t_, bt, here)) = it in
    match t_ with
    (* Base cases *)
    | Const _ | Sym _ | Nil _ -> it
    | SizeOf _ | OffsetOf _ | Representable _ | Good _ -> aux it
    (* Recusrive cases *)
    | Unop (op, it') -> aux (IT (Unop (op, loop it'), bt, here))
    | Binop (op, it1, it2) -> aux (IT (Binop (op, loop it1, loop it2), bt, here))
    | ITE (it_if, it_then, it_else) ->
      aux (IT (ITE (loop it_if, loop it_then, loop it_else), bt, here))
    | EachI (range, it') -> aux (IT (EachI (range, loop it'), bt, here))
    | Tuple its -> aux (IT (Tuple (List.map loop its), bt, here))
    | NthTuple (i, it') -> aux (IT (NthTuple (i, loop it'), bt, here))
    | Struct (tag, xits) ->
      aux (IT (Struct (tag, List.map (fun (x, it) -> (x, loop it)) xits), bt, here))
    | StructMember (it', member) -> aux (IT (StructMember (loop it', member), bt, here))
    | StructUpdate ((it_struct, member), it_value) ->
      aux (IT (StructUpdate ((loop it_struct, member), loop it_value), bt, here))
    | Record xits ->
      aux (IT (Record (List.map (fun (x, it) -> (x, loop it)) xits), bt, here))
    | RecordMember (it', member) -> aux (IT (RecordMember (loop it', member), bt, here))
    | RecordUpdate ((it_struct, member), it_value) ->
      aux (IT (RecordUpdate ((loop it_struct, member), loop it_value), bt, here))
    | Constructor (constr, xits) ->
      aux
        (IT (Constructor (constr, List.map (fun (x, it) -> (x, loop it)) xits), bt, here))
    | MemberShift (it', tag, member) ->
      aux (IT (MemberShift (loop it', tag, member), bt, here))
    | ArrayShift { base; ct; index } ->
      aux (IT (ArrayShift { base = loop base; ct; index = loop index }, bt, here))
    | CopyAllocId { addr; loc } ->
      aux (IT (CopyAllocId { addr = loop addr; loc = loop loc }, bt, here))
    | Cons (it_head, it_tail) -> aux (IT (Cons (loop it_head, loop it_tail), bt, here))
    | Head it' -> aux (IT (Head (loop it'), bt, here))
    | Tail it' -> aux (IT (Tail (loop it'), bt, here))
    | NthList (i, xs, d) -> aux (IT (NthList (loop i, loop xs, loop d), bt, here))
    | ArrayToList (arr, i, len) ->
      aux (IT (ArrayToList (loop arr, loop i, loop len), bt, here))
    | Aligned { t; align } ->
      aux (IT (Aligned { t = loop t; align = loop align }, bt, here))
    | WrapI (ct, it') -> aux (IT (WrapI (ct, loop it'), bt, here))
    | MapConst (bt', it') -> aux (IT (MapConst (bt', loop it'), bt, here))
    | MapSet (it_m, it_k, it_v) ->
      aux (IT (MapSet (loop it_m, loop it_k, loop it_v), bt, here))
    | MapGet (it_m, it_key) -> aux (IT (MapGet (loop it_m, loop it_key), bt, here))
    | MapDef (sbt, it') -> aux (IT (MapDef (sbt, loop it'), bt, here))
    | Apply (fsym, its) ->
      let it' = IT.IT (Apply (fsym, List.map loop its), bt, here) in
      (match List.assoc_opt Sym.equal fsym prog5.mu_logical_predicates with
       | Some { definition = Def _; _ } -> aux it'
       | Some { definition = Rec_Def _; _ } -> aux ~mode:Strict it'
       | Some { definition = Uninterp; _ } | None -> it')
    | Let ((x, it_v), it_rest) -> aux (IT (Let ((x, loop it_v), loop it_rest), bt, here))
    | Match (it', pits) ->
      aux (IT (Match (loop it', List.map (fun (p, it) -> (p, loop it)) pits), bt, here))
    | Cast (bt', it') -> aux (IT (Cast (bt, loop it'), bt', here))
  in
  loop it
