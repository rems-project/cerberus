module BT = BaseTypes
module CF = Cerb_frontend
include Terms

let equal = equal_annot BT.equal

let compare = compare_annot BT.compare

type t' = BT.t term

type t = BT.t annot

module Surface = struct
  type t' = BaseTypes.Surface.t term

  type t = BaseTypes.Surface.t annot

  let compare = Terms.compare_annot BaseTypes.Surface.compare

  let proj = Terms.map_annot BaseTypes.Surface.proj

  let inj x = Terms.map_annot BaseTypes.Surface.inj x
end

let basetype : 'a. 'a annot -> 'a = function IT (_, bt, _) -> bt

(* TODO rename this get_bt *)
let bt = basetype

(* TODO rename this get_term *)
let term (IT (t, _, _)) = t

(* TODO rename this get_loc *)
let loc (IT (_, _, l)) = l

let pp ?(prec = 0) = Terms.pp ~prec

let pp_with_typf f it = Pp.typ (pp it) (f (bt it))

let pp_with_typ = pp_with_typf BT.pp

let pp_with_eval eval_f =
  let open Cerb_pp_prelude in
  let pp_v tm std_pp =
    match eval_f tm with
    | None -> !^"/* NO_EVAL */" ^^ std_pp
    | Some (IT (_, BT.Struct _, _))
    | Some (IT (_, BT.Record _, _))
    | Some (IT (_, BT.Map (_, _), _)) ->
      std_pp
    | Some v -> !^"/*" ^^^ pp v ^^^ !^"*/" ^^ std_pp
  in
  pp ~f:pp_v


let rec bound_by_pattern (Pat (pat_, bt, _)) =
  match pat_ with
  | PSym s -> [ (s, bt) ]
  | PWild -> []
  | PConstructor (_s, args) ->
    List.concat_map (fun (_id, pat) -> bound_by_pattern pat) args


let rec free_vars_bts (it : 'a annot) : BT.t Sym.Map.t =
  match term it with
  | Const _ -> Sym.Map.empty
  | Sym s -> Sym.Map.singleton s (bt it)
  | Unop (_uop, t1) -> free_vars_bts t1
  | Binop (_bop, t1, t2) -> free_vars_bts_list [ t1; t2 ]
  | ITE (t1, t2, t3) -> free_vars_bts_list [ t1; t2; t3 ]
  | EachI ((_, (s, _), _), t) -> Sym.Map.remove s (free_vars_bts t)
  | Tuple ts -> free_vars_bts_list ts
  | NthTuple (_, t) -> free_vars_bts t
  | Struct (_tag, members) -> free_vars_bts_list (List.map snd members)
  | StructMember (t, _member) -> free_vars_bts t
  | StructUpdate ((t1, _member), t2) -> free_vars_bts_list [ t1; t2 ]
  | Record members -> free_vars_bts_list (List.map snd members)
  | RecordMember (t, _member) -> free_vars_bts t
  | RecordUpdate ((t1, _member), t2) -> free_vars_bts_list [ t1; t2 ]
  | Cast (_cbt, t) -> free_vars_bts t
  | MemberShift (t, _tag, _id) -> free_vars_bts t
  | ArrayShift { base; ct = _; index } -> free_vars_bts_list [ base; index ]
  | CopyAllocId { addr; loc } -> free_vars_bts_list [ addr; loc ]
  | HasAllocId loc -> free_vars_bts_list [ loc ]
  | SizeOf _t -> Sym.Map.empty
  | OffsetOf (_tag, _member) -> Sym.Map.empty
  | Nil _bt -> Sym.Map.empty
  | Cons (t1, t2) -> free_vars_bts_list [ t1; t2 ]
  | Head t -> free_vars_bts t
  | Tail t -> free_vars_bts t
  | NthList (i, xs, d) -> free_vars_bts_list [ i; xs; d ]
  | ArrayToList (arr, i, len) -> free_vars_bts_list [ arr; i; len ]
  | Representable (_sct, t) -> free_vars_bts t
  | Good (_sct, t) -> free_vars_bts t
  | WrapI (_ity, t) -> free_vars_bts t
  | Aligned { t; align } -> free_vars_bts_list [ t; align ]
  | MapConst (_bt, t) -> free_vars_bts t
  | MapSet (t1, t2, t3) -> free_vars_bts_list [ t1; t2; t3 ]
  | MapGet (t1, t2) -> free_vars_bts_list [ t1; t2 ]
  | MapDef ((s, _bt), t) -> Sym.Map.remove s (free_vars_bts t)
  | Apply (_pred, ts) -> free_vars_bts_list ts
  | Let ((nm, t1), t2) ->
    Sym.Map.union
      (fun _ bt1 bt2 ->
        assert (BT.equal bt1 bt2);
        Some bt1)
      (free_vars_bts t1)
      (Sym.Map.remove nm (free_vars_bts t2))
  | Match (e, cases) ->
    let rec aux acc = function
      | [] -> acc
      | (pat, body) :: cases ->
        let bound = Sym.Set.of_list (List.map fst (bound_by_pattern pat)) in
        let more =
          Sym.Map.filter (fun x _ -> not (Sym.Set.mem x bound)) (free_vars_bts body)
        in
        aux
          (Sym.Map.union
             (fun _ bt1 bt2 ->
               assert (BT.equal bt1 bt2);
               Some bt1)
             more
             acc)
          cases
    in
    aux (free_vars_bts e) cases
  | Constructor (_s, args) -> free_vars_bts_list (List.map snd args)


and free_vars_bts_list : 'a annot list -> BT.t Sym.Map.t =
  fun xs ->
  List.fold_left
    (fun ss t ->
      Sym.Map.union
        (fun _ bt1 bt2 ->
          assert (BT.equal bt1 bt2);
          Some bt1)
        ss
        (free_vars_bts t))
    Sym.Map.empty
    xs


let free_vars (it : 'a annot) : Sym.Set.t =
  it |> free_vars_bts |> Sym.Map.bindings |> List.map fst |> Sym.Set.of_list


let free_vars_ (t_ : 'a Terms.term) : Sym.Set.t =
  IT (t_, Unit, Locations.other "")
  |> free_vars_bts
  |> Sym.Map.bindings
  |> List.map fst
  |> Sym.Set.of_list


let free_vars_list (its : 'a annot list) : Sym.Set.t =
  its |> free_vars_bts_list |> Sym.Map.bindings |> List.map fst |> Sym.Set.of_list


type 'bt bindings = ('bt pattern * 'bt annot option) list

type t_bindings = BT.t bindings

let rec fold_ f binders acc = function
  | Sym _s -> acc
  | Const _c -> acc
  | Unop (_uop, t1) -> fold f binders acc t1
  | Binop (_bop, t1, t2) -> fold_list f binders acc [ t1; t2 ]
  | ITE (t1, t2, t3) -> fold_list f binders acc [ t1; t2; t3 ]
  | EachI ((_, (s, bt), _), t) ->
    (* TODO - add location information to binders *)
    let here = Locations.other __FUNCTION__ in
    fold f (binders @ [ (Pat (PSym s, bt, here), None) ]) acc t
  | Tuple ts -> fold_list f binders acc ts
  | NthTuple (_, t) -> fold f binders acc t
  | Struct (_tag, members) -> fold_list f binders acc (List.map snd members)
  | StructMember (t, _member) -> fold f binders acc t
  | StructUpdate ((t1, _member), t2) -> fold_list f binders acc [ t1; t2 ]
  | Record members -> fold_list f binders acc (List.map snd members)
  | RecordMember (t, _member) -> fold f binders acc t
  | RecordUpdate ((t1, _member), t2) -> fold_list f binders acc [ t1; t2 ]
  | Cast (_cbt, t) -> fold f binders acc t
  | MemberShift (t, _tag, _id) -> fold f binders acc t
  | ArrayShift { base; ct = _; index } -> fold_list f binders acc [ base; index ]
  | CopyAllocId { addr; loc } -> fold_list f binders acc [ addr; loc ]
  | HasAllocId loc -> fold_list f binders acc [ loc ]
  | SizeOf _ct -> acc
  | OffsetOf (_tag, _member) -> acc
  | Nil _bt -> acc
  | Cons (t1, t2) -> fold_list f binders acc [ t1; t2 ]
  | Head t -> fold f binders acc t
  | Tail t -> fold f binders acc t
  | NthList (i, xs, d) -> fold_list f binders acc [ i; xs; d ]
  | ArrayToList (arr, i, len) -> fold_list f binders acc [ arr; i; len ]
  | Representable (_sct, t) -> fold f binders acc t
  | Good (_sct, t) -> fold f binders acc t
  | WrapI (_ity, t) -> fold f binders acc t
  | Aligned { t; align } -> fold_list f binders acc [ t; align ]
  | MapConst (_bt, t) -> fold f binders acc t
  | MapSet (t1, t2, t3) -> fold_list f binders acc [ t1; t2; t3 ]
  | MapGet (t1, t2) -> fold_list f binders acc [ t1; t2 ]
  | MapDef ((s, bt), t) ->
    (* TODO - add location information to binders *)
    let here = Locations.other __FUNCTION__ in
    fold f (binders @ [ (Pat (PSym s, bt, here), None) ]) acc t
  | Apply (_pred, ts) -> fold_list f binders acc ts
  | Let ((nm, t1), t2) ->
    let acc' = fold f binders acc t1 in
    (* TODO - add location information to binders *)
    let here = Locations.other __FUNCTION__ in
    fold f (binders @ [ (Pat (PSym nm, basetype t1, here), Some t1) ]) acc' t2
  | Match (e, cases) ->
    (* TODO: check this is good *)
    let acc' = fold f binders acc e in
    let rec aux acc = function
      | [] -> acc
      | (pat, body) :: cases ->
        let acc' = fold f (binders @ [ (pat, Some e) ]) acc body in
        aux acc' cases
    in
    aux acc' cases
  | Constructor (_sym, args) -> fold_list f binders acc (List.map snd args)


and fold f binders acc (IT (term_, _bt, loc)) =
  let acc' = fold_ f binders acc term_ in
  f binders acc' (IT (term_, _bt, loc))


and fold_list f binders acc xs =
  match xs with
  | [] -> acc
  | x :: xs ->
    let acc' = fold f binders acc x in
    fold_list f binders acc' xs


let fold_subterms
  : 'a.
  ?bindings:'bt bindings ->
  ('bt bindings -> 'a -> 'bt annot -> 'a) ->
  'a ->
  'bt annot ->
  'a
  =
  fun ?(bindings = []) f acc t -> fold f bindings acc t


let is_call (f : Sym.t) (IT (it_, _bt, _loc)) =
  match it_ with Apply (f', _) when Sym.equal f f' -> true | _ -> false


let is_good (ct : Sctypes.t) (IT (it_, _bt, _loc)) =
  match it_ with Good (ct', _) when Sctypes.equal ct ct' -> true | _ -> false


let mentions_call f = fold_subterms (fun _binders acc it -> acc || is_call f it) false

let mentions_good ct = fold_subterms (fun _binders acc it -> acc || is_good ct it) false

let preds_of t =
  let add_p s = function IT (Apply (id, _), _, _) -> Sym.Set.add id s | _ -> s in
  fold_subterms (fun _ -> add_p) Sym.Set.empty t


let json it : Yojson.Safe.t = `String (Pp.plain (pp it))

let free_vars_with_rename = function
  | `Term t -> free_vars t
  | `Rename s -> Sym.Set.singleton s


let make_rename ~from ~to_ = Subst.make free_vars_with_rename [ (from, `Rename to_) ]

let make_subst assoc =
  Subst.make free_vars_with_rename (List.map (fun (s, t) -> (s, `Term t)) assoc)


let substitute_lets_flag = Sym.fresh_named "substitute_lets"

let rec subst (su : [ `Term of t | `Rename of Sym.t ] Subst.t) (IT (it, bt, loc)) =
  match it with
  | Sym sym ->
    (match List.assoc_opt Sym.equal sym su.replace with
     | Some (`Term after) ->
       if BT.equal bt (basetype after) then
         ()
       else
         failwith
           ("ill-typed substitution: "
            ^ Pp.plain (Pp.list pp_with_typ [ IT (it, bt, loc); after ]));
       after
     | Some (`Rename sym) -> IT (Sym sym, bt, loc)
     | None -> IT (Sym sym, bt, loc))
  | Const const -> IT (Const const, bt, loc)
  | Unop (uop, it) -> IT (Unop (uop, subst su it), bt, loc)
  | Binop (bop, t1, t2) -> IT (Binop (bop, subst su t1, subst su t2), bt, loc)
  | ITE (it, it', it'') -> IT (ITE (subst su it, subst su it', subst su it''), bt, loc)
  | EachI ((i1, (s, s_bt), i2), t) ->
    let s, t = suitably_alpha_rename su.relevant s t in
    IT (EachI ((i1, (s, s_bt), i2), subst su t), bt, loc)
  | Tuple its -> IT (Tuple (List.map (subst su) its), bt, loc)
  | NthTuple (n, it') -> IT (NthTuple (n, subst su it'), bt, loc)
  | Struct (tag, members) -> IT (Struct (tag, List.map_snd (subst su) members), bt, loc)
  | StructMember (t, m) -> IT (StructMember (subst su t, m), bt, loc)
  | StructUpdate ((t, m), v) -> IT (StructUpdate ((subst su t, m), subst su v), bt, loc)
  | Record members -> IT (Record (List.map_snd (subst su) members), bt, loc)
  | RecordMember (t, m) -> IT (RecordMember (subst su t, m), bt, loc)
  | RecordUpdate ((t, m), v) -> IT (RecordUpdate ((subst su t, m), subst su v), bt, loc)
  | Cast (cbt, t) -> IT (Cast (cbt, subst su t), bt, loc)
  | MemberShift (t, tag, member) -> IT (MemberShift (subst su t, tag, member), bt, loc)
  | ArrayShift { base; ct; index } ->
    IT (ArrayShift { base = subst su base; ct; index = subst su index }, bt, loc)
  | CopyAllocId { addr; loc = ptr } ->
    IT (CopyAllocId { addr = subst su addr; loc = subst su ptr }, bt, loc)
  | HasAllocId ptr -> IT (HasAllocId (subst su ptr), bt, loc)
  | SizeOf t -> IT (SizeOf t, bt, loc)
  | OffsetOf (tag, member) -> IT (OffsetOf (tag, member), bt, loc)
  | Aligned t -> IT (Aligned { t = subst su t.t; align = subst su t.align }, bt, loc)
  | Representable (rt, t) -> IT (Representable (rt, subst su t), bt, loc)
  | Good (rt, t) -> IT (Good (rt, subst su t), bt, loc)
  | WrapI (ity, t) -> IT (WrapI (ity, subst su t), bt, loc)
  | Nil bt' -> IT (Nil bt', bt, loc)
  | Cons (it1, it2) -> IT (Cons (subst su it1, subst su it2), bt, loc)
  | Head it -> IT (Head (subst su it), bt, loc)
  | Tail it -> IT (Tail (subst su it), bt, loc)
  | NthList (i, xs, d) -> IT (NthList (subst su i, subst su xs, subst su d), bt, loc)
  | ArrayToList (arr, i, len) ->
    IT (ArrayToList (subst su arr, subst su i, subst su len), bt, loc)
  | MapConst (arg_bt, t) -> IT (MapConst (arg_bt, subst su t), bt, loc)
  | MapSet (t1, t2, t3) -> IT (MapSet (subst su t1, subst su t2, subst su t3), bt, loc)
  | MapGet (it, arg) -> IT (MapGet (subst su it, subst su arg), bt, loc)
  | MapDef ((s, abt), body) ->
    let s, body = suitably_alpha_rename su.relevant s body in
    IT (MapDef ((s, abt), subst su body), bt, loc)
  | Apply (name, args) -> IT (Apply (name, List.map (subst su) args), bt, loc)
  | Let ((name, t1), t2) ->
    if Sym.Set.mem substitute_lets_flag su.flags then (
      let t1 = subst su t1 in
      subst (Subst.add free_vars_with_rename (name, `Term t1) su) t2)
    else (
      let name, t2 = suitably_alpha_rename su.relevant name t2 in
      IT (Let ((name, subst su t1), subst su t2), bt, loc))
  | Match (e, cases) ->
    let e = subst su e in
    let cases = List.map (subst_under_pattern su) cases in
    IT (Match (e, cases), bt, loc)
  | Constructor (s, args) ->
    let args = List.map (fun (id, e) -> (id, subst su e)) args in
    IT (Constructor (s, args), bt, loc)


and alpha_rename s body =
  let s' = Sym.fresh_same s in
  (s', subst (make_rename ~from:s ~to_:s') body)


and suitably_alpha_rename syms s body =
  if Sym.Set.mem s syms then
    alpha_rename s body
  else
    (s, body)


and subst_under_pattern su (pat, body) =
  let pat, body = suitably_alpha_rename_pattern su (pat, body) in
  (pat, subst su body)


and suitably_alpha_rename_pattern su (Pat (pat_, bt, loc), body) =
  match pat_ with
  | PSym s ->
    let s, body = suitably_alpha_rename su.relevant s body in
    (Pat (PSym s, bt, loc), body)
  | PWild -> (Pat (PWild, bt, loc), body)
  | PConstructor (s, args) ->
    let body, args =
      List.fold_left_map
        (fun body (id, pat') ->
          let pat', body = suitably_alpha_rename_pattern su (pat', body) in
          (body, (id, pat')))
        body
        args
    in
    (Pat (PConstructor (s, args), bt, loc), body)


let substitute_lets =
  let flags = Sym.Set.of_list [ substitute_lets_flag ] in
  subst { (make_subst []) with flags }


let is_const = function IT (Const const, bt, _loc) -> Some (const, bt) | _ -> None

let is_z = function IT (Const (Z z), _bt, _loc) -> Some z | _ -> None

let is_z_ it = Option.is_some (is_z it)

let get_num_z it =
  match term it with
  | Const (Z _) -> is_z it
  | Const (Bits (info, z)) -> Some (BT.normalise_to_range info z)
  | _ -> None


let is_bits_const = function
  | IT (Const (Bits (info, n)), _, _) -> Some (info, n)
  | _ -> None


let is_pointer = function
  | IT (Const (Pointer { alloc_id; addr }), _bt, _) -> Some (alloc_id, addr)
  | _ -> None


let is_alloc_id = function
  | IT (Const (Alloc_id alloc_id), _bt, _) -> Some alloc_id
  | _ -> None


let is_sym = function IT (Sym sym, bt, _) -> Some (sym, bt) | _ -> None

let is_bool = function IT (Const (Bool b), _, _) -> Some b | _ -> None

let is_q = function IT (Const (Q q), _, _) -> Some q | _ -> None

let is_map_get = function IT (MapGet (f, arg), _, _) -> Some (f, arg) | _ -> None

let zero_frac = function
  | IT (Const (Q q), _, _) when Q.equal Q.zero q -> true
  | _ -> false


let is_true = function IT (Const (Bool true), _, _) -> true | _ -> false

let is_false = function IT (Const (Bool false), _, _) -> true | _ -> false

let is_eq = function IT (Binop (EQ, lhs, rhs), _, _) -> Some (lhs, rhs) | _ -> None

let is_and = function IT (Binop (And, it, it'), _, _) -> Some (it, it') | _ -> None

let is_or = function IT (Binop (Or, it, it'), _, _) -> Some (it, it') | _ -> None

let is_implies = function
  | IT (Binop (Implies, it, it'), _, _) -> Some (it, it')
  | _ -> None


let is_not = function IT (Unop (Not, it), _, _) -> Some it | _ -> None

let is_negate = function IT (Unop (Negate, it), _, _) -> Some it | _ -> None

let is_lt = function IT (Binop (LT, x, y), _, _) -> Some (x, y) | _ -> None

let is_le = function IT (Binop (LE, x, y), _, _) -> Some (x, y) | _ -> None

let rec split_and it =
  match is_and it with Some (it1, it2) -> split_and it1 @ split_and it2 | None -> [ it ]


let rec is_const_val = function
  | IT (Const _, _, _) -> true
  | IT (Nil _, _, _) -> true
  | IT (Cons (hd, tl), _, _) -> is_const_val hd && is_const_val tl
  | _ -> false


let is_pred_ = function IT (Apply (name, args), _, _) -> Some (name, args) | _ -> None

let is_member = function IT (StructMember (it, id), _, _) -> Some (it, id) | _ -> None

(* shorthands *)

let use_vip = ref true

(* lit *)
let sym_ (sym, bt, loc) = IT (Sym sym, bt, loc)

let z_ n loc = IT (Const (Z n), BT.Integer, loc)

let alloc_id_ n loc = IT (Const (Alloc_id n), BT.Alloc_id, loc)

let num_lit_ n bt loc =
  match bt with
  | BT.Bits (sign, sz) ->
    assert (BT.fits_range (sign, sz) n);
    IT (Const (Bits ((sign, sz), n)), bt, loc)
  | BT.Integer -> z_ n loc
  | _ -> failwith ("num_lit_: not a type with numeric literals: " ^ Pp.plain (BT.pp bt))


let q_ (n, n') loc = IT (Const (Q (Q.make (Z.of_int n) (Z.of_int n'))), BT.Real, loc)

let q1_ q loc = IT (Const (Q q), BT.Real, loc)

let pointer_ ~alloc_id ~addr loc =
  let alloc_id = if !use_vip then alloc_id else Z.zero in
  IT (Const (Pointer { alloc_id; addr }), BT.Loc (), loc)


let bool_ b loc = IT (Const (Bool b), BT.Bool, loc)

let unit_ loc = IT (Const Unit, BT.Unit, loc)

let int_ n loc = z_ (Z.of_int n) loc

let int_lit_ n bt loc = num_lit_ (Z.of_int n) bt loc

let default_ bt loc = IT (Const (Default bt), bt, loc)

let const_ctype_ ct loc = IT (Const (CType_const ct), BT.CType, loc)

(* cmp_op *)
let lt_ (it, it') loc =
  if BT.equal (bt it) (bt it') then
    ()
  else
    failwith ("lt_: type mismatch: " ^ Pp.plain (Pp.list pp_with_typ [ it; it' ]));
  IT (Binop (LT, it, it'), BT.Bool, loc)


let le_ (it, it') loc =
  if BT.equal (bt it) (bt it') then
    ()
  else
    failwith ("le_: type mismatch: " ^ Pp.plain (Pp.list pp_with_typ [ it; it' ]));
  IT (Binop (LE, it, it'), BT.Bool, loc)


let gt_ (it, it') = lt_ (it', it)

let ge_ (it, it') = le_ (it', it)

(* bool_op *)
let vargs_binop basevalue binop = function
  | [] -> basevalue
  | it :: its -> List.fold_left binop it its


let and2_ (it, it') loc = IT (Binop (And, it, it'), BT.Bool, loc)

let or2_ (it, it') loc = IT (Binop (Or, it, it'), BT.Bool, loc)

let and_ its loc = vargs_binop (bool_ true loc) (Tools.curry (fun p -> and2_ p loc)) its

let or_ its loc = vargs_binop (bool_ false loc) (Tools.curry (fun p -> or2_ p loc)) its

let impl_ (it, it') loc = IT (Binop (Implies, it, it'), BT.Bool, loc)

let not_ it loc = IT (Unop (Not, it), bt it, loc)

let bw_compl_ it loc = IT (Unop (BW_Compl, it), bt it, loc)

let ite_ (it, it', it'') loc = IT (ITE (it, it', it''), bt it', loc)

let eq_ (it, it') loc =
  if BT.equal (bt it) (bt it') then
    ()
  else
    failwith ("eq_: type mismatch: " ^ Pp.plain (Pp.list pp_with_typ [ it; it' ]));
  IT (Binop (EQ, it, it'), BT.Bool, loc)


let eq__ it it' = eq_ (it, it')

let ne_ (it, it') loc = not_ (eq_ (it, it') loc) loc

let ne__ it it' = ne_ (it, it')

let eq_sterm_ (it, it') loc = IT (Binop (EQ, it, it'), BT.Bool, loc)

let bool_sterm_ b loc = IT (Const (Bool b), BT.Bool, loc)

let and2_sterm_ (it, it') loc = IT (Binop (And, it, it'), BT.Bool, loc)

let and_sterm_ its loc =
  vargs_binop (bool_sterm_ true loc) (Tools.curry (fun p -> and2_sterm_ p loc)) its


let or2_sterm_ (it, it') loc = IT (Binop (Or, it, it'), BT.Bool, loc)

let or_sterm_ its loc =
  vargs_binop (bool_sterm_ true loc) (Tools.curry (fun p -> or2_sterm_ p loc)) its


let let_ ((nm, x), y) loc = IT (Let ((nm, x), y), basetype y, loc)

(* let disperse_not_ it = *)
(*   match term it with *)
(*   | And xs -> or_ (List.map not_ xs) *)
(*   | Or xs -> and_ (List.map not_ xs) *)
(*   | Implies (x, y) -> and_ [x; not_ y] *)
(*   | _ -> not_ it *)

let eachI_ (i1, (s, bt), i2) t loc = IT (EachI ((i1, (s, bt), i2), t), BT.Bool, loc)
(* let existsI_ (i1, s, i2) t = not_ (eachI_ (i1, s, i2) (not_ t)) *)

(* arith_op *)
let negate it loc = IT (Unop (Negate, it), bt it, loc)

let add_ (it, it') loc = IT (Binop (Add, it, it'), bt it, loc)

let sub_ (it, it') loc = IT (Binop (Sub, it, it'), bt it, loc)

let mul_ (it, it') loc =
  if BT.equal (bt it) (bt it') then
    IT (Binop (Mul, it, it'), bt it, loc)
  else
    failwith ("mul_: type mismatch: " ^ Pp.plain (Pp.list pp_with_typ [ it; it' ]))


let mul_no_smt_ (it, it') loc = IT (Binop (MulNoSMT, it, it'), bt it, loc)

let div_ (it, it') loc = IT (Binop (Div, it, it'), bt it, loc)

let div_no_smt_ (it, it') loc = IT (Binop (DivNoSMT, it, it'), bt it, loc)

let exp_ (it, it') loc = IT (Binop (Exp, it, it'), bt it, loc)

let exp_no_smt_ (it, it') loc = IT (Binop (ExpNoSMT, it, it'), bt it, loc)

let rem_ (it, it') loc = IT (Binop (Rem, it, it'), bt it, loc)

let rem_no_smt_ (it, it') loc = IT (Binop (RemNoSMT, it, it'), bt it, loc)

let mod_ (it, it') loc = IT (Binop (Mod, it, it'), bt it, loc)

let mod_no_smt_ (it, it') loc = IT (Binop (ModNoSMT, it, it'), bt it, loc)

let divisible_ (it, it') loc = eq_ (mod_ (it, it') loc, int_lit_ 0 (bt it) loc) loc

let rem_f_ (it, it') loc = mod_ (it, it') loc

let min_ (it, it') loc = IT (Binop (Min, it, it'), bt it, loc)

let max_ (it, it') loc = IT (Binop (Max, it, it'), bt it, loc)

let intToReal_ it loc = IT (Cast (Real, it), BT.Real, loc)

let realToInt_ it loc = IT (Cast (Integer, it), BT.Integer, loc)

let arith_binop op (it, it') loc = IT (Binop (op, it, it'), bt it, loc)

let arith_unop op it loc = IT (Unop (op, it), bt it, loc)

let arith_binop_check op (it, it') loc =
  assert (BT.equal (bt it) (bt it'));
  arith_binop op (it, it') loc


let add_check_ = arith_binop_check Add

let ( %+ ) t t' = add_ (t, t')

let ( %- ) t t' = sub_ (t, t')

let ( %* ) t t' = mul_ (t, t')

let ( %/ ) t t' = div_ (t, t')

let ( %== ) t t' = eq_ (t, t')

let ( %!= ) t t' = ne_ (t, t')

let ( %< ) t t' = lt_ (t, t')

let ( %<= ) t t' = le_ (t, t')

let ( %> ) t t' = gt_ (t, t')

let ( %>= ) t t' = ge_ (t, t')

(* tuple_op *)
let tuple_ its loc = IT (Tuple its, BT.Tuple (List.map bt its), loc)

let nthTuple_ ~item_bt (n, it) loc = IT (NthTuple (n, it), item_bt, loc)

(* struct_op *)
let struct_ (tag, members) loc = IT (Struct (tag, members), BT.Struct tag, loc)

let member_ ~member_bt (it, member) loc = IT (StructMember (it, member), member_bt, loc)

let ( %. ) struct_decls t member =
  let tag =
    match bt t with
    | BT.Struct tag -> tag
    | _ -> Cerb_debug.error "illtyped index term. not a struct"
  in
  let member_bt =
    match
      List.assoc_opt Id.equal member (Memory.member_types (Sym.Map.find tag struct_decls))
    with
    | Some sct -> Memory.bt_of_sct sct
    | None ->
      Cerb_debug.error
        ("struct " ^ Sym.pp_string tag ^ " does not have member " ^ Id.pp_string member)
  in
  member_ ~member_bt (t, member)


let record_ members loc =
  IT (Record members, BT.Record (List.map (fun (s, t) -> (s, basetype t)) members), loc)


let recordMember_ ~member_bt (t, member) loc =
  IT (RecordMember (t, member), member_bt, loc)


(* pointer_op *)
let null_ loc = IT (Const Null, BT.Loc (), loc)

let ltPointer_ (it, it') loc = IT (Binop (LTPointer, it, it'), BT.Bool, loc)

let lePointer_ (it, it') loc = IT (Binop (LEPointer, it, it'), BT.Bool, loc)

let gtPointer_ (it, it') loc = ltPointer_ (it', it) loc

let gePointer_ (it, it') loc = lePointer_ (it', it) loc

let cast_ bt' it loc = if BT.equal bt' (bt it) then it else IT (Cast (bt', it), bt', loc)

let uintptr_const_ n loc = num_lit_ n Memory.uintptr_bt loc

let uintptr_int_ n loc = uintptr_const_ (Z.of_int n) loc
(* for integer-mode: z_ n *)

let addr_ it loc =
  assert (BT.equal (bt it) (Loc ()));
  cast_ Memory.uintptr_bt it loc


(* for integer-mode: cast_ Integer it *)

let allocId_ it loc = cast_ Alloc_id it loc

let memberShift_ (base, tag, member) loc =
  IT (MemberShift (base, tag, member), BT.Loc (), loc)


let arrayShift_ ~base ~index ct loc = IT (ArrayShift { base; ct; index }, BT.Loc (), loc)

let copyAllocId_ ~addr ~loc:ptr loc = IT (CopyAllocId { addr; loc = ptr }, BT.Loc (), loc)

let hasAllocId_ ptr loc =
  (* Futzing seems to be necessary because given the current SMT sovler mapping,
     the solver can't conclude `has_alloc_id(&p[x]) ==> has_alloc_id(p)` and
     similarly for &p->x. This may be avoidable with a different solver mapping. *)
  let rec futz = function
    | IT ((MemberShift (base, _, _) | ArrayShift { base; _ }), _, _) -> futz base
    | it -> it
  in
  IT (HasAllocId (futz ptr), BT.Bool, loc)


let sizeOf_ ct loc = IT (SizeOf ct, Memory.size_bt, loc)

let isIntegerToPointerCast = function
  | IT (Cast (BT.Loc (), IT (_, BT.Integer, _)), _, _) -> true
  | IT (Cast (BT.Loc (), IT (_, BT.Bits _, _)), _, _) -> true
  | _ -> false


let pointer_offset_ (base, offset) loc =
  arrayShift_ ~base (Sctypes.Integer Char) ~index:offset loc


(* list_op *)
let nil_ ~item_bt loc = IT (Nil item_bt, BT.List item_bt, loc)

let cons_ (it, it') loc = IT (Cons (it, it'), bt it', loc)

let list_ ~item_bt its ~nil_loc =
  let rec aux = function
    | [] -> IT (Nil item_bt, BT.List item_bt, nil_loc)
    | x :: xs -> IT (Cons (x, aux xs), BT.List item_bt, loc x)
  in
  aux its


let head_ ~item_bt it loc = IT (Head it, item_bt, loc)

let tail_ it loc = IT (Tail it, bt it, loc)

let nthList_ (n, it, d) loc = IT (NthList (n, it, d), bt d, loc)

let array_to_list_ (arr, i, len) bt loc = IT (ArrayToList (arr, i, len), bt, loc)

let rec dest_list it =
  match term it with
  | Nil _bt -> Some []
  | Cons (x, xs) -> Option.map (fun ys -> x :: ys) (dest_list xs)
  (* TODO: maybe include Tail, if we ever actually use it? *)
  | _ -> None


(* set_op *)
let setMember_ (it, it') loc = IT (Binop (SetMember, it, it'), BT.Bool, loc)

(* let setUnion_ its = IT (Set_op (SetUnion its), bt (hd its))
 * let setIntersection_ its = IT (Set_op (SetIntersection its), bt (hd its)) *)
let setDifference_ (it, it') loc = IT (Binop (SetDifference, it, it'), bt it, loc)

let subset_ (it, it') loc = IT (Binop (Subset, it, it'), BT.Bool, loc)

(* ct_pred *)
let representable_ (t, it) loc = IT (Representable (t, it), BT.Bool, loc)

let good_ (sct, it) loc = IT (Good (sct, it), BT.Bool, loc)

let wrapI_ (ity, arg) loc =
  IT (WrapI (ity, arg), Memory.bt_of_sct (Sctypes.Integer ity), loc)


let alignedI_ ~t ~align loc =
  assert (BT.equal (bt t) (Loc ()));
  assert (BT.equal Memory.uintptr_bt (bt align));
  IT (Aligned { t; align }, BT.Bool, loc)


let aligned_ (t, ct) loc =
  alignedI_ ~t ~align:(int_lit_ (Memory.align_of_ctype ct) Memory.uintptr_bt loc) loc


let const_map_ index_bt t loc = IT (MapConst (index_bt, t), BT.Map (index_bt, bt t), loc)

let map_set_ t1 (t2, t3) loc = IT (MapSet (t1, t2, t3), bt t1, loc)

let map_get_ v arg loc =
  match bt v with
  | BT.Map (dt, rbt) ->
    if BT.equal dt (bt arg) then
      ()
    else
      failwith ("mag_get_: type mismatch: " ^ Pp.plain (Pp.list pp_with_typ [ v; arg ]));
    IT (MapGet (v, arg), rbt, loc)
  | _ -> Cerb_debug.error "illtyped index term"


let map_def_ (s, abt) body loc = IT (MapDef ((s, abt), body), BT.Map (abt, bt body), loc)

let make_array_ ~index_bt ~item_bt items (* assumed all of item_bt *) loc =
  let base_value = const_map_ index_bt (default_ item_bt loc) loc in
  let _, value =
    List.fold_left
      (fun (index, value) item ->
        let index_it = num_lit_ (Z.of_int index) index_bt loc in
        (index + 1, map_set_ value (index_it, item) loc))
      (0, base_value)
      items
  in
  value


let apply_ name args rbt loc = IT (Apply (name, args), rbt, loc)

(* let let_ sym e body = *)
(*   subst (make_subst [(sym, e)]) body *)

let fresh bt loc =
  let symbol = Sym.fresh () in
  (symbol, sym_ (symbol, bt, loc))


let fresh_named bt name loc =
  let symbol = Sym.fresh_named name in
  (symbol, sym_ (symbol, bt, loc))


let fresh_same bt symbol' loc =
  let symbol = Sym.fresh_same symbol' in
  (symbol, sym_ (symbol, bt, loc))


let def_ sym e loc = eq_ (sym_ (sym, bt e, loc), e) loc

let in_range within (min, max) loc =
  and_ [ le_ (min, within) loc; le_ (within, max) loc ] loc


let rec in_z_range within (min_z, max_z) loc =
  match bt within with
  | BT.Integer -> in_range within (z_ min_z loc, z_ max_z loc) loc
  | BT.Bits (sign, sz) ->
    let the_bt = bt within in
    let min_possible, max_possible = BT.bits_range (sign, sz) in
    let min_c =
      if Z.leq min_z min_possible then
        bool_ true loc
      else if Z.leq min_z max_possible then
        le_ (num_lit_ min_z the_bt loc, within) loc
      else
        bool_ false loc
    in
    let max_c =
      if Z.leq max_possible max_z then
        bool_ true loc
      else if Z.leq min_possible max_z then
        le_ (within, num_lit_ max_z the_bt loc) loc
      else
        bool_ false loc
    in
    and_ [ min_c; max_c ] loc
  | Loc () ->
    (* §6.3.2.3#6 allows converting pointers to any integer type so long as the value of
       the pointer fits. If uintptr_t and intptr_t exist, then they are guaranteed to be
       big enough to fit any valid pointer (to void). From there, it's just a matter of
       checking the bits fit. *)
    or_
      [ in_z_range (cast_ Memory.uintptr_bt within loc) (min_z, max_z) loc;
        in_z_range (cast_ Memory.intptr_bt within loc) (min_z, max_z) loc
      ]
      loc
  | _ -> failwith ("in_z_range: unsupported type: " ^ Pp.plain (pp_with_typ within))


let const_of_c_sig (c_sig : Sctypes.c_concrete_sig) loc =
  (* ideally the ctypes would have location information attached *)
  let open Option in
  let@ ret_ct = Sctypes.of_ctype c_sig.sig_return_ty in
  let@ arg_cts = ListM.mapM Sctypes.of_ctype c_sig.sig_arg_tys in
  let arg_cts = List.map (Fun.flip const_ctype_ loc) arg_cts in
  let arg_v = list_ ~item_bt:BT.CType arg_cts ~nil_loc:loc in
  return
    (tuple_
       [ const_ctype_ ret_ct loc;
         arg_v;
         bool_ c_sig.sig_variadic loc;
         bool_ c_sig.sig_has_proto loc
       ]
       loc)


(* let _non_vip_constraint about loc =  *)
(*   eq_ (allocId_ about loc, alloc_id_ Z.zero loc) loc *)

(* TODO: are the constraints `0<about` and `about+pointee_size-1 <= max-pointer`
   required? *)
let value_check_pointer mode ~pointee_ct about loc =
  match mode with
  | `Representable -> bool_ true loc
  | `Good ->
    (* let about_int = addr_ about loc in *)
    (* let pointee_size = match pointee_ct with *)
    (*   | Sctypes.Void -> 1 *)
    (*   | Function _ -> 1 *)
    (*   | _ -> Memory.size_of_ctype pointee_ct *)
    (* in *)
    and_
      (List.filter_map
         Fun.id
         [ (* Some (le_ (intptr_int_ 0 loc, about_int) loc); *)
           (* Some (le_ (sub_ (add_ (about_int, intptr_int_ pointee_size loc) loc,
              intptr_int_ 1 loc) loc, *)
           (*         intptr_const_ Memory.max_pointer loc) loc); *)
           (* if !use_vip then None else Some (non_vip_constraint about loc); *)
           Some (aligned_ (about, pointee_ct) loc)
         ])
      loc


let value_check_array_size_warning = ref 100

let value_check mode (struct_layouts : Memory.struct_decls) ct about loc =
  let open Sctypes in
  let open Memory in
  let rec aux (ct_ : Sctypes.t) about =
    match ct_ with
    | Void -> bool_ true loc
    | Integer it ->
      in_z_range about (Memory.min_integer_type it, Memory.max_integer_type it) loc
    | Array (_, None) ->
      Cerb_debug.error "todo: 'representable' for arrays with unknown length"
    | Array (item_ct, Some n) ->
      if n > !value_check_array_size_warning then (
        (* FIXME: handle this better rather than just warning *)
        Pp.warn
          loc
          (Pp.string ("good/value_check of array of large size: " ^ Int.to_string n));
        value_check_array_size_warning := n)
      else
        ();
      (* let partiality = partiality_check_array ~length:n ~item_ct about in *)
      let ix_bt =
        match BT.is_map_bt (bt about) with
        | Some (abt, _) -> abt
        | _ ->
          failwith ("value_check: argument not a map: " ^ Pp.plain (pp_with_typ about))
      in
      let () =
        if BT.equal ix_bt Memory.uintptr_bt then
          ()
        else
          Pp.warn
            (Locations.other __FUNCTION__)
            (Pp.item "unexpected type of array arg" (pp_with_typ about))
      in
      let i_s, i = fresh ix_bt loc in
      eachI_ (0, (i_s, ix_bt), n - 1) (aux item_ct (map_get_ about i loc)) loc
    | Pointer pointee_ct -> value_check_pointer mode ~pointee_ct about loc
    | Struct tag ->
      and_
        (List.filter_map
           (fun piece ->
             match piece.member_or_padding with
             | Some (member, mct) ->
               let member_bt = Memory.bt_of_sct mct in
               let member_it = member_ ~member_bt (about, member) loc in
               Some (aux mct member_it)
             | None -> None)
           (Sym.Map.find tag struct_layouts))
        loc
    | Function _ -> Cerb_debug.error "todo: function types"
  in
  aux ct about


let good_value = value_check `Good

let representable = value_check `Representable

let good_pointer = value_check_pointer `Good

let promote_to_compare it it' loc =
  let res_bt =
    match (bt it, bt it') with
    | bt1, bt2 when BT.equal bt1 bt2 -> bt1
    | BT.Bits (_, sz), BT.Bits (_, sz') -> BT.Bits (BT.Signed, sz + sz' + 2)
    | _ ->
      failwith
        ("promote to compare: impossible types to compare: "
         ^ Pp.plain (Pp.list pp_with_typ [ it; it' ]))
  in
  let cast it = if BT.equal (bt it) res_bt then it else cast_ res_bt it loc in
  (cast it, cast it')


let nth_array_to_list_fact n xs d =
  let here = Locations.other __FUNCTION__ in
  match term xs with
  | ArrayToList (arr, i, len) ->
    let lt_n_len = lt_ (promote_to_compare n len here) here in
    let lhs = nthList_ (n, xs, d) here in
    let rhs =
      ite_
        ( and_ [ le_ (int_lit_ 0 (bt n) here, n) here; lt_n_len ] here,
          map_get_ arr (add_ (i, cast_ (bt i) n here) here) here,
          d )
        here
    in
    Some (eq_ (lhs, rhs) here)
  | _ -> None


let rec wrap_bindings_match bs default_v v =
  match (bs, v) with
  | _, None -> None
  | [], _ -> v
  | (pat, x) :: bindings, _ ->
    (match wrap_bindings_match bindings default_v v with
     | None -> None
     | Some v2 ->
       let pat_ss = Sym.Set.of_list (List.map fst (bound_by_pattern pat)) in
       if Sym.Set.is_empty (Sym.Set.inter pat_ss (free_vars v2)) then
         Some v2
       else (
         match x with
         | None -> None
         | Some match_e ->
           let here = Locations.other __FUNCTION__ in
           Some
             (IT
                ( Match
                    ( match_e,
                      [ (pat, v2); (Pat (PWild, basetype match_e, here), default_v) ] ),
                  basetype v2,
                  here ))))


let nth_array_to_list_facts (binders_terms : (t_bindings * t) list) =
  let here = Locations.other __FUNCTION__ in
  let nths =
    List.filter_map
      (fun (bs, it) ->
        match term it with NthList (n, xs, d) -> Some (bs, (n, d, bt xs)) | _ -> None)
      binders_terms
  in
  let arr_lists =
    List.filter_map
      (fun (bs, it) ->
        match term it with ArrayToList _ -> Some (bs, (it, bt it)) | _ -> None)
      binders_terms
  in
  List.concat_map
    (fun (bs1, (n, d, bt1)) ->
      List.filter_map
        (fun (bs2, (xs, bt2)) ->
          if BT.equal bt1 bt2 then
            wrap_bindings_match
              (bs1 @ bs2)
              (bool_ true here)
              (nth_array_to_list_fact n xs d)
          else
            None)
        arr_lists)
    nths


let rec map_term_pre (f : t -> t) (it : t) : t =
  let (IT (it_, bt, here)) = f it in
  let loop = map_term_pre f in
  let it_ : t' =
    match it_ with
    | Const _ | Sym _ | Nil _ | SizeOf _ | OffsetOf _ -> it_
    | Unop (op, it') -> Unop (op, loop it')
    | Binop (op, it1, it2) -> Binop (op, loop it1, loop it2)
    | ITE (it_if, it_then, it_else) -> ITE (loop it_if, loop it_then, loop it_else)
    | EachI (range, it') -> EachI (range, loop it')
    | Tuple its -> Tuple (List.map loop its)
    | NthTuple (i, it') -> NthTuple (i, loop it')
    | Struct (tag, xits) -> Struct (tag, List.map_snd loop xits)
    | StructMember (it', member) -> StructMember (loop it', member)
    | StructUpdate ((it_struct, member), it_value) ->
      StructUpdate ((loop it_struct, member), loop it_value)
    | Record xits -> Record (List.map_snd loop xits)
    | RecordMember (it', member) -> RecordMember (loop it', member)
    | RecordUpdate ((it_struct, member), it_value) ->
      RecordUpdate ((loop it_struct, member), loop it_value)
    | Constructor (constr, xits) -> Constructor (constr, List.map_snd loop xits)
    | MemberShift (it', tag, member) -> MemberShift (loop it', tag, member)
    | ArrayShift { base; ct; index } ->
      ArrayShift { base = loop base; ct; index = loop index }
    | CopyAllocId { addr; loc } -> CopyAllocId { addr = loop addr; loc = loop loc }
    | Cons (it_head, it_tail) -> Cons (loop it_head, loop it_tail)
    | Head it' -> Head (loop it')
    | Tail it' -> Tail (loop it')
    | NthList (i, xs, d) -> NthList (loop i, loop xs, loop d)
    | ArrayToList (arr, i, len) -> ArrayToList (loop arr, loop i, loop len)
    | Representable (ct, it') -> Representable (ct, loop it')
    | Good (ct, it') -> Good (ct, loop it')
    | Aligned { t; align } -> Aligned { t = loop t; align = loop align }
    | WrapI (ct, it') -> WrapI (ct, loop it')
    | MapConst (bt', it') -> MapConst (bt', loop it')
    | MapSet (it_m, it_k, it_v) -> MapSet (loop it_m, loop it_k, loop it_v)
    | MapGet (it_m, it_key) -> MapGet (loop it_m, loop it_key)
    | MapDef (sbt, it') -> MapDef (sbt, loop it')
    | Apply (fsym, its) -> Apply (fsym, List.map loop its)
    | Let ((x, it_v), it_rest) -> Let ((x, loop it_v), loop it_rest)
    | Match (it', pits) -> Match (loop it', List.map_snd loop pits)
    | Cast (bt', it') -> Cast (bt', loop it')
    | HasAllocId it' -> HasAllocId (loop it')
  in
  IT (it_, bt, here)


let rec map_term_post (f : t -> t) (it : t) : t =
  let (IT (it_, bt, here)) = it in
  let loop = map_term_post f in
  let it_ : t' =
    match it_ with
    | Const _ | Sym _ | Nil _ | SizeOf _ | OffsetOf _ -> it_
    | Unop (op, it') -> Unop (op, loop it')
    | Binop (op, it1, it2) -> Binop (op, loop it1, loop it2)
    | ITE (it_if, it_then, it_else) -> ITE (loop it_if, loop it_then, loop it_else)
    | EachI (range, it') -> EachI (range, loop it')
    | Tuple its -> Tuple (List.map loop its)
    | NthTuple (i, it') -> NthTuple (i, loop it')
    | Struct (tag, xits) -> Struct (tag, List.map_snd loop xits)
    | StructMember (it', member) -> StructMember (loop it', member)
    | StructUpdate ((it_struct, member), it_value) ->
      StructUpdate ((loop it_struct, member), loop it_value)
    | Record xits -> Record (List.map_snd loop xits)
    | RecordMember (it', member) -> RecordMember (loop it', member)
    | RecordUpdate ((it_struct, member), it_value) ->
      RecordUpdate ((loop it_struct, member), loop it_value)
    | Constructor (constr, xits) -> Constructor (constr, List.map_snd loop xits)
    | MemberShift (it', tag, member) -> MemberShift (loop it', tag, member)
    | ArrayShift { base; ct; index } ->
      ArrayShift { base = loop base; ct; index = loop index }
    | CopyAllocId { addr; loc } -> CopyAllocId { addr = loop addr; loc = loop loc }
    | HasAllocId it' -> HasAllocId (loop it')
    | Cons (it_head, it_tail) -> Cons (loop it_head, loop it_tail)
    | Head it' -> Head (loop it')
    | Tail it' -> Tail (loop it')
    | NthList (i, xs, d) -> NthList (loop i, loop xs, loop d)
    | ArrayToList (arr, i, len) -> ArrayToList (loop arr, loop i, loop len)
    | Representable (ct, it') -> Representable (ct, loop it')
    | Good (ct, it') -> Good (ct, loop it')
    | Aligned { t; align } -> Aligned { t = loop t; align = loop align }
    | WrapI (ct, it') -> WrapI (ct, loop it')
    | MapConst (bt', it') -> MapConst (bt', loop it')
    | MapSet (it_m, it_k, it_v) -> MapSet (loop it_m, loop it_k, loop it_v)
    | MapGet (it_m, it_key) -> MapGet (loop it_m, loop it_key)
    | MapDef (sbt, it') -> MapDef (sbt, loop it')
    | Apply (fsym, its) -> Apply (fsym, List.map loop its)
    | Let ((x, it_v), it_rest) -> Let ((x, loop it_v), loop it_rest)
    | Match (it', pits) -> Match (loop it', List.map_snd loop pits)
    | Cast (bt', it') -> Cast (bt', loop it')
  in
  f (IT (it_, bt, here))
