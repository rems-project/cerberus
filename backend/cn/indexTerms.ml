open List
open Pp
module BT=BaseTypes
module CT = Sctypes
module CF=Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
open Subst


include Terms

let equal = equal_term BT.equal
let compare = compare_term BT.compare



type typed = BT.t term
type t = BT.t term



let basetype (IT (_, bt)) : BT.t = bt
let bt = basetype

let term (IT (t, _)) = t



let pp = 
  let rec aux atomic (IT (it, bt)) = 
    let mparens pped = if atomic then parens pped else pped in    
    match it with
    | Lit lit -> 
       begin match lit with
       | Sym sym -> Sym.pp sym
       | Z i -> !^(Z.to_string i)
       | Q q -> !^(Q.to_string q)
       | Pointer i ->
          begin match !Pp.loc_pp with
          |  Dec -> !^(Z.to_string i)
          | _ -> !^("0X" ^ (Z.format "016X" i))
          end
       | Bool true -> !^"true"
       | Bool false -> !^"false"
       | Unit -> !^"void"
       | Default bt -> c_app !^"default" [BT.pp bt]
       | Null -> !^"null"
       end
    | Arith_op arith_op -> 
       begin match arith_op with 
       | Add (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; plus; aux true it2])
       | Sub (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; minus; aux true it2])
       | Mul (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; star; aux true it2])
       | MulNoSMT (it1,it2) -> 
          mparens (c_app !^"mul_uf" [aux true it1; aux true it2])
       | Div (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; slash; aux true it2])
       | DivNoSMT (it1,it2) -> 
          mparens (c_app !^"div_uf" [aux true it1; aux true it2])
       | Exp (it1,it2) -> 
          c_app !^"power" [aux true it1; aux true it2]
       | ExpNoSMT (it1,it2) ->
          c_app !^"power_uf" [aux true it1; aux true it2]
       | Rem (it1,it2) -> 
          c_app !^"rem" [aux true it1; aux true it2]
       | RemNoSMT (it1,it2) -> 
          mparens (c_app !^"rem_uf" [aux true it1; aux true it2])
       | Mod (it1,it2) -> 
          c_app !^"mod" [aux true it1; aux true it2]
       | ModNoSMT (it1,it2) -> 
          mparens (c_app !^"mod_uf" [aux true it1; aux true it2])
       | LT (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle (); aux true o2])
       | LE (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle () ^^ equals; aux true o2])
       | Min (o1,o2) -> 
          c_app !^"min" [aux false o1; aux false o2]
       | Max (o1,o2) -> 
          c_app !^"max" [aux false o1; aux false o2]
       | IntToReal t ->
          c_app !^"intToReal" [aux false t]
       | RealToInt t ->
          c_app !^"realToInt" [aux false t]
       | XORNoSMT (t1, t2) ->
          c_app !^"xor_uf" [aux false t1; aux false t2]
       end
    | Bool_op bool_op -> 
       begin match bool_op with
       | And o -> 
          Pp.group (mparens (flow_map (break 1 ^^ !^"&&" ^^ break 1) (aux true) o))
       | Or o -> 
          Pp.group (mparens (flow_map (break 1 ^^ !^"||" ^^ break 1) (aux true) o))
       | Impl (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; equals ^^ rangle (); aux true o2])
       | Not (o1) -> 
          mparens (!^"!" ^^ parens (aux false o1))
       | ITE (o1,o2,o3) -> 
          parens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
       | EQ (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; equals ^^ equals; aux true o2])
       | EachI ((i1, s, i2), t) ->
          mparens
            (!^"for" ^^ parens(int i1 ^^ comma ^^^ Sym.pp s ^^ comma ^^^ int i2) ^^^
               braces (aux false t))
       end
    | Tuple_op tuple_op -> 
       begin match tuple_op with
       | NthTuple (n,it2) -> 
          mparens (aux true it2 ^^ dot ^^ !^("member" ^ string_of_int n))
       | Tuple its -> 
          braces (separate_map (semi ^^ space) (aux false) its)
       end
    | Struct_op struct_op -> 
       begin match struct_op with
       | Struct (_tag, members) ->
          braces (flow_map (comma ^^ break 1) (fun (member,it) -> 
                      dot ^^ Id.pp member ^^^ equals ^^^ aux false it 
                    ) members)
       | StructMember (t, member) ->
          aux true t ^^ dot ^^ Id.pp member
       | StructUpdate ((t, member), v) ->
          mparens (aux true t ^^ braces (dot ^^ Id.pp member ^^^ equals ^^^ aux true v))
       end
    | Record_op record_op -> 
       begin match record_op with
       | Record members ->
          braces (flow_map (comma ^^ break 1) (fun (member,it) -> 
                      dot ^^ Sym.pp member ^^^ equals ^^^ aux false it 
                    ) members)
       | RecordMember (t, member) ->
          aux true t ^^ dot ^^ Sym.pp member
       | RecordUpdate ((t, member), v) ->
          mparens (aux true t ^^ braces (dot ^^ Sym.pp member ^^^ equals ^^^ aux true v))
       end
    | Datatype_op datatype_op ->
       begin match datatype_op with
       | DatatypeCons (nm, members_rec) -> mparens (Sym.pp nm ^^^ aux false members_rec)
       | DatatypeMember (x, nm) -> aux true x ^^ dot ^^ Sym.pp nm
       | DatatypeIsCons (nm, x) -> mparens (aux false x ^^^ !^ "is" ^^^ Sym.pp nm)
       end
    | Pointer_op pointer_op -> 
       begin match pointer_op with
       | LTPointer (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle (); aux true o2])
       | LEPointer (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle () ^^ equals; aux true o2])
       | IntegerToPointerCast t ->
          mparens (parens(!^"pointer") ^^ aux true t)
       | PointerToIntegerCast t ->
          mparens (parens(!^"integer") ^^ aux true t)
       | MemberOffset (tag, member) ->
          mparens (c_app !^"offsetof" [Sym.pp tag; Id.pp member])
       | ArrayOffset (ct, t) ->
          mparens (c_app !^"arrayOffset" [Sctypes.pp ct; aux false t])
       end
    | CT_pred ct_pred -> 
       begin match ct_pred with
       | Aligned (t, rt) ->
          c_app !^"aligned" [aux false t; CT.pp rt]
       | AlignedI t ->
          c_app !^"aligned" [aux false t.t; aux false t.align]
       | Representable (rt, t) ->
          c_app !^"repr" [CT.pp rt; aux false t]
       | Good (rt, t) ->
          c_app !^"good" [CT.pp rt; aux false t]
       end
    | List_op list_op -> 
       begin match list_op with
       | Head (o1) -> 
          c_app !^"hd" [aux false o1]
       | Tail (o1) -> 
          c_app !^"tl" [aux false o1]
       | Nil -> 
          brackets empty
       | Cons (t1,t2) -> 
          mparens (aux true t1 ^^ colon ^^ colon ^^ aux true t2)
       | List its -> 
          mparens (brackets (separate_map (comma ^^ space) (aux false) its))
       | NthList (n, t) ->
          mparens (aux true t ^^ brackets !^(string_of_int n))
       end
    | Set_op set_op -> 
       begin match set_op with
       | SetMember (t1,t2) ->
          c_app !^"member" [aux false t1; aux false t2]
       | SetUnion ts ->
          c_app !^"union" (List.map (aux false) ts)
       | SetIntersection ts ->
          c_app !^"intersection" (List.map (aux false) ts)
       | SetDifference (t1, t2) ->
          c_app !^"difference" [aux false t1; aux false t2]
       | Subset (t1, t2) ->
          c_app !^"subset" [aux false t1; aux false t2]
       end
    | Map_op map_op -> 
       begin match map_op with
       | Const (_, t) ->
          braces (aux false t)
       | Set (t1,t2,t3) ->
          mparens (aux true t1 ^^ lbracket ^^ aux false t2 ^^^ equals ^^^ aux false t3 ^^ rbracket)
       | Get (t, args) ->
          mparens ((aux true t) ^^ brackets (aux false args))
       | Def ((s, abt), body) ->
          braces (BT.pp abt ^^^ Sym.pp s ^^^ !^"->" ^^^ aux false body)
       end
    | Pred (name, args) ->
       c_app (Sym.pp name) (List.map (aux false) args)
  in
  fun (it : 'bt term) -> aux false it


let free_vars_lit = function
  | Sym s -> SymSet.singleton s
  | Z _ -> SymSet.empty
  | Q _ -> SymSet.empty
  | Pointer _ -> SymSet.empty
  | Bool _ -> SymSet.empty
  | Unit -> SymSet.empty
  | Default _ -> SymSet.empty
  | Null -> SymSet.empty

let rec free_vars_arith_op = function
  | Add (t1, t2) -> free_vars_list [t1; t2]
  | Sub (t1, t2) -> free_vars_list [t1; t2]
  | Mul (t1, t2) -> free_vars_list [t1; t2]
  | MulNoSMT (t1, t2) -> free_vars_list [t1; t2]
  | Div (t1, t2) -> free_vars_list [t1; t2]
  | DivNoSMT (t1, t2) -> free_vars_list [t1; t2]
  | Exp (t1, t2) -> free_vars_list [t1; t2]
  | ExpNoSMT (t1, t2) -> free_vars_list [t1; t2]
  | Rem (t1, t2) -> free_vars_list [t1; t2]
  | RemNoSMT (t1, t2) -> free_vars_list [t1; t2]
  | Mod (t1, t2) -> free_vars_list [t1; t2]
  | ModNoSMT (t1, t2) -> free_vars_list [t1; t2]
  | LT (t1, t2) -> free_vars_list [t1; t2]
  | LE (t1, t2) -> free_vars_list [t1; t2]
  | Min (t1, t2) -> free_vars_list [t1; t2]
  | Max (t1, t2) -> free_vars_list [t1; t2]
  | IntToReal t1 -> free_vars t1
  | RealToInt t1 -> free_vars t1
  | XORNoSMT (t1, t2) -> free_vars_list [t1; t2]

and free_vars_bool_op = function
  | And ts -> free_vars_list ts
  | Or ts -> free_vars_list ts
  | Impl (t1, t2) -> free_vars_list [t1; t2]
  | Not t1 -> free_vars t1
  | ITE (t1, t2, t3) -> free_vars_list [t1; t2; t3]
  | EQ (t1, t2) -> free_vars_list [t1; t2]
  | EachI ((_, s, _), t) -> SymSet.remove s (free_vars t)

and free_vars_tuple_op = function
  | Tuple ts -> free_vars_list ts
  | NthTuple (_, t) -> free_vars t

and free_vars_struct_op = function
  | Struct (_tag, members) -> free_vars_list (List.map snd members)
  | StructMember (t, _member) -> free_vars t
  | StructUpdate ((t1, _member), t2) -> free_vars_list [t1; t2]

and free_vars_record_op = function
  | Record members -> free_vars_list (List.map snd members)
  | RecordMember (t, _member) -> free_vars t
  | RecordUpdate ((t1, _member), t2) -> free_vars_list [t1; t2]

and free_vars_datatype_op = function
  | DatatypeCons (tag, members_xs) -> free_vars members_xs
  | DatatypeMember (t, member) -> free_vars t
  | DatatypeIsCons (tag, t) -> free_vars t

and free_vars_pointer_op = function
  | LTPointer (t1, t2) -> free_vars_list [t1; t2]
  | LEPointer (t1, t2) -> free_vars_list [t1; t2]
  | IntegerToPointerCast t1 -> free_vars t1
  | PointerToIntegerCast t1 -> free_vars t1
  | MemberOffset (_tag, _id) -> SymSet.empty
  | ArrayOffset (_sct, t) -> free_vars t

and free_vars_list_op = function
  | Nil -> SymSet.empty
  | Cons (t1, t2) -> free_vars_list [t1; t2]
  | List ts -> free_vars_list ts
  | Head t -> free_vars t
  | Tail t -> free_vars t
  | NthList (_i, t) -> free_vars t

and free_vars_set_op = function
  | SetMember (t1, t2) -> free_vars_list [t1; t2]
  | SetUnion ts -> free_vars_list ts
  | SetIntersection ts -> free_vars_list ts
  | SetDifference (t1, t2) -> free_vars_list [t1; t2]
  | Subset (t1, t2) -> free_vars_list [t1; t2]

and free_vars_ct_pred = function
  | Representable (_sct, t) -> free_vars t
  | Good (_sct, t) -> free_vars t
  | AlignedI {t; align} -> free_vars_list [t; align]
  | Aligned (t, _sct) -> free_vars t

and free_vars_map_op = function
  | Const (_bt, t) -> free_vars t
  | Set (t1, t2, t3) -> free_vars_list [t1; t2; t3]
  | Get (t1, t2) -> free_vars_list [t1; t2]
  | Def ((s, _bt), t) -> SymSet.remove s (free_vars t)

and free_vars_info (_str, ts) = 
  free_vars_list ts

and free_vars_pred (_pred, ts) =
  free_vars_list ts

and free_vars_term_ = function
  | Lit lit -> free_vars_lit lit
  | Arith_op arith_op -> free_vars_arith_op arith_op
  | Bool_op bool_op -> free_vars_bool_op bool_op
  | Tuple_op tuple_op -> free_vars_tuple_op tuple_op
  | Struct_op struct_op -> free_vars_struct_op struct_op
  | Record_op record_op -> free_vars_record_op record_op
  | Datatype_op datatype_op -> free_vars_datatype_op datatype_op
  | Pointer_op pointer_op -> free_vars_pointer_op pointer_op
  | List_op list_op -> free_vars_list_op list_op
  | Set_op set_op -> free_vars_set_op set_op
  | CT_pred ct_pred -> free_vars_ct_pred ct_pred
  | Map_op map_op -> free_vars_map_op map_op
  | Pred (pred, ts) -> free_vars_pred (pred, ts)

and free_vars (IT (term_, _bt)) =
  free_vars_term_ term_

and free_vars_list xs = 
  List.fold_left (fun ss t -> 
      SymSet.union ss (free_vars t)
    ) SymSet.empty xs


let no_free_vars t = SymSet.is_empty (free_vars t)


let fold_lit f binders acc = function
  | Sym s -> acc
  | Z _ -> acc
  | Q _ -> acc
  | Pointer _ -> acc
  | Bool _ -> acc
  | Unit -> acc
  | Default _ -> acc
  | Null -> acc

let rec fold_arith_op f binders acc = function
  | Add (t1, t2) -> fold_list f binders acc [t1; t2]
  | Sub (t1, t2) -> fold_list f binders acc [t1; t2]
  | Mul (t1, t2) -> fold_list f binders acc [t1; t2]
  | MulNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]
  | Div (t1, t2) -> fold_list f binders acc [t1; t2]
  | DivNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]
  | Exp (t1, t2) -> fold_list f binders acc [t1; t2]
  | ExpNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]
  | Rem (t1, t2) -> fold_list f binders acc [t1; t2]
  | RemNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]
  | Mod (t1, t2) -> fold_list f binders acc [t1; t2]
  | ModNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]
  | LT (t1, t2) -> fold_list f binders acc [t1; t2]
  | LE (t1, t2) -> fold_list f binders acc [t1; t2]
  | Min (t1, t2) -> fold_list f binders acc [t1; t2]
  | Max (t1, t2) -> fold_list f binders acc [t1; t2]
  | IntToReal t1 -> fold f binders acc t1
  | RealToInt t1 -> fold f binders acc t1
  | XORNoSMT (t1, t2) -> fold_list f binders acc [t1; t2]

and fold_bool_op f binders acc = function
  | And ts -> fold_list f binders acc ts
  | Or ts -> fold_list f binders acc ts
  | Impl (t1, t2) -> fold_list f binders acc [t1; t2]
  | Not t1 -> fold f binders acc t1
  | ITE (t1, t2, t3) -> fold_list f binders acc [t1; t2; t3]
  | EQ (t1, t2) -> fold_list f binders acc [t1; t2]
  | EachI ((_, s, _), t) -> 
     fold f (binders @ [(s, BT.Integer)]) acc t

and fold_tuple_op f binders acc = function
  | Tuple ts -> fold_list f binders acc ts
  | NthTuple (_, t) -> fold f binders acc t

and fold_struct_op f binders acc = function
  | Struct (_tag, members) -> fold_list f binders acc (List.map snd members)
  | StructMember (t, _member) -> fold f binders acc t
  | StructUpdate ((t1, _member), t2) -> fold_list f binders acc [t1; t2]

and fold_record_op f binders acc = function
  | Record members -> fold_list f binders acc (List.map snd members)
  | RecordMember (t, _member) -> fold f binders acc t
  | RecordUpdate ((t1, _member), t2) -> fold_list f binders acc [t1; t2]

and fold_datatype_op f binders acc = function
  | DatatypeCons (tag, members_rec) -> fold f binders acc members_rec
  | DatatypeMember (t, _member) -> fold f binders acc t
  | DatatypeIsCons (tag, t) -> fold f binders acc t

and fold_pointer_op f binders acc = function
  | LTPointer (t1, t2) -> fold_list f binders acc [t1; t2]
  | LEPointer (t1, t2) -> fold_list f binders acc [t1; t2]
  | IntegerToPointerCast t1 -> fold f binders acc t1
  | PointerToIntegerCast t1 -> fold f binders acc t1
  | MemberOffset (_tag, _id) -> acc
  | ArrayOffset (_sct, t) -> fold f binders acc t

and fold_list_op f binders acc = function
  | Nil -> acc
  | Cons (t1, t2) -> fold_list f binders acc [t1; t2]
  | List ts -> fold_list f binders acc ts
  | Head t -> fold f binders acc t
  | Tail t -> fold f binders acc t
  | NthList (_i, t) -> fold f binders acc t

and fold_set_op f binders acc = function
  | SetMember (t1, t2) -> fold_list f binders acc [t1; t2]
  | SetUnion ts -> fold_list f binders acc ts
  | SetIntersection ts -> fold_list f binders acc ts
  | SetDifference (t1, t2) -> fold_list f binders acc [t1; t2]
  | Subset (t1, t2) -> fold_list f binders acc [t1; t2]

and fold_ct_pred f binders acc = function
  | Representable (_sct, t) -> fold f binders acc t
  | Good (_sct, t) -> fold f binders acc t
  | AlignedI {t; align} -> fold_list f binders acc [t; align]
  | Aligned (t, _sct) -> fold f binders acc t

and fold_map_op f binders acc = function
  | Const (_bt, t) -> fold f binders acc t
  | Set (t1, t2, t3) -> fold_list f binders acc [t1; t2; t3]
  | Get (t1, t2) -> fold_list f binders acc [t1; t2]
  | Def ((s, bt), t) -> fold f (binders @ [(s, bt)]) acc t

and fold_info f binders acc (_str, ts) = 
  fold_list f binders acc ts

and fold_pred f binders acc (_pred, ts) =
  fold_list f binders acc ts

and fold_term_ f binders acc = function
  | Lit lit -> fold_lit f binders acc lit
  | Arith_op arith_op -> fold_arith_op f binders acc arith_op
  | Bool_op bool_op -> fold_bool_op f binders acc bool_op
  | Tuple_op tuple_op -> fold_tuple_op f binders acc tuple_op
  | Struct_op struct_op -> fold_struct_op f binders acc struct_op
  | Record_op record_op -> fold_record_op f binders acc record_op
  | Datatype_op datatype_op -> fold_datatype_op f binders acc datatype_op
  | Pointer_op pointer_op -> fold_pointer_op f binders acc pointer_op
  | List_op list_op -> fold_list_op f binders acc list_op
  | Set_op set_op -> fold_set_op f binders acc set_op
  | CT_pred ct_pred -> fold_ct_pred f binders acc ct_pred
  | Map_op map_op -> fold_map_op f binders acc map_op
  | Pred (pred, ts) -> fold_pred f binders acc (pred, ts)

and fold f binders acc (IT (term_, _bt)) =
  let acc' = fold_term_ f binders acc term_ in
  f binders acc' (IT (term_, _bt))

and fold_list f binders acc xs = 
  match xs with
  | [] -> acc
  | x :: xs -> 
     let acc' = fold f binders acc x in
     fold_list f binders acc' xs


let fold_subterms : 'a 'bt. ((Sym.t * BT.t) list -> 'a -> 'bt term -> 'a) -> 'a -> 'bt term -> 'a =
  fun f acc t -> fold f [] acc t


let todo_is_pred (pred: string) (IT (it_, bt)) = 
  match pred, it_ with
  | _, Pred (name, _) when String.equal (Tools.todo_string_of_sym name) pred -> true
  | "good", CT_pred (Good _) -> true
  | _ -> false

let todo_mentions_pred (pred: Id.t) =
  let pred = Id.s pred in
  fold_subterms (fun _binders acc it ->
      acc || todo_is_pred pred it
    ) false

let preds_of t =
  let add_p s = function
    | IT (Pred (id, _), _) -> SymSet.add id s
    | _ -> s
  in
  fold_subterms (fun _ -> add_p) SymSet.empty t



let json it : Yojson.Safe.t = 
  `String (Pp.plain (pp it))


let make_subst = Subst.make free_vars

let rec subst (su : typed subst) (IT (it, bt)) =
  match it with
  | Lit lit -> 
     begin match lit with
     | Sym sym ->
        begin match List.assoc_opt Sym.equal sym su.replace with
        | Some after -> after
        | None -> IT (Lit lit, bt)
        end
     | lit -> IT (Lit lit, bt)
     end
  | Arith_op arith_op -> 
     let arith_op = match arith_op with
       | Add (it, it') -> Add (subst su it, subst su it')
       | Sub (it, it') -> Sub (subst su it, subst su it')
       | Mul (it, it') -> Mul (subst su it, subst su it')
       | MulNoSMT (it, it') -> MulNoSMT (subst su it, subst su it')
       | Div (it, it') -> Div (subst su it, subst su it')
       | DivNoSMT (it, it') -> DivNoSMT (subst su it, subst su it')
       | Exp (it, it') -> Exp (subst su it, subst su it')
       | ExpNoSMT (it, it') -> ExpNoSMT (subst su it, subst su it')
       | Rem (it, it') -> Rem (subst su it, subst su it')
       | RemNoSMT (it, it') -> RemNoSMT (subst su it, subst su it')
       | Mod (it, it') -> Mod (subst su it, subst su it')
       | ModNoSMT (it, it') -> ModNoSMT (subst su it, subst su it')
       | LT (it, it') -> LT (subst su it, subst su it')
       | LE (it, it') -> LE (subst su it, subst su it')
       | Min (it, it') -> Min (subst su it, subst su it')
       | Max (it, it') -> Max (subst su it, subst su it')
       | IntToReal it -> IntToReal (subst su it)
       | RealToInt it -> RealToInt (subst su it)
       | XORNoSMT (it, it') -> XORNoSMT (subst su it, subst su it')
     in
     IT (Arith_op arith_op, bt)
  | Bool_op bool_op -> 
     let bool_op = match bool_op with
       | And its -> And (map (subst su) its)
       | Or its -> Or (map (subst su) its)
       | Impl (it, it') -> Impl (subst su it, subst su it')
       | Not it -> Not (subst su it)
       | ITE (it,it',it'') -> ITE (subst su it, subst su it', subst su it'')
       | EQ (it, it') -> EQ (subst su it, subst su it')
       | EachI ((i1, s, i2), t) ->
          let s, t = suitably_alpha_rename su.relevant (s, BT.Integer) t in
          EachI ((i1, s, i2), subst su t)
     in
     IT (Bool_op bool_op, bt)
  | Tuple_op tuple_op -> 
     let tuple_op = match tuple_op with
       | Tuple its ->
          Tuple (map (subst su) its)
       | NthTuple (n, it') ->
          NthTuple (n, subst su it')
     in
     IT (Tuple_op tuple_op, bt)
  | Struct_op struct_op -> 
     let struct_op = match struct_op with
       | Struct (tag, members) ->
          let members = 
            map (fun (member,it) -> 
                (member,subst su it)
              ) members 
          in
          Struct (tag, members)
       | StructMember (t, m) ->
          StructMember (subst su t, m)
       | StructUpdate ((t, m), v) ->
          StructUpdate ((subst su t, m), subst su v)
     in
     IT (Struct_op struct_op, bt)
  | Record_op record_op -> 
     let record_op = match record_op with
       | Record members ->
          let members = 
            map (fun (member,it) -> 
                (member,subst su it)
              ) members 
          in
          Record members
       | RecordMember (t, m) ->
          RecordMember (subst su t, m)
       | RecordUpdate ((t, m), v) ->
          RecordUpdate ((subst su t, m), subst su v)
     in
     IT (Record_op record_op, bt)
  | Datatype_op datatype_op -> 
     let datatype_op = match datatype_op with
       | DatatypeCons (tag, members_rec) ->
          DatatypeCons (tag, subst su members_rec)
       | DatatypeMember (t, m) ->
          DatatypeMember (subst su t, m)
       | DatatypeIsCons (tag, t) ->
          DatatypeIsCons (tag, subst su t)
     in
     IT (Datatype_op datatype_op, bt)
  | Pointer_op pointer_op -> 
     let pointer_op = match pointer_op with
       | LTPointer (it, it') -> 
          LTPointer (subst su it, subst su it')
       | LEPointer (it, it') -> 
          LEPointer (subst su it, subst su it')
       | IntegerToPointerCast t -> 
          IntegerToPointerCast (subst su t)
       | PointerToIntegerCast t -> 
          PointerToIntegerCast (subst su t)
       | MemberOffset (tag, member) ->
          MemberOffset (tag, member)
       | ArrayOffset (tag, t) ->
          ArrayOffset (tag, subst su t)
     in
     IT (Pointer_op pointer_op, bt)
  | CT_pred ct_pred -> 
     let ct_pred = match ct_pred with
       | Aligned (t, ct) -> Aligned (subst su t, ct)
       | AlignedI t -> AlignedI {t= subst su t.t; align= subst su t.align}
       | Representable (rt, t) -> Representable (rt, subst su t)
       | Good (rt, t) -> Good (rt, subst su t)
     in
     IT (CT_pred ct_pred, bt)
  | List_op list_op -> 
     let list_op = match list_op with
       | Nil -> Nil
       | Cons (it1,it2) -> Cons (subst su it1, subst su it2)
       | List its -> List (map (subst su) its)
       | Head it -> Head (subst su it)
       | Tail it -> Tail (subst su it)
       | NthList (i, it) -> NthList (i, subst su it)
     in
     IT (List_op list_op, bt)
  | Set_op set_op -> 
     let set_op = match set_op with
       | SetMember (t1,t2) -> SetMember (subst su t1, subst su t2)
       | SetUnion ts -> SetUnion (List.map (subst su) ts)
       | SetIntersection ts -> SetIntersection (List.map (subst su) ts)
       | SetDifference (t1, t2) -> SetDifference (subst su t1, subst su t2)
       | Subset (t1, t2) -> Subset (subst su t1, subst su t2)
     in
     IT (Set_op set_op, bt)
  | Map_op map_op -> 
     let map_op = match map_op with
       | Const (bt, t) -> 
          Const (bt, subst su t)
       | Set (t1, t2, t3) -> 
          Set (subst su t1, subst su t2, subst su t3)
       | Get (it, arg) -> 
          Get (subst su it, subst su arg)
       | Def ((s, abt), body) ->
          let s, body = suitably_alpha_rename su.relevant (s, abt) body in
          Def ((s, abt), subst su body)
     in
     IT (Map_op map_op, bt)
  | Pred (name, args) ->
     IT (Pred (name, List.map (subst su) args), bt)

and alpha_rename (s, bt) body = 
  let s' = Sym.fresh_same s in
  (s', subst (make_subst [(s, IT (Lit (Sym s'), bt))]) body)

and suitably_alpha_rename syms (s, bt) body = 
  if SymSet.mem s syms 
  then alpha_rename (s, bt) body
  else (s, body)
  









let is_lit = function
  | IT (Lit lit, bt) -> Some (lit, bt)
  | _ -> None

let is_z = function
  | IT (Lit (Z z), bt) -> Some z
  | _ -> None

let is_z_ it = Option.is_some (is_z it)

let is_pointer = function
  | IT (Lit (Pointer z), bt) -> Some z
  | _ -> None

let is_sym = function
  | IT (Lit (Sym sym), bt) -> Some (sym, bt)
  | _ -> None

let is_bool = function
  | IT (Lit (Bool b), _) -> Some b
  | _ -> None

let is_q = function
  | IT (Lit (Q q), _) -> Some q
  | _ -> None

let is_map_get = function
  | IT (Map_op (Get (f,arg)), _) -> Some (f, arg)
  | _ -> None

let zero_frac = function
  | IT (Lit (Q q), _) when Q.equal Q.zero q -> true
  | _ -> false

let is_true = function
  | IT (Lit (Bool true), _) -> true
  | _ -> false

let is_false = function
  | IT (Lit (Bool false), _) -> true
  | _ -> false

let is_eq = function
  | (IT (Bool_op (EQ (lhs, rhs)), _)) -> Some (lhs, rhs)
  | _ -> None

let is_and = function
  | IT (Bool_op (And its), _) -> Some its
  | _ -> None

let is_or = function
  | IT (Bool_op (Or its), _) -> Some its
  | _ -> None

let is_not = function
  | IT (Bool_op (Not it), _) -> Some it
  | _ -> None

let is_lt = function
  | IT (Arith_op (LT (x, y)), _) -> Some (x, y)
  | _ -> None

let is_le = function
  | IT (Arith_op (LE (x, y)), _) -> Some (x, y)
  | _ -> None



let rec split_and it = match is_and it with
  | Some its -> List.concat (List.map split_and its)
  | _ -> [it]

(* shorthands *)


(* lit *)
let sym_ (sym, bt) = IT (Lit (Sym sym), bt)
let z_ n = IT (Lit (Z n), BT.Integer)
let q_ (n,n') = IT (Lit (Q (Q.make (Z.of_int n) (Z.of_int  n'))), BT.Real)
let q1_ q = IT (Lit (Q q), BT.Real)
let pointer_ n = IT (Lit (Pointer n), BT.Loc)
let bool_ b = IT (Lit (Bool b), BT.Bool)
let unit_ = IT (Lit Unit, BT.Unit)
let int_ n = z_ (Z.of_int n)
let default_ bt = IT (Lit (Default bt), bt)

(* cmp_op *)
let lt_ (it, it') = IT (Arith_op (LT (it, it')), BT.Bool)
let le_ (it, it') = IT (Arith_op (LE (it, it')), BT.Bool)
let gt_ (it, it') = lt_ (it', it)
let ge_ (it, it') = le_ (it', it)

(* bool_op *)
let and_ its = IT (Bool_op (And its), BT.Bool)
let and2_ (it, it') = match is_and it' with
  | None -> and_ [it; it']
  | Some its -> and_ (it :: its)
let or_ its = IT (Bool_op (Or its), BT.Bool)
let or2_ (it, it') = match is_or it' with
  | None -> or_ [it; it']
  | Some its -> or_ (it :: its)
let impl_ (it, it') = IT (Bool_op (Impl (it, it')), BT.Bool)
let not_ it = 
  match it with
  | IT (Lit (Bool b), _) -> bool_ (not b)
  | IT (Bool_op (Not a), _) -> a
  | _ -> IT (Bool_op (Not it), BT.Bool)

let ite_ (it, it', it'') = IT (Bool_op (ITE (it, it', it'')), bt it')
let eq_ (it, it') = IT (Bool_op (EQ (it, it')), BT.Bool)
let eq__ it it' = eq_ (it, it')
let ne_ (it, it') = not_ (eq_ (it, it'))
let ne__ it it' = ne_ (it, it')



let eachI_ (i1, s, i2) t = IT (Bool_op (EachI ((i1, s, i2), t)), BT.Bool)
(* let existsI_ (i1, s, i2) t = not_ (eachI_ (i1, s, i2) (not_ t)) *)


(* arith_op *)
let add_ (it, it') = IT (Arith_op (Add (it, it')), bt it)
let sub_ (it, it') = IT (Arith_op (Sub (it, it')), bt it)
let mul_ (it, it') = IT (Arith_op (Mul (it, it')), bt it)
let mul_no_smt_ (it, it') = IT (Arith_op (MulNoSMT (it, it')), bt it)
let div_ (it, it') = IT (Arith_op (Div (it, it')), bt it)
let div_no_smt_ (it, it') = IT (Arith_op (DivNoSMT (it, it')), bt it)
let exp_ (it, it') = IT (Arith_op (Exp (it, it')), bt it)
let exp_no_smt_ (it, it') = IT (Arith_op (ExpNoSMT (it, it')), bt it)
let rem_ (it, it') = IT (Arith_op (Rem (it, it')), BT.Integer)
let rem_no_smt_ (it, it') = IT (Arith_op (RemNoSMT (it, it')), BT.Integer)
let mod_ (it, it') = IT (Arith_op (Mod (it, it')), BT.Integer)
let mod_no_smt_ (it, it') = IT (Arith_op (ModNoSMT (it, it')), BT.Integer)
let divisible_ (it, it') = eq_ (mod_ (it, it'), int_ 0)
let rem_f_ (it, it') = mod_ (it, it')
let min_ (it, it') = IT (Arith_op (Min (it, it')), bt it)
let max_ (it, it') = IT (Arith_op (Max (it, it')), bt it)
let intToReal_ it = IT (Arith_op (IntToReal it), BT.Real)
let realToInt_ it = IT (Arith_op (RealToInt it), BT.Integer)
let xor_no_smt_ (it, it') = IT (Arith_op (XORNoSMT (it, it')), BT.Integer)

let (%+) t t' = add_ (t, t')
let (%-) t t' = sub_ (t, t')
let (%*) t t' = mul_ (t, t')
let (%/) t t' = div_ (t, t')

let (%==) t t' = eq_ (t, t')
let (%!=) t t' = ne_ (t, t')
let (%<) t t' = lt_ (t, t')
let (%<=) t t' = le_ (t, t')
let (%>) t t' = gt_ (t, t')
let (%>=) t t' = ge_ (t, t')




(* tuple_op *)
let tuple_ its = IT (Tuple_op (Tuple its), BT.Tuple (List.map bt its))
let nthTuple_ ~item_bt (n, it) = IT (Tuple_op (NthTuple (n, it)), item_bt)

(* struct_op *)
let struct_ (tag, members) = 
  IT (Struct_op (Struct (tag, members)), BT.Struct tag) 
let member_ ~member_bt (tag, it, member) =
  IT (Struct_op (StructMember (it, member)), member_bt)

let (%.) struct_decls t member = 
  let tag = match bt t with
    | BT.Struct tag -> tag
    | _ -> Debug_ocaml.error "illtyped index term. not a struct"
  in
  let member_bt = match List.assoc_opt Id.equal member
         (Memory.member_types (SymMap.find tag struct_decls))
  with
    | Some sct -> BT.of_sct sct
    | None -> Debug_ocaml.error ("struct " ^ Sym.pp_string tag ^
        " does not have member " ^ (Id.pp_string member))
  in
  member_ ~member_bt (tag, t, member)




let record_ members = 
  IT (Record_op (Record members), 
      BT.Record (List.map (fun (s,t) -> (s, basetype t)) members))
let recordMember_ ~member_bt (t, member) = 
  IT (Record_op (RecordMember (t, member)), member_bt)

let datatype_cons_ nm dt_tag members =
  IT (Datatype_op (DatatypeCons (nm, record_ members)), BT.Datatype dt_tag)

let datatype_is_cons_ nm t =
  IT (Datatype_op (DatatypeIsCons (nm, t)), BT.Bool)


(* pointer_op *)
let null_ = IT (Lit Null, BT.Loc)
let ltPointer_ (it, it') = IT (Pointer_op (LTPointer (it, it')), BT.Bool)
let lePointer_ (it, it') = IT (Pointer_op (LEPointer (it, it')), BT.Bool)
let gtPointer_ (it, it') = ltPointer_ (it', it)
let gePointer_ (it, it') = lePointer_ (it', it)
let integerToPointerCast_ it = 
  IT (Pointer_op (IntegerToPointerCast it), BT.Loc)
let pointerToIntegerCast_ it = 
  IT (Pointer_op (PointerToIntegerCast it), BT.Integer)
let memberOffset_ (tag, member) = 
  IT (Pointer_op (MemberOffset (tag, member)), BT.Integer)
let arrayOffset_ (ct, t) = 
  IT (Pointer_op (ArrayOffset (ct, t)), BT.Integer)

let isIntegerToPointerCast = function
  | IT (Pointer_op (IntegerToPointerCast _), _) -> true
  | _ -> false

let pointer_offset_ (p, n) =
  integerToPointerCast_ (add_ (pointerToIntegerCast_ p, n))

let memberShift_ (t, tag, member) =
  pointer_offset_ (t, memberOffset_ (tag, member))
let arrayShift_ (t1, ct, t2) =
  pointer_offset_ (t1, arrayOffset_ (ct, t2))





let array_index_to_pointer ~base ~item_ct ~index =
  arrayShift_ (base, item_ct, index)

let array_offset_of_pointer ~base ~pointer = 
  sub_ (pointerToIntegerCast_ pointer, 
        pointerToIntegerCast_ base)

let array_pointer_to_index ~base ~item_size ~pointer =
  div_ (array_offset_of_pointer ~base ~pointer, 
        item_size)

let subarray_condition ~base ~item_size ~from_index ~to_index ~qpointer =
  let offset = array_offset_of_pointer ~base ~pointer:qpointer in
  and_ [
      lePointer_ (pointer_offset_ (base, mul_ (item_size, from_index)),
                  qpointer);
      ltPointer_ (qpointer,
                  pointer_offset_ (base, mul_ (item_size, to_index)));
      divisible_ (offset, item_size)
    ]

  


let cellPointer_ ~base ~step ~starti ~endi ~p =
  subarray_condition ~base ~item_size:step 
    ~from_index:starti ~to_index:endi ~qpointer:p




let container_of_ (t, tag, member) =
  integerToPointerCast_
    (sub_ (pointerToIntegerCast_ t, memberOffset_ (tag, member)))

(* list_op *)
let nil_ ~item_bt = IT (List_op Nil, BT.List item_bt)
let cons_ (it, it') = IT (List_op (Cons (it, it')), bt it')
let list_ ~item_bt its = IT (List_op (List its), BT.List item_bt)
let head_ ~item_bt it = IT (List_op (Head it), item_bt)
let tail_ it = IT (List_op (Tail it), bt it)
let nthList_ ~item_bt (n, it) = IT (List_op (NthList (n, it)), item_bt)

(* set_op *)
let setMember_ bt (it, it') = IT (Set_op (SetMember (it, it')), BT.Bool)
(* let setUnion_ its = IT (Set_op (SetUnion its), bt (hd its))
 * let setIntersection_ its = IT (Set_op (SetIntersection its), bt (hd its)) *)
let setDifference_ (it, it') = IT (Set_op (SetDifference (it, it')), bt it)
let subset_ (it, it') = IT (Set_op (Subset (it, it')), BT.Bool)



(* ct_pred *)
let minInteger_ t = 
  z_ (Memory.min_integer_type t)
let maxInteger_ t = 
  z_ (Memory.max_integer_type t)
let representable_ (t, it) = 
  IT (CT_pred (Representable (t, it)), BT.Bool)
let good_ (sct, it) =
  IT (CT_pred (Good (sct, it)), BT.Bool)
let aligned_ (t, it) = 
  IT (CT_pred (Aligned (t, it)), BT.Bool)
let alignedI_ ~t ~align = 
  IT (CT_pred (AlignedI {t; align}), BT.Bool)

let const_map_ index_bt t = 
  IT (Map_op (Const (index_bt, t)), BT.Map (index_bt, bt t))
let map_set_ t1 (t2, t3) = 
  IT (Map_op (Set (t1, t2, t3)), bt t1)
let map_get_ v arg = 
  match bt v with
  | BT.Map (_, rbt) ->
     IT (Map_op (Get (v, arg)), rbt)
  | _ -> Debug_ocaml.error "illtyped index term"
let map_def_ (s, abt) body = 
  IT (Map_op (Def ((s, abt), body)), BT.Map (abt, bt body))

let make_array_ ~item_bt items (* assumed all of item_bt *) =
  let (_, value) = 
    List.fold_left (fun (index, value) item -> 
        (index + 1, map_set_ value (int_ index, item))
      ) (0, const_map_ Integer (default_ item_bt)) items
  in
  value
  



let pred_ name args rbt =
  IT (Pred (name, args), rbt)


let let_ sym e body = 
  subst (make_subst [(sym, e)]) body




let fresh bt = 
  let symbol = Sym.fresh () in
  (symbol, sym_ (symbol, bt))

let fresh_named bt name = 
  let symbol = Sym.fresh_named name in
  (symbol, sym_ (symbol, bt))

let fresh_same bt symbol' = 
  let symbol = Sym.fresh_same symbol' in
  (symbol, sym_ (symbol, bt))







let def_ sym e = eq_ (sym_ (sym, bt e), e)

let in_range within (min, max) = 
  and_ [le_ (min, within); le_ (within, max)]




let value_check_pointer alignment ~pointee_ct about = 
  let about_int = pointerToIntegerCast_ about in
  let pointee_size = match pointee_ct with
    | Sctypes.Void -> 1
    | Function _ -> 1
    | _ -> Memory.size_of_ctype pointee_ct 
  in
  and_ [le_ (z_ Z.zero, about_int);
        le_ (sub_ (add_ (about_int, int_ pointee_size), int_ 1), z_ Memory.max_pointer);
        if alignment then aligned_ (about, pointee_ct) else bool_ true]

let value_check alignment (struct_layouts : Memory.struct_decls) ct about =
  let open Sctypes in
  let open Memory in
  let rec aux (ct_ : Sctypes.t) about = 
    match ct_ with
    | Void -> 
       bool_ true
    | Integer it -> 
       in_range about (z_ (min_integer_type it), z_ (max_integer_type it))
    | Array (it, None) -> 
       Debug_ocaml.error "todo: 'representable' for arrays with unknown length"
    | Array (item_ct, Some n) -> 
       (* let partiality = partiality_check_array ~length:n ~item_ct about in *)
       let i_s, i = fresh BT.Integer in
       and_ 
         [eachI_ (0, i_s, n - 1) (aux item_ct (map_get_ about i))]
    | Pointer pointee_ct -> 
       value_check_pointer alignment ~pointee_ct about
    | Struct tag -> 
       and_ begin
           List.filter_map (fun piece ->
               match piece.member_or_padding with
               | Some (member, mct) ->
                  let member_bt = BT.of_sct mct in
                  let member_it = member_ ~member_bt (tag, about, member) in
                  Some (aux mct member_it)
               | None -> 
                  None
             ) (SymMap.find tag struct_layouts)
         end
    | Function _ -> 
       Debug_ocaml.error "todo: function types"
  in
  aux ct about

let good_value = value_check true
let representable = value_check false

let good_pointer = value_check_pointer true 



