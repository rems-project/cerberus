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
       | Pointer i when !Pp.loc_pp = Dec -> !^(Z.to_string i)
       | Pointer i -> !^("0X" ^ (Z.format "016X" i))
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
       | Div (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; slash; aux true it2])
       | Exp (it1,it2) -> 
          c_app !^"power" [aux true it1; aux true it2]
       | Rem (it1,it2) -> 
          mparens (flow (break 1) [aux true it1; !^"%"; aux true it2])
       | Mod (it1,it2) -> 
          c_app !^"mod" [aux true it1; aux true it2]
       | LT (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle; aux true o2])
       | LE (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; (langle ^^ equals); aux true o2])
       | Min (o1,o2) -> 
          c_app !^"min" [aux false o1; aux false o2]
       | Max (o1,o2) -> 
          c_app !^"max" [aux false o1; aux false o2]
       | IntToReal t ->
          c_app !^"intToReal" [aux false t]
       | RealToInt t ->
          c_app !^"realToInt" [aux false t]
       | FlipBit fb ->
          c_app !^"flipBit" [aux false fb.bit; aux false fb.t]
       | XOR (ity, t1, t2) -> 
          c_app !^"xor" [Sctypes.IntegerTypes.pp ity ; aux false t1; aux false t2]
       end
    | Bool_op bool_op -> 
       begin match bool_op with
       | And o -> 
          Pp.group (mparens (flow_map (break 1 ^^ !^"&&" ^^ break 1) (aux true) o))
       | Or o -> 
          Pp.group (mparens (flow_map (break 1 ^^ !^"||" ^^ break 1) (aux true) o))
       | Impl (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; (equals ^^ rangle); aux true o2])
       | Not (o1) -> 
          mparens (!^"!" ^^ parens (aux false o1))
       | ITE (o1,o2,o3) -> 
          parens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
       | EQ (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; equals ^^ equals; aux true o2])
       | EachI ((i1, s, i2), t) ->
          mparens (c_app ((c_app !^"eachI" [!^(string_of_int i1); Sym.pp s; !^(string_of_int i2)])) [aux false t])
       end
    | Tuple_op tuple_op -> 
       begin match tuple_op with
       | NthTuple (n,it2) -> 
          mparens (aux true it2 ^^ dot ^^ !^("component" ^ string_of_int n))
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
       end
    | Pointer_op pointer_op -> 
       begin match pointer_op with
       | LTPointer (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle; aux true o2])
       | LEPointer (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; langle ^^ equals; aux true o2])
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
    (* | Option_op option_op -> *)
    (*    begin match option_op with *)
    (*    | Nothing bt -> !^"nothing" *)
    (*    | Something t -> c_app !^"some" [aux false t] *)
    (*    | Is_nothing t -> c_app !^"is_nothing" [aux false t] *)
    (*    | Is_something t -> c_app !^"is_something" [aux false t] *)
    (*    | Get_some_value t -> c_app !^"value" [aux false t] *)
    (*    end *)
    | Let ((s, bound), body) ->
       !^"let" ^^^ Sym.pp s ^^^ equals ^^^ aux true bound ^^^ semi ^^^ parens (aux false body)
  in
  fun (it : 'bt term) -> aux false it


let subterms : 'bt. 'bt term -> ('bt term) list =
  fun (IT (it, _)) ->
  match it with
  | Arith_op arith_op -> 
     begin match arith_op with
     | Add (it, it') -> [it; it'] 
     | Sub (it, it') -> [it; it']
     | Mul (it, it') -> [it; it']
     | Div (it, it') -> [it; it']
     | Exp (it, it') -> [it; it']
     | Rem (it, it') -> [it; it']
     | Mod (it, it') -> [it; it']
     | LT (it, it') -> [it; it']
     | LE (it, it') -> [it; it']
     | Min (it, it') -> [it; it']
     | Max (it, it') -> [it; it']
     | IntToReal t -> [t]
     | RealToInt t -> [t]
     | FlipBit fb -> [fb.bit; fb.t]
     | XOR (_, it, it') -> [it; it']
     end
  | Bool_op bool_op ->
     begin match bool_op with
     | And its -> its
     | Or its -> its
     | Impl (it, it') -> [it; it']
     | Not it -> [it]
     | ITE (it,it',it'') -> [it;it';it'']
     | EQ (it, it') -> [it; it']
     | EachI _ -> (* in binders set below *) []
     end
  | Tuple_op tuple_op -> 
     begin match tuple_op with
     | Tuple its -> its
     | NthTuple ( _, it) -> [it]
     end
  | Struct_op struct_op -> 
     begin match struct_op with
     | Struct (_tag, members) -> map snd members
     | StructMember (it, s) -> [it;it]
     end
  | Pointer_op pointer_op ->
     begin match pointer_op with
     | LTPointer (it, it')  -> [it; it']
     | LEPointer (it, it') -> [it; it']
     | IntegerToPointerCast t -> [t]
     | PointerToIntegerCast t -> [t]
     | MemberOffset (_, _) -> []
     | ArrayOffset (_, t) -> [t]
     end
  | CT_pred ct_pred ->
     begin match ct_pred with
     | Aligned (t, _rt) -> [t]
     | AlignedI t -> [t.t; t.align]
     | Representable (_rt,t) -> [t]
     | Good (_rt,t) -> [t]
     end
  | List_op list_op ->
     begin match list_op with
     | Nil  -> []
     | Cons (it, it') -> [it; it']
     | List its -> its
     | Head it -> [it]
     | Tail it -> [it]
     | NthList (_,it) -> [it]
     end
  | Set_op set_op ->
     begin match set_op with
     | SetMember (t1,t2) -> [t1;t2]
     | SetUnion ts -> ts
     | SetIntersection ts -> ts
     | SetDifference (t1, t2) -> [t1;t2]
     | Subset (t1, t2) -> [t1;t2]
     end
  | Map_op map_op -> 
     begin match map_op with
     | Const (_, t) -> [t]
     | Set (t1,t2,t3) -> [t1;t2;t3]
     | Get (t, arg) -> [t; arg]
     | Def ((s, _), body) -> (* in binders *) []
     end
  | Let ((s, bound), body) -> [bound] (* s/body in binders *)
  | _ -> []

let subterm_binder : 'bt. 'bt term -> (Sym.t * 'bt term) option =
  fun (IT (it, _)) ->
  match it with
  | Bool_op (EachI ((_, s, _), t)) -> Some (s, t)
  | Map_op (Def ((s, _), body)) -> Some (s, body)
  | Let ((s, bound), body) -> Some (s, body)
  | _ -> None

let fold_subterms : 'a 'bt. (Sym.t list -> 'a -> 'bt term -> 'a) -> 'a -> 'bt term -> 'a =
  fun f acc t ->
  let rec g xs acc = function
    | [] -> acc
    | [] :: tss -> g xs acc tss
    | (t :: ts) :: tss ->
    let acc = f xs acc t in
    let acc = match subterm_binder t with
      | None -> acc
      | Some (sym, t) -> g (sym :: xs) acc [[t]]
    in
    g xs acc (subterms t :: ts :: tss)
  in
  g [] acc [[t]]


let free_vars : 'bt. 'bt term -> SymSet.t =
  fun t ->
  let add_sym ss = fun (IT (it, _)) ->
    match it with
    | Lit (Sym symbol) -> SymSet.add symbol ss
    | _ -> ss
  in
  let rec f ss = function
    | [] -> ss
    | [] :: tss -> f ss tss
    | (t :: ts) :: tss ->
    let ss = add_sym ss t in
    let ss = match subterm_binder t with
      | None -> ss
      | Some (sym, t) -> SymSet.union ss (SymSet.remove sym (f SymSet.empty [[t]]))
    in
    f ss (subterms t :: ts :: tss)
  in
  f SymSet.empty [[t]]

let free_vars_list xs = List.fold_left
    (fun ss t -> SymSet.union ss (free_vars t)) SymSet.empty xs


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
       | Div (it, it') -> Div (subst su it, subst su it')
       | Exp (it, it') -> Exp (subst su it, subst su it')
       | Rem (it, it') -> Rem (subst su it, subst su it')
       | Mod (it, it') -> Mod (subst su it, subst su it')
       | LT (it, it') -> LT (subst su it, subst su it')
       | LE (it, it') -> LE (subst su it, subst su it')
       | Min (it, it') -> Min (subst su it, subst su it')
       | Max (it, it') -> Max (subst su it, subst su it')
       | IntToReal it -> IntToReal (subst su it)
       | RealToInt it -> RealToInt (subst su it)
       | FlipBit {bit; t} -> FlipBit {bit = subst su bit; t = subst su t}
       | XOR (ity, it, it') -> XOR (ity, subst su it, subst su it')
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
          if SymSet.mem s su.relevant then
            let s' = Sym.fresh_same s in
            let t = subst (make_subst [(s, IT (Lit (Sym s'), BT.Integer))]) t in
            let t = subst su t in
            EachI ((i1, s', i2), t)
          else
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
       | StructMember (t, f) ->
          StructMember (subst su t, f)
     in
     IT (Struct_op struct_op, bt)
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
          if SymSet.mem s su.relevant then
            let s' = Sym.fresh_same s in 
            let body = subst (make_subst [(s, IT (Lit (Sym s'), abt))]) body in
            let body = subst su body in
            Def ((s', abt), body)
          else 
            Def ((s, abt), subst su body)
     in
     IT (Map_op map_op, bt)
  (* | Option_op option_op ->  *)
  (*    let option_op = match option_op with *)
  (*      | Nothing bt -> Nothing bt *)
  (*      | Something t -> Something (subst su t) *)
  (*      | Is_nothing t -> Is_nothing (subst su t) *)
  (*      | Is_something t -> Is_something (subst su t) *)
  (*      | Get_some_value t -> Get_some_value (subst su t) *)
  (*    in *)
  (*    IT (Option_op option_op, bt) *)
  | Let ((s, bound), body) ->
     let bound = subst su bound in
     if SymSet.mem s su.relevant then
       let s' = Sym.fresh_same s in
       let body = subst (make_subst [(s, IT (Lit (Sym s'), basetype bound))]) body in
       let body = subst su body in
       IT (Let ((s', bound), body), bt)
     else
       IT (Let ((s, bound), subst su body), bt)







let is_lit = function
  | IT (Lit lit, bt) -> Some (lit, bt)
  | _ -> None

let is_z = function
  | IT (Lit (Z z), bt) -> Some z
  | _ -> None

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
let or_ its = IT (Bool_op (Or its), BT.Bool)
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

(* arith_op *)
let add_ (it, it') = IT (Arith_op (Add (it, it')), bt it)
let sub_ (it, it') = IT (Arith_op (Sub (it, it')), bt it)
let mul_ (it, it') = IT (Arith_op (Mul (it, it')), bt it)
let div_ (it, it') = IT (Arith_op (Div (it, it')), bt it)
let exp_ (it, it') = 
  match is_z it, is_z it' with
  | Some z, Some z' when Z.fits_int z' ->
     z_ (Z.pow z (Z.to_int z'))
  | _ ->
     IT (Arith_op (Exp (it, it')), bt it)
let rem_ (it, it') = IT (Arith_op (Rem (it, it')), BT.Integer)
let mod_ (it, it') = IT (Arith_op (Mod (it, it')), BT.Integer)
let rem_t___ (it, it') = failwith "rem_t"
let rem_f___ (it, it') = mod_ (it, it')
let min_ (it, it') = IT (Arith_op (Min (it, it')), bt it)
let max_ (it, it') = IT (Arith_op (Max (it, it')), bt it)
let intToReal_ it = IT (Arith_op (IntToReal it), BT.Real)
let realToInt_ it = IT (Arith_op (RealToInt it), BT.Integer)
let xor_ ity (it, it') = IT (Arith_op (XOR (ity, it, it')), BT.Integer)

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


let ne_array_prop_ (q : Sym.t) it = 
  let q = sym_ (q, BT.Integer) in
  or_ [q %<= (it %- (int_ 1));
       (it %+ (int_ 1)) %<= q]




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
  let member_bt = 
    BT.of_sct
      (List.assoc Id.equal member 
         (Memory.member_types (SymMap.find tag struct_decls)))
  in
  member_ ~member_bt (tag, t, member)








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

let memberShift_ (t, tag, member) = 
  integerToPointerCast_ 
    (add_ (pointerToIntegerCast_ t, memberOffset_ (tag, member)))
let arrayShift_ (t1, ct, t2) = 
  integerToPointerCast_
    (add_ (pointerToIntegerCast_ t1, arrayOffset_ (ct, t2)))






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
  let index = array_pointer_to_index ~base ~item_size ~pointer:qpointer in
  and_ [lePointer_ (base, qpointer);
        eq_ (rem_ (offset, item_size), int_ 0);
        le_ (from_index, index); lt_ (index, to_index)]  


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
let good_ (t, it) = 
  IT (CT_pred (Good (t, it)), BT.Bool)
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


(* let nothing_ bt =  *)
(*   IT (Option_op (Nothing bt), BT.Option bt) *)
(* let something_ t = *)
(*   IT (Option_op (Something t), BT.Option (basetype t)) *)
(* let is_nothing_ t = *)
(*   IT (Option_op (Is_nothing t), BT.Bool) *)
(* let is_something_ t = *)
(*   IT (Option_op (Is_something t), BT.Bool) *)
(* let get_some_value_ t = *)
(*   let vbt = BT.option_bt (basetype t) in *)
(*   IT (Option_op (Get_some_value t), vbt) *)


let let_ (s, bound) body = 
  IT (Let ((s, bound), body), basetype body)
let let__ (name, bound) body =
  let s = Sym.fresh_named name in
  let_ (s, bound) (body (sym_ (s, basetype bound)))




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

let disjoint_int_ (p1i, sz1) (p2i, sz2) =
  or_ [le_ (add_ (p1i, sz1), p2i);
       le_ (add_ (p2i, sz2), p1i)]

let disjoint_ (p1, sz1) (p2, sz2) = 
  let p1i = pointerToIntegerCast_ p1 in
  let p2i = pointerToIntegerCast_ p2 in
  disjoint_int_ (p1i, sz1) (p2i, sz2)



(* let in_footprint within (pointer, size) = 
 *   and_ [lePointer_ (pointer, within); 
 *         ltPointer_ (within, addPointer_ (pointer, size))] *)



(* let disjoint_from fp fps =
 *   List.map (fun fp' -> disjoint_ (fp, fp')) fps *)






(* rubbish hash function *)
let hash (IT (it, _bt)) =
  match it with
  | Arith_op _ -> 1
  | Bool_op _ -> 2
  | Tuple_op _ -> 3
  | Struct_op _ -> 4
  | Pointer_op _ -> 5
  | CT_pred _ -> 6
  | List_op _ -> 7
  | Set_op _ -> 8
  | Map_op _ -> 9
  (* | Option_op _ -> 10 *)
  | Let _ -> 11
  | Lit lit ->
     begin match lit with
     | Z z -> 20
     | Q q -> 21
     | Pointer p -> 22
     | Bool b -> 23
     | Unit -> 24
     | Default _ -> 25
     | Null -> 26
     | Sym (Symbol (_,i, _)) -> 100 + i
     end




(* let partiality_check_array ~length ~item_ct value =  *)
(*   let unmapped =  *)
(*     let rec aux i acc =  *)
(*       if i > (length - 1) then acc else  *)
(*         aux (i + 1) (map_set_ acc (int_ i, default_ (BT.of_sct item_ct))) *)
(*     in *)
(*     aux 0 value *)
(*   in *)
(*   let empty = const_map_ Integer (default_ (BT.of_sct item_ct)) in *)
(*   eq_ (unmapped, empty) *)



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



