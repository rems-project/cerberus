open Subst
open List
open Pp
module BT=BaseTypes
module CT = Sctypes
module CF=Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)


type lit = 
  | Sym of Sym.t
  | Z of Z.t
  | Q of int * int
  | Pointer of Z.t
  | Bool of bool
  | Unit
  | Default of BT.t
(* Default bt: equivalent to a unique variable of base type bt, that
   we know nothing about other than Default bt = Default bt *)

(* over integers and reals *)
type 'bt arith_op =
  | Add of 'bt term * 'bt term
  | Sub of 'bt term * 'bt term
  | Mul of 'bt term * 'bt term
  | Div of 'bt term * 'bt term
  | Exp of 'bt term * 'bt term
  | Rem of 'bt term * 'bt term
  (* | Min of 'bt term * 'bt term
   * | Max of 'bt term * 'bt term *)

(* over integers and reals *)
and 'bt cmp_op =
  | LT of 'bt term * 'bt term
  | LE of 'bt term * 'bt term

and 'bt bool_op = 
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term
  | EQ of 'bt term * 'bt term

and 'bt tuple_op = 
  | Tuple of 'bt term list
  | NthTuple of int * 'bt term

and 'bt struct_op =
  | Struct of BT.tag * (BT.member * 'bt term) list
  | StructMember of 'bt term * BT.member

and 'bt pointer_op = 
  | Null
  | AddPointer of 'bt term * 'bt term
  | SubPointer of 'bt term * 'bt term
  | MulPointer of 'bt term * 'bt term
  | LTPointer of 'bt term * 'bt term
  | LEPointer of 'bt term * 'bt term
  | IntegerToPointerCast of 'bt term
  | PointerToIntegerCast of 'bt term
  | MemberOffset of BT.tag * Id.t
  | ArrayOffset of Sctypes.t (*element ct*) * 'bt term (*index*)

and 'bt list_op = 
  | Nil
  | Cons of 'bt term * 'bt term
  | List of 'bt term list
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of int * 'bt term

and 'bt set_op = 
  | SetMember of 'bt term * 'bt term
  | SetUnion of ('bt term) List1.t
  | SetIntersection of ('bt term) List1.t
  | SetDifference of 'bt term * 'bt term
  | Subset of 'bt term * 'bt term



and 'bt ct_pred = 
  (* | MinInteger of CF.Ctype.integerType
   * | MaxInteger of CF.Ctype.integerType *)
  | Representable of CT.t * 'bt term
  | AlignedI of {t : 'bt term; align : 'bt term}
  | Aligned of 'bt term * CT.t

and 'bt option_op = 
  | Something of 'bt term
  | Nothing of BT.t
  | Is_some of 'bt term
  | Value_of_some of 'bt term

and 'bt array_op = 
  | Const of 'bt term
  | Mod of 'bt term * 'bt term * 'bt term
  | App of 'bt term * 'bt term

and 'bt term_ =
  | Lit of lit
  | Arith_op of 'bt arith_op
  | Bool_op of 'bt bool_op
  | Cmp_op of 'bt cmp_op
  | Tuple_op of 'bt tuple_op
  | Struct_op of 'bt struct_op
  | Pointer_op of 'bt pointer_op
  | List_op of 'bt list_op
  | Set_op of 'bt set_op
  | CT_pred of 'bt ct_pred
  | Option_op of 'bt option_op
  | Array_op of 'bt array_op

and 'bt term =
  | IT of 'bt term_ * 'bt



type typed = BT.t term
type untyped = unit term

type it = typed
type t = typed


let bt (IT (_, bt)) : BT.t = bt


let rec equal (IT (it, _)) (IT (it', _)) = 

  let lit it it' =
    match it, it' with
    | Sym sym, Sym sym' -> Sym.equal sym sym'
    | Z n, Z n' -> Z.equal n n'
    | Q (n1,n2), Q (n1',n2') -> n1 = n1' && n2 = n2'
    | Pointer p, Pointer p' -> Z.equal p p'
    | Bool b, Bool b' -> b = b'
    | Unit, Unit -> true
    | Default bt, Default bt' -> BT.equal bt bt'
    | Sym _, _ -> false
    | Z _, _ -> false
    | Q _, _ -> false
    | Pointer _, _ -> false
    | Bool _, _ -> false
    | Unit, _ -> false
    | Default _, _ -> false
  in

  let arith_op it it' =
    match it, it' with
    | Add (t1,t2), Add (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Sub (t1,t2), Sub (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Mul (t1,t2), Mul (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Div (t1,t2), Div (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Exp (t1,t2), Exp (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Rem (t1,t2), Rem (t1',t2') -> equal t1 t1' && equal t2 t2' 
    (* | Min (t1,t2), Min (t1',t2') -> equal t1 t1' && equal t2 t2' 
     * | Max (t1,t2), Max (t1',t2') -> equal t1 t1' && equal t2 t2'  *)
    | Add _, _ -> false
    | Sub _, _ -> false
    | Mul _, _ -> false 
    | Div _, _ -> false
    | Exp _, _ -> false
    | Rem _, _ -> false
    (* | Min _, _ -> false
     * | Max _, _ -> false *)
  in

  let cmp_op it it' = 
    match it, it' with
    | LT (t1,t2), LT (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | LE (t1,t2), LE (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | LT _, _ -> false
    | LE _, _ -> false
  in

  let bool_op it it' = 
    match it, it' with
    | And ts, And ts' -> 
       List.equal equal ts ts'
    | Or ts, Or ts' -> 
       List.equal equal ts ts'
    | Impl (t1,t2), Impl (t1',t2') -> 
       equal t1 t1' && equal t2 t2' 
    | Not t, Not t' -> 
       equal t t' 
    | ITE (t1,t2,t3), ITE (t1',t2',t3') -> 
       equal t1 t1' && equal t2 t2' && equal t3 t3'
    | EQ (t1,t2), EQ (t1',t2') -> 
       equal t1 t1' && equal t2 t2' 
    | And _, _ -> 
       false
    | Or _, _ -> 
       false
    | Impl _, _ -> 
       false
    | Not _, _ ->
       false
    | ITE _, _ ->
       false
    | EQ _, _ -> 
       false
  in

  let tuple_op it it' =
    match it, it' with
    | Tuple its, Tuple its' -> 
       List.equal equal its its'
    | NthTuple (n,t), NthTuple (n',t') -> 
       n = n' && equal t t' 
    | Tuple _, _ -> false
    | NthTuple _, _ -> false
  in

  let struct_op it it' =
    match it, it' with
    | Struct (tag, members), Struct (tag2, members2) ->
       Sym.equal tag tag2 && 
         List.equal (fun (m,t) (m',t') -> Id.equal m m' && equal t t') 
           members members2
    | StructMember (t,member), StructMember (t',member') ->
       equal t t' && Id.equal member member'
    | Struct _, _ -> false
    | StructMember _, _ -> false
  in

  let pointer_op it it' =
    match it, it' with
    | Null, Null -> 
       true
    | AddPointer (t1, t2), AddPointer (t1', t2') -> 
       equal t1 t1' && equal t2 t2'
    | SubPointer (t1, t2), SubPointer (t1', t2') -> 
       equal t1 t1' && equal t2 t2'
    | MulPointer (t1, t2), MulPointer (t1', t2') -> 
       equal t1 t1' && equal t2 t2'
    | LTPointer (t1, t2), LTPointer (t1', t2') -> 
       equal t1 t1' && equal t2 t2'
    | LEPointer (t1, t2), LEPointer (t1', t2') -> 
       equal t1 t1' && equal t2 t2'
    | IntegerToPointerCast t1, IntegerToPointerCast t2 -> 
       equal t1 t2
    | PointerToIntegerCast t1, PointerToIntegerCast t2 -> 
       equal t1 t2
    | MemberOffset (s, m), MemberOffset (s', m') ->
       Sym.equal s s' && Id.equal m m'
    | ArrayOffset (ct, t), ArrayOffset (ct', t') ->
       Sctypes.equal ct ct' && equal t t'
    | Null, _ -> false
    | AddPointer _, _ -> false
    | SubPointer _, _ -> false
    | MulPointer _, _ -> false
    | LTPointer _, _ -> false
    | LEPointer _, _ -> false
    | IntegerToPointerCast _, _ -> false
    | PointerToIntegerCast _, _ -> false
    | MemberOffset _, _ -> false
    | ArrayOffset _, _ -> false
  in

  let list_op it it' = 
    match it, it' with
    | Nil, Nil -> 
       true
    | Cons (t1,t2), Cons (t1',t2') -> 
       equal t1 t1' && equal t2 t2'
    | List its, List its' ->
       List.equal equal its its'
    | Head t, Head t' ->
       equal t t'
    | Tail t, Tail t' ->
       equal t t'
    | NthList (n,t), NthList (n',t') ->
       n = n' && equal t t'
    | Nil, _ -> false
    | Cons _, _ -> false
    | List _, _ -> false
    | Head _, _ -> false
    | Tail _, _ -> false
    | NthList _, _ -> false
  in


  let set_op it it' =
    match it, it' with
    | SetMember (t1,t2), SetMember (t1',t2') ->
       equal t1 t1' && equal t1' t2'
    | SetUnion ts, SetUnion ts' ->
       List1.equal equal ts ts'
    | SetIntersection ts, SetIntersection ts' ->
       List1.equal equal ts ts'
    | SetDifference (t1, t2), SetDifference (t1', t2') ->
       equal t1 t1' && equal t1' t2'
    | Subset (t1, t2), Subset (t1', t2') ->
       equal t1 t1' && equal t1' t2'
    | SetMember _, _ -> false
    | SetUnion _, _ -> false
    | SetIntersection _, _ -> false
    | SetDifference _, _ -> false
    | Subset _, _ -> false
  in



  let ct_pred it it' = 
    match it, it' with
    | Aligned (t, ct), Aligned (t', ct') ->
       equal t t' && CT.equal ct ct'
    | AlignedI t1, AlignedI t2 ->
       equal t1.t t2.t && equal t1.align t2.align
    | Representable (rt, t), Representable (rt', t') ->
       CT.equal rt rt' && equal t t'
    (* | MinInteger it, MinInteger it' ->
     *    CF.Ctype.integerTypeEqual it it'
     * | MaxInteger it, MaxInteger it' ->
     *    CF.Ctype.integerTypeEqual it it' *)
    | Aligned _, _ -> false
    | AlignedI _, _ -> false
    | Representable _, _ -> false
    (* | MinInteger _, _ -> false
     * | MaxInteger _, _ -> false *)
  in

  let option_op it it' = 
    match it, it' with
    | Something it, Something it' -> equal it it'
    | Nothing bt, Nothing bt' -> BT.equal bt bt'
    | Is_some it, Is_some it' -> equal it it'
    | Value_of_some it, Value_of_some it' -> equal it it'
    | Something _, _ -> false
    | Nothing _, _ -> false
    | Is_some _, _ -> false
    | Value_of_some _, _ ->false
  in

  let array_op it it' = 
    match it, it' with
    | Const t, Const t' ->
       equal t t'
    | Mod (t1,t2,t3), Mod (t1',t2',t3') ->
       equal t1 t1' && equal t2 t2' && equal t3 t3'
    | App (t, args), App (t', args') ->
       equal t t' && (* List.equal *) equal args args'
    | Const _, _ -> false
    | Mod _, _ -> false
    | App _, _ -> false
  in

  match it, it' with
  | Lit it, Lit it' -> lit it it'
  | Arith_op it, Arith_op it' -> arith_op it it'
  | Bool_op it, Bool_op it' -> bool_op it it'
  | Cmp_op it, Cmp_op it' -> cmp_op it it'
  | Tuple_op it, Tuple_op it' -> tuple_op it it'
  | Struct_op it, Struct_op it' -> struct_op it it'
  | Pointer_op it, Pointer_op it' -> pointer_op it it'
  | List_op it, List_op it' -> list_op it it'
  | Set_op it, Set_op it' -> set_op it it'
  | CT_pred it, CT_pred it' -> ct_pred it it'
  | Option_op it, Option_op it' -> option_op it it'
  | Array_op it, Array_op it' -> array_op it it'
  | Lit _, _ -> false
  | Arith_op _, _ -> false
  | Bool_op _, _ -> false
  | Cmp_op _, _ -> false
  | Tuple_op _, _ -> false
  | Struct_op _, _ -> false
  | Pointer_op _, _ -> false
  | List_op _, _ -> false
  | Set_op _, _ -> false
  | CT_pred _, _ -> false
  | Option_op _, _ -> false
  | Array_op _, _ -> false





let pp (it : 'bt term) : PPrint.document = 

  let rec aux atomic (IT (it, bt)) = 

    let mparens pped = if atomic then parens pped else pped in
    
    let lit = function
      | Sym sym -> Sym.pp sym
      | Z i -> Z.pp i
      | Q (i,i') -> c_app !^"frac" [!^(string_of_int i); !^(string_of_int i')]
      | Pointer i -> Z.pp i
      | Bool true -> !^"true"
      | Bool false -> !^"false"
      | Unit -> !^"void"
      | Default bt -> c_app !^"default" [BT.pp bt]
    in

    let arith_op = function
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
         c_app !^"rem" [aux true it1; aux true it2]
      (* | Min (it1,it2) -> 
       *    c_app !^"min" [aux true it1; aux true it2]
       * | Max (it1,it2) -> 
       *    c_app !^ "max" [aux true it1; aux true it2] *)
    in

    let cmp_op = function
      | LT (o1,o2) -> 
         mparens (flow (break 1) [aux true o1; langle; aux true o2])
      | LE (o1,o2) -> 
         mparens (flow (break 1) [aux true o1; (langle ^^ equals); aux true o2])
    in

    let bool_op = function
      | And o -> 
         Pp.group (mparens (flow_map (break 1 ^^ !^"&&" ^^ break 1) (aux false) o))
      | Or o -> 
         Pp.group (mparens (flow_map (break 1 ^^ !^"||" ^^ break 1) (aux false) o))
      | Impl (o1,o2) -> 
         mparens (flow (break 1) [aux true o1; (equals ^^ rangle); aux true o2])
      | Not (o1) -> 
         mparens (!^"not" ^^^ aux true o1)
      | ITE (o1,o2,o3) -> 
         mparens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
      | EQ (o1,o2) -> 
         mparens (flow (break 1) [aux true o1; equals ^^ equals; aux true o2])
    in

    let tuple_op = function
      | NthTuple (n,it2) -> 
         mparens (aux true it2 ^^ dot ^^ !^("component" ^ string_of_int n))
      | Tuple its -> 
         braces (separate_map (semi ^^ space) (aux false) its)
    in

    let struct_op = function
      | Struct (_tag, members) ->
         braces (flow_map (comma ^^ break 1) (fun (member,it) -> 
                     Id.pp member ^^^ equals ^^^ aux false it 
                   ) members)
      | StructMember (t, member) ->
         aux true t ^^ dot ^^ Id.pp member
    in

    let pointer_op = function    
      | Null -> 
         !^"null"
      | AddPointer (t1, t2) ->
         mparens (flow (break 1) [aux true t1; plus; aux true t2])
      | SubPointer (t1, t2) ->
         mparens (flow (break 1) [aux true t1; minus; aux true t2])
      | MulPointer (t1, t2) ->
         mparens (flow (break 1) [aux true t1; star; aux true t2])
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
         
    in

    let ct_pred = function
      | Aligned (t, rt) ->
         c_app !^"aligned" [aux false t; CT.pp rt]
      | AlignedI t ->
         c_app !^"aligned" [aux false t.t; aux false t.align]
      (* | MinInteger it ->
       *    c_app !^"min" [CF.Pp_core_ctype.pp_integer_ctype it]
       * | MaxInteger it ->
       *    c_app !^"max" [CF.Pp_core_ctype.pp_integer_ctype it] *)
      | Representable (rt, t) ->
         c_app !^"repr" [CT.pp rt; aux false t]
    in

    let list_op = function    
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
    in

    let set_op = function
      | SetMember (t1,t2) ->
         c_app !^"member" [aux false t1; aux false t2]
      | SetUnion ts ->
         c_app !^"union" (List.map (aux false) (List1.to_list ts))
      | SetIntersection ts ->
         c_app !^"intersection" (List.map (aux false) (List1.to_list ts))
      | SetDifference (t1, t2) ->
         c_app !^"difference" [aux false t1; aux false t2]
      | Subset (t1, t2) ->
         c_app !^"subset" [aux false t1; aux false t2]
    in

    let option_op = function
      | Something it -> 
         c_app !^"something" [aux atomic it]
      | Nothing bt ->
         c_app !^"nothing" [BT.pp bt]
      | Is_some it ->
         c_app !^"is_some" [aux false it]
      | Value_of_some it ->
         c_app !^"value_of_some" [aux false it]
    in

    let array_op = function
      | Const t ->
         c_app !^"const" [aux false t]
      | Mod (t1,t2,t3) ->
         aux false t1 ^^ lbracket ^^ aux false t2 ^^^ equals ^^^ aux false t3 ^^ rbracket
      | App (t, args) ->
         c_app (aux true t) [aux false args]
    in

    match it with
    | Lit it -> lit it
    | Arith_op it -> arith_op it
    | Cmp_op it -> cmp_op it
    | Bool_op it -> bool_op it
    | Tuple_op it -> tuple_op it
    | Struct_op it -> struct_op it
    | Pointer_op it -> pointer_op it
    | CT_pred it -> ct_pred it
    | List_op it -> list_op it
    | Set_op it -> set_op it
    | Option_op it -> option_op it
    | Array_op it -> array_op it

  in

  aux false it


let rec free_vars : 'bt. 'bt term -> SymSet.t =

  let lit : lit -> SymSet.t = function
    | Sym symbol -> SymSet.singleton symbol
    | Z _ -> SymSet.empty
    | Q _ -> SymSet.empty
    | Pointer _ -> SymSet.empty
    | Bool _ -> SymSet.empty
    | Unit -> SymSet.empty
    | Default _ -> SymSet.empty
  in

  let arith_op : 'bt arith_op -> SymSet.t = function
    | Add (it, it') -> free_vars_list [it; it']
    | Sub (it, it') -> free_vars_list [it; it']
    | Mul (it, it') -> free_vars_list [it; it']
    | Div (it, it') -> free_vars_list [it; it']
    | Exp (it, it') -> free_vars_list [it; it']
    | Rem (it, it') -> free_vars_list [it; it']
    (* | Min (it, it') -> free_vars_list [it; it']
     * | Max (it, it') -> free_vars_list [it; it'] *)
  in

  let cmp_op : 'bt cmp_op -> SymSet.t = function
    | LT (it, it') -> free_vars_list [it; it']
    | LE (it, it') -> free_vars_list [it; it']
  in

  let bool_op : 'bt bool_op -> SymSet.t = function
    | And its -> free_vars_list its
    | Or its -> free_vars_list its
    | Impl (it, it') -> free_vars_list [it; it']
    | Not it -> free_vars it
    | ITE (it,it',it'') -> free_vars_list [it;it';it'']
    | EQ (it, it') -> free_vars_list [it; it']
  in

  let tuple_op : 'bt tuple_op -> SymSet.t = function
    | Tuple its -> free_vars_list its
    | NthTuple ( _, it) -> free_vars it
  in
  
  let struct_op : 'bt struct_op -> SymSet.t = function
    | Struct (_tag, members) -> free_vars_list (map snd members)
    | StructMember (it, s) -> free_vars_list [it;it]
  in

  let pointer_op : 'bt pointer_op -> SymSet.t = function
    | Null -> SymSet.empty
    | AddPointer (it, it') -> free_vars_list [it; it']
    | SubPointer (it, it') -> free_vars_list [it; it']
    | MulPointer (it, it') -> free_vars_list [it; it']
    | LTPointer (it, it')  -> free_vars_list [it; it']
    | LEPointer (it, it') -> free_vars_list [it; it']
    | IntegerToPointerCast t -> free_vars t
    | PointerToIntegerCast t -> free_vars t
    | MemberOffset (_, _) -> SymSet.empty
    | ArrayOffset (_, t) -> free_vars t
  in

  let ct_pred : 'bt ct_pred -> SymSet.t = function
    | Aligned (t, _rt) -> free_vars t
    | AlignedI t -> free_vars_list [t.t; t.align]
    (* | MinInteger _ -> SymSet.empty
     * | MaxInteger _ -> SymSet.empty *)
    | Representable (_rt,t) -> free_vars t
  in

  let list_op : 'bt list_op -> SymSet.t = function
    | Nil  -> SymSet.empty
    | Cons (it, it') -> free_vars_list [it; it']
    | List its -> free_vars_list its
    | Head it -> free_vars it
    | Tail it -> free_vars it
    | NthList (_,it) -> free_vars it
  in

  let set_op : 'bt set_op -> SymSet.t = function
    | SetMember (t1,t2) -> free_vars_list [t1;t2]
    | SetUnion ts -> free_vars_list (List1.to_list ts)
    | SetIntersection ts -> free_vars_list (List1.to_list ts)
    | SetDifference (t1, t2) -> free_vars_list [t1;t2]
    | Subset (t1, t2) -> free_vars_list [t1;t2]
  in
  
  let option_op = function
    | Something it -> free_vars it
    | Nothing _ -> SymSet.empty
    | Is_some it -> free_vars it
    | Value_of_some it -> free_vars it
  in

  let array_op = function
    | Const t -> free_vars t
    | Mod (t1,t2,t3) -> free_vars_list [t1;t2;t3]
    | App (t, arg) -> free_vars_list ([t; arg])
  in

  fun (IT (it, _)) ->
  match it with
  | Lit it -> lit it
  | Arith_op it -> arith_op it
  | Cmp_op it -> cmp_op it
  | Bool_op it -> bool_op it
  | Tuple_op it -> tuple_op it
  | Struct_op it -> struct_op it
  | Pointer_op it -> pointer_op it
  | CT_pred it -> ct_pred it
  | List_op it -> list_op it
  | Set_op it -> set_op it
  | Option_op it -> option_op it
  | Array_op it -> array_op it


and free_vars_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (free_vars sym)
    ) SymSet.empty l


let json it : Yojson.Safe.t = `String (Pp.plain (pp it))


let subst (substitution : (Sym.t, 'bt -> 'bt term) Subst.t) =

  let rec aux = 

    let lit it bt = 
      match it with
      | Sym symbol when Sym.equal symbol substitution.before ->
         substitution.after bt
      | it -> IT (Lit it, bt)
    in

    let arith_op it bt = 
      let it = match it with
        | Add (it, it') -> Add (aux it, aux it')
        | Sub (it, it') -> Sub (aux it, aux it')
        | Mul (it, it') -> Mul (aux it, aux it')
        | Div (it, it') -> Div (aux it, aux it')
        | Exp (it, it') -> Exp (aux it, aux it')
        | Rem (it, it') -> Rem (aux it, aux it')
        (* | Min (it, it') -> Min (aux it, aux it')
         * | Max (it, it') -> Max (aux it, aux it') *)
      in
      IT (Arith_op it, bt)
    in

    let cmp_op it bt = 
      let it = match it with
        | LT (it, it') -> LT (aux it, aux it')
        | LE (it, it') -> LE (aux it, aux it')
      in
      IT (Cmp_op it, bt)
    in

    let bool_op it bt = 
      let it = match it with
        | And its -> And (map (aux) its)
        | Or its -> Or (map (aux) its)
        | Impl (it, it') -> Impl (aux it, aux it')
        | Not it -> Not (aux it)
        | ITE (it,it',it'') -> ITE (aux it, aux it', aux it'')
        | EQ (it, it') -> EQ (aux it, aux it')
      in
      IT (Bool_op it, bt)
    in

    let tuple_op it bt = 
      let it = match it with
        | Tuple its ->
           Tuple (map aux its)
        | NthTuple (n, it') ->
           NthTuple (n, aux it')
      in
      IT (Tuple_op it, bt)
    in
    
    let struct_op it bt =
      let it = match it with
        | Struct (tag, members) ->
           let members = map (fun (member,it) -> (member,aux it)) members in
           Struct (tag, members)
        | StructMember (t, f) ->
           StructMember (aux t, f)
      in
      IT (Struct_op it, bt)
    in

    let pointer_op it bt =
      let it = match it with
        | Null -> 
           Null
        | AddPointer (it, it') -> 
           AddPointer (aux it, aux it')
        | SubPointer (it, it') -> 
           SubPointer (aux it, aux it')
        | MulPointer (it, it') -> 
           MulPointer (aux it, aux it')
        | LTPointer (it, it') -> 
           LTPointer (aux it, aux it')
        | LEPointer (it, it') -> 
           LEPointer (aux it, aux it')
        | IntegerToPointerCast t -> 
           IntegerToPointerCast (aux t)
        | PointerToIntegerCast t -> 
           PointerToIntegerCast (aux t)
        | MemberOffset (tag, member) ->
           MemberOffset (tag, member)
        | ArrayOffset (tag, t) ->
           ArrayOffset (tag, aux t)
      in
      IT (Pointer_op it, bt)
    in

    let ct_pred it bt =
      let it = match it with
        | Aligned (t, ct) -> Aligned (aux t, ct)
        | AlignedI t -> AlignedI {t= aux t.t; align= aux t.align}
        (* | MinInteger it -> MinInteger it
         * | MaxInteger it -> MaxInteger it *)
        | Representable (rt,t) -> Representable (rt,aux t)
      in
      IT (CT_pred it, bt)
    in

    let list_op it bt =
      let it = match it with
        | Nil -> Nil
        | Cons (it1,it2) -> Cons (aux it1, aux it2)
        | List its -> List (map aux its)
        | Head it -> Head (aux it)
        | Tail it -> Tail (aux it)
        | NthList (i, it) -> NthList (i, aux it)
      in
      IT (List_op it, bt)
    in

    let set_op it bt = 
      let it = match it with
        | SetMember (t1,t2) -> SetMember (aux t1, aux t2)
        | SetUnion ts -> SetUnion (List1.map aux ts)
        | SetIntersection ts -> SetIntersection (List1.map aux ts)
        | SetDifference (t1, t2) -> SetDifference (aux t1, aux t2)
        | Subset (t1, t2) -> Subset (aux t1, aux t2)
      in
      IT (Set_op it, bt)
    in

    let option_op it bt = 
      let it = match it with
        | Something it -> Something (aux it)
        | Nothing bt' -> Nothing bt'
        | Is_some it -> Is_some (aux it)
        | Value_of_some it -> Value_of_some (aux it)
      in
      IT (Option_op it, bt)
    in

    let array_op it bt =
      let it = match it with
        | Const t ->
           Const (aux t)
        | Mod (t1, t2, t3) ->
           Mod (aux t1, aux t2, aux t3)
        | App (it, arg) ->
           App (aux it, aux arg)
      in
      IT (Array_op it, bt)
    in


    fun (IT (it, bt)) ->
    match it with
    | Lit it -> lit it bt
    | Arith_op it -> arith_op it bt
    | Cmp_op it -> cmp_op it bt
    | Bool_op it -> bool_op it bt
    | Tuple_op it -> tuple_op it bt
    | Struct_op it -> struct_op it bt
    | Pointer_op it -> pointer_op it bt
    | CT_pred it -> ct_pred it bt
    | List_op it -> list_op it bt
    | Set_op it -> set_op it bt
    | Option_op it -> option_op it bt
    | Array_op it -> array_op it bt
  in

  fun it -> aux it


let subst_var (substitution : (Sym.t, Sym.t) Subst.t) it =
  let substitution = 
    {before = substitution.before;
     after = 
       fun bt ->
       IT (Lit (Sym (substitution.after)), bt)}
  in
  subst substitution it


let subst_it (substitution : (Sym.t, 'bt term) Subst.t) it =
  let substitution = 
    {before = substitution.before;
     after = fun bt -> substitution.after}
  in
  subst substitution it


let subst_vars it = make_substs subst_var it

let subst_its it = make_substs subst_it it


(* not general unification: match left-hand side against right-hand
   side, where right-hand side is fully concrete *)
let rec unify it it' res = 
  let equal_it = equal in
  let open Option in
  let open Uni in
  let match_symbol s it' res = 
    let@ uni = SymMap.find_opt s res in
    match uni.resolved with
    | Some it_res when equal_it it_res it' -> return res 
    | Some _ -> fail
    | None -> return (SymMap.add s {resolved = Some it'} res)
  in
  if equal_it it it' then return res else
    match it, it' with
    | IT (Lit (Sym s), _), _ -> 
       match_symbol s it' res
    | IT (Array_op (App (IT (Lit (Sym f), _), arg)), _), 
      IT (Array_op (App (f_it', arg')), _) ->
       let@ res = match_symbol f f_it' res in
       unify arg arg' res
    | _ -> fail




let rec unifiable = function
  | IT (Lit (Sym s), _) -> Some s
  | IT (Array_op (App (it, args)), _) -> unifiable it
  | _ -> None





let is_sym = function
  | IT (Lit (Sym sym), bt) -> Some (sym, bt)
  | _ -> None

let is_app = function
  | IT (Array_op (App (f,arg)), _) -> Some (f, arg)
  | _ -> None



let zero_frac = function
  | IT (Lit (Q (i,j)), _) when i = 0 -> true
  | _ -> false

let is_true = function
  | IT (Lit (Bool true), _) -> true
  | _ -> false

let is_false = function
  | IT (Lit (Bool false), _) -> true
  | _ -> false


(* shorthands *)


(* lit *)
let sym_ (sym, bt) = IT (Lit (Sym sym), bt)
let z_ n = IT (Lit (Z n), BT.Integer)
let q_ (n,n') = IT (Lit (Q (n,n')), BT.Real)
let pointer_ n = IT (Lit (Pointer n), BT.Loc)
let bool_ b = IT (Lit (Bool b), BT.Bool)
let unit_ = IT (Lit Unit, BT.Unit)
let int_ n = z_ (Z.of_int n)
let default_ bt = IT (Lit (Default bt), bt)

(* cmp_op *)
let lt_ (it, it') = IT (Cmp_op (LT (it, it')), BT.Bool)
let le_ (it, it') = IT (Cmp_op (LE (it, it')), BT.Bool)
let gt_ (it, it') = lt_ (it', it)
let ge_ (it, it') = le_ (it', it)

(* bool_op *)
let and_ its = IT (Bool_op (And its), BT.Bool)
let or_ its = IT (Bool_op (Or its), BT.Bool)
let impl_ (it, it') = IT (Bool_op (Impl (it, it')), BT.Bool)
let not_ it = IT (Bool_op (Not it), BT.Bool)
let ite_ (it, it', it'') = IT (Bool_op (ITE (it, it', it'')), bt it')
let eq_ (it, it') = IT (Bool_op (EQ (it, it')), BT.Bool)
let eq__ it it' = eq_ (it, it')
let ne_ (it, it') = not_ (eq_ (it, it'))
let ne__ it it' = ne_ (it, it')

(* arith_op *)
let add_ (it, it') = IT (Arith_op (Add (it, it')), bt it)
let sub_ (it, it') = IT (Arith_op (Sub (it, it')), bt it)
let mul_ (it, it') = IT (Arith_op (Mul (it, it')), bt it)
let div_ (it, it') = IT (Arith_op (Div (it, it')), bt it)
let exp_ (it, it') = IT (Arith_op (Exp (it, it')), bt it)
let rem_ (it, it') = IT (Arith_op (Rem (it, it')), BT.Integer)
let rem_t___ (it, it') = rem_ (it, it')
let rem_f___ (it, it') = rem_ (it, it')
let min_ (it, it') = ite_ (le_ (it, it'), it, it')
let max_ (it, it') = ite_ (ge_ (it, it'), it, it')

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
  let member_bt = 
    BT.of_sct
      (List.assoc Id.equal member 
         (Memory.member_types (SymMap.find tag struct_decls)))
  in
  member_ ~member_bt (tag, t, member)








(* pointer_op *)
let null_ = IT (Pointer_op Null, BT.Loc)
let addPointer_ (it, it') = IT (Pointer_op (AddPointer (it, it')), BT.Loc)
let subPointer_ (it, it') = IT (Pointer_op (SubPointer (it, it')), BT.Loc)
let mulPointer_ (it, it') = IT (Pointer_op (MulPointer (it, it')), BT.Loc)
let ltPointer_ (it, it') = IT (Pointer_op (LTPointer (it, it')), BT.Bool)
let lePointer_ (it, it') = IT (Pointer_op (LEPointer (it, it')), BT.Bool)
let gtPointer_ (it, it') = ltPointer_ (it', it)
let gePointer_ (it, it') = lePointer_ (it', it)
let disjoint_ ((p1, s1), (p2, s2)) = 
  or_ [lePointer_ (addPointer_ (p1, s1), p2); 
       lePointer_ (addPointer_ (p2, s2), p1)] 
let integerToPointerCast_ it = 
  IT (Pointer_op (IntegerToPointerCast it), BT.Loc)
let pointerToIntegerCast_ it = 
  IT (Pointer_op (PointerToIntegerCast it), BT.Integer)
let memberOffset_ (tag, member) = 
  IT (Pointer_op (MemberOffset (tag, member)), BT.Integer)
let arrayOffset_ (ct, t) = 
  IT (Pointer_op (ArrayOffset (ct, t)), BT.Integer)
let memberShift_ (t, tag, member) = 
  addPointer_ (t, memberOffset_ (tag, member))
let arrayShift_ (t1, ct, t2) = 
  addPointer_ (t1, arrayOffset_ (ct, t2))

let (%+.) it it' = addPointer_ (it, it')





let container_of_ (t, tag, member) =
  subPointer_ (t, memberOffset_ (tag, member))

(* list_op *)
let nil_ ~item_bt = IT (List_op Nil, BT.List item_bt)
let cons_ (it, it') = IT (List_op (Cons (it, it')), bt it')
let list_ ~item_bt its = IT (List_op (List its), BT.List item_bt)
let head_ ~item_bt it = IT (List_op (Head it), item_bt)
let tail_ it = IT (List_op (Tail it), bt it)
let nthList_ ~item_bt (n, it) = IT (List_op (NthList (n, it)), item_bt)

(* set_op *)
let setMember_ bt (it, it') = IT (Set_op (SetMember (it, it')), BT.Bool)
let setUnion_ its = IT (Set_op (SetUnion its), bt (List1.head its))
let setIntersection_ its = IT (Set_op (SetIntersection its), bt (List1.head its))
let setDifference_ (it, it') = IT (Set_op (SetDifference (it, it')), bt it)
let subset_ (it, it') = IT (Set_op (Subset (it, it')), BT.Bool)



(* ct_pred *)
let minInteger_ t = 
  z_ (Memory.min_integer_type t)
let maxInteger_ t = 
  z_ (Memory.max_integer_type t)
let representable_ (t, it) = 
  IT (CT_pred (Representable (t, it)), BT.Bool)
let aligned_ (t, it) = 
  IT (CT_pred (Aligned (t, it)), BT.Bool)
let alignedI_ ~t ~align = 
  IT (CT_pred (AlignedI {t; align}), BT.Bool)

(* point_value *)
let something_ v = 
  IT (Option_op (Something v), BT.Option (bt v))
let nothing_ bt = 
  IT (Option_op (Nothing bt), BT.Option bt)
let is_some_ v = 
  IT (Option_op (Is_some v), BT.Bool)
let value_of_some_ v = 
  match bt v with
  | BT.Option bt -> 
     IT (Option_op (Value_of_some v), bt)
  | _ -> Debug_ocaml.error "illtyped index term"

let const_ t = 
  IT (Array_op (Const t), BT.Array (Integer, bt t))
let mod_ (t1, t2, t3) = 
  IT (Array_op (Mod (t1, t2, t3)), bt t1)
let app_ v arg = 
  match bt v with
  | BT.Array (_, bt) ->
     IT (Array_op (App (v, arg)), bt)
  | _ -> Debug_ocaml.error "illtyped index term"

let (%@) it it' = app_ it it'






let fresh bt = 
  let symbol = Sym.fresh () in
  (symbol, sym_ (symbol, bt))

let fresh_named bt name = 
  let symbol = Sym.fresh_named name in
  (symbol, sym_ (symbol, bt))







let def_ sym e = eq_ (sym_ (sym, bt e), e)

let in_range within (min, max) = 
  and_ [le_ (min, within); le_ (within, max)]

let in_footprint within (pointer, size) = 
  and_ [lePointer_ (pointer, within); 
        ltPointer_ (within, addPointer_ (pointer, size))]



let disjoint_from fp fps =
  List.map (fun fp' -> disjoint_ (fp, fp')) fps






(* rubbish hash function *)
let hash (IT (it, _bt)) =
  match it with
  | Arith_op it -> 1
  | Cmp_op it -> 2
  | Bool_op it -> 3
  | Tuple_op it -> 4
  | Struct_op it -> 5
  | Pointer_op it -> 6
  | CT_pred it -> 7
  | List_op it -> 8
  | Set_op it -> 9
  (* | Array_op it -> 10 *)
  | Option_op it -> 11
  | Array_op it -> 12
  | Lit lit ->
     begin match lit with
     | Z z -> 20
     | Q (i, j) -> 21
     | Pointer p -> 22
     | Bool b -> 23
     | Unit -> 24
     | Default _ -> 25
     | Sym (Symbol (_,i, _)) -> 100 + i
     end



let rec representable_ctype struct_layouts (Sctype (_, ct) : Sctypes.t) about =
  let open Sctypes in
  let open Memory in
  match ct with
  | Void -> 
     bool_ true
  | Integer it -> 
     in_range about (z_ (min_integer_type it), z_ (max_integer_type it))
  | Array (it, None) -> 
     Debug_ocaml.error "todo: 'representable' for arrays with unknown length"
  | Array (ct, Some n) -> 
     let lcs = 
       List.init n (fun i ->
           (representable_ctype struct_layouts ct
              (app_ about (int_ i)))
         )
     in
     and_ lcs
  | Pointer _ -> 
     let pointer_byte_size = size_of_pointer in
     let pointer_size = Z.mult_big_int pointer_byte_size (Z.of_int 8) in
     let max = Z.power_int_positive_big_int 2 pointer_size in
     and_ [lePointer_ (pointer_ Z.zero, about); 
           ltPointer_ (about, pointer_ max)]
  | Struct tag -> 
     let layout = struct_layouts tag in
     and_ begin
         List.filter_map (fun piece ->
             match piece.member_or_padding with
             | Some (member, sct) ->
                let rangef = representable_ctype struct_layouts sct in
                let bt = BT.of_sct sct in
                let member_it = member_ ~member_bt:bt (tag, about, member) in
                Some (rangef member_it)
             | None -> 
                None
           ) layout
       end
  | Function _ -> 
     Debug_ocaml.error "todo: function types"


let good_pointer pointer_it pointee_sct = 
  match pointee_sct with
  | CT.Sctype (_, Void) ->
     representable_ (CT.pointer_sct pointee_sct, pointer_it);
  | _ -> 
     and_ [
         representable_ (CT.pointer_sct pointee_sct, pointer_it);
         aligned_ (pointer_it, pointee_sct);
       ]

let rec good_value struct_layouts ct about =
  let open Sctypes in
  let open Memory in
  let (Sctype (_, ct_)) = ct in
  match ct_ with
  | Void -> 
     representable_ctype struct_layouts ct about
  | Integer it -> 
     representable_ctype struct_layouts ct about
  | Array (it, None) -> 
     Debug_ocaml.error "todo: 'representable' for arrays with unknown length"
  | Array (ct, Some n) -> 
     let lcs = 
       List.init n (fun i ->
           good_value struct_layouts ct
             (app_ about (int_ i))
         )
     in
     and_ lcs
  | Pointer (_, pointee_ct) -> 
     good_pointer about pointee_ct
  | Struct tag -> 
     let layout = struct_layouts tag in
     and_ begin
         List.filter_map (fun piece ->
             match piece.member_or_padding with
             | Some (member, sct) ->
                let bt = BT.of_sct sct in
                let member_it = member_ ~member_bt:bt (tag, about, member) in
                Some (good_value struct_layouts sct member_it)
             | None -> 
                None
           ) layout
       end
  | Function _ -> 
     Debug_ocaml.error "todo: function types"



