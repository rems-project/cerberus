open Subst
open List
open Pp
module BT=BaseTypes
module CT = Sctypes
module CF=Cerb_frontend
module SymSet = Set.Make(Sym)


type 'bt lit = 
  | Sym of 'bt * Sym.t
  | Num of Z.t
  | Pointer of Z.t
  | Bool of bool
  | Unit

type 'bt arith_op =
  | Add of 'bt term * 'bt term
  | Sub of 'bt term * 'bt term
  | Mul of 'bt term * 'bt term
  | Div of 'bt term * 'bt term
  | Exp of 'bt term * 'bt term
  | Rem_t of 'bt term * 'bt term
  | Rem_f of 'bt term * 'bt term
  | Min of 'bt term * 'bt term
  | Max of 'bt term * 'bt term

and 'bt cmp_op =
  | EQ of 'bt term * 'bt term
  | NE of 'bt term * 'bt term
  | LT of 'bt term * 'bt term
  | GT of 'bt term * 'bt term
  | LE of 'bt term * 'bt term
  | GE of 'bt term * 'bt term

and 'bt bool_op = 
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term

and 'bt tuple_op = 
  | Tuple of 'bt list * 'bt term list
  | NthTuple of 'bt * int * 'bt term (* bt is tuple bt *)
  | Struct of BT.tag * (BT.member * 'bt term) list
  | StructMember of BT.tag * 'bt term * BT.member
  | StructMemberOffset of BT.tag * 'bt term * BT.member

and 'bt pointer_op = 
  | Null of 'bt term
  | AllocationSize of 'bt term
  | AddPointer of 'bt term * 'bt term
  | SubPointer of 'bt term * 'bt term
  | MulPointer of 'bt term * 'bt term
  | LTPointer of 'bt term * 'bt term
  | LEPointer of 'bt term * 'bt term
  | Disjoint of ('bt term * 'bt term) * ('bt term * 'bt term)
  | IntegerToPointerCast of 'bt term
  | PointerToIntegerCast of 'bt term

and 'bt list_op = 
  | Nil of 'bt
  | Cons of 'bt term * 'bt term
  | List of 'bt term list * 'bt
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of int * 'bt term

and 'bt set_op = 
  | SetMember of 'bt term * 'bt term
  | SetUnion of ('bt term) List1.t
  | SetIntersection of ('bt term) List1.t
  | SetDifference of 'bt term * 'bt term
  | Subset of 'bt term * 'bt term

and 'bt array_op = 
  | ConstArray of 'bt term * 'bt
  | ArrayGet of 'bt term * 'bt term
  | ArraySet of 'bt term * 'bt term * 'bt term
  | ArrayEqualOnRange of 'bt term * 'bt term * 'bt term * 'bt term
  | ArraySelectAfter of ('bt term * 'bt term) * 'bt term
  | ArrayIndexShiftRight of 'bt term * 'bt term

and 'bt ct_pred = 
  | MinInteger of CF.Ctype.integerType
  | MaxInteger of CF.Ctype.integerType
  | Representable of CT.t * 'bt term
  | AlignedI of 'bt term * 'bt term
  | Aligned of CT.t * 'bt term

and 'bt term =
  | Lit of 'bt lit
  | Arith_op of 'bt arith_op
  | Bool_op of 'bt bool_op
  | Cmp_op of 'bt cmp_op
  | Tuple_op of 'bt tuple_op
  | Pointer_op of 'bt pointer_op
  | List_op of 'bt list_op
  | Set_op of 'bt set_op
  | Array_op of 'bt array_op
  | CT_pred of 'bt ct_pred

type typed = BT.t term
type untyped = unit term

type it = typed
type t = typed


let rec equal it it' = 

  let lit it it' =
    match it, it' with
    | Sym (_,sym), Sym (_,sym') -> Sym.equal sym sym'
    | Num n, Num n' -> Z.equal n n'
    | Pointer p, Pointer p' -> Z.equal p p'
    | Bool b, Bool b' -> b = b'
    | Unit, Unit -> true
    | Sym _, _ -> false
    | Num _, _ -> false
    | Pointer _, _ -> false
    | Bool _, _ -> false
    | Unit, _ -> false
  in

  let arith_op it it' =
    match it, it' with
    | Add (t1,t2), Add (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Sub (t1,t2), Sub (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Mul (t1,t2), Mul (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Div (t1,t2), Div (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Exp (t1,t2), Exp (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Rem_t (t1,t2), Rem_t (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Rem_f (t1,t2), Rem_f (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Min (t1,t2), Min (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Max (t1,t2), Max (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | Add _, _ -> false
    | Sub _, _ -> false
    | Mul _, _ -> false 
    | Div _, _ -> false
    | Exp _, _ -> false
    | Rem_t _, _ -> false
    | Rem_f _, _ -> false
    | Min _, _ -> false
    | Max _, _ -> false
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
  in

  let cmp_op it it' = 
    match it, it' with
    | EQ (t1,t2), EQ (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | NE (t1,t2), NE (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | LT (t1,t2), LT (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | GT (t1,t2), GT (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | LE (t1,t2), LE (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | GE (t1,t2), GE (t1',t2') -> equal t1 t1' && equal t2 t2' 
    | EQ _, _ -> false
    | NE _, _ -> false
    | LT _, _ -> false
    | GT _, _ -> false
    | LE _, _ -> false
    | GE _, _ -> false
  in

  let tuple_op it it' =
    match it, it' with
    | Tuple (bts,its), Tuple (bts',its') -> 
       List.equal BT.equal bts bts' &&
       List.equal equal its its'
    | NthTuple (bt, n,t), NthTuple (bt', n',t') -> 
       BT.equal bt bt' && n = n' && equal t t' 
    | Struct (tag, members), Struct (tag2, members2) ->
       Sym.equal tag tag2 && 
         List.equal (fun (m,t) (m',t') -> Id.equal m m' && equal t t') 
           members members2
    | StructMember (tag,t,member), StructMember (tag',t',member') ->
       Sym.equal tag tag' && equal t t' && Id.equal member member'
    | StructMemberOffset (tag,t,member), StructMemberOffset (tag',t',member') ->
       Sym.equal tag tag' && equal t t' && Id.equal member member'
    | Tuple _, _ -> false
    | NthTuple _, _ -> false
    | Struct _, _ -> false
    | StructMember _, _ -> false
    | StructMemberOffset _, _ -> false
  in

  let pointer_op it it' =
    match it, it' with
    | Null t, Null t' -> 
       equal t t' 
    | AllocationSize t1, AllocationSize t1' -> 
       equal t1 t1'
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
    | Disjoint ((t1, s1), (t2, s2)), Disjoint ((t1', s1'), (t2', s2')) -> 
       equal t1 t1' && equal t2 t2' && 
         equal s1 s1' && equal s2 s2'
    | IntegerToPointerCast t1, IntegerToPointerCast t2 -> 
       equal t1 t2
    | PointerToIntegerCast t1, PointerToIntegerCast t2 -> 
       equal t1 t2
    | Null _, _ -> false
    | AllocationSize _, _ -> false
    | AddPointer _, _ -> false
    | SubPointer _, _ -> false
    | MulPointer _, _ -> false
    | LTPointer _, _ -> false
    | LEPointer _, _ -> false
    | Disjoint _, _ -> false
    | IntegerToPointerCast _, _ -> false
    | PointerToIntegerCast _, _ -> false
  in

  let list_op it it' = 
    match it, it' with
    | Nil bt, Nil bt' -> 
       BT.equal bt bt'
    | Cons (t1,t2), Cons (t1',t2') -> 
       equal t1 t1' && equal t2 t2'
    | List (its,bt), List (its',bt') ->
       List.equal equal its its' && BT.equal bt bt'
    | Head t, Head t' ->
       equal t t'
    | Tail t, Tail t' ->
       equal t t'
    | NthList (n,t), NthList (n',t') ->
       n = n' && equal t t'
    | Nil _, _ -> false
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

  let array_op it it' =
    match it, it' with
    | ConstArray (t,bt), ConstArray (t',bt') ->
       equal t t' && BT.equal bt bt'
    | ArrayGet (t1,t2), ArrayGet (t1',t2') ->
       equal t1 t1' && equal t2 t2'
    | ArraySet (t1,t2,t3), ArraySet (t1',t2',t3') ->
       equal t1 t1' && equal t2 t2' && equal t3 t3'
    | ArrayEqualOnRange (t1,t2,t3,t4), ArrayEqualOnRange (t1',t2',t3',t4') ->
       equal t1 t1' && equal t2 t2' && equal t3 t3' && equal t4 t4'
    | ArraySelectAfter ((t1,t2), t3), ArraySelectAfter ((t1',t2'), t3') ->
       equal t1 t1' && equal t2 t2' && equal t3 t3'
    | ArrayIndexShiftRight (t1, t2), ArrayIndexShiftRight (t1', t2') ->
       equal t1 t1' && equal t2 t2'
    | ConstArray _, _ -> false
    | ArrayGet _, _ -> false
    | ArraySet _, _ -> false
    | ArrayEqualOnRange _, _ -> false
    | ArraySelectAfter _, _ -> false
    | ArrayIndexShiftRight _, _ -> false
  in

  let ct_pred it it' = 
    match it, it' with
    | Aligned (rt, t), Aligned (rt', t') ->
       CT.equal rt rt' && equal t t'
    | AlignedI (t1, t2), AlignedI (t1', t2') ->
       equal t1 t1' && equal t2 t2'
    | Representable (rt, t), Representable (rt', t') ->
       CT.equal rt rt' && equal t t'
    | MinInteger it, MinInteger it' ->
       CF.Ctype.integerTypeEqual it it'
    | MaxInteger it, MaxInteger it' ->
       CF.Ctype.integerTypeEqual it it'
    | Aligned _, _ -> false
    | AlignedI _, _ -> false
    | Representable _, _ -> false
    | MinInteger _, _ -> false
    | MaxInteger _, _ -> false
  in


  match it, it' with
  | Lit it, Lit it' -> lit it it'
  | Arith_op it, Arith_op it' -> arith_op it it'
  | Bool_op it, Bool_op it' -> bool_op it it'
  | Cmp_op it, Cmp_op it' -> cmp_op it it'
  | Tuple_op it, Tuple_op it' -> tuple_op it it'
  | Pointer_op it, Pointer_op it' -> pointer_op it it'
  | List_op it, List_op it' -> list_op it it'
  | Set_op it, Set_op it' -> set_op it it'
  | Array_op it, Array_op it' -> array_op it it'
  | CT_pred it, CT_pred it' -> ct_pred it it'
  | Lit _, _ -> false
  | Arith_op _, _ -> false
  | Bool_op _, _ -> false
  | Cmp_op _, _ -> false
  | Tuple_op _, _ -> false
  | Pointer_op _, _ -> false
  | List_op _, _ -> false
  | Set_op _, _ -> false
  | Array_op _, _ -> false
  | CT_pred _, _ -> false





let pp (type bt) (it : bt term) : PPrint.document = 

  let rec aux atomic it = 

    let mparens pped = if atomic then parens pped else pped in
    
    let lit = function
      | Sym (_,sym) -> Sym.pp sym
      | Num i -> Z.pp i
      | Pointer i -> Z.pp i
      | Bool true -> !^"true"
      | Bool false -> !^"false"
      | Unit -> !^"void"
    in

    let arith_op = function
      | Add (it1,it2) -> 
         mparens (aux true it1 ^^^ plus ^^^ aux true it2)
      | Sub (it1,it2) -> 
         mparens (aux true it1 ^^^ minus ^^^ aux true it2)
      | Mul (it1,it2) -> 
         mparens (aux true it1 ^^^ star ^^^ aux true it2)
      | Div (it1,it2) -> 
         mparens (aux true it1 ^^^ slash ^^^ aux true it2)
      | Exp (it1,it2) -> 
         c_app !^"power" [aux true it1; aux true it2]
      | Rem_t (it1,it2) -> 
         c_app !^"rem_t" [aux true it1; aux true it2]
      | Rem_f (it1,it2) -> 
         c_app !^"rem_f" [aux true it1; aux true it2]
      | Min (it1,it2) -> 
         c_app !^"min" [aux true it1; aux true it2]
      | Max (it1,it2) -> 
         c_app !^ "max" [aux true it1; aux true it2]
    in

    let cmp_op = function
      | EQ (o1,o2) -> 
         mparens (aux true o1 ^^^ equals ^^ equals ^^^ aux true o2)
      | NE (o1,o2) -> 
         mparens (aux true o1 ^^^ !^"!=" ^^^ aux true o2)
      | LT (o1,o2) -> 
         mparens (aux true o1 ^^^ langle ^^^ aux true o2)
      | GT (o1,o2) -> 
         mparens (aux true o1 ^^^ rangle ^^^ aux true o2)
      | LE (o1,o2) -> 
         mparens (aux true o1 ^^^ langle ^^ equals ^^^ aux true o2)
      | GE (o1,o2) -> 
         mparens (aux true o1 ^^^ rangle ^^ equals ^^^ aux true o2)
    in

    let bool_op = function
    | And o -> 
       Pp.group (mparens (flow_map (space ^^ !^"&&" ^^ space) (aux false) o))
    | Or o -> 
       Pp.group (mparens (flow_map (space ^^ !^"||" ^^ space) (aux false) o))
    | Impl (o1,o2) -> 
       mparens (aux true o1 ^^^ equals ^^ rangle ^^^ aux true o2)
    | Not (o1) -> 
       mparens (!^"not" ^^^ aux true o1)
    | ITE (o1,o2,o3) -> 
       mparens (aux true o1 ^^^ !^"?" ^^^ aux true o2 ^^^ colon ^^^ aux false o3)
    in

    let tuple_op = function
      | NthTuple (bt,n,it2) -> 
         mparens (aux true it2 ^^ dot ^^ !^("component" ^ string_of_int n))
      | Tuple (_, its) -> 
         braces (separate_map (semi ^^ space) (aux false) its)
      | Struct (_tag, members) ->
         braces (separate_map (comma ^^ space) (fun (member,it) -> 
                     Id.pp member ^^^ equals ^^^ aux false it 
                   ) members)
      | StructMember (_tag, t, member) ->
         aux true t ^^ dot ^^ Id.pp member
      | StructMemberOffset (_tag, t, member) ->
         mparens (ampersand ^^ aux true t ^^ !^"->" ^^ Id.pp member)
    in

    let pointer_op = function    
      | Null o1 -> 
         c_app !^"null" [aux false o1]
      | AllocationSize t1 ->
         c_app !^"allocationSize" [aux false t1]
      | AddPointer (t1, t2) ->
         mparens (aux true t1 ^^^ plus ^^ dot ^^^ aux true t2)
      | SubPointer (t1, t2) ->
         mparens (aux true t1 ^^^ minus ^^ dot ^^^ aux true t2)
      | MulPointer (t1, t2) ->
         mparens (aux true t1 ^^^ star ^^^ aux true t2)
      | LTPointer (o1,o2) -> 
         mparens (aux true o1 ^^^ langle ^^^ aux true o2)
      | LEPointer (o1,o2) -> 
         mparens (aux true o1 ^^^ langle ^^ equals ^^^ aux true o2)
      | Disjoint ((o1,s1),(o2,s2)) ->
         c_app !^"disj" [aux false o1; aux false s1; aux false o2; aux false s2]
      | IntegerToPointerCast t ->
         mparens (parens(!^"pointer") ^^ aux true t)
      | PointerToIntegerCast t ->
         mparens (parens(!^"integer") ^^ aux true t)
    in

    let ct_pred = function
      | Aligned (rt, t) ->
         c_app !^"aligned" [CT.pp rt; aux false t]
      | AlignedI (t, t') ->
         c_app !^"aligned" [aux false t; aux false t']
      | MinInteger it ->
         c_app !^"min" [CF.Pp_core_ctype.pp_integer_ctype it]
      | MaxInteger it ->
         c_app !^"max" [CF.Pp_core_ctype.pp_integer_ctype it]
      | Representable (rt, t) ->
         c_app !^"repr" [CT.pp rt; aux false t]
    in

    let list_op = function    
      | Head (o1) -> 
         c_app !^"hd" [aux false o1]
      | Tail (o1) -> 
         c_app !^"tl" [aux false o1]
      | Nil _ -> 
         brackets empty
      | Cons (t1,t2) -> 
         mparens (aux true t1 ^^ colon ^^ colon ^^ aux true t2)
      | List (its, _bt) -> 
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

    let array_op = function    
      | ConstArray (t,_) ->
         c_app !^"all" [aux false t]
      | ArrayGet (t1,t2) ->
         aux true t1 ^^ lbracket ^^ aux false t2 ^^ rbracket
      | ArraySet (t1,t2,t3) ->
         aux false t1 ^^ lbracket ^^ aux false t2 ^^^ equals ^^^ aux false t3 ^^ rbracket
      | ArrayEqualOnRange (t1,t2,t3,t4) ->
         c_app !^"equalOnRange" [aux false t1; aux false t2; aux false t3; aux false t4]
      | ArraySelectAfter ((t1,t2), t3) ->
         c_app !^"array_select_after" [aux false t1; aux false t2; aux false t3]
      | ArrayIndexShiftRight (t1, t2) ->
         c_app !^"array_index_shift_right" [aux false t1; aux false t2]
    in

    match it with
    | Lit it -> lit it
    | Arith_op it -> arith_op it
    | Cmp_op it -> cmp_op it
    | Bool_op it -> bool_op it
    | Tuple_op it -> tuple_op it
    | Pointer_op it -> pointer_op it
    | CT_pred it -> ct_pred it
    | List_op it -> list_op it
    | Set_op it -> set_op it
    | Array_op it -> array_op it

  in

  aux false it


let rec vars_in : 'bt. 'bt term -> SymSet.t =

  let lit : 'bt lit -> SymSet.t = function
    | Sym (_, symbol) -> SymSet.singleton symbol
    | Num _ -> SymSet.empty
    | Pointer _ -> SymSet.empty
    | Bool _ -> SymSet.empty
    | Unit -> SymSet.empty
  in

  let arith_op : 'bt arith_op -> SymSet.t = function
    | Add (it, it') -> vars_in_list [it; it']
    | Sub (it, it') -> vars_in_list [it; it']
    | Mul (it, it') -> vars_in_list [it; it']
    | Div (it, it') -> vars_in_list [it; it']
    | Exp (it, it') -> vars_in_list [it; it']
    | Rem_t (it, it') -> vars_in_list [it; it']
    | Rem_f (it, it') -> vars_in_list [it; it']
    | Min (it, it') -> vars_in_list [it; it']
    | Max (it, it') -> vars_in_list [it; it']
  in

  let cmp_op : 'bt cmp_op -> SymSet.t = function
    | EQ (it, it') -> vars_in_list [it; it']
    | NE (it, it') -> vars_in_list [it; it']
    | LT (it, it') -> vars_in_list [it; it']
    | GT (it, it') -> vars_in_list [it; it']
    | LE (it, it') -> vars_in_list [it; it']
    | GE (it, it') -> vars_in_list [it; it']
  in

  let bool_op : 'bt bool_op -> SymSet.t = function
    | And its -> vars_in_list its
    | Or its -> vars_in_list its
    | Impl (it, it') -> vars_in_list [it; it']
    | Not it -> vars_in it
    | ITE (it,it',it'') -> vars_in_list [it;it';it'']
  in

  let tuple_op : 'bt tuple_op -> SymSet.t = function
    | Tuple (_, its) -> vars_in_list its
    | NthTuple (_, _, it) -> vars_in it
    | Struct (_tag, members) -> vars_in_list (map snd members)
    | StructMember (_tag, it, s) -> vars_in_list [it;it]
    | StructMemberOffset (_tag, it, s) -> vars_in_list [it;it]
  in

  let pointer_op : 'bt pointer_op -> SymSet.t = function
    | Null it -> vars_in it
    | AddPointer (it, it') -> vars_in_list [it; it']
    | SubPointer (it, it') -> vars_in_list [it; it']
    | MulPointer (it, it') -> vars_in_list [it; it']
    | LTPointer (it, it')  -> vars_in_list [it; it']
    | LEPointer (it, it') -> vars_in_list [it; it']
    | Disjoint ((it,_), (it',_)) -> vars_in_list [it; it']
    | AllocationSize it -> vars_in it
    | IntegerToPointerCast t -> vars_in t
    | PointerToIntegerCast t -> vars_in t
  in

  let ct_pred : 'bt ct_pred -> SymSet.t = function
    | Aligned (_rt, t) -> vars_in t
    | AlignedI (t, t') -> vars_in_list [t; t']
    | MinInteger _ -> SymSet.empty
    | MaxInteger _ -> SymSet.empty
    | Representable (_rt,t) -> vars_in t
  in

  let list_op : 'bt list_op -> SymSet.t = function
    | Nil _  -> SymSet.empty
    | Cons (it, it') -> vars_in_list [it; it']
    | List (its,bt) -> vars_in_list its
    | Head it -> vars_in it
    | Tail it -> vars_in it
    | NthList (_,it) -> vars_in it
  in

  let set_op : 'bt set_op -> SymSet.t = function
    | SetMember (t1,t2) -> vars_in_list [t1;t2]
    | SetUnion ts -> vars_in_list (List1.to_list ts)
    | SetIntersection ts -> vars_in_list (List1.to_list ts)
    | SetDifference (t1, t2) -> vars_in_list [t1;t2]
    | Subset (t1, t2) -> vars_in_list [t1;t2]
  in

  let array_op : 'bt array_op -> SymSet.t = function
    | ConstArray (t,_) -> vars_in t
    | ArrayGet (t1,t2) -> vars_in_list [t1;t2]
    | ArraySet (t1,t2,t3) -> vars_in_list [t1;t2;t3]
    | ArrayEqualOnRange (t1,t2,t3,t4) -> vars_in_list [t1;t2;t3; t4]
    | ArraySelectAfter ((t1, t2), t3) -> vars_in_list [t1; t2; t3]
    | ArrayIndexShiftRight (t1, t2) -> vars_in_list [t1; t2]
  in
  
  function
  | Lit it -> lit it
  | Arith_op it -> arith_op it
  | Cmp_op it -> cmp_op it
  | Bool_op it -> bool_op it
  | Tuple_op it -> tuple_op it
  | Pointer_op it -> pointer_op it
  | CT_pred it -> ct_pred it
  | List_op it -> list_op it
  | Set_op it -> set_op it
  | Array_op it -> array_op it


and vars_in_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (vars_in sym)
    ) SymSet.empty l


let json it : Yojson.Safe.t = `String (Pp.plain (pp it))



let map_sym (type bt) (f : bt * Sym.t -> bt term) =

  let rec aux = 

    let lit = function
      | Sym (bt, symbol) -> f (bt, symbol)
      | it -> Lit it
    in

    let arith_op it = 
      Arith_op 
        begin match it with
        | Add (it, it') -> Add (aux it, aux it')
        | Sub (it, it') -> Sub (aux it, aux it')
        | Mul (it, it') -> Mul (aux it, aux it')
        | Div (it, it') -> Div (aux it, aux it')
        | Exp (it, it') -> Exp (aux it, aux it')
        | Rem_t (it, it') -> Rem_t (aux it, aux it')
        | Rem_f (it, it') -> Rem_f (aux it, aux it')
        | Min (it, it') -> Min (aux it, aux it')
        | Max (it, it') -> Max (aux it, aux it')
        end
    in

    let cmp_op it = 
      Cmp_op 
        begin match it with
        | EQ (it, it') -> EQ (aux it, aux it')
        | NE (it, it') -> NE (aux it, aux it')
        | LT (it, it') -> LT (aux it, aux it')
        | GT (it, it') -> GT (aux it, aux it')
        | LE (it, it') -> LE (aux it, aux it')
        | GE (it, it') -> GE (aux it, aux it')
        end
    in

    let bool_op it = 
      Bool_op 
        begin match it with
        | And its -> And (map (aux) its)
        | Or its -> Or (map (aux) its)
        | Impl (it, it') -> Impl (aux it, aux it')
        | Not it -> Not (aux it)
        | ITE (it,it',it'') -> ITE (aux it, aux it', aux it'')
        end
    in

    let tuple_op it = 
      Tuple_op
        begin match it with
        | Tuple (bt, its) ->
           Tuple (bt, map aux its)
        | NthTuple (bt, n, it') ->
           NthTuple (bt, n, aux it')
        | Struct (tag, members) ->
           let members = map (fun (member,it) -> (member,aux it)) members in
           Struct (tag, members)
        | StructMember (tag, t, f) ->
           StructMember (tag, aux t, f)
        | StructMemberOffset (tag,t,f) ->
           StructMemberOffset (tag,aux t, f)
        end
    in

    let pointer_op it =
      Pointer_op
        begin match it with
        | Null it -> 
           Null (aux it)
        | AllocationSize it -> 
           AllocationSize (aux it)
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
        | Disjoint ((it1,it2), (it1',it2')) -> 
           Disjoint ((aux it1, aux it2), (aux it1', aux it2'))
        | IntegerToPointerCast t -> 
           IntegerToPointerCast (aux t)
        | PointerToIntegerCast t -> 
           PointerToIntegerCast (aux t)
        end
    in

    let ct_pred it =
      CT_pred
        begin match it with
        | Aligned (rt,t) -> Aligned (rt, aux t)
        | AlignedI (t,t') -> AlignedI (aux t, aux t')
        | MinInteger it -> MinInteger it
        | MaxInteger it -> MaxInteger it
        | Representable (rt,t) -> Representable (rt,aux t)
        end
    in

    let list_op it =
      List_op
        begin match it with
        | Nil bt -> Nil bt
        | Cons (it1,it2) -> Cons (aux it1, aux it2)
        | List (its,bt) -> List (map aux its, bt)
        | Head it -> Head (aux it)
        | Tail it -> Tail (aux it)
        | NthList (i, it) -> NthList (i, aux it)
        end
    in

    let set_op it = 
      Set_op 
        begin match it with
        | SetMember (t1,t2) -> SetMember (aux t1, aux t2)
        | SetUnion ts -> SetUnion (List1.map aux ts)
        | SetIntersection ts -> SetIntersection (List1.map aux ts)
        | SetDifference (t1, t2) -> SetDifference (aux t1, aux t2)
        | Subset (t1, t2) -> Subset (aux t1, aux t2)
        end
    in

    let array_op it = 
      Array_op
        begin match it with
        | ConstArray (t, bt) ->
           ConstArray (aux t, bt)
        | ArrayGet (t1, t2) ->
           ArrayGet (aux t1, aux t2)
        | ArraySet (t1, t2, t3) ->
           ArraySet (aux t1, aux t2, aux t3)
        | ArrayEqualOnRange (t1, t2, t3, t4) ->
           ArrayEqualOnRange (aux t1, aux t2, aux t3, aux t4)
        | ArraySelectAfter ((t1,t2),t3) ->
           ArraySelectAfter ((aux t1,aux t2),aux t3)
        | ArrayIndexShiftRight (t1, t2) ->
           ArrayIndexShiftRight (aux t1, aux t2)
        end
    in

    function
    | Lit it -> lit it
    | Arith_op it -> arith_op it
    | Cmp_op it -> cmp_op it
    | Bool_op it -> bool_op it
    | Tuple_op it -> tuple_op it
    | Pointer_op it -> pointer_op it
    | CT_pred it -> ct_pred it
    | List_op it -> list_op it
    | Set_op it -> set_op it
    | Array_op it -> array_op it

  in

  fun it -> aux it


let subst_var (subst : (Sym.t, Sym.t) Subst.t) it =
  map_sym (fun (bt, s) ->
      Lit (Sym (bt, Sym.subst subst s))
    ) it

let subst_vars it = make_substs subst_var it


let subst_it (subst : (Sym.t, 'bt term) Subst.t) it =
  map_sym (fun (bt, s) ->
      if Sym.equal s subst.before 
      then subst.after
      else Lit (Sym (bt, s))
    ) it

let subst_its it = make_substs subst_var it



(* shorthands *)


(* lit *)
let sym_ (bt, sym) = Lit (Sym (bt, sym))
let num_ n = Lit (Num n)
let pointer_ n = Lit (Pointer n)
let bool_ b = Lit (Bool b)
let unit = Lit Unit

let int_ n = num_ (Z.of_int n)


(* arith_op *)
let add_ (it, it') = Arith_op (Add (it, it'))
let sub_ (it, it') = Arith_op (Sub (it, it'))
let mul_ (it, it') = Arith_op (Mul (it, it'))
let div_ (it, it') = Arith_op (Div (it, it'))
let exp_ (it, it') = Arith_op (Exp (it, it'))
let rem_t_ (it, it') = Arith_op (Rem_t (it, it'))
let rem_f_ (it, it') = Arith_op (Rem_f (it, it'))
let min_ (it, it') = Arith_op (Min (it, it'))
let max_ (it, it') = Arith_op (Max (it, it'))

(* cmp_op *)
let eq_ (it, it') = Cmp_op (EQ (it, it'))
let ne_ (it, it') = Cmp_op (NE (it, it'))
let lt_ (it, it') = Cmp_op (LT (it, it'))
let gt_ (it, it') = Cmp_op (GT (it, it'))
let le_ (it, it') = Cmp_op (LE (it, it'))
let ge_ (it, it') = Cmp_op (GE (it, it'))

(* bool_op *)
let and_ its = Bool_op (And its)
let or_ its = Bool_op (Or its)
let impl_ (it, it') = Bool_op (Impl (it, it'))
let not_ it = Bool_op (Not it)
let ite_ (it, it', it'') = Bool_op (ITE (it, it', it''))

(* tuple_op *)
let tuple_ (bts, its) = Tuple_op (Tuple (bts, its))
let nthTuple_ (bt, n, it) = Tuple_op (NthTuple (bt, n, it))
let struct_ (s, members) = Tuple_op (Struct (s, members))
let structMember_ (s, it, member) = Tuple_op (StructMember (s, it, member))
let structMemberOffset_ (s, it, member) = Tuple_op (StructMemberOffset (s, it, member))

(* pointer_op *)
let null_ it = Pointer_op (Null it)
let allocationSize_ it = Pointer_op (AllocationSize it)
let addPointer_ (it, it') = Pointer_op (AddPointer (it, it'))
let subPointer_ (it, it') = Pointer_op (SubPointer (it, it'))
let mulPointer_ (it, it') = Pointer_op (MulPointer (it, it'))
let ltPointer_ (it, it') = Pointer_op (LTPointer (it, it'))
let lePointer_ (it, it') = Pointer_op (LEPointer (it, it'))
let disjoint_ (fp, fp') = Pointer_op (Disjoint (fp, fp'))
let integerToPointerCast_ it = Pointer_op (IntegerToPointerCast it)
let pointerToIntegerCast_ it = Pointer_op (PointerToIntegerCast it)

(* list_op *)
let nil_ bt = List_op (Nil bt)
let cons_ (it, it') = List_op (Cons (it, it'))
let list_ (its, bt) = List_op (List (its, bt))
let head_ it = List_op (Head it)
let tail_ it = List_op (Tail it)
let nthList_ (n, it) = List_op (NthList (n, it))

(* set_op *)
let setMember_ (it, it') = Set_op (SetMember (it, it'))
let setUnion_ its = Set_op (SetUnion its)
let setIntersection_ its = Set_op (SetIntersection its)
let setDifference_ (it, it') = Set_op (SetDifference (it, it'))
let subset_ (it, it') = Set_op (Subset (it, it'))

(* array_op *)
let constArray_ (it, bt) = Array_op (ConstArray (it, bt))
let arrayGet_ (it, it') = Array_op (ArrayGet (it, it'))
let arraySet_ (it, it', it'') = Array_op (ArraySet (it, it', it''))
let arrayEqualOnRange_ (it, it', it'', it''') = Array_op (ArrayEqualOnRange (it, it', it'', it'''))
let arraySelectAfter_ ((it, it'), it'') =  Array_op (ArraySelectAfter ((it, it'), it''))
let arrayIndexShiftRight_ (it, it') = Array_op (ArrayIndexShiftRight (it, it'))

(* ct_pred *)
let minInteger_ t = CT_pred (MinInteger t)
let maxInteger_ t = CT_pred (MaxInteger t)
let representable_ (t, it) = CT_pred (Representable (t, it))
let aligned_ (t, it) = CT_pred (Aligned (t, it))
let alignedI_ (it, it') = CT_pred (AlignedI (it, it'))



let in_range within (min, max) = 
  and_ [le_ (min, within); le_ (within, max)]

let in_footprint within (pointer, size) = 
  and_ [lePointer_ (pointer, within); 
        ltPointer_ (within, addPointer_ (pointer, size))]




let disjoint_from fp fps =
  List.map (fun fp' -> disjoint_ (fp, fp')) fps



let good_pointer_it pointer_it pointee_sct = 
  match pointee_sct with
  | CT.Sctype (_, Void) ->
     representable_ (CT.pointer_sct pointee_sct, pointer_it);
  | _ -> 
     and_ [
         representable_ (CT.pointer_sct pointee_sct, pointer_it);
         aligned_ (pointee_sct, pointer_it);
       ]

let good_pointer pointer pointee_sct = 
  let pointer_it = sym_ (BT.Loc, pointer) in
  good_pointer_it pointer_it pointee_sct


let good_value v sct =
  let v_it = sym_ (BT.of_sct sct, v) in
  match sct with
  | Sctype (_, Pointer (qualifiers, pointee_sct)) ->
     good_pointer v pointee_sct
  | _ ->
     CT_pred (Representable (sct, v_it))



