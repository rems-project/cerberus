open Subst
open List
open Pp
module BT=BaseTypes
module CF=Cerb_frontend

module SymSet = Set.Make(Sym)


module ST = struct

  type t = 
    | ST_Ctype of Sctypes.t
    | ST_Pointer


  let equal rt1 rt2 = 
    match rt1, rt2 with
    | ST_Ctype ct1, ST_Ctype ct2 -> Sctypes.equal ct1 ct2
    | ST_Pointer, ST_Pointer -> true

    | ST_Ctype _, _
    | ST_Pointer, _ -> 
       false

  let pp = function
    | ST_Ctype ct -> Sctypes.pp ct
    | ST_Pointer -> Pp.string "pointer"

  let of_ctype ct = ST_Ctype ct

  let to_bt = function
    | ST_Pointer -> BT.Loc
    | ST_Ctype sct -> BT.of_sct sct

end




type 'bt term =
  (* literals *)
  | S of 'bt * Sym.t
  | Num of Z.t
  | Pointer of Z.t
  | Bool of bool
  | Unit
  (* arithmetic *)
  | Add of 'bt term * 'bt term
  | Sub of 'bt term * 'bt term
  | Mul of 'bt term * 'bt term
  | Div of 'bt term * 'bt term
  | Exp of 'bt term * 'bt term
  | Rem_t of 'bt term * 'bt term
  | Rem_f of 'bt term * 'bt term
  | Min of 'bt term * 'bt term
  | Max of 'bt term * 'bt term
  (* comparisons *)
  | EQ of 'bt term * 'bt term
  | NE of 'bt term * 'bt term
  | LT of 'bt term * 'bt term
  | GT of 'bt term * 'bt term
  | LE of 'bt term * 'bt term
  | GE of 'bt term * 'bt term
  (* booleans *)
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term  (* bool -> int -> int *)
  (* tuples *)
  | Tuple of 'bt term list
  | NthTuple of 'bt * int * 'bt term (* bt is tuple bt *)
  | Struct of BT.tag * (BT.member * 'bt term) list
  | StructMember of BT.tag * 'bt term * BT.member
  | StructMemberOffset of BT.tag * 'bt term * BT.member
  (* pointers *)
  | Null of 'bt term
  | AllocationSize of 'bt term
  | Offset of 'bt term * 'bt term
  | LocLT of 'bt term * 'bt term
  | LocLE of 'bt term * 'bt term
  | Disjoint of ('bt term * 'bt term) * ('bt term * 'bt term)
  | AlignedI of 'bt term * 'bt term
  | Aligned of ST.t * 'bt term
  | IntegerToPointerCast of 'bt term
  | PointerToIntegerCast of 'bt term
  (* representability *)
  | MinInteger of CF.Ctype.integerType
  | MaxInteger of CF.Ctype.integerType
  | Representable of ST.t * 'bt term
  (* lists *)
  | Nil of 'bt
  | Cons of 'bt term * 'bt term
  | List of 'bt term list * 'bt
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of int * 'bt term
  (* sets *)
  | SetMember of 'bt term * 'bt term
  | SetAdd of 'bt term * 'bt term
  | SetRemove of 'bt term * 'bt term
  | SetUnion of ('bt term) List1.t
  | SetIntersection of ('bt term) List1.t
  | SetDifference of 'bt term * 'bt term
  | Subset of 'bt term * 'bt term


type typed = BT.t term
type untyped = unit term

type t = typed


let rec equal it it' = 
  match it, it' with
  (* literals *)
  | S (bt,sym), S (bt',sym') -> 
     let eq = Sym.equal sym sym' in
     if eq && !Debug_ocaml.debug_level >= 1 && not (BT.equal bt bt')
     then Debug_ocaml.error "equal symbols with different base type"
     else eq
  | Num n, Num n' -> 
     Z.equal n n'
  | Pointer p, Pointer p' -> 
     Z.equal p p'
  | Bool b, Bool b' -> 
     b = b'
  | Unit, Unit -> 
     true
  (* arithmetic *)
  | Add (t1,t2), Add (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Sub (t1,t2), Sub (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Mul (t1,t2), Mul (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Div (t1,t2), Div (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Exp (t1,t2), Exp (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Rem_t (t1,t2), Rem_t (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Rem_f (t1,t2), Rem_f (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Min (t1,t2), Min (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | Max (t1,t2), Max (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  (* comparisons *)
  | EQ (t1,t2), EQ (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | NE (t1,t2), NE (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | LT (t1,t2), LT (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | GT (t1,t2), GT (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | LE (t1,t2), LE (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  | GE (t1,t2), GE (t1',t2') -> 
     equal t1 t1' && equal t2 t2' 
  (* booleans *)
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
  (* tuples *)
  | Tuple its, Tuple its' -> 
     List.equal equal its its'
  | NthTuple (bt, n,t), NthTuple (bt', n',t') -> 
     BT.equal bt bt' && n = n' && equal t t' 
  | Struct (tag, members), Struct (tag2, members2) ->
     tag = tag2 && 
       List.equal (fun (m,t) (m',t') -> m = m' && equal t t') 
         members members2
  | StructMember (tag,t,member), StructMember (tag',t',member') ->
     tag = tag' && equal t t' && member = member'
  | StructMemberOffset (tag,t,member), StructMemberOffset (tag',t',member') ->
     tag = tag' && equal t t' && member = member'
  (* pointers *)
  | Null t, Null t' -> 
     equal t t' 
  | AllocationSize t1, AllocationSize t1' -> 
     equal t1 t1'
  | Offset (t1, t2), Offset (t1', t2') -> 
     equal t1 t1' && equal t2 t2'
  | LocLT (t1, t2), LocLT (t1', t2') -> 
     equal t1 t1' && equal t2 t2'
  | LocLE (t1, t2), LocLE (t1', t2') -> 
     equal t1 t1' && equal t2 t2'
  | Disjoint ((t1, s1), (t2, s2)), Disjoint ((t1', s1'), (t2', s2')) -> 
     equal t1 t1' && equal t2 t2' && 
       equal s1 s1' && equal s2 s2'
  | IntegerToPointerCast t1, IntegerToPointerCast t2 -> 
     equal t1 t2
  | PointerToIntegerCast t1, PointerToIntegerCast t2 -> 
     equal t1 t2
  | AlignedI (t1, t2), AlignedI (t1', t2') ->
     equal t1 t1' && equal t2 t2'
  | Aligned (rt, t), Aligned (rt', t') ->
     ST.equal rt rt' && equal t t'
  (* representability *)
  | Representable (rt, t), Representable (rt', t') ->
     ST.equal rt rt' && equal t t'
  | MinInteger it, MinInteger it' ->
     CF.Ctype.integerTypeEqual it it'
  | MaxInteger it, MaxInteger it' ->
     CF.Ctype.integerTypeEqual it it'
  (* lists *)
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
  (* sets *)
  | SetMember (t1,t2), SetMember (t1',t2') ->
     equal t1 t1' && equal t1' t2'
  | SetAdd (t1,t2), SetAdd (t1',t2') ->
     equal t1 t1' && equal t1' t2'
  | SetRemove (t1, t2), SetRemove (t1', t2') ->
     equal t1 t1' && equal t1' t2'
  | SetUnion ts, SetUnion ts' ->
     List1.equal equal ts ts'
  | SetIntersection ts, SetIntersection ts' ->
     List1.equal equal ts ts'
  | SetDifference (t1, t2), SetDifference (t1', t2') ->
     equal t1 t1' && equal t1' t2'
  | Subset (t1, t2), Subset (t1', t2') ->
     equal t1 t1' && equal t1' t2'

  (* literals *)
  | S _, _
  | Num _, _
  | Pointer _, _
  | Bool _, _
  | Unit, _
  (* arithmetic *)
  | Add _, _
  | Sub _, _
  | Mul _, _
  | Div _, _
  | Exp _, _
  | Rem_t _, _
  | Rem_f _, _
  | Min _, _
  | Max _, _
  (* comparisons *)
  | EQ _, _
  | NE _, _
  | LT _, _
  | GT _, _
  | LE _, _
  | GE _, _
  (* booleans *)
  | And _, _
  | Or _, _
  | Impl _, _
  | Not _, _
  | ITE _, _
  (* tuples *)
  | Tuple _, _
  | NthTuple _, _
  | Struct _, _
  | StructMember _, _
  | StructMemberOffset _, _
  (* pointers *)
  | Null _, _
  | AllocationSize _, _
  | Offset _, _
  | LocLT _, _
  | LocLE _, _
  | Disjoint _, _
  | AlignedI _, _
  | Aligned _, _
  | IntegerToPointerCast _, _
  | PointerToIntegerCast _, _
  (* representability *)
  | Representable _, _
  | MinInteger _, _
  | MaxInteger _, _
  (* lists *)
  | Nil _, _
  | Cons _, _
  | List _, _
  | Head _, _
  | Tail _, _
  | NthList _, _
  (* sets *)
  | SetMember _, _
  | SetAdd _, _
  | SetRemove _, _
  | SetUnion _, _
  | SetIntersection _, _
  | SetDifference _, _
  | Subset _, _

    -> false




let pp (type bt) (it : bt term) : PPrint.document = 

  let rec aux atomic it = 
    let mparens pped = if atomic then parens pped else pped in
    match it with
    (* literals *)
    | S (_,sym) -> 
       Sym.pp sym
    | Num i -> 
       Z.pp i
    | Pointer i -> 
       Z.pp i
    | Bool true -> 
       !^"true"
    | Bool false -> 
       !^"false"
    | Unit -> 
       !^"void"
    (* arithmetic *)
    | Add (it1,it2) -> 
       mparens (aux true it1 ^^^ plus ^^^ aux true it2)
    | Sub (it1,it2) -> 
       mparens (aux true it1 ^^^ minus ^^^ aux true it2)
    | Mul (it1,it2) -> 
       mparens (aux true it1 ^^^ star ^^^ aux true it2)
    | Div (it1,it2) -> 
       mparens (aux true it1 ^^^ slash ^^^ aux true it2)
    | Exp (it1,it2) -> 
       mparens (aux true it1 ^^^ caret ^^^ aux true it2)
    | Rem_t (it1,it2) -> 
       mparens (!^ "rem_t" ^^^ aux true it1 ^^^ aux true it2)
    | Rem_f (it1,it2) -> 
       mparens (!^ "rem_f" ^^^ aux true it1 ^^^ aux true it2)
    | Min (it1,it2) -> 
       mparens (!^ "min" ^^^ aux true it1 ^^^ aux true it2)
    | Max (it1,it2) -> 
       mparens (!^ "max" ^^^ aux true it1 ^^^ aux true it2)
    (* comparisons *)
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
    (* booleans *)
    | And o -> 
       Pp.group (mparens (flow_map (space ^^ !^"&&" ^^ space) (aux false) o))
    | Or o -> 
       Pp.group (mparens (flow_map (space ^^ !^"||" ^^ space) (aux false) o))
    | Impl (o1,o2) -> 
       mparens (aux true o1 ^^^ equals ^^ rangle ^^^ aux true o2)
    | Not (o1) -> 
       mparens (!^"not" ^^^ aux true o1)
    | ITE (o1,o2,o3) -> 
       mparens (!^"?" ^^^ parens (separate_map comma (aux false) [o1; o2; o3]))
    (* tuples *)
    | NthTuple (bt,n,it2) -> 
       mparens (aux true it2 ^^ dot ^^ !^(string_of_int n))
    | Tuple its -> 
       braces (separate_map (semi ^^ space) (aux false) its)
    | Struct (_tag, members) ->
       braces (separate_map comma (fun (member,it) -> 
                   Id.pp member ^^^ equals ^^^ aux false it 
                 ) members)
    | StructMember (_tag, t, member) ->
       aux true t ^^ dot ^^ Id.pp member
    | StructMemberOffset (_tag, t, member) ->
       mparens (ampersand ^^ aux true t ^^ !^"->" ^^ Id.pp member)
    (* pointers *)
    | Null o1 -> 
       mparens (!^"null" ^^ parens (aux false o1))
    | AllocationSize t1 ->
       mparens (!^"allocationSize" ^^ parens (aux false t1))
    | Offset (t1, t2) ->
       mparens (!^"offset" ^^ parens (aux false t1 ^^ comma ^^ aux false t2))
    | LocLT (o1,o2) -> 
       mparens (aux true o1 ^^^ langle ^^^ aux true o2)
    | LocLE (o1,o2) -> 
       mparens (aux true o1 ^^^ langle ^^ equals ^^^ aux true o2)
    | Disjoint ((o1,s1),(o2,s2)) ->
       mparens (!^"disjoint" ^^ 
                  parens (
                    parens (aux false o1 ^^ comma ^^ aux false s1) ^^ comma ^^
                      parens (aux false o2 ^^ comma ^^ aux false s2)))

    | AlignedI (t, t') ->
       mparens (!^"aligned" ^^ parens (aux false t ^^ comma ^^ aux false t'))
    | Aligned (rt, t) ->
       mparens (!^"aligned" ^^ parens (ST.pp rt ^^ comma ^^ aux false t))
    | IntegerToPointerCast t ->
       mparens (parens(!^"pointer") ^^ aux true t)
    | PointerToIntegerCast t ->
       mparens (parens(!^"integer") ^^ aux true t)
    (* representability *)
    | MinInteger it ->
       mparens (!^"min" ^^ parens (CF.Pp_core_ctype.pp_integer_ctype it))
    | MaxInteger it ->
       mparens (!^"max" ^^ parens (CF.Pp_core_ctype.pp_integer_ctype it))
    | Representable (rt, t) ->
       mparens (!^"representable" ^^ parens (ST.pp rt ^^ comma ^^ aux false t))
    (* lists *)
    | Head (o1) -> 
       mparens (!^"hd" ^^ parens (aux false o1))
    | Tail (o1) -> 
       mparens (!^"tl" ^^^ parens (aux false o1))
    | Nil _ -> 
       brackets empty
    | Cons (t1,t2) -> 
       mparens (aux true t1 ^^ colon ^^ colon ^^ aux true t2)
    | List (its, _bt) -> 
       mparens (brackets (separate_map comma (aux false) its))
    | NthList (n, t) ->
       mparens (aux true t ^^ brackets !^(string_of_int n))
    (* sets *)
    | SetMember (t1,t2) ->
       mparens (aux false t1 ^^^ !^"IN" ^^^ aux false t2)
    | SetAdd (t1,t2) ->
       mparens (braces (aux false t1) ^^^ !^"union" ^^^ aux false t2)
    | SetRemove (t1, t2) ->
       mparens (aux false t1 ^^^ !^"/" ^^^ braces (aux false t2))
    | SetUnion ts ->
       mparens (!^"union" ^^^ Pp.list (aux false) (List1.to_list ts))
    | SetIntersection ts ->
       mparens (!^"intersection" ^^^ Pp.list (aux false) (List1.to_list ts))
    | SetDifference (t1, t2) ->
       mparens (aux false t1 ^^^ !^"/" ^^^ aux false t2)
    | Subset (t1, t2) ->
       mparens (aux false t1 ^^^ !^"<=" ^^^ aux false t2)
  in
  aux false it


let rec vars_in it : SymSet.t = 
  match it with
  | S (_, symbol) -> SymSet.singleton symbol
  | Num _ -> SymSet.empty
  | Pointer _ -> SymSet.empty
  | Bool _ -> SymSet.empty
  | Unit -> SymSet.empty
  (* arithmetic *)
  | Add (it, it') -> vars_in_list [it; it']
  | Sub (it, it') -> vars_in_list [it; it']
  | Mul (it, it') -> vars_in_list [it; it']
  | Div (it, it') -> vars_in_list [it; it']
  | Exp (it, it') -> vars_in_list [it; it']
  | Rem_t (it, it') -> vars_in_list [it; it']
  | Rem_f (it, it') -> vars_in_list [it; it']
  | Min (it, it') -> vars_in_list [it; it']
  | Max (it, it') -> vars_in_list [it; it']
  (* comparisons *)
  | EQ (it, it') -> vars_in_list [it; it']
  | NE (it, it') -> vars_in_list [it; it']
  | LT (it, it') -> vars_in_list [it; it']
  | GT (it, it') -> vars_in_list [it; it']
  | LE (it, it') -> vars_in_list [it; it']
  | GE (it, it') -> vars_in_list [it; it']
  (* booleans *)
  | And its -> vars_in_list its
  | Or its -> vars_in_list its
  | Impl (it, it') -> vars_in_list [it; it']
  | Not it -> vars_in it
  | ITE (it,it',it'') -> vars_in_list [it;it';it'']
  (* tuples *)
  | Tuple its -> vars_in_list (it :: its)
  | NthTuple (_, _, it) -> vars_in it
  | Struct (_tag, members) -> vars_in_list (map snd members)
  | StructMember (_tag, it, s) -> vars_in_list [it;it]
  | StructMemberOffset (_tag, it, s) -> vars_in_list [it;it]
  (* pointers *)
  | Null it -> vars_in it
  | Offset (it, it') -> vars_in_list [it; it']
  | LocLT (it, it')  -> vars_in_list [it; it']
  | LocLE (it, it') -> vars_in_list [it; it']
  | Disjoint ((it,_), (it',_)) -> vars_in_list [it; it']
  | AllocationSize it -> vars_in it
  | AlignedI (it, it') -> vars_in_list [it;it]
  | Aligned (_rt, t) -> vars_in t
  | IntegerToPointerCast t -> vars_in t
  | PointerToIntegerCast t -> vars_in t
  (* representability *)
  | MinInteger _ -> SymSet.empty
  | MaxInteger _ -> SymSet.empty
  | Representable (_rt,t) -> vars_in t
  (* lists *)
  | Nil _  -> SymSet.empty
  | Cons (it, it') -> vars_in_list [it; it']
  | List (its,bt) -> vars_in_list its
  | Head it -> vars_in it
  | Tail it -> vars_in it
  | NthList (_,it) -> vars_in it
  (* sets *)
  | SetMember (t1,t2) -> vars_in_list [t1;t2]
  | SetAdd (t1,t2) -> vars_in_list [t1;t2]
  | SetRemove (t1, t2) -> vars_in_list [t1;t2]
  | SetUnion ts -> vars_in_list (List1.to_list ts)
  | SetIntersection ts -> vars_in_list (List1.to_list ts)
  | SetDifference (t1, t2) -> vars_in_list [t1;t2]
  | Subset (t1, t2) -> vars_in_list [t1;t2]

and vars_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (vars_in sym))
    SymSet.empty l


let json it : Yojson.Safe.t =
  `String (Pp.plain (pp it))



let map_sym f it : t = 
  let rec aux it = 
    match it with
    (* literals *)
    | S (bt, symbol) -> f (bt, symbol)
    | Num _ -> it
    | Pointer _ -> it
    | Bool _ -> it
    | Unit -> it
    (* arithmetic *)
    | Add (it, it') -> Add (aux it, aux it')
    | Sub (it, it') -> Sub (aux it, aux it')
    | Mul (it, it') -> Mul (aux it, aux it')
    | Div (it, it') -> Div (aux it, aux it')
    | Exp (it, it') -> Exp (aux it, aux it')
    | Rem_t (it, it') -> Rem_t (aux it, aux it')
    | Rem_f (it, it') -> Rem_f (aux it, aux it')
    | Min (it, it') -> Min (aux it, aux it')
    | Max (it, it') -> Max (aux it, aux it')
    (* comparisons *)
    | EQ (it, it') -> EQ (aux it, aux it')
    | NE (it, it') -> NE (aux it, aux it')
    | LT (it, it') -> LT (aux it, aux it')
    | GT (it, it') -> GT (aux it, aux it')
    | LE (it, it') -> LE (aux it, aux it')
    | GE (it, it') -> GE (aux it, aux it')
    (* booleans *)
    | And its -> And (map (aux) its)
    | Or its -> Or (map (aux) its)
    | Impl (it, it') -> Impl (aux it, aux it')
    | Not it -> Not (aux it)
    | ITE (it,it',it'') -> 
       ITE (aux it, aux it', aux it'')
    (* tuples *)
    | Tuple its ->
       Tuple (map (fun it -> aux it) its)
    | NthTuple (bt, n, it') ->
       NthTuple (bt, n, aux it')
    | Struct (tag, members) ->
       let members = map (fun (member,it) -> (member,aux it)) members in
       Struct (tag, members)
    | StructMember (tag, t, f) ->
       StructMember (tag, aux t, f)
    | StructMemberOffset (tag,t,f) ->
       StructMemberOffset (tag,aux t, f)
    (* pointers *)
    | Null it -> Null (aux it)
    | AllocationSize it -> AllocationSize (aux it)
    | Offset (it, it') -> Offset (aux it, aux it')
    | LocLT (it, it') -> LocLT (aux it, aux it')
    | LocLE (it, it') -> LocLE (aux it, aux it')
    | Disjoint ((it1,it2), (it1',it2')) -> 
       Disjoint ((aux it1, aux it2), (aux it1', aux it2'))
    | AlignedI (it,it') -> AlignedI (aux it, aux it')
    | Aligned (rt,t) -> Aligned (rt, aux t)
    | IntegerToPointerCast t -> IntegerToPointerCast (aux t)
    | PointerToIntegerCast t -> PointerToIntegerCast (aux t)
    (* representability *)
    | MinInteger it -> MinInteger it
    | MaxInteger it -> MaxInteger it
    | Representable (rt,t) -> Representable (rt,aux t)
    (* lists *)
    | Nil _ -> it
    | Cons (it1,it2) -> Cons (aux it1, aux it2)
    | List (its,bt) -> 
       List (map (fun it -> aux it) its, bt)
    | Head it ->
       Head (aux it)
    | Tail it ->
       Tail (aux it)
    | NthList (i, it) ->
       NthList (i, aux it)
    (* sets *)
    | SetMember (t1,t2) ->
       SetMember (aux t1, aux t2)
    | SetAdd (t1,t2) ->
       SetAdd (aux t1, aux t2)
    | SetRemove (t1, t2) ->
       SetRemove (aux t1, aux t2)
    | SetUnion ts ->
       SetUnion (List1.map (aux) ts)
    | SetIntersection ts ->
       SetIntersection (List1.map (aux) ts)
    | SetDifference (t1, t2) ->
       SetDifference (aux t1, aux t2)
    | Subset (t1, t2) ->
       Subset (aux t1, aux t2)
  in
  aux it


let subst_var (subst : (Sym.t, Sym.t) Subst.t) it =
  map_sym (fun (bt, s) ->
      S (bt, Sym.subst subst s)
    ) it

let subst_vars = make_substs subst_var


let subst_it (subst : (Sym.t, 'bt term) Subst.t) it =
  map_sym (fun (bt, s) ->
      if Sym.equal s subst.before 
      then subst.after
      else S (bt, s)
    ) it

let subst_its = make_substs subst_var




let (%+) t1 t2 = Add (t1,t2)
let (%-) t1 t2 = Sub (t1,t2)
let (%*) t1 t2 = Mul (t1,t2)
let (%/) t1 t2 = Div (t1,t2)
let (%^) t1 t2 = Exp (t1,t2)

let (%=) t1 t2 = EQ (t1, t2)
let (%!=) t1 t2 = NE (t1, t2)
let (%<) t1 t2 = LT (t1, t2)
let (%>) t1 t2 = GT (t1, t2)
let (%<=) t1 t2 = LE (t1, t2)
let (%>=) t1 t2 = GE (t1, t2)



let in_range within (min, max) = And [LE (min, within); LE (within, max)]


let int x = Num (Z.of_int x)



let disjoint_from fp fps =
  And (List.map (fun fp' -> Disjoint (fp, fp')) fps)



let good_pointer_it pointer_it pointee_sct = 
  match pointee_sct with
  | Sctypes.Sctype (_, Void) ->
     Representable (ST_Ctype (Sctypes.pointer_sct pointee_sct), pointer_it);
  | _ -> 
     And [
         Representable (ST_Ctype (Sctypes.pointer_sct pointee_sct), pointer_it);
         Aligned (ST_Ctype pointee_sct, pointer_it);
       ]

let good_pointer pointer pointee_sct = 
  let pointer_it = S (BT.Loc, pointer) in
  good_pointer_it pointer_it pointee_sct


let good_value v sct =
  let v_it = S (BT.of_sct sct, v) in
  match sct with
  | Sctype (_, Pointer (qualifiers, pointee_sct)) ->
     good_pointer v pointee_sct
  | _ ->
     Representable (ST_Ctype sct, v_it)
