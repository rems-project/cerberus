open Subst
open List
open Pp
module Loc=Locations
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
  | S of Sym.t
  | Num of Z.t
  | Pointer of Z.t
  | Bool of bool
  | Unit

  | Add of 'bt term * 'bt term
  | Sub of 'bt term * 'bt term
  | Mul of 'bt term * 'bt term
  | Div of 'bt term * 'bt term
  | Exp of 'bt term * 'bt term
  | Rem_t of 'bt term * 'bt term
  | Rem_f of 'bt term * 'bt term
  | Min of 'bt term * 'bt term
  | Max of 'bt term * 'bt term

  | EQ of 'bt term * 'bt term
  | NE of 'bt term * 'bt term
  | LT of 'bt term * 'bt term
  | GT of 'bt term * 'bt term
  | LE of 'bt term * 'bt term
  | GE of 'bt term * 'bt term

  | Null of 'bt term
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term  (* bool -> int -> int *)

  | Tuple of 'bt term list
  | Nth of 'bt * int * 'bt term (* bt is tuple bt *)

  | AllocationSize of 'bt term
  | Offset of 'bt term * 'bt term
  | LocLT of 'bt term * 'bt term
  | LocLE of 'bt term * 'bt term
  | Disjoint of ('bt term * Z.t) * ('bt term * Z.t)
  | AlignedI of 'bt term * 'bt term
  | Aligned of ST.t * 'bt term

  | Representable of ST.t * 'bt term

  | Struct of BT.tag * (BT.member * 'bt term) list
  | StructMember of BT.tag * 'bt term * BT.member
  | StructMemberOffset of BT.tag * 'bt term * BT.member

  | Nil of 'bt
  | Cons of 'bt term * 'bt term
  | List of 'bt term list * 'bt
  | Head of 'bt term
  | Tail of 'bt term

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
  | S sym, S sym' -> Sym.equal sym sym'
  | Num n, Num n' -> Z.equal n n'
  | Pointer p, Pointer p' -> Z.equal p p'
  | Bool b, Bool b' -> b = b'
  | Unit, Unit -> true

  | Add (t1,t2), Add (t1',t2')
  | Sub (t1,t2), Sub (t1',t2')
  | Mul (t1,t2), Mul (t1',t2')
  | Div (t1,t2), Div (t1',t2')
  | Exp (t1,t2), Exp (t1',t2')
  | Rem_t (t1,t2), Rem_t (t1',t2')
  | Rem_f (t1,t2), Rem_f (t1',t2') 
  | Min (t1,t2), Min (t1',t2')
  | Max (t1,t2), Max (t1',t2') 
    -> equal t1 t1' && equal t2 t2' 

  | EQ (t1,t2), EQ (t1',t2')
  | NE (t1,t2), NE (t1',t2')
  | LT (t1,t2), LT (t1',t2')
  | GT (t1,t2), GT (t1',t2')
  | LE (t1,t2), LE (t1',t2')
  | GE (t1,t2), GE (t1',t2') 
    -> equal t1 t1' && equal t2 t2' 

  | Null t, Null t' -> equal t t' 
  | And ts, And ts' -> List.equal equal ts ts'
  | Or ts, Or ts' -> List.equal equal ts ts'
  | Impl (t1,t2), Impl (t1',t2') -> equal t1 t1' && equal t2 t2' 
  | Not t, Not t' -> equal t t' 
  | ITE (t1,t2,t3), ITE (t1',t2',t3') -> 
     equal t1 t1' && equal t2 t2' && equal t3 t3'

  | Tuple its, Tuple its' -> List.equal equal its its'
  | Nth (bt, n,t), Nth (bt', n',t') -> BT.equal bt bt' && n = n' && equal t t' 


  | AllocationSize t1, AllocationSize t1' -> equal t1 t1'
  | Offset (t1, t2), Offset (t1', t2') -> equal t1 t1' && equal t2 t2'
  | LocLT (t1, t2), LocLT (t1', t2') -> equal t1 t1' && equal t2 t2'
  | LocLE (t1, t2), LocLE (t1', t2') ->equal t1 t1' && equal t2 t2'
  | Disjoint ((t1, s1), (t2, s2)), Disjoint ((t1', s1'), (t2', s2')) -> 
     equal t1 t1' && equal t2 t2' && Z.equal s1 s1' && Z.equal s2 s2'

  | Struct (tag, members), Struct (tag2, members2) ->
     tag = tag2 && 
       List.equal (fun (m,t) (m',t') -> m = m' && equal t t') 
         members members2
  | StructMember (tag,t,member), StructMember (tag',t',member')
  | StructMemberOffset (tag,t,member), StructMemberOffset (tag',t',member') 
    -> tag = tag' && equal t t' && member = member'

  | Nil bt, Nil bt' 
    -> BT.equal bt bt'
  | Cons (t1,t2), Cons (t1',t2') 
    -> equal t1 t1' && equal t2 t2'
  | List (its,bt), List (its',bt') 
    -> List.equal equal its its' && BT.equal bt bt'
  | Head t, Head t'
  | Tail t, Tail t'
    -> equal t t'

  | AlignedI (t1, t2), AlignedI (t1', t2') ->
     equal t1 t1' && equal t2 t2'

  | Aligned (rt, t), Aligned (rt', t')
  | Representable (rt, t), Representable (rt', t') ->
     ST.equal rt rt' && equal t t'

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


  | Num _, _
  | Pointer _, _
  | Bool _, _
  | Unit, _

  | Add _, _
  | Sub _, _
  | Mul _, _
  | Div _, _
  | Exp _, _
  | Rem_t _, _
  | Rem_f _, _
  | Min _, _
  | Max _, _

  | EQ _, _
  | NE _, _
  | LT _, _
  | GT _, _
  | LE _, _
  | GE _, _

  | Null _, _
  | And _, _
  | Or _, _
  | Impl _, _
  | Not _, _
  | ITE _, _

  | Tuple _, _
  | Nth _, _

  | AllocationSize _, _
  | Offset _, _
  | LocLT _, _
  | LocLE _, _
  | Disjoint _, _
  | AlignedI _, _
  | Aligned _, _

  | Representable _, _

  | Struct _, _
  | StructMember _, _
  | StructMemberOffset _, _

  | Nil _, _
  | Cons _, _
  | List _, _
  | Head _, _
  | Tail _, _

  | SetMember _, _
  | SetAdd _, _
  | SetRemove _, _
  | SetUnion _, _
  | SetIntersection _, _
  | SetDifference _, _
  | Subset _, _

  | S _, _ ->

     false




let pp (type bt) (it : bt term) : PPrint.document = 

  let rec aux atomic it = 
    let mparens pped = if atomic then parens pped else pped in
    match it with
    | Num i -> 
       Z.pp i
    | Pointer i -> 
       Z.pp i
    | Bool true -> 
       !^"true"
    | Bool false -> 
       !^"false"
    | Unit -> 
       !^"()"

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

    | EQ (o1,o2) -> 
       mparens (aux true o1 ^^^ equals ^^ equals ^^^ aux true o2)
    | NE (o1,o2) -> 
       if !unicode then mparens (aux true o1 ^^^ utf8string "\u{2260}" ^^^ aux true o2)
       else mparens (aux true o1 ^^^ langle ^^ rangle ^^^ aux true o2)
    | LT (o1,o2) -> 
       mparens (aux true o1 ^^^ langle ^^^ aux true o2)
    | GT (o1,o2) -> 
       mparens (aux true o1 ^^^ rangle ^^^ aux true o2)
    | LE (o1,o2) -> 
       if !unicode then mparens (aux true o1 ^^^ utf8string "\u{2264}"  ^^^ aux true o2)
       else mparens (aux true o1 ^^^ langle ^^ equals ^^^ aux true o2)
    | GE (o1,o2) -> 
       if !unicode then mparens (aux true o1 ^^^ utf8string "\u{2265}"  ^^^ aux true o2)
       else mparens (aux true o1 ^^^ rangle ^^ equals ^^^ aux true o2)

    | Null o1 -> 
       mparens (!^"null" ^^ parens (aux false o1))
    | And o -> 
       mparens (!^"and" ^^^ brackets (separate_map comma (aux false) o))
    | Or o -> 
       mparens (!^"or" ^^^ brackets (separate_map comma (aux false) o))
    | Impl (o1,o2) -> 
       mparens (aux true o1 ^^^ equals ^^ rangle ^^^ aux true o2)
    | Not (o1) -> 
       mparens (!^"not" ^^^ aux true o1)
    | ITE (o1,o2,o3) -> 
       mparens (!^"?" ^^^ parens (separate_map comma (aux false) [o1; o2; o3]))

    | Nth (bt,n,it2) -> 
       mparens (aux true it2 ^^ dot ^^ !^(string_of_int n))
    | Head (o1) -> 
       mparens (!^"hd" ^^ parens (aux false o1))
    | Tail (o1) -> 
       mparens (!^"tl" ^^^ parens (aux false o1))

    | Tuple its -> 
       braces (separate_map (semi ^^ space) (aux false) its)
    | Nil _ -> 
       brackets empty
    | Cons (t1,t2) -> 
       mparens (aux true t1 ^^ colon ^^ colon ^^ aux true t2)
    | List (its, _bt) -> 
       mparens (brackets (separate_map comma (aux false) its))

    | Struct (_tag, members) ->
       braces (separate_map comma (fun (member,it) -> 
                   Id.pp member ^^^ equals ^^^ aux false it 
                 ) members)
    | StructMember (_tag, t, member) ->
       aux true t ^^ dot ^^ Id.pp member
    | StructMemberOffset (_tag, t, member) ->
       mparens (ampersand ^^ aux true t ^^ !^"->" ^^ Id.pp member)

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
                    parens (aux false o1 ^^ comma ^^ Z.pp s1) ^^ comma ^^
                      parens (aux false o2 ^^ comma ^^ Z.pp s2)))

    | AlignedI (t, t') ->
       mparens (!^"aligned" ^^ parens (aux false t ^^ comma ^^ aux false t'))
    | Aligned (rt, t) ->
       mparens (!^"aligned" ^^ parens (ST.pp rt ^^ comma ^^ aux false t))
    | Representable (rt, t) ->
       mparens (!^"representable" ^^ parens (ST.pp rt ^^ comma ^^ aux false t))

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


    | S sym -> 
       Sym.pp sym
  in
  aux false it


let rec vars_in it : SymSet.t = 
  match it with
  | Num _  
  | Pointer _
  | Bool _
  | Nil _ 
  | Unit ->
     SymSet.empty
  | Add (it, it')
  | Sub (it, it') 
  | Mul (it, it') 
  | Div (it, it') 
  | Exp (it, it') 
  | Rem_t (it, it') 
  | Rem_f (it, it')
  | Min (it, it') 
  | Max (it, it')
  | EQ (it, it') 
  | NE (it, it') 
  | LT (it, it') 
  | GT (it, it') 
  | LE (it, it') 
  | GE (it, it')
  | Impl (it, it')
  | Cons (it, it')
  | Offset (it, it')
  | LocLT (it, it') 
  | LocLE (it, it')
  | Disjoint ((it,_), (it',_))  ->
     vars_in_list [it; it']
  | And its
  | Or its ->
     vars_in_list its
  | Nth (_, _, it)
  | Null it
  | Not it 
  | Head it
  | Tail it
  | AllocationSize it
    -> 
     vars_in it
  | ITE (it,it',it'') ->
     vars_in_list [it;it';it'']
  | Tuple its -> 
     vars_in_list (it :: its)
  | Struct (_tag, members) ->
     vars_in_list (map snd members)
  | StructMember (_tag, it, s)
  | StructMemberOffset (_tag, it, s) -> 
     vars_in_list [it;it]
  | List (its,bt) ->
     vars_in_list its
  | AlignedI (it, it') ->
     vars_in_list [it;it]
  | Aligned (_rt, t)
  | Representable (_rt,t) ->
     vars_in t

  | SetMember (t1,t2) ->
     vars_in_list [t1;t2]
  | SetAdd (t1,t2) ->
     vars_in_list [t1;t2]
  | SetRemove (t1, t2) ->
     vars_in_list [t1;t2]
  | SetUnion ts ->
     vars_in_list (List1.to_list ts)
  | SetIntersection ts ->
     vars_in_list (List1.to_list ts)
  | SetDifference (t1, t2) ->
     vars_in_list [t1;t2]
  | Subset (t1, t2) ->
     vars_in_list [t1;t2]

  | S symbol -> 
     SymSet.singleton symbol

and vars_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (vars_in sym))
    SymSet.empty l


let json it : Yojson.Safe.t =
  `String (Pp.plain (pp it))



let rec subst_var subst it : t = 
  match it with
  | Num _ -> it
  | Pointer _ -> it
  | Bool _ -> it
  | Unit -> it
  | Add (it, it') -> Add (subst_var subst it, subst_var subst it')
  | Sub (it, it') -> Sub (subst_var subst it, subst_var subst it')
  | Mul (it, it') -> Mul (subst_var subst it, subst_var subst it')
  | Div (it, it') -> Div (subst_var subst it, subst_var subst it')
  | Exp (it, it') -> Exp (subst_var subst it, subst_var subst it')
  | Rem_t (it, it') -> Rem_t (subst_var subst it, subst_var subst it')
  | Rem_f (it, it') -> Rem_f (subst_var subst it, subst_var subst it')
  | Min (it, it') -> Min (subst_var subst it, subst_var subst it')
  | Max (it, it') -> Max (subst_var subst it, subst_var subst it')
  | EQ (it, it') -> EQ (subst_var subst it, subst_var subst it')
  | NE (it, it') -> NE (subst_var subst it, subst_var subst it')
  | LT (it, it') -> LT (subst_var subst it, subst_var subst it')
  | GT (it, it') -> GT (subst_var subst it, subst_var subst it')
  | LE (it, it') -> LE (subst_var subst it, subst_var subst it')
  | GE (it, it') -> GE (subst_var subst it, subst_var subst it')
  | Null it -> Null (subst_var subst it)
  | And its -> And (map (subst_var subst) its)
  | Or its -> Or (map (subst_var subst) its)
  | Impl (it, it') -> Impl (subst_var subst it, subst_var subst it')
  | Not it -> Not (subst_var subst it)
  | ITE (it,it',it'') -> 
     ITE (subst_var subst it, subst_var subst it', subst_var subst it'')
  | Tuple its ->
     Tuple (map (fun it -> subst_var subst it) its)
  | Nth (bt, n, it') ->
     Nth (bt, n, subst_var subst it')
  | Nil _ -> it
  | Cons (it1,it2) -> Cons (subst_var subst it1, subst_var subst it2)
  | List (its,bt) -> 
     List (map (fun it -> subst_var subst it) its, bt)
  | Head it ->
     Head (subst_var subst it)
  | Tail it ->
     Tail (subst_var subst it)
  | Struct (tag, members) ->
     let members = map (fun (member,it) -> (member,subst_var subst it)) members in
     Struct (tag, members)
  | StructMember (tag, t, f) ->
     StructMember (tag, subst_var subst t, f)
  | StructMemberOffset (tag,t,f) ->
     StructMemberOffset (tag,subst_var subst t, f)
  | AllocationSize it -> AllocationSize (subst_var subst it)
  | Offset (it, it') -> Offset (subst_var subst it, subst_var subst it')
  | LocLT (it, it') -> LocLT (subst_var subst it, subst_var subst it')
  | LocLE (it, it') -> LocLE (subst_var subst it, subst_var subst it')
  | Disjoint ((it,s), (it',s')) -> 
     Disjoint ((subst_var subst it,s), (subst_var subst it',s'))
  | AlignedI (it,it') -> AlignedI (subst_var subst it, subst_var subst it')
  | Aligned (rt,t) -> Aligned (rt, subst_var subst t)
  | Representable (rt,t) -> Representable (rt,subst_var subst t)

  | SetMember (t1,t2) ->
     SetMember (subst_var subst t1, subst_var subst t2)
  | SetAdd (t1,t2) ->
     SetAdd (subst_var subst t1, subst_var subst t2)
  | SetRemove (t1, t2) ->
     SetRemove (subst_var subst t1, subst_var subst t2)
  | SetUnion ts ->
     SetUnion (List1.map (subst_var subst) ts)
  | SetIntersection ts ->
     SetIntersection (List1.map (subst_var subst) ts)
  | SetDifference (t1, t2) ->
     SetDifference (subst_var subst t1, subst_var subst t2)
  | Subset (t1, t2) ->
     Subset (subst_var subst t1, subst_var subst t2)

  | S symbol -> 
     if symbol = subst.before then S subst.after else S symbol


let subst_vars = make_substs subst_var



let rec subst_it subst it : t = 
  match it with
  | Num _ -> it
  | Pointer _ -> it
  | Bool _ -> it
  | Unit -> it
  | Add (it, it') -> Add (subst_it subst it, subst_it subst it')
  | Sub (it, it') -> Sub (subst_it subst it, subst_it subst it')
  | Mul (it, it') -> Mul (subst_it subst it, subst_it subst it')
  | Div (it, it') -> Div (subst_it subst it, subst_it subst it')
  | Exp (it, it') -> Exp (subst_it subst it, subst_it subst it')
  | Rem_t (it, it') -> Rem_t (subst_it subst it, subst_it subst it')
  | Rem_f (it, it') -> Rem_f (subst_it subst it, subst_it subst it')
  | Min (it, it') -> Min (subst_it subst it, subst_it subst it')
  | Max (it, it') -> Max (subst_it subst it, subst_it subst it')
  | EQ (it, it') -> EQ (subst_it subst it, subst_it subst it')
  | NE (it, it') -> NE (subst_it subst it, subst_it subst it')
  | LT (it, it') -> LT (subst_it subst it, subst_it subst it')
  | GT (it, it') -> GT (subst_it subst it, subst_it subst it')
  | LE (it, it') -> LE (subst_it subst it, subst_it subst it')
  | GE (it, it') -> GE (subst_it subst it, subst_it subst it')
  | Null it -> Null (subst_it subst it)
  | And its -> And (map (subst_it subst) its)
  | Or its -> Or (map (subst_it subst) its)
  | Impl (it, it') -> Impl (subst_it subst it, subst_it subst it')
  | Not it -> Not (subst_it subst it)
  | ITE (it,it',it'') -> 
     ITE (subst_it subst it, subst_it subst it', subst_it subst it'')
  | Tuple its ->
     Tuple (map (fun it -> subst_it subst it) its)
  | Nth (bt, n, it') ->
     Nth (bt, n, subst_it subst it')
  | Nil _ -> it
  | Cons (it1,it2) -> Cons (subst_it subst it1, subst_it subst it2)
  | List (its,bt) -> 
     List (map (fun it -> subst_it subst it) its, bt)
  | Head it ->
     Head (subst_it subst it)
  | Tail it ->
     Tail (subst_it subst it)
  | Struct (tag, members) ->
     let members = map (fun (member,it) -> (member,subst_it subst it)) members in
     Struct (tag, members)
  | StructMember (tag, t, f) ->
     StructMember (tag, subst_it subst t, f)
  | StructMemberOffset (tag,t,f) ->
     StructMemberOffset (tag,subst_it subst t, f)
  | AllocationSize it -> AllocationSize (subst_it subst it)
  | Offset (it, it') -> Offset (subst_it subst it, subst_it subst it')
  | LocLT (it, it') -> LocLT (subst_it subst it, subst_it subst it')
  | LocLE (it, it') -> LocLE (subst_it subst it, subst_it subst it')
  | Disjoint ((it,s), (it',s')) -> 
     Disjoint ((subst_it subst it,s), (subst_it subst it',s'))
  | AlignedI (it,it') -> AlignedI (subst_it subst it, subst_it subst it')
  | Aligned (rt,t) -> Aligned (rt,subst_it subst t)
  | Representable (rt,t) -> Representable (rt,subst_it subst t)
  | SetMember (t1,t2) ->
     SetMember (subst_it subst t1, subst_it subst t2)
  | SetAdd (t1,t2) ->
     SetAdd (subst_it subst t1, subst_it subst t2)
  | SetRemove (t1, t2) ->
     SetRemove (subst_it subst t1, subst_it subst t2)
  | SetUnion ts ->
     SetUnion (List1.map (subst_it subst) ts)
  | SetIntersection ts ->
     SetIntersection (List1.map (subst_it subst) ts)
  | SetDifference (t1, t2) ->
     SetDifference (subst_it subst t1, subst_it subst t2)
  | Subset (t1, t2) ->
     Subset (subst_it subst t1, subst_it subst t2)  
  | S symbol -> 
     if symbol = subst.before then subst.after else S symbol


(* let rec unify it it' (res : (t Uni.t) SymMap.t) = 
 *   match it, it' with
 *   | Num n, Num n' when n = n' -> return res
 *   | Bool b, Bool b' when b = b' -> return res
 * 
 *   | Add (it1, it2), Add (it1', it2')
 *   | Sub (it1, it2), Sub (it1', it2')
 *   | Mul (it1, it2), Mul (it1', it2')
 *   | Div (it1, it2), Div (it1', it2')
 *   | Exp (it1, it2), Exp (it1', it2')
 *   | Rem_t (it1, it2), Rem_t (it1', it2')
 *   | Rem_f (it1, it2), Rem_f (it1', it2')
 *   | Min (it1, it2), Min (it1', it2')
 *   | Max (it1, it2), Max (it1', it2')
 * 
 *   | EQ (it1, it2), EQ (it1', it2')
 *   | NE (it1, it2), NE (it1', it2')
 *   | LT (it1, it2), LT (it1', it2')
 *   | GT (it1, it2), GT (it1', it2')
 *   | LE (it1, it2), LE (it1', it2')
 *   | GE (it1, it2), GE (it1', it2')
 *     ->
 *      let* res = unify it1 it1' res in
 *      unify it2 it2' res
 * 
 * 
 *   | And its, And its'
 *   | Or its, Or its' 
 *     ->
 *      unify_list its its' res
 * 
 *   | Null it, Null it'
 *   | Not it, Not it' 
 *   | Head it, Head it' 
 *   | Tail it, Tail it' 
 *     -> 
 *      unify it it' res
 *   | ITE (it1,it2,it3), ITE (it1',it2',it3') ->
 *      unify_list [it1;it2;it3] [it1';it2';it3'] res
 * 
 *   | Tuple its, Tuple its' ->
 *      unify_list (it::its) (it'::its') res
 *   | Nth (bt, n, it2), Nth (bt', n', it2') when BT.equal bt bt' && n = n'
 *     -> 
 *      unify it it' res
 * 
 *   | List (its,bt), List (its',bt') when BT.equal bt bt' ->
 *      unify_list its its' res
 * 
 *   | Struct (tag, members), Struct (tag', members') 
 *        when tag = tag' ->
 *      let rec aux members members' res = 
 *        match members, members' with
 *        | [], [] -> return res
 *        | (BT.Member m, it)::members, (BT.Member m', it')::members' 
 *             when m = m' ->
 *           let* res = unify it it' res in
 *           aux members members' res
 *        | _ -> fail
 *      in
 *      aux members members' res
 * 
 *   | Member (tag, t, m), Member (tag', t', m') 
 *   | MemberOffset (tag, t, m), MemberOffset (tag', t', m') 
 *        when tag = tag' && m = m' ->
 *      unify t t' res
 * 
 *   | S sym, it' ->
 *      if S sym = it' then Some res else
 *        let* uni = SymMap.find_opt sym res in
 *        begin match uni.resolved with
 *        | Some s when s = it' -> return res 
 *        | Some s -> fail
 *        | None -> return (SymMap.add sym (Uni.{resolved = Some it'}) res)
 *        end
 * 
 *   | _, _ ->
 *      fail
 * 
 * and unify_list its its' res =
 *   match its, its' with
 *   | [], [] -> return res
 *   | (it :: its), (it' :: its') ->
 *      let* res = unify it it' res in
 *      unify_list its its' res
 *   | _, _ ->
 *      fail *)




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

(* for some reason ocaml wants the 'type id' and the 'unit' *)
let min_u32 (type bt) () : bt term = Num Z.zero
let max_u32 (type bt) () : bt term = Num (Z.sub (Z.power_int_positive_int 2 32) (Z.of_int 1))
let min_u64 (type bt) () : bt term = Num Z.zero
let max_u64 (type bt) () : bt term = Num (Z.sub (Z.power_int_positive_int 2 64) (Z.of_int 1))

let min_i32 (type bt) () : bt term = Num (Z.sub (Z.of_int 0) (Z.power_int_positive_int 2 (32 - 1)))
let max_i32 (type bt) () : bt term = Num (Z.sub (Z.power_int_positive_int 2 (32 - 1)) (Z.of_int 1))
let min_i64 (type bt) () : bt term = Num (Z.sub (Z.of_int 0) (Z.power_int_positive_int 2 (64 - 1)))
let max_i64 (type bt) () : bt term = Num (Z.sub (Z.power_int_positive_int 2 (64 - 1)) (Z.of_int 1))

let int x = Num (Z.of_int x)



