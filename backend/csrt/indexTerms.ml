open Subst
open List
open Pp
module Loc=Locations
module BT=BaseTypes
module CF=Cerb_frontend

module SymSet = Set.Make(Sym)





type stored_type = 
  | ST_Integer of CF.Ctype.integerType
  | ST_Struct of BT.tag
  | ST_Pointer
(* others later *)



let st_to_bt = function
  | ST_Integer _ -> BT.Integer
  | ST_Struct tag -> BT.Struct tag
  | ST_Pointer -> BT.Loc


let stored_type_equal rt1 rt2 = 
  match rt1, rt2 with
  | ST_Integer it1, ST_Integer it2 -> CF.Ctype.integerTypeEqual it1 it2
  | ST_Struct tag1, ST_Struct tag2 -> BT.tag_equal tag1 tag2
  | ST_Pointer, ST_Pointer -> true

  | ST_Integer _, _
  | ST_Struct _, _
  | ST_Pointer, _ -> 
     false


let pp_stored_type = function
  | ST_Integer it -> squotes (CF.Pp_core_ctype.pp_integer_ctype it)
  | ST_Struct (Tag tag) -> squotes (CF.Pp_core_ctype.pp_ctype (Ctype ([], Struct tag)))
  | ST_Pointer -> squotes (BT.pp false BT.Loc)




type 'id term =
  | Num of Z.t
  | Pointer of Z.t
  | Bool of bool
  | Unit

  | Add of 'id term * 'id term
  | Sub of 'id term * 'id term
  | Mul of 'id term * 'id term
  | Div of 'id term * 'id term
  | Exp of 'id term * 'id term
  | Rem_t of 'id term * 'id term
  | Rem_f of 'id term * 'id term
  | Min of 'id term * 'id term
  | Max of 'id term * 'id term

  | EQ of 'id term * 'id term
  | NE of 'id term * 'id term
  | LT of 'id term * 'id term
  | GT of 'id term * 'id term
  | LE of 'id term * 'id term
  | GE of 'id term * 'id term

  | Null of 'id term
  | And of 'id term list
  | Or of 'id term list
  | Impl of 'id term * 'id term
  | Not of 'id term
  | ITE of 'id term * 'id term * 'id term  (* bool -> int -> int *)

  | Tuple of 'id term list
  | Nth of BT.t * int * 'id term

  | Offset of 'id term * 'id term
  | LocLT of 'id term * 'id term
  | LocLE of 'id term * 'id term
  | Disjoint of ('id term * Z.t) * ('id term * Z.t)

  | Struct of BT.tag * (BT.member * 'id term) list
  | Member of BT.tag * 'id term * BT.member
  | MemberOffset of BT.tag * 'id term * BT.member

  | Nil of BT.t
  | Cons of 'id term * 'id term
  | List of 'id term list * BT.t
  | Head of 'id term
  | Tail of 'id term

  | AlignedI of 'id term * 'id term
  | Aligned of stored_type * 'id term
  | InRange of stored_type * 'id term

  | S of 'id


type parse_ast = string term
type t = Sym.t term





let rec equal it it' = 
  match it, it' with
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


  | Offset (t1, t2), Offset (t1', t2') -> equal t1 t1' && equal t2 t2'
  | LocLT (t1, t2), LocLT (t1', t2') -> equal t1 t1' && equal t2 t2'
  | LocLE (t1, t2), LocLE (t1', t2') -> equal t1 t1' && equal t2 t2'
  | Disjoint ((t1, s1), (t2, s2)), Disjoint ((t1', s1'), (t2', s2')) -> 
     equal t1 t1' && equal t2 t2' && Z.equal s1 s1' && Z.equal s2 s2'

  | Struct (tag, members), Struct (tag2, members2) ->
     tag = tag2 && 
       List.equal (fun (m,t) (m',t') -> m = m' && equal t t') 
         members members2
  | Member (tag,t,member), Member (tag',t',member')
  | MemberOffset (tag,t,member), MemberOffset (tag',t',member') 
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
  | InRange (rt, t), InRange (rt', t') ->
     stored_type_equal rt rt' && equal t t'

  | S sym, S sym' 
    -> Sym.equal sym sym'


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

  | AlignedI _, _
  | Aligned _, _
  | Offset _, _
  | LocLT _, _
  | LocLE _, _
  | Disjoint _, _

  | Struct _, _
  | Member _, _
  | MemberOffset _, _

  | Nil _, _
  | Cons _, _
  | List _, _
  | Head _, _
  | Tail _, _

  | InRange _, _

  | S _, _ ->

     false




let pp ?(quote=true) it : PPrint.document = 

  let rec aux atomic it = 
    let mparens pped = if atomic then parens pped else pped in
    let aux = aux true in
    match it with
    | Num i -> Z.pp i
    | Pointer i -> Z.pp i
    | Bool true -> !^"true"
    | Bool false -> !^"false"
    | Unit -> !^"()"

    | Add (it1,it2) -> mparens (aux it1 ^^^ plus ^^^ aux it2)
    | Sub (it1,it2) -> mparens (aux it1 ^^^ minus ^^^ aux it2)
    | Mul (it1,it2) -> mparens (aux it1 ^^^ star ^^^ aux it2)
    | Div (it1,it2) -> mparens (aux it1 ^^^ slash ^^^ aux it2)
    | Exp (it1,it2) -> mparens (aux it1 ^^^ caret ^^^ aux it2)
    | Rem_t (it1,it2) -> mparens (!^ "rem_t" ^^^ aux it1 ^^^ aux it2)
    | Rem_f (it1,it2) -> mparens (!^ "rem_f" ^^^ aux it1 ^^^ aux it2)
    | Min (it1,it2) -> mparens (!^ "min" ^^^ aux it1 ^^^ aux it2)
    | Max (it1,it2) -> mparens (!^ "max" ^^^ aux it1 ^^^ aux it2)

    | EQ (o1,o2) -> mparens (aux o1 ^^^ equals ^^^ aux o2)
    | NE (o1,o2) -> 
       if !unicode then mparens (aux o1 ^^^ utf8string "\u{2260}" ^^^ aux o2)
       else mparens (aux o1 ^^^ langle ^^ rangle ^^^ aux o2)
    | LT (o1,o2) -> mparens (aux o1 ^^^ langle ^^^ aux o2)
    | GT (o1,o2) -> mparens (aux o1 ^^^ rangle ^^^ aux o2)
    | LE (o1,o2) -> 
       if !unicode then mparens (aux o1 ^^^ utf8string "\u{2264}"  ^^^ aux o2)
       else mparens (aux o1 ^^^ langle ^^ equals ^^^ aux o2)
    | GE (o1,o2) -> 
       if !unicode then mparens (aux o1 ^^^ utf8string "\u{2265}"  ^^^ aux o2)
       else mparens (aux o1 ^^^ rangle ^^ equals ^^^ aux o2)

    | Null o1 -> mparens (!^"null" ^^^ aux o1)
    | And o -> mparens (separate_map (space ^^ ampersand ^^ space) aux o)
    | Or o -> mparens (separate_map (space ^^ bar ^^ bar ^^ space) aux o)
    | Impl (o1,o2) -> mparens (aux o1 ^^^ equals ^^ rangle ^^^ aux o2)
    | Not (o1) -> mparens (!^"not" ^^^ aux o1)
    | ITE (o1,o2,o3) -> mparens (!^"ite" ^^^ aux o1 ^^^ aux o2 ^^^ aux o3)

    | Nth (bt,n,it2) -> mparens (!^"nth" ^^^ !^(string_of_int n) ^^^ aux it2)
    | Head (o1) -> mparens (!^"hd" ^^^ aux o1)
    | Tail (o1) -> mparens (!^"tl" ^^^ aux o1)

    | Tuple its -> mparens (!^"tuple" ^^^ separate_map space aux its)
    | Nil _ -> brackets empty
    | Cons (t1,t2) -> mparens (aux t1 ^^ colon ^^ colon ^^ aux t2)
    | List (its, bt) -> 
       mparens (brackets (separate_map comma aux its) ^^^ colon ^^ BT.pp false bt)

    | Struct (_tag, members) ->
       braces (separate_map comma (fun (BT.Member member,it) -> 
                   !^member ^^^ equals ^^^ aux it ) members)
    | Member (_tag, t, Member s) ->
       aux t ^^ dot ^^ !^s
    | MemberOffset (_tag, t, Member s) ->
       mparens (ampersand ^^ aux t ^^ !^"->" ^^ !^s)
    | Offset (t1, t2) ->
       mparens (!^"offset" ^^^ aux t1 ^^^ aux t2)
    | LocLT (o1,o2) -> mparens (aux o1 ^^^ langle ^^^ aux o2)
    | LocLE (o1,o2) -> mparens (aux o1 ^^^ langle ^^ equals ^^^ aux o2)
    | Disjoint ((o1,s1),(o2,s2)) ->
       mparens (!^"disjoint" ^^^ 
                  parens (aux o1 ^^ comma ^^^ Z.pp s1) ^^^
                    parens (aux o2 ^^ comma ^^^ Z.pp s2))

    | AlignedI (t, t') ->
       mparens (!^"aligned" ^^^ aux t ^^^ aux t')
    | Aligned (rt, t) ->
       mparens (!^"aligned" ^^^ pp_stored_type rt ^^^ aux t)
    | InRange (rt, t) ->
       mparens (!^"representable" ^^^ pp_stored_type rt ^^^ aux t)

    | S sym -> Sym.pp sym
  in
  (if quote then dquotes else (fun pp -> pp)) (aux false it)


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
    -> 
     vars_in it
  | ITE (it,it',it'') ->
     vars_in_list [it;it';it'']
  | Tuple its -> 
     vars_in_list (it :: its)
  | Struct (_tag, members) ->
     vars_in_list (map snd members)
  | Member (_tag, it, s)
  | MemberOffset (_tag, it, s) -> 
     vars_in_list [it;it]
  | List (its,bt) ->
     vars_in_list its
  | AlignedI (it, it') ->
     vars_in_list [it;it]
  | Aligned (_rt, t)
  | InRange (_rt,t) ->
     vars_in t
  | S symbol -> 
     SymSet.singleton symbol

and vars_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (vars_in sym))
    SymSet.empty l


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
  | Member (tag, t, f) ->
     Member (tag, subst_var subst t, f)
  | MemberOffset (tag,t,f) ->
     MemberOffset (tag,subst_var subst t, f)
  | Offset (it, it') -> Offset (subst_var subst it, subst_var subst it')
  | LocLT (it, it') -> LocLT (subst_var subst it, subst_var subst it')
  | LocLE (it, it') -> LocLE (subst_var subst it, subst_var subst it')
  | Disjoint ((it,s), (it',s')) -> 
     Disjoint ((subst_var subst it,s), (subst_var subst it',s'))
  | AlignedI (it,it') -> AlignedI (subst_var subst it, subst_var subst it')
  | Aligned (rt,t) -> Aligned (rt, subst_var subst t)
  | InRange (rt,t) -> InRange (rt,subst_var subst t)
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
  | Member (tag, t, f) ->
     Member (tag, subst_it subst t, f)
  | MemberOffset (tag,t,f) ->
     MemberOffset (tag,subst_it subst t, f)
  | Offset (it, it') -> Offset (subst_it subst it, subst_it subst it')
  | LocLT (it, it') -> LocLT (subst_it subst it, subst_it subst it')
  | LocLE (it, it') -> LocLE (subst_it subst it, subst_it subst it')
  | Disjoint ((it,s), (it',s')) -> 
     Disjoint ((subst_it subst it,s), (subst_it subst it',s'))
  | AlignedI (it,it') -> AlignedI (subst_it subst it, subst_it subst it')
  | Aligned (rt,t) -> Aligned (rt,subst_it subst t)
  | InRange (rt,t) -> InRange (rt,subst_it subst t)
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


open Z

let in_range min max within = And [LE (min, within); LE (within, max)]

let min_u32 = Num zero
let max_u32 = Num (sub (power_int_positive_int 2 32) (of_int 1))
let min_u64 = Num zero
let max_u64 = Num (sub (power_int_positive_int 2 64) (of_int 1))

let min_i32 = Num (sub (of_int 0) (power_int_positive_int 2 (32 - 1)))
let max_i32 = Num (sub (power_int_positive_int 2 (32 - 1)) (of_int 1))
let min_i64 = Num (sub (of_int 0) (power_int_positive_int 2 (64 - 1)))
let max_i64 = Num (sub (power_int_positive_int 2 (64 - 1)) (of_int 1))

let int x = Num (Z.of_int x)


