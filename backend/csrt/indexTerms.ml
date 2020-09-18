open Subst
open Uni
open Option
open List
open Pp
module Loc=Locations
module BT=BaseTypes

module SymSet = Set.Make(Sym)


type 'id term =
  | Num of Num.t
  | Bool of bool

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

  | Member of BT.tag * 'id term * BT.member
  | MemberOffset of BT.tag * 'id term * BT.member

  | Nil of BT.t
  | Cons of 'id term * 'id term
  | List of 'id term list * BT.t
  | Head of 'id term
  | Tail of 'id term

  | S of 'id


type parse_ast = string term
type t = Sym.t term

let int x = Num (Num.of_int x)

let in_range between min max = 
  And [LE (min, between); LE (between, max)]



let rec pp atomic it : PPrint.document = 

  let mparens pped = if atomic then parens pped else pped in
  let pp = pp true in
  match it with
  | Num i -> Num.pp i
  | Bool true -> !^"true"
  | Bool false -> !^"false"

  | Add (it1,it2) -> mparens (pp it1 ^^^ plus ^^^ pp it2)
  | Sub (it1,it2) -> mparens (pp it1 ^^^ minus ^^^ pp it2)
  | Mul (it1,it2) -> mparens (pp it1 ^^^ star ^^^ pp it2)
  | Div (it1,it2) -> mparens (pp it1 ^^^ slash ^^^ pp it2)
  | Exp (it1,it2) -> mparens (pp it1 ^^^ caret ^^^ pp it2)
  | Rem_t (it1,it2) -> mparens (!^ "rem_t" ^^^ pp it1 ^^^ pp it2)
  | Rem_f (it1,it2) -> mparens (!^ "rem_f" ^^^ pp it1 ^^^ pp it2)
  | Min (it1,it2) -> mparens (!^ "min" ^^^ pp it1 ^^^ pp it2)
  | Max (it1,it2) -> mparens (!^ "max" ^^^ pp it1 ^^^ pp it2)

  | EQ (o1,o2) -> mparens (pp o1 ^^^ equals ^^^ pp o2)
  | NE (o1,o2) -> 
     if !unicode then mparens (pp o1 ^^^ utf8string "\u{2260}" ^^^ pp o2)
     else mparens (pp o1 ^^^ langle ^^ rangle ^^^ pp o2)
  | LT (o1,o2) -> mparens (pp o1 ^^^ langle ^^^ pp o2)
  | GT (o1,o2) -> mparens (pp o1 ^^^ rangle ^^^ pp o2)
  | LE (o1,o2) -> 
     if !unicode then mparens (pp o1 ^^^ utf8string "\u{2264}"  ^^^ pp o2)
     else mparens (pp o1 ^^^ langle ^^ equals ^^^ pp o2)
  | GE (o1,o2) -> 
     if !unicode then mparens (pp o1 ^^^ utf8string "\u{2265}"  ^^^ pp o2)
     else mparens (pp o1 ^^^ rangle ^^ equals ^^^ pp o2)

  | Null o1 -> mparens (!^"null" ^^^ pp o1)
  | And o -> mparens (separate_map (space ^^ ampersand ^^ space) pp o)
  | Or o -> mparens (separate_map (space ^^ bar ^^ bar ^^ space) pp o)
  | Impl (o1,o2) -> mparens (pp o1 ^^^ equals ^^ rangle ^^^ pp o2)
  | Not (o1) -> mparens (!^"not" ^^^ pp o1)
  | ITE (o1,o2,o3) -> mparens (!^"ite" ^^^ pp o1 ^^^ pp o2 ^^^ pp o3)

  | Nth (bt,n,it2) -> mparens (!^"nth" ^^^ !^(string_of_int n) ^^^ pp it2)
  | Head (o1) -> mparens (!^"hd" ^^^ pp o1)
  | Tail (o1) -> mparens (!^"tl" ^^^ pp o1)

  | Tuple its -> mparens (!^"tuple" ^^^ separate_map space pp its)
  | Nil _ -> brackets empty
  | Cons (t1,t2) -> mparens (pp t1 ^^ colon ^^ colon ^^ pp t2)
  | List (its, bt) -> 
     mparens (brackets (separate_map comma pp its) ^^^ colon ^^ BT.pp false bt)

  | Member (_tag, t, Member s) ->
     pp t ^^ dot ^^ !^s
  | MemberOffset (_tag, t, Member s) ->
     mparens (!^"offset" ^^^ pp t ^^^ !^s)

  | S sym -> Sym.pp sym


let rec vars_in it : SymSet.t = 
  match it with
  | Num _  
  | Bool _
  | Nil _ ->
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
  | Cons (it, it')  ->
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
  | Member (_tag, it, s)
  | MemberOffset (_tag, it, s) -> 
     vars_in_list [it;it]
  | List (its,bt) ->
     vars_in_list its
  | S symbol -> 
     SymSet.singleton symbol

and vars_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (vars_in sym))
    SymSet.empty l


let rec subst_var subst it : t = 
  match it with
  | Num _ -> it
  | Bool _ -> it
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
  | Member (tag, t, f) ->
     Member (tag, subst_var subst t, f)
  | MemberOffset (tag,t,f) ->
     MemberOffset (tag,subst_var subst t, f)
  | S symbol -> 
     if symbol = subst.s then subst.swith else S symbol


let subst_vars = make_substs subst_var


let rec instantiate_struct_member subst it : t = 
  match it with
  | Num _ -> it
  | Bool _ -> it
  | Add (it, it') -> 
     Add (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | Sub (it, it') -> 
     Sub (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | Mul (it, it') -> 
     Mul (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | Div (it, it') -> 
     Div (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | Exp (it, it') -> 
     Exp (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | Rem_t (it, it') -> 
     Rem_t (instantiate_struct_member subst it, 
            instantiate_struct_member subst it')
  | Rem_f (it, it') -> 
     Rem_f (instantiate_struct_member subst it, 
            instantiate_struct_member subst it')
  | Min (it, it') -> 
     Min (instantiate_struct_member subst it, 
            instantiate_struct_member subst it')
  | Max (it, it') -> 
     Max (instantiate_struct_member subst it, 
          instantiate_struct_member subst it')
  | EQ (it, it') -> 
     EQ (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | NE (it, it') -> 
     NE (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | LT (it, it') -> 
     LT (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | GT (it, it') -> 
     GT (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | LE (it, it') -> 
     LE (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | GE (it, it') -> 
     GE (instantiate_struct_member subst it, 
         instantiate_struct_member subst it')
  | Null it -> 
     Null (instantiate_struct_member subst it)
  | And its -> 
     And (map (instantiate_struct_member subst) its)
  | Or its -> 
     Or (map (instantiate_struct_member subst) its)
  | Impl (it, it') -> 
     Impl (instantiate_struct_member subst it, 
           instantiate_struct_member subst it')
  | Not it -> 
     Not (instantiate_struct_member subst it)
  | ITE (it,it',it'') -> 
     ITE (instantiate_struct_member subst it,
          instantiate_struct_member subst it,
          instantiate_struct_member subst it)
  | Tuple its ->
     Tuple (map (fun it -> instantiate_struct_member subst it) its)
  | Nth (bt, n, it') ->
     Nth (bt, n, instantiate_struct_member subst it')
  | Nil bt -> 
     Nil bt
  | Cons (it1,it2) -> 
     Cons (instantiate_struct_member subst it1,
           instantiate_struct_member subst it2)
  | List (its,bt) -> 
     List (map (fun it -> instantiate_struct_member subst it) its, bt)
  | Head it ->
     Head (instantiate_struct_member subst it)
  | Tail it ->
     Tail (instantiate_struct_member subst it)
  | (Member (tag, t, f)) as member ->
     if subst.s = member then subst.swith 
     else Member (tag, instantiate_struct_member subst t, f)
  | MemberOffset (tag,t,f) ->
     MemberOffset (tag,instantiate_struct_member subst t, f)
  | S symbol -> S symbol



let rec unify it it' (res : (t Uni.t) SymMap.t) = 
  match it, it' with
  | Num n, Num n' when n = n' -> return res
  | Bool b, Bool b' when b = b' -> return res

  | Add (it1, it2), Add (it1', it2')
  | Sub (it1, it2), Sub (it1', it2')
  | Mul (it1, it2), Mul (it1', it2')
  | Div (it1, it2), Div (it1', it2')
  | Exp (it1, it2), Exp (it1', it2')
  | Rem_t (it1, it2), Rem_t (it1', it2')
  | Rem_f (it1, it2), Rem_f (it1', it2')
  | Min (it1, it2), Min (it1', it2')
  | Max (it1, it2), Max (it1', it2')

  | EQ (it1, it2), EQ (it1', it2')
  | NE (it1, it2), NE (it1', it2')
  | LT (it1, it2), LT (it1', it2')
  | GT (it1, it2), GT (it1', it2')
  | LE (it1, it2), LE (it1', it2')
  | GE (it1, it2), GE (it1', it2')
    ->
     let* res = unify it1 it1' res in
     unify it2 it2' res


  | And its, And its'
  | Or its, Or its' 
    ->
     unify_list its its' res

  | Null it, Null it'
  | Not it, Not it' 
  | Head it, Head it' 
  | Tail it, Tail it' 
    -> 
     unify it it' res
  | ITE (it1,it2,it3), ITE (it1',it2',it3') ->
     unify_list [it1;it2;it3] [it1';it2';it3'] res

  | Tuple its, Tuple its' ->
     unify_list (it::its) (it'::its') res
  | Nth (bt, n, it2), Nth (bt', n', it2') when BT.equal bt bt' && n = n'
    -> 
     unify it it' res

  | List (its,bt), List (its',bt') when BT.equal bt bt' ->
     unify_list its its' res

  | Member (tag, t, m), Member (tag', t', m') 
  | MemberOffset (tag, t, m), MemberOffset (tag', t', m') 
       when tag = tag' && m = m' ->
     unify t t' res

  | S sym, it' ->
     if S sym = it' then Some res else
       let* uni = SymMap.find_opt sym res in
       begin match uni.resolved with
       | Some s when s = it' -> return res 
       | Some s -> fail
       | None -> return (SymMap.add sym (Uni.{resolved = Some it'}) res)
       end

  | _, _ ->
     fail

and unify_list its its' res =
  match its, its' with
  | [], [] -> return res
  | (it :: its), (it' :: its') ->
     let* res = unify it it' res in
     unify_list its its' res
  | _, _ ->
     fail

let rec equal it it' = 
  match it, it' with
  | Num n, Num n' -> Num.equal n n'
  | Bool b, Bool b' -> b = b'

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

  | Impl (t1,t2), Impl (t1',t2')
    -> equal t1 t1' && equal t2 t2' 


  | And ts, And ts'
  | Or ts, Or ts'
    -> List.equal equal ts ts'

  | Null t, Null t'
  | Not t, Not t' 
    -> equal t t' 

  | Tuple its, Tuple its' 
    -> List.equal equal its its'
  | Nth (bt, n,t), Nth (bt', n',t') 
    -> BT.equal bt bt' && n = n' && equal t t' 

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

  | S sym, S sym' 
    -> Sym.equal sym sym'

  | _ -> 
     false


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


let min_u32 = Num Num.zero
let min_u62 = Num Num.zero
let max_u32 = (int 2 %^ int 32) %- int 1
let max_u64 = (int 2 %^ int 64) %- int 1

let min_i32 = int 1 %- (int 2 %^ (int 32 %- int 1))
let min_i64 = int 1 %- (int 2 %^ (int 64 %- int 1))
let max_i32 = (int 2 %^ (int 32 %- int 1)) %- int 1
let max_i64 = (int 2 %^ (int 64 %- int 1)) %- int 1
