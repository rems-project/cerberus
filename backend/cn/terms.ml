open Pp
module CT = Sctypes

type const = 
  | Z of Z.t
  | Q of Q.t
  | Pointer of Z.t
  | Bool of bool
  | Unit
  | Default of BaseTypes.t
  | Null
(* Default bt: equivalent to a unique variable of base type bt, that
   we know nothing about other than Default bt = Default bt *)
[@@deriving eq, ord]

type binop =
  | Add
  | Sub
  | Mul
  | MulNoSMT
  | Div
  | DivNoSMT
  | Exp
  | ExpNoSMT
  | Rem
  | RemNoSMT
  | Mod
  | ModNoSMT
  | XORNoSMT
  | LT
  | LE
  | Min
  | Max
  | EQ
  | LTPointer
  | LEPointer
  | SetUnion
  | SetIntersection
  | SetDifference
  | SetMember
  | Subset
[@@deriving eq, ord]

(* over integers and reals *)
type 'bt term_ =
  | Const of const
  | Sym of Sym.t
  | Binop of binop * 'bt term * 'bt term
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term
  | EachI of (int * Sym.t * int) * 'bt term
  (* add Z3's Distinct for separation facts  *)
  | Tuple of 'bt term list
  | NthTuple of int * 'bt term
  | Struct of BaseTypes.tag * (BaseTypes.member * 'bt term) list
  | StructMember of 'bt term * BaseTypes.member
  | StructUpdate of ('bt term * BaseTypes.member) * 'bt term
  | Record of (Sym.t * 'bt term) list
  | RecordMember of 'bt term * Sym.t
  | RecordUpdate of ('bt term * Sym.t) * 'bt term
  | DatatypeCons of Sym.t * 'bt term
  | DatatypeMember of 'bt term * Sym.t
  | DatatypeIsCons of Sym.t * 'bt term
  | MemberOffset of BaseTypes.tag * Id.t
  | ArrayOffset of Sctypes.t (*element ct*) * 'bt term (*index*)
  | Nil
  | Cons of 'bt term * 'bt term
  | List of 'bt term list
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of 'bt term * 'bt term * 'bt term
  | ArrayToList of 'bt term * 'bt term * 'bt term
  | Representable of Sctypes.t * 'bt term
  | Good of Sctypes.t * 'bt term
  | AlignedI of {t : 'bt term; align : 'bt term}
  | MapConst of BaseTypes.t * 'bt term
  | MapSet of 'bt term * 'bt term * 'bt term
  | MapGet of 'bt term * 'bt term
  | MapDef of (Sym.t * BaseTypes.t) * 'bt term
  | Apply of Sym.t * ('bt term) list
  | Cast of BaseTypes.t * 'bt term

and 'bt term =
  | IT of 'bt term_ * 'bt
[@@deriving eq, ord, map]


let equal = equal_term
let compare = compare_term

let pp : 'bt 'a. ?atomic:bool -> ?f:('bt term -> Pp.doc -> Pp.doc) -> 'bt term -> Pp.doc =
  fun ?(atomic=false) ?(f=fun _ x -> x) ->
  let rec aux atomic (IT (it, _) as it_) =
    let aux b x = f x (aux b x) in
    (* Without the `lparen` inside `nest 2`, the printed `rparen` is indented
       by 2 (wrt to the lparen). I don't quite understand it, but it works. *)
    let mparens pped =
      if atomic then
        Pp.group ((nest 2 @@ lparen ^^ break 0 ^^ pped) ^^ break 0 ^^ rparen)
      else
        Pp.group pped in
    let break_op x = break 1 ^^ x ^^ space in

    

    match it with
    | Const const ->
       begin match const with
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
       | Default bt -> c_app !^"default" [BaseTypes.pp bt]
       | Null -> !^"null"
       end
    | Sym sym -> Sym.pp sym
    (* | Arith_op arith_op -> *)
    (*    begin match arith_op with *)
    | Binop (bop, it1, it2) ->
       begin match bop with
       | Add ->
          mparens (flow (break_op plus) [aux true it1; aux true it2])
       | Sub ->
          mparens (flow (break_op minus) [aux true it1; aux true it2])
       | Mul ->
          mparens (flow (break_op star) [aux true it1; aux true it2])
       | MulNoSMT ->
          mparens (c_app !^"mul_uf" [aux true it1; aux true it2])
       | Div ->
          mparens (flow (break_op slash) [aux true it1; aux true it2])
       | DivNoSMT ->
          mparens (c_app !^"div_uf" [aux true it1; aux true it2])
       | Exp ->
          c_app !^"power" [aux true it1; aux true it2]
       | ExpNoSMT ->
          c_app !^"power_uf" [aux true it1; aux true it2]
       | Rem ->
          c_app !^"rem" [aux true it1; aux true it2]
       | RemNoSMT ->
          mparens (c_app !^"rem_uf" [aux true it1; aux true it2])
       | Mod ->
          c_app !^"mod" [aux true it1; aux true it2]
       | ModNoSMT ->
          mparens (c_app !^"mod_uf" [aux true it1; aux true it2])
       | EQ ->
          mparens (flow (break_op (equals ^^ equals)) [aux true it1; aux true it2])
       | LT ->
          mparens (flow (break_op @@ langle ()) [aux true it1; aux true it2])
       | LE ->
          mparens (flow (break_op @@ langle () ^^ equals) [aux true it1; aux true it2])
       | LTPointer ->
          mparens (flow (break_op @@ langle ()) [aux true it1; aux true it2])
       | LEPointer ->
          mparens (flow (break_op @@ langle () ^^ equals) [aux true it1; aux true it2])
       | Min ->
          c_app !^"min" [aux false it1; aux false it2]
       | Max ->
          c_app !^"max" [aux false it1; aux false it2]
       | XORNoSMT ->
          c_app !^"xor_uf" [aux false it1; aux false it2]
       | SetMember ->
          c_app !^"member" [aux false it1; aux false it2]
       | SetUnion ->
          c_app !^"union" [aux false it1; aux false it2]
       | SetIntersection ->
          c_app !^"inter" [aux false it1; aux false it2]
       | SetDifference ->
          c_app !^"difference" [aux false it1; aux false it2]
       | Subset ->
          c_app !^"subset" [aux false it1; aux false it2]
       end
       (* end *)
    (* | Bool_op bool_op -> *)
    (*    begin match bool_op with *)
       | And o ->
          let rec consolidate = function
            | IT (And o, _) -> List.concat_map consolidate o
            | it_ -> [ it_ ] in
          let o = consolidate it_ in
          mparens (flow_map (break_op !^"&&") (aux true) o)
       | Or o ->
          let rec consolidate = function
            | IT (Or o, _) -> List.concat_map consolidate o
            | it_ -> [ it_ ] in
          let o = consolidate it_ in
          mparens (flow_map (break_op !^"||") (aux true) o)
       | Impl (o1,o2) ->
          mparens (flow (break_op (equals ^^ rangle ())) [aux true o1; aux true o2])
       | Not (o1) ->
          mparens (!^"!" ^^ parens (aux false o1))
       | ITE (o1,o2,o3) ->
          parens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
       | EachI ((i1, s, i2), t) ->
         Pp.(group @@ group (c_app !^"for" [int i1; Sym.pp s; int i2])
             ^/^ group ((nest 2 @@ lbrace ^^ break 0 ^^ (aux false t)) ^^ break 0 ^^ rbrace))
       (* end *)
    (* | Tuple_op tuple_op -> *)
    (*    begin match tuple_op with *)
       | NthTuple (n,it2) ->
          mparens (aux true it2 ^^ dot ^^ !^("member" ^ string_of_int n))
       | Tuple its ->
          braces (separate_map (semi ^^ space) (aux false) its)
       (* end *)
    (* | Struct_op struct_op -> *)
    (*    begin match struct_op with *)
       | Struct (_tag, members) ->
         align @@ lbrace ^^^ flow_map (break 0 ^^ comma ^^ space) (fun (member,it) ->
             Pp.group @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals) ^^^ align (aux false it)
           ) members ^^^ rbrace
       | StructMember (t, member) ->
          prefix 0 0 (aux true t) (dot ^^ Id.pp member )
       | StructUpdate ((t, member), v) ->
          mparens (aux true t ^^ braces @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals) ^^^ align (aux true v))
       (* end *)
    (* | Record_op record_op -> *)
    (*    begin match record_op with *)
       | Record members ->
         align @@ lbrace ^^^ flow_map (break 0 ^^ comma ^^ space) (fun (member,it) ->
             Pp.group @@ (Pp.group @@ dot ^^ Sym.pp member ^^^ equals) ^^^ align (aux false it)
           ) members ^^^ rbrace
       | RecordMember (t, member) ->
          prefix 0 0 (aux true t) (dot ^^ Sym.pp member)
       | RecordUpdate ((t, member), v) ->
          mparens (aux true t ^^ braces @@ (Pp.group @@ dot ^^ Sym.pp member ^^^ equals) ^^^ align (aux true v))
       (* end *)
    (* | Datatype_op datatype_op -> *)
    (*    begin match datatype_op with *)
       | DatatypeCons (nm, members_rec) -> mparens (Sym.pp nm ^^^ aux false members_rec)
       | DatatypeMember (x, nm) -> aux true x ^^ dot ^^ Sym.pp nm
       | DatatypeIsCons (nm, x) -> mparens (aux false x ^^^ !^ "is" ^^^ Sym.pp nm)
       (* end *)
    (* | Pointer_op pointer_op -> *)
    (*    begin match pointer_op with *)
       | Cast (cbt, t) ->
          mparens (align @@ parens(BaseTypes.pp cbt) ^^ break 0 ^^ aux true t)
       | MemberOffset (tag, member) ->
          mparens (c_app !^"offsetof" [Sym.pp tag; Id.pp member])
       | ArrayOffset (ct, t) ->
          mparens (c_app !^"arrayOffset" [Sctypes.pp ct; aux false t])
       (* end *)
    (* | CT_pred ct_pred -> *)
    (*    begin match ct_pred with *)
       | AlignedI t ->
          c_app !^"aligned" [aux false t.t; aux false t.align]
       | Representable (rt, t) ->
          c_app !^"repr" [CT.pp rt; aux false t]
       | Good (rt, t) ->
          c_app !^"good" [CT.pp rt; aux false t]
       (* end *)
    (* | List_op list_op -> *)
    (*    begin match list_op with *)
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
       | NthList (n, xs, d) ->
          c_app !^"nth_list" [aux false n; aux false xs; aux false d]
       | ArrayToList (arr, i, len) ->
          c_app !^"array_to_list" [aux false arr; aux false i; aux false len]
       (* end *)
    (* | Set_op set_op -> *)
    (*    begin match set_op with *)
       (* end *)
       | MapConst (_bt, t) ->
          c_app !^"const" [aux false t]
       | MapGet (t1, t2) ->
          aux true t1 ^^ brackets (aux false t2)
       | MapSet (t1, t2, t3) ->
          aux true t1 ^^ 
            brackets (aux false t2 ^^^ equals ^^^ aux false t3)
       | MapDef ((s,bt), t) ->
          brackets (BaseTypes.pp bt ^^^ Sym.pp s ^^^ !^"->" ^^^ aux false t)
    (* | Map_op map_op -> *)

       (* disabling that for now, because I'll add an expression for updating multiple cells at once *)
      (* let rec consolidate ops = function *)
      (*   | IT (Map_op (MapSet (t1, t2, t3)), _) -> consolidate (`Set (t2, t3) :: ops) t1 *)
      (*   | IT (Map_op (MapGet (t, args)), _) ->  consolidate ((`Get args) :: ops) t *)
      (*   | it_ -> (it_, ops) in *)
      (* let pp_op = function *)
      (*  | `Set (t2,t3) -> *)
      (*    Pp.group @@ brackets @@ (aux false t2 ^/^ equals) ^/^ align (aux false t3) *)
      (*  | `Get args -> *)
      (*     Pp.group @@ brackets @@ aux false args in *)
      (* let (root, ops) = consolidate [] it_ in *)
      (* let root_pp = match root with *)
      (*  | IT (Map_op (MapConst (_, t)), _) -> *)
      (*     Pp.group @@ brackets @@ aux false t *)
      (*  | IT (Map_op (MapDef ((s, abt), body)), _) -> *)
      (*     Pp.group @@ braces (BaseTypes.pp abt ^^^ Sym.pp s ^^^ !^"->" ^^^ aux false body) *)
      (*  | it_ -> aux true it_ *)
      (*  in *)
      (*  prefix 2 0 root_pp @@ align (flow_map (break 0) pp_op ops) *)
    | Apply (name, args) ->
       c_app (Sym.pp name) (List.map (aux false) args)
  in
  fun (it : 'bt term) -> aux atomic it












open Pp_prelude 
open Cerb_frontend.Pp_ast

let rec dtree (IT (it_, bt)) =
  match it_ with
  | (Sym s) -> Dleaf (Sym.pp s)
  | Const (Z z) -> Dleaf !^(Z.to_string z)
  | Const (Q q) -> Dleaf !^(Q.to_string q)
  | Const (Pointer z) -> Dleaf !^(Z.to_string z)
  | Const (Bool b) -> Dleaf !^(if b then "true" else "false")
  | Const Unit -> Dleaf !^"unit"
  | Const (Default _) -> Dleaf !^"default"
  | Const Null -> Dleaf !^"null"
  | Binop (Add, t1, t2) -> Dnode (pp_ctor "Add", [dtree t1; dtree t2])
  | Binop (Sub, t1, t2) -> Dnode (pp_ctor "Sub", [dtree t1; dtree t2])
  | Binop (Mul, t1, t2) -> Dnode (pp_ctor "Mul", [dtree t1; dtree t2])
  | Binop (MulNoSMT, t1, t2) -> Dnode (pp_ctor "MulNoSMT", [dtree t1; dtree t2])
  | Binop (Div, t1, t2) -> Dnode (pp_ctor "Div", [dtree t1; dtree t2])
  | Binop (DivNoSMT, t1, t2) -> Dnode (pp_ctor "DivNoSMT", [dtree t1; dtree t2])
  | Binop (Exp, t1, t2) -> Dnode (pp_ctor "Exp", [dtree t1; dtree t2])
  | Binop (ExpNoSMT, t1, t2) -> Dnode (pp_ctor "ExpNoSMT", [dtree t1; dtree t2])
  | Binop (Rem, t1, t2) -> Dnode (pp_ctor "Rem", [dtree t1; dtree t2])
  | Binop (RemNoSMT, t1, t2) -> Dnode (pp_ctor "RemNoSMT", [dtree t1; dtree t2])
  | Binop (Mod, t1, t2) -> Dnode (pp_ctor "Mod", [dtree t1; dtree t2])
  | Binop (ModNoSMT, t1, t2) -> Dnode (pp_ctor "ModNoSMT", [dtree t1; dtree t2])
  | Binop (LT, t1, t2) -> Dnode (pp_ctor "LT", [dtree t1; dtree t2])
  | Binop (LE, t1, t2) -> Dnode (pp_ctor "LE", [dtree t1; dtree t2])
  | Binop (Min, t1, t2) -> Dnode (pp_ctor "Min", [dtree t1; dtree t2])
  | Binop (Max, t1, t2) -> Dnode (pp_ctor "Max", [dtree t1; dtree t2])
  | Binop (XORNoSMT, t1, t2) -> Dnode (pp_ctor "XORNoSMT", [dtree t1; dtree t2])
  | (And ts) -> Dnode (pp_ctor "And", List.map dtree ts)
  | (Or ts) -> Dnode (pp_ctor "Or", List.map dtree ts)
  | (Impl (t1, t2)) -> Dnode (pp_ctor "Impl", [dtree t1; dtree t2])
  | (Not t) -> Dnode (pp_ctor "Not", [dtree t])
  | (ITE (t1, t2, t3)) -> Dnode (pp_ctor "Impl", [dtree t1; dtree t2; dtree t3])
  | Binop (EQ, t1, t2) -> Dnode (pp_ctor "EQ", [dtree t1; dtree t2])
  | (EachI ((starti,i,endi), body)) -> Dnode (pp_ctor "EachI", [Dleaf !^(string_of_int starti); Dleaf (Sym.pp i); Dleaf !^(string_of_int endi); dtree body])
  | (Tuple its) -> Dnode (pp_ctor "Tuple", List.map dtree its)
  | (NthTuple (i, t)) -> Dnode (pp_ctor "NthTuple", [Dleaf !^(string_of_int i); dtree t])
  | (Struct (tag, members)) ->
     Dnode (pp_ctor ("Struct("^Sym.pp_string tag^")"), List.map (fun (member,e) -> Dnode (pp_ctor "Member", [Dleaf (Id.pp member); dtree e])) members)
  | (StructMember (e, member)) ->
     Dnode (pp_ctor "StructMember", [dtree e; Dleaf (Id.pp member)])
  | (StructUpdate ((base, member), v)) ->
     Dnode (pp_ctor "StructUpdate", [dtree base; Dleaf (Id.pp member); dtree v])
  | (Record members) ->
     Dnode (pp_ctor "Record", List.map (fun (member,e) -> Dnode (pp_ctor "Member", [Dleaf (Sym.pp member); dtree e])) members)
  | (RecordMember (e, member)) ->
     Dnode (pp_ctor "RecordMember", [dtree e; Dleaf (Sym.pp member)])
  | (RecordUpdate ((base, member), v)) ->
     Dnode (pp_ctor "RecordUpdate", [dtree base; Dleaf (Sym.pp member); dtree v])
  | (DatatypeCons (s, t)) ->
     Dnode (pp_ctor "DatatypeCons", [Dleaf (Sym.pp s); dtree t])
  | (DatatypeMember (t, s)) ->
     Dnode (pp_ctor "DatatypeMember", [dtree t; Dleaf (Sym.pp s)])
  | (DatatypeIsCons (s, t)) ->
     Dnode (pp_ctor "DatatypeIsCons", [Dleaf (Sym.pp s); dtree t])
  | Binop (LTPointer, t1, t2) -> Dnode (pp_ctor "LTPointer", [dtree t1; dtree t2])
  | Binop (LEPointer, t1, t2) -> Dnode (pp_ctor "LEPointer", [dtree t1; dtree t2])
  | Cast (cbt, t) -> Dnode (pp_ctor "Cast", [Dleaf (BaseTypes.pp cbt); dtree t])
  | (MemberOffset (tag, id)) -> Dnode (pp_ctor "MemberOffset", [Dleaf (Sym.pp tag); Dleaf (Id.pp id)])
  | (ArrayOffset (ty, t)) -> Dnode (pp_ctor "ArrayOffset", [Dleaf (Sctypes.pp ty); dtree t])
  | (Representable (ty, t)) -> Dnode (pp_ctor "Representable", [Dleaf (Sctypes.pp ty); dtree t])
  | (Good (ty, t)) -> Dnode (pp_ctor "Good", [Dleaf (Sctypes.pp ty); dtree t])
  | (AlignedI a) -> Dnode (pp_ctor "AlignedI", [dtree a.t; dtree a.align])
  | (MapConst (bt, t)) -> Dnode (pp_ctor "MapConst", [dtree t])
  | (MapSet (t1, t2, t3)) -> Dnode (pp_ctor "MapSet", [dtree t1; dtree t2; dtree t3])
  | (MapGet (t1, t2)) -> Dnode (pp_ctor "MapGet", [dtree t1; dtree t2])
  | (MapDef ((s, bt), t)) -> Dnode (pp_ctor "MapDef", [Dleaf (Sym.pp s); dtree t])
  | Apply (f, args) -> Dnode (pp_ctor "Apply", (Dleaf (Sym.pp f) :: List.map dtree args))
  | _ -> failwith "todo"
