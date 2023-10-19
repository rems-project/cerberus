open Pp
module CT = Sctypes

type const =
  | Z of Z.t
  | Q of Q.t
  | Pointer of Z.t
  | Alloc_id of Z.t
  | Bool of bool
  | Unit
  | Null
  | CType_const of Sctypes.ctype
  | Default of BaseTypes.t
(* Default bt: equivalent to a unique variable of base type bt, that
   we know nothing about other than Default bt = Default bt *)
[@@deriving eq, ord]

type unop =
  | Not
  | BWCLZNoSMT
  | BWCTZNoSMT
  | BWFFSNoSMT
[@@deriving eq, ord, show]

type binop =
  | And
  | Or
  | Impl
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
  | BWAndNoSMT
  | BWOrNoSMT
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
[@@deriving eq, ord, show]

type 'bt pattern_ =
  | PSym of Sym.t
  | PWild
  | PConstructor of Sym.t * (Id.t * 'bt pattern) list

and 'bt pattern =
  | Pat of 'bt pattern_ * 'bt
[@@deriving eq, ord, map]

(* over integers and reals *)
type 'bt term_ =
  | Const of const
  | Sym of Sym.t
  | Unop of unop * 'bt term
  | Binop of binop * 'bt term * 'bt term
  | ITE of 'bt term * 'bt term * 'bt term
  | EachI of (int * (Sym.t * 'bt) * int) * 'bt term
  (* add Z3's Distinct for separation facts  *)
  | Tuple of 'bt term list
  | NthTuple of int * 'bt term
  | Struct of Sym.t * (Id.t * 'bt term) list
  | StructMember of 'bt term * Id.t
  | StructUpdate of ('bt term * Id.t) * 'bt term
  | Record of (Id.t * 'bt term) list
  | RecordMember of 'bt term * Id.t
  | RecordUpdate of ('bt term * Id.t) * 'bt term
  | Constructor of Sym.t * (Id.t * 'bt term) list
  | MemberOffset of Sym.t * Id.t
  | ArrayOffset of Sctypes.t (*element ct*) * 'bt term (*index*)
  | SizeOf of Sctypes.t
  | Nil of BaseTypes.t
  | Cons of 'bt term * 'bt term
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of 'bt term * 'bt term * 'bt term
  | ArrayToList of 'bt term * 'bt term * 'bt term
  | Representable of Sctypes.t * 'bt term
  | Good of Sctypes.t * 'bt term
  | Aligned of {t : 'bt term; align : 'bt term}
  | WrapI of Sctypes.IntegerTypes.t * 'bt term
  | MapConst of BaseTypes.t * 'bt term
  | MapSet of 'bt term * 'bt term * 'bt term
  | MapGet of 'bt term * 'bt term
  | MapDef of (Sym.t * BaseTypes.t) * 'bt term
  | Apply of Sym.t * ('bt term) list
  | Let of (Sym.t * 'bt term) * 'bt term
  | Match of 'bt term * ('bt pattern * 'bt term) list
  | Cast of BaseTypes.t * 'bt term

and 'bt term =
  | IT of 'bt term_ * 'bt
[@@deriving eq, ord, map]


let equal = equal_term
let compare = compare_term



let rec pp_pattern (Pat (pat_, _bt)) =
  match pat_ with
  | PSym s ->
     Sym.pp s
  | PWild ->
     underscore
  | PConstructor (c, args) ->
     Sym.pp c ^^^
       braces (separate_map (comma ^^ space) (fun (id, pat) ->
                   Id.pp id ^^ colon ^^^ pp_pattern pat
                 ) args)

let pp : 'bt 'a. ?atomic:bool -> ?f:('bt term -> Pp.doc -> Pp.doc) -> 'bt term -> Pp.doc =
  fun ?(atomic=false) ?(f=fun _ x -> x) ->
  let rec aux atomic (IT (it, _)) =
    let aux b x = f x (aux b x) in
    (* Without the `lparen` inside `nest 2`, the printed `rparen` is indented
       by 2 (wrt to the lparen). I don't quite understand it, but it works. *)
    let parens pped =
      Pp.group ((nest 2 @@ lparen ^^ break 0 ^^ pped) ^^ break 0 ^^ rparen) in
    let braces pped =
      Pp.group ((nest 2 @@ lbrace ^^ break 0 ^^ pped) ^^ break 0 ^^ rbrace) in
    let mparens pped =
      if atomic then parens pped else Pp.group pped in
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
       | Alloc_id i -> !^("@" ^ Z.to_string i)
       | Bool true -> !^"true"
       | Bool false -> !^"false"
       | Unit -> !^"void"
       | Default bt -> c_app !^"default" [BaseTypes.pp bt]
       | Null -> !^"null"
       | CType_const ct -> Pp.squotes (Sctypes.pp ct)
       end
    | Sym sym -> Sym.pp sym
    (* | Arith_op arith_op -> *)
    (*    begin match arith_op with *)
    | Unop (uop, it1) ->
       begin match uop with
       | BWCLZNoSMT ->
          c_app !^"bw_clz_uf" [aux false it1]
       | BWCTZNoSMT ->
          c_app !^"bw_ctz_uf" [aux false it1]
       | BWFFSNoSMT ->
          c_app !^"bw_ffs_uf" [aux false it1]
       | Not ->
          mparens (!^"!" ^^ parens (aux false it1))
       end
    | Binop (bop, it1, it2) ->
       begin match bop with
       | And ->
          mparens (flow (break_op (ampersand ^^ ampersand)) [aux true it1; aux true it2])
       | Or ->
          mparens (flow (break_op (bar ^^ bar)) [aux true it1; aux true it2])
       | Impl ->
          mparens (flow (break_op (minus ^^ rangle ())) [aux true it1; aux true it2])
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
       | BWAndNoSMT ->
          c_app !^"bw_and_uf" [aux false it1; aux false it2]
       | BWOrNoSMT ->
          c_app !^"bw_or_uf" [aux false it1; aux false it2]
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
       | ITE (o1,o2,o3) ->
          parens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
       | EachI ((i1, (s, _), i2), t) ->
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
             Pp.group @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals) ^^^ align (aux false it)
           ) members ^^^ rbrace
       | RecordMember (t, member) ->
          prefix 0 0 (aux true t) (dot ^^ Id.pp member)
       | RecordUpdate ((t, member), v) ->
          mparens (aux true t ^^ braces @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals) ^^^ align (aux true v))
       (* end *)
    (* | Pointer_op pointer_op -> *)
    (*    begin match pointer_op with *)
       | Cast (cbt, t) ->
          mparens (align @@ parens(BaseTypes.pp cbt) ^^ break 0 ^^ aux true t)
       | MemberOffset (tag, member) ->
          mparens (c_app !^"offsetof" [Sym.pp tag; Id.pp member])
       | ArrayOffset (ct, t) ->
          mparens (c_app !^"arrayOffset" [Sctypes.pp ct; aux false t])
       | SizeOf t ->
          mparens (c_app !^"sizeof" [Sctypes.pp t])
       (* end *)
    (* | CT_pred ct_pred -> *)
    (*    begin match ct_pred with *)
       | Aligned t ->
          mparens (c_app !^"aligned" [aux false t.t; aux false t.align])
       | Representable (rt, t) ->
          mparens (c_app (!^"repr" ^^ angles (CT.pp rt)) [aux false t])
       | Good (rt, t) ->
          mparens (c_app (!^"good" ^^ angles (CT.pp rt)) [aux false t])
       | WrapI (ity, t) ->
          mparens (c_app (!^"wrapI" ^^ angles (CT.pp (Integer ity))) [aux false t])
       (* end *)
    (* | List_op list_op -> *)
    (*    begin match list_op with *)
       | Head (o1) ->
          mparens (c_app !^"hd" [aux false o1])
       | Tail (o1) ->
          mparens (c_app !^"tl" [aux false o1])
       | Nil bt ->
          !^"nil" ^^ angles (BaseTypes.pp bt)
       | Cons (t1,t2) ->
          mparens (aux true t1 ^^ colon ^^ colon ^^ aux true t2)
       | NthList (n, xs, d) ->
          mparens (c_app !^"nth_list" [aux false n; aux false xs; aux false d])
       | ArrayToList (arr, i, len) ->
          mparens (c_app !^"array_to_list" [aux false arr; aux false i; aux false len])
       (* end *)
    (* | Set_op set_op -> *)
    (*    begin match set_op with *)
       (* end *)
       | MapConst (_bt, t) ->
          mparens (c_app !^"const" [aux false t])
       | MapGet (t1, t2) ->
          mparens (aux true t1 ^^ brackets (aux false t2))
       | MapSet (t1, t2, t3) ->
          mparens (aux true t1 ^^
                     brackets (aux false t2 ^^^ equals ^^^ aux false t3))
       | MapDef ((s,_), t) ->
          brackets (Sym.pp s ^^^ !^"->" ^^^ aux false t)
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
    | Let ((name, x1), x2) ->
       parens (!^ "let" ^^^ Sym.pp name ^^^ Pp.equals ^^^
                 aux false x1 ^^^ !^ "in" ^^^ aux false x2)
    | Match (e, cases) ->
        !^"match" ^^^ aux false e ^^^ braces (
          (* copying from mparens *)
          Pp.group (nest 2 @@ (
            separate_map (break 0) (fun (pattern, body) ->
                pp_pattern pattern ^^^ !^"=>" ^^^
                  braces (aux false body)
              ) cases))
        )
    | Constructor (s, args) ->
       Sym.pp s ^^^ braces (separate_map (comma ^^ space) (fun (id, e) -> Id.pp id ^^ colon ^^^ aux false e) args)
  in
  fun (it : 'bt term) -> aux atomic it












open Cerb_pp_prelude
open Cerb_frontend.Pp_ast

let rec dtree_of_pat (Pat (pat_, _bt)) =
  match pat_ with
  | PSym s ->
     Dnode (pp_ctor "PSym", [Dleaf (Sym.pp s)])
  | PWild ->
     Dleaf (pp_ctor "PWild")
  | PConstructor (s, pats) ->
     Dnode (pp_ctor "PConstructor",
            Dleaf (Sym.pp s) ::
              List.map (fun (id, pat) ->
                  Dnode (pp_ctor "Arg", [Dleaf (Id.pp id); dtree_of_pat pat])
                ) pats
       )

let rec dtree (IT (it_, bt)) =
  match it_ with
  | Sym s ->
     Dleaf (Sym.pp s)
  | Const (Z z) ->
     Dleaf !^(Z.to_string z)
  | Const (Q q) ->
     Dleaf !^(Q.to_string q)
  | Const (Pointer z) ->
     Dleaf !^(Z.to_string z)
  | Const (Bool b) ->
     Dleaf !^(if b then "true" else "false")
  | Const Unit ->
     Dleaf !^"unit"
  | Const (Default _) ->
     Dleaf !^"default"
  | Const Null ->
     Dleaf !^"null"
  | Const (Alloc_id z) ->
     Dnode (pp_ctor "alloc_id", [Dleaf !^(Z.to_string z)])
  | Const (CType_const ct) ->
     Dleaf (Sctypes.pp ct)
  | Unop (op, t1) ->
     Dnode (pp_ctor (show_unop op), [dtree t1])
  | Binop (op, t1, t2) ->
     Dnode (pp_ctor (show_binop op), [dtree t1; dtree t2])
  | ITE (t1, t2, t3) ->
     Dnode (pp_ctor "Impl", [dtree t1; dtree t2; dtree t3])
  | EachI ((starti,(i,_),endi), body) ->
     Dnode (pp_ctor "EachI", [
           Dleaf !^(string_of_int starti);
           Dleaf (Sym.pp i);
           Dleaf !^(string_of_int endi);
           dtree body
       ])
  | Tuple its ->
     Dnode (pp_ctor "Tuple", List.map dtree its)
  | NthTuple (i, t) ->
     Dnode (pp_ctor "NthTuple", [Dleaf !^(string_of_int i); dtree t])
  | Struct (tag, members) ->
     Dnode (pp_ctor ("Struct("^Sym.pp_string tag^")"),
            List.map (fun (member,e) ->
                Dnode (pp_ctor "Member", [Dleaf (Id.pp member); dtree e])
              ) members)
  | StructMember (e, member) ->
     Dnode (pp_ctor "StructMember", [dtree e; Dleaf (Id.pp member)])
  | StructUpdate ((base, member), v) ->
     Dnode (pp_ctor "StructUpdate", [
           dtree base;
           Dleaf (Id.pp member); dtree v
       ])
  | Record members ->
     Dnode (pp_ctor "Record",
            List.map (fun (member,e) ->
                Dnode (pp_ctor "Member", [Dleaf (Id.pp member); dtree e])
              ) members)
  | RecordMember (e, member) ->
     Dnode (pp_ctor "RecordMember", [dtree e; Dleaf (Id.pp member)])
  | RecordUpdate ((base, member), v) ->
     Dnode (pp_ctor "RecordUpdate", [dtree base; Dleaf (Id.pp member); dtree v])
  | Cast (cbt, t) ->
     Dnode (pp_ctor "Cast", [Dleaf (BaseTypes.pp cbt); dtree t])
  | MemberOffset (tag, id) ->
     Dnode (pp_ctor "MemberOffset", [Dleaf (Sym.pp tag); Dleaf (Id.pp id)])
  | ArrayOffset (ty, t) ->
     Dnode (pp_ctor "ArrayOffset", [Dleaf (Sctypes.pp ty); dtree t])
  | Representable (ty, t) ->
     Dnode (pp_ctor "Representable", [Dleaf (Sctypes.pp ty); dtree t])
  | Good (ty, t) ->
     Dnode (pp_ctor "Good", [Dleaf (Sctypes.pp ty); dtree t])
  | Aligned a ->
     Dnode (pp_ctor "Aligned", [dtree a.t; dtree a.align])
  | MapConst (bt, t) ->
     Dnode (pp_ctor "MapConst", [dtree t])
  | MapSet (t1, t2, t3) ->
     Dnode (pp_ctor "MapSet", [dtree t1; dtree t2; dtree t3])
  | MapGet (t1, t2) ->
     Dnode (pp_ctor "MapGet", [dtree t1; dtree t2])
  | MapDef ((s, bt), t) ->
     Dnode (pp_ctor "MapDef", [Dleaf (Sym.pp s); dtree t])
  | Apply (f, args) ->
     Dnode (pp_ctor "Apply", (Dleaf (Sym.pp f) :: List.map dtree args))
  | Constructor (s, args) ->
     Dnode (pp_ctor "Constructor",
           Dleaf (Sym.pp s) ::
           List.map (fun (id, t) ->
               Dnode (pp_ctor "Arg", [Dleaf (Id.pp id); dtree t])
             ) args
       )
  | Match (t, pats) ->
     Dnode (pp_ctor "Match",
            dtree t ::
              List.map (fun (pat, body) ->
                  Dnode (pp_ctor "Case", [dtree_of_pat pat; dtree body])
                ) pats
       )
  | Nil bt ->
     Dleaf (!^"Nil" ^^ angles (BaseTypes.pp bt))
  | Cons (t1, t2) ->
     Dnode (pp_ctor "Cons", [dtree t1; dtree t2])
  | Head t ->
     Dnode (pp_ctor "Head", [dtree t])
  | Tail t ->
     Dnode (pp_ctor "Tail", [dtree t])
  | NthList (t1, t2, t3) ->
     Dnode (pp_ctor "NthList", [dtree t1; dtree t2; dtree t3])
  | ArrayToList (t1, t2, t3) ->
     Dnode (pp_ctor "ArrayToList", [dtree t1; dtree t2; dtree t3])
  | WrapI (it, t) ->
     Dnode (pp_ctor "WrapI", [
           Dleaf (Sctypes.pp (Integer it));
           dtree t
       ])
  | SizeOf ct ->
     Dnode (pp_ctor "SizeOf", [Dleaf (Sctypes.pp ct)])
  | Let ((s, t1), t2) ->
     Dnode (pp_ctor "Let", [Dleaf (Sym.pp s); dtree t1; dtree t2])
