open Pp
module CT = Sctypes

type loc = Cerb_location.t

type const =
  | Z of Z.t
  | Bits of (BaseTypes.sign * int) * Z.t
  | Q of Q.t
  | Pointer of
      { alloc_id : Z.t;
        addr : Z.t
      }
  | Alloc_id of Z.t
  | Bool of bool
  | Unit
  | Null
  | CType_const of Sctypes.ctype
  | Default of BaseTypes.t
(* Default bt: equivalent to a unique variable of base type bt, that we know nothing about
   other than Default bt = Default bt *)
[@@deriving eq, ord]

type unop =
  | Not
  | Negate
  | BW_CLZ_NoSMT
  | BW_CTZ_NoSMT
  | BW_FFS_NoSMT
  | BW_FLS_NoSMT
  | BW_Compl
[@@deriving eq, ord, show]

type binop =
  | And
  | Or
  | Implies
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
  | BW_And
  | BWOrNoSMT
  | ShiftLeft
  | ShiftRight
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
  | Pat of 'bt pattern_ * 'bt * (loc[@equal fun _ _ -> true] [@compare fun _ _ -> 0])
[@@deriving eq, ord, map]

(* over integers and reals *)
type 'bt term_ =
  | Const of const
  | Sym of Sym.t
  | Unop of unop * 'bt term
  | Binop of binop * 'bt term * 'bt term
  | ITE of 'bt term * 'bt term * 'bt term
  | EachI of (int * (Sym.t * BaseTypes.t) * int) * 'bt term
  (* add Z3's Distinct for separation facts *)
  | Tuple of 'bt term list
  | NthTuple of int * 'bt term
  | Struct of Sym.t * (Id.t * 'bt term) list
  | StructMember of 'bt term * Id.t
  | StructUpdate of ('bt term * Id.t) * 'bt term
  | Record of (Id.t * 'bt term) list
  | RecordMember of 'bt term * Id.t
  | RecordUpdate of ('bt term * Id.t) * 'bt term (* this is currently unused *)
  | Constructor of Sym.t * (Id.t * 'bt term) list
  | MemberShift of 'bt term * Sym.t * Id.t
  | ArrayShift of
      { base : 'bt term;
        ct : Sctypes.t;
        index : 'bt term
      }
  | CopyAllocId of
      { addr : 'bt term;
        loc : 'bt term
      }
  | SizeOf of Sctypes.t
  | OffsetOf of Sym.t * Id.t
  | Nil of BaseTypes.t
  | Cons of 'bt term * 'bt term
  | Head of 'bt term
  | Tail of 'bt term
  | NthList of 'bt term * 'bt term * 'bt term
  | ArrayToList of 'bt term * 'bt term * 'bt term
  | Representable of Sctypes.t * 'bt term
  | Good of Sctypes.t * 'bt term
  | Aligned of
      { t : 'bt term;
        align : 'bt term
      }
  | WrapI of Sctypes.IntegerTypes.t * 'bt term
  | MapConst of BaseTypes.t * 'bt term
  | MapSet of 'bt term * 'bt term * 'bt term
  | MapGet of 'bt term * 'bt term
  | MapDef of (Sym.t * BaseTypes.t) * 'bt term
  | Apply of Sym.t * 'bt term list
  | Let of (Sym.t * 'bt term) * 'bt term
  | Match of 'bt term * ('bt pattern * 'bt term) list
  | Cast of BaseTypes.t * 'bt term

and 'bt term =
  | IT of 'bt term_ * 'bt * (loc[@equal fun _ _ -> true] [@compare fun _ _ -> 0])
[@@deriving eq, ord, map]

let equal = equal_term

let compare = compare_term

let rec pp_pattern (Pat (pat_, _bt, _)) =
  match pat_ with
  | PSym s -> Sym.pp s
  | PWild -> underscore
  | PConstructor (c, args) ->
    Sym.pp c
    ^^^ braces
          (separate_map
             (comma ^^ space)
             (fun (id, pat) -> Id.pp id ^^ colon ^^^ pp_pattern pat)
             args)


(* Precedences:
   Reference: https://en.cppreference.com/w/c/language/operator_precedence
   The number we use are `16 - p` where `p` is the precedence in the table.
   We do this so bigger numbers are higher precedence.

   Highest

   15: . [] ->         selectors
   14: ! - ~ & cast    unary
   13: * / %
   12: + -
   10: < <= > >=
   9: == !=
   8: &
   7: ^
   6: |
   5: &&
   4: ||
   3: ? :              ternary

   Lowest
*)

let pp
  : 'bt 'a.
  ?prec:int -> ?f:('bt term -> Pp.document -> Pp.document) -> 'bt term -> Pp.document
  =
  fun ?(prec = 0) ?(f = fun _ x -> x) ->
  let rec aux prec (IT (it, _, _)) =
    let aux prec x = f x (aux prec x) in
    (* Without the `lparen` inside `nest 2`, the printed `rparen` is indented by 2 (wrt to
       the lparen). I don't quite understand it, but it works. *)
    let parens pped =
      Pp.group ((nest 2 @@ lparen ^^ break 0 ^^ pped) ^^ break 0 ^^ rparen)
    in
    let braces pped =
      Pp.group ((nest 2 @@ lbrace ^^ break 0 ^^ pped) ^^ break 0 ^^ rbrace)
    in
    let wrap_after tgt doc = if prec > tgt then parens doc else doc in
    let break_op x = break 1 ^^ x ^^ space in
    let alloc_id i = !^("@" ^ Z.to_string i) in
    match it with
    | Const const ->
      (match const with
       | Z i -> !^(Z.to_string i)
       | Bits ((sign, n), v) ->
         let dec =
           !^(Z.to_string v)
           ^^ (match sign with Unsigned -> !^"'u" | Signed -> !^"'i")
           ^^ !^(string_of_int n)
         in
         if Z.lt v (Z.of_int 16) then
           dec
         else
           dec
           ^^^ !^"/*"
           ^^^ !^("0x" ^ Z.format "%x" (BaseTypes.normalise_to_range (Unsigned, n) v))
           ^^^ !^"*/"
       | Q q -> !^(Q.to_string q)
       | Pointer { alloc_id = id; addr } ->
         braces (alloc_id id ^^ Pp.semi ^^ Pp.space ^^ !^("0x" ^ Z.format "%x" addr))
       | Alloc_id i -> !^("@" ^ Z.to_string i)
       | Bool true -> !^"true"
       | Bool false -> !^"false"
       | Unit -> !^"void"
       | Default bt -> c_app !^"default" [ BaseTypes.pp bt ]
       | Null -> !^"NULL"
       | CType_const ct -> Pp.squotes (Sctypes.pp ct))
    | Sym sym -> Sym.pp sym
    | Unop (uop, it1) ->
      let prefix x op p = wrap_after x (!^op ^^ aux p it1) in
      (match uop with
       | BW_CLZ_NoSMT -> c_app !^"bw_clz_uf" [ aux 0 it1 ]
       | BW_CTZ_NoSMT -> c_app !^"bw_ctz_uf" [ aux 0 it1 ]
       | BW_FFS_NoSMT -> c_app !^"bw_ffs_uf" [ aux 0 it1 ]
       | BW_FLS_NoSMT -> c_app !^"bw_fls_uf" [ aux 0 it1 ]
       | Not ->
         let infix p op l r =
           wrap_after p (flow (break 1 ^^ op ^^ space) [ aux p l; aux p r ])
         in
         (match it1 with
          | IT (Binop (EQ, l, r), _, _) -> infix 9 (!^"!" ^^ equals) l r
          | IT (Binop (LT, l, r), _, _) -> infix 10 (rangle () ^^ equals) l r
          | IT (Binop (LE, l, r), _, _) -> infix 10 (rangle ()) l r
          | IT (Binop (LTPointer, l, r), _, _) -> infix 10 (rangle () ^^ equals) l r
          | IT (Binop (LEPointer, l, r), _, _) -> infix 10 (rangle ()) l r
          | _ -> prefix 14 "!" 14)
       | Negate -> prefix 14 "-" 14
       | BW_Compl -> prefix 14 "~" 14)
    | Binop (bop, it1, it2) ->
      let infix x op l r = wrap_after x (flow (break_op op) [ aux l it1; aux r it2 ]) in
      let prefix x = c_app !^x [ aux 0 it1; aux 0 it2 ] in
      (match bop with
       | And -> infix 5 (ampersand ^^ ampersand) 5 5
       | Or -> infix 4 (bar ^^ bar) 4 4
       | Implies -> prefix "implies"
       | Add -> infix 12 !^"+" 12 12
       | Sub -> infix 12 !^"-" 12 13
       | Mul -> infix 13 !^"*" 13 13
       | MulNoSMT -> prefix "mul_uf"
       | Div -> infix 13 slash 14 14
       | DivNoSMT -> prefix "div_uf"
       | Exp -> prefix "power"
       | ExpNoSMT -> prefix "power_uf"
       | Rem -> infix 13 !^"%" 14 14
       | RemNoSMT -> prefix "rem_uf"
       | Mod -> prefix "mod"
       | ModNoSMT -> prefix "mod_uf"
       | EQ -> infix 9 (equals ^^ equals) 9 9
       | LT -> infix 10 (langle ()) 10 10
       | LE -> infix 10 (langle () ^^ equals) 10 10
       | LTPointer -> infix 10 (langle ()) 10 10
       | LEPointer -> infix 10 (langle () ^^ equals) 10 10
       | Min -> prefix "min"
       | Max -> prefix "max"
       | XORNoSMT -> infix 7 !^"^" 7 7
       | BW_And -> infix 8 ampersand 8 8
       | BWOrNoSMT -> infix 6 bar 6 6
       | ShiftLeft ->
         infix 0 (langle () ^^ langle ()) 1 1 (* easier to read with parens *)
       | ShiftRight ->
         infix 0 (rangle () ^^ rangle ()) 1 1 (* easier to read with parens *)
       | SetMember -> prefix "member"
       | SetUnion -> prefix "union"
       | SetIntersection -> prefix "inter"
       | SetDifference -> prefix "difference"
       | Subset -> prefix "subset")
    | ITE (o1, o2, o3) ->
      wrap_after 2 (flow (break 1) [ aux 3 o1; !^"?"; aux 3 o2; colon; aux 3 o3 ])
    | EachI ((i1, (s, _), i2), t) ->
      Pp.(
        group
        @@ group (c_app !^"for" [ int i1; Sym.pp s; int i2 ])
        ^/^ group ((nest 2 @@ lbrace ^^ break 0 ^^ aux 0 t) ^^ break 0 ^^ rbrace))
    | NthTuple (n, it2) ->
      wrap_after 15 (aux 15 it2 ^^ dot ^^ !^("member" ^ string_of_int n))
    | Tuple its -> braces (separate_map (semi ^^ space) (aux 0) its)
    | Struct (_tag, members) ->
      lbrace
      ^^ hardline
      ^^ flow_map
           (comma ^^ hardline)
           (fun (member, it) ->
             Pp.group @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals) ^^^ align (aux 0 it))
           members
      ^^^ rbrace
    | StructMember (t, member) -> wrap_after 15 (aux 15 t ^^ dot ^^ Id.pp member)
    | StructUpdate ((t, member), v) ->
      braces (dot ^^ Id.pp member ^^ colon ^^^ aux 0 v ^^ comma ^^^ !^".." ^^ aux 0 t)
    | Record members ->
      align
      @@ lbrace
      ^^^ flow_map
            (break 0 ^^ comma ^^ space)
            (fun (member, it) ->
              Pp.group
              @@ (Pp.group @@ dot ^^ Id.pp member ^^^ equals)
              ^^^ align (aux 0 it))
            members
      ^^^ rbrace
    | RecordMember (t, member) -> wrap_after 15 (aux 15 t ^^ dot ^^ Id.pp member)
    | RecordUpdate ((t, member), v) ->
      braces (dot ^^ Id.pp member ^^ colon ^^^ aux 0 v ^^ comma ^^^ !^".." ^^ aux 0 t)
    | Cast (cbt, t) -> wrap_after 14 (align @@ parens (BaseTypes.pp cbt) ^^ aux 14 t)
    | MemberShift (t, _tag, member) ->
      wrap_after 14 (ampersand ^^ aux 15 t ^^ (!^"-" ^^ rangle ()) ^^ Id.pp member)
    | ArrayShift { base; ct = _ct; index } ->
      wrap_after 14 (ampersand ^^ aux 15 base ^^ brackets (aux 0 index))
    | CopyAllocId { addr; loc } -> c_app !^"copy_alloc_id" [ aux 0 addr; aux 0 loc ]
    | SizeOf t -> c_app !^"sizeof" [ Sctypes.pp t ]
    | OffsetOf (tag, member) -> c_app !^"offsetof" [ Sym.pp tag; Id.pp member ]
    | Aligned t -> c_app !^"aligned" [ aux 0 t.t; aux 0 t.align ]
    | Representable (rt, t) -> c_app (!^"repr" ^^ angles (CT.pp rt)) [ aux 0 t ]
    | Good (rt, t) -> c_app (!^"good" ^^ angles (CT.pp rt)) [ aux 0 t ]
    | WrapI (ity, t) -> c_app (!^"wrapI" ^^ angles (CT.pp (Integer ity))) [ aux 0 t ]
    | Head o1 -> c_app !^"hd" [ aux 0 o1 ]
    | Tail o1 -> c_app !^"tl" [ aux 0 o1 ]
    | Nil bt -> !^"nil" ^^ angles (BaseTypes.pp bt)
    | Cons (t1, t2) -> c_app !^"cons" [ aux 0 t1; aux 0 t2 ]
    | NthList (n, xs, d) -> c_app !^"nth_list" [ aux 0 n; aux 0 xs; aux 0 d ]
    | ArrayToList (arr, i, len) ->
      c_app !^"array_to_list" [ aux 0 arr; aux 0 i; aux 0 len ]
    | MapConst (_bt, t) -> c_app !^"const" [ aux 0 t ]
    | MapGet (t1, t2) -> wrap_after 15 (aux 15 t1 ^^ brackets (aux 0 t2))
    | MapSet (t1, t2, t3) ->
      wrap_after 15 (aux 15 t1 ^^ brackets (aux 0 t2 ^^^ equals ^^^ aux 0 t3))
    | MapDef ((s, _), t) -> brackets (Sym.pp s ^^^ (!^"-" ^^ rangle ()) ^^^ aux 0 t)
    | Apply (name, args) -> c_app (Sym.pp name) (List.map (aux 0) args)
    | Let ((name, x1), x2) ->
      parens (!^"let" ^^^ Sym.pp name ^^^ Pp.equals ^^^ aux 0 x1 ^^^ !^"in" ^^^ aux 0 x2)
    | Match (e, cases) ->
      !^"match"
      ^^^ aux 0 e
      ^^^ braces
            ((* copying from mparens *)
             Pp.group
               (nest 2
                @@ separate_map
                     (break 0)
                     (fun (pattern, body) ->
                       pp_pattern pattern ^^^ !^"=>" ^^^ braces (aux 0 body))
                     cases))
    | Constructor (s, args) ->
      Sym.pp s
      ^^^ braces
            (separate_map
               (comma ^^ space)
               (fun (id, e) -> Id.pp id ^^ colon ^^^ aux 0 e)
               args)
  in
  fun (it : 'bt term) -> aux prec it


open Cerb_pp_prelude
open Cerb_frontend.Pp_ast

let rec dtree_of_pat (Pat (pat_, _bt, _)) =
  match pat_ with
  | PSym s -> Dnode (pp_ctor "PSym", [ Dleaf (Sym.pp s) ])
  | PWild -> Dleaf (pp_ctor "PWild")
  | PConstructor (s, pats) ->
    Dnode
      ( pp_ctor "PConstructor",
        Dleaf (Sym.pp s)
        :: List.map
             (fun (id, pat) ->
               Dnode (pp_ctor "Arg", [ Dleaf (Id.pp id); dtree_of_pat pat ]))
             pats )


let rec dtree (IT (it_, bt, loc)) =
  let alloc_id z = Dnode (pp_ctor "alloc_id", [ Dleaf !^(Z.to_string z) ]) in
  let dtree =
    match it_ with
    | Sym s -> Dleaf (Sym.pp s)
    | Const (Z z) -> Dleaf !^(Z.to_string z)
    | Const (Bits _) -> Dleaf (pp (IT (it_, bt, loc)))
    | Const (Q q) -> Dleaf !^(Q.to_string q)
    | Const (Pointer { alloc_id = id; addr }) ->
      Dnode (pp_ctor "pointer", [ alloc_id id; Dleaf !^(Z.to_string addr) ])
    | Const (Bool b) -> Dleaf !^(if b then "true" else "false")
    | Const Unit -> Dleaf !^"unit"
    | Const (Default _) -> Dleaf !^"default"
    | Const Null -> Dleaf !^"null"
    | Const (Alloc_id z) -> alloc_id z
    | Const (CType_const ct) -> Dleaf (Sctypes.pp ct)
    | Unop (op, t1) -> Dnode (pp_ctor (show_unop op), [ dtree t1 ])
    | Binop (op, t1, t2) -> Dnode (pp_ctor (show_binop op), [ dtree t1; dtree t2 ])
    | ITE (t1, t2, t3) -> Dnode (pp_ctor "Implies", [ dtree t1; dtree t2; dtree t3 ])
    | EachI ((starti, (i, _), endi), body) ->
      Dnode
        ( pp_ctor "EachI",
          [ Dleaf !^(string_of_int starti);
            Dleaf (Sym.pp i);
            Dleaf !^(string_of_int endi);
            dtree body
          ] )
    | Tuple its -> Dnode (pp_ctor "Tuple", List.map dtree its)
    | NthTuple (i, t) -> Dnode (pp_ctor "NthTuple", [ Dleaf !^(string_of_int i); dtree t ])
    | Struct (tag, members) ->
      Dnode
        ( pp_ctor ("Struct(" ^ Sym.pp_string tag ^ ")"),
          List.map
            (fun (member, e) ->
              Dnode (pp_ctor "Member", [ Dleaf (Id.pp member); dtree e ]))
            members )
    | StructMember (e, member) ->
      Dnode (pp_ctor "StructMember", [ dtree e; Dleaf (Id.pp member) ])
    | StructUpdate ((base, member), v) ->
      Dnode (pp_ctor "StructUpdate", [ dtree base; Dleaf (Id.pp member); dtree v ])
    | Record members ->
      Dnode
        ( pp_ctor "Record",
          List.map
            (fun (member, e) ->
              Dnode (pp_ctor "Member", [ Dleaf (Id.pp member); dtree e ]))
            members )
    | RecordMember (e, member) ->
      Dnode (pp_ctor "RecordMember", [ dtree e; Dleaf (Id.pp member) ])
    | RecordUpdate ((base, member), v) ->
      Dnode (pp_ctor "RecordUpdate", [ dtree base; Dleaf (Id.pp member); dtree v ])
    | Cast (cbt, t) -> Dnode (pp_ctor "Cast", [ Dleaf (BaseTypes.pp cbt); dtree t ])
    | MemberShift (t, tag, id) ->
      Dnode (pp_ctor "MemberShift", [ dtree t; Dleaf (Sym.pp tag); Dleaf (Id.pp id) ])
    | ArrayShift { base; ct = ty; index = t } ->
      Dnode (pp_ctor "ArrayShift", [ Dleaf (Sctypes.pp ty); dtree base; dtree t ])
    | CopyAllocId { addr; loc } -> Dnode (pp_ctor "CopyAllocId", [ dtree addr; dtree loc ])
    | Representable (ty, t) ->
      Dnode (pp_ctor "Representable", [ Dleaf (Sctypes.pp ty); dtree t ])
    | Good (ty, t) -> Dnode (pp_ctor "Good", [ Dleaf (Sctypes.pp ty); dtree t ])
    | Aligned a -> Dnode (pp_ctor "Aligned", [ dtree a.t; dtree a.align ])
    | MapConst (_bt, t) -> Dnode (pp_ctor "MapConst", [ dtree t ])
    | MapSet (t1, t2, t3) -> Dnode (pp_ctor "MapSet", [ dtree t1; dtree t2; dtree t3 ])
    | MapGet (t1, t2) -> Dnode (pp_ctor "MapGet", [ dtree t1; dtree t2 ])
    | MapDef ((s, _bt), t) -> Dnode (pp_ctor "MapDef", [ Dleaf (Sym.pp s); dtree t ])
    | Apply (f, args) -> Dnode (pp_ctor "Apply", Dleaf (Sym.pp f) :: List.map dtree args)
    | Constructor (s, args) ->
      Dnode
        ( pp_ctor "Constructor",
          Dleaf (Sym.pp s)
          :: List.map
               (fun (id, t) -> Dnode (pp_ctor "Arg", [ Dleaf (Id.pp id); dtree t ]))
               args )
    | Match (t, pats) ->
      Dnode
        ( pp_ctor "Match",
          dtree t
          :: List.map
               (fun (pat, body) ->
                 Dnode (pp_ctor "Case", [ dtree_of_pat pat; dtree body ]))
               pats )
    | Nil bt -> Dleaf (!^"Nil" ^^ angles (BaseTypes.pp bt))
    | Cons (t1, t2) -> Dnode (pp_ctor "Cons", [ dtree t1; dtree t2 ])
    | Head t -> Dnode (pp_ctor "Head", [ dtree t ])
    | Tail t -> Dnode (pp_ctor "Tail", [ dtree t ])
    | NthList (t1, t2, t3) -> Dnode (pp_ctor "NthList", [ dtree t1; dtree t2; dtree t3 ])
    | ArrayToList (t1, t2, t3) ->
      Dnode (pp_ctor "ArrayToList", [ dtree t1; dtree t2; dtree t3 ])
    | WrapI (it, t) ->
      Dnode (pp_ctor "WrapI", [ Dleaf (Sctypes.pp (Integer it)); dtree t ])
    | SizeOf ct -> Dnode (pp_ctor "SizeOf", [ Dleaf (Sctypes.pp ct) ])
    | OffsetOf (tag, member) ->
      Dnode (pp_ctor "OffsetOf", [ Dleaf (Sym.pp tag); Dleaf (Id.pp member) ])
    | Let ((s, t1), t2) -> Dnode (pp_ctor "Let", [ Dleaf (Sym.pp s); dtree t1; dtree t2 ])
  in
  let loc_doc = parens !^(Locations.to_string loc) in
  match dtree with
  | Dnode (doc, dtrees) -> Dnode (doc ^^^ loc_doc, dtrees)
  | Dleaf doc -> Dleaf (doc ^^^ loc_doc)
  | _ -> assert false
