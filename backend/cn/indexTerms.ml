open List
open Pp
module BT=BaseTypes
module CT = Sctypes
module CF=Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
open Subst


type lit = 
  | Sym of Sym.t
  | Z of Z.t
  | Q of Q.t
  | Pointer of Z.t
  | Bool of bool
  | Unit
  | Default of BT.t
  | Null
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
  | Mod of 'bt term * 'bt term
  | LT of 'bt term * 'bt term
  | LE of 'bt term * 'bt term
  | IntToReal of 'bt term
  | RealToInt of 'bt term

and 'bt bool_op = 
  | And of 'bt term list
  | Or of 'bt term list
  | Impl of 'bt term * 'bt term
  | Not of 'bt term
  | ITE of 'bt term * 'bt term * 'bt term
  | EQ of 'bt term * 'bt term
  | EachI of (int * Sym.t * int) * 'bt term
  (* add Z3's Distinct for separation facts  *)

and 'bt tuple_op = 
  | Tuple of 'bt term list
  | NthTuple of int * 'bt term

and 'bt struct_op =
  | Struct of BT.tag * (BT.member * 'bt term) list
  | StructMember of 'bt term * BT.member

and 'bt pointer_op = 
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
  | Representable of CT.t * 'bt term
  | Good of CT.t * 'bt term
  | AlignedI of {t : 'bt term; align : 'bt term}
  | Aligned of 'bt term * CT.t

and 'bt array_op = 
  | Const of BT.t * 'bt term
  | Set of 'bt term * 'bt term * 'bt term
  | Get of 'bt term * 'bt term
  | Def of (Sym.t * BT.t) * 'bt term

and 'bt term_ =
  | Lit of lit
  | Arith_op of 'bt arith_op
  | Bool_op of 'bt bool_op
  | Tuple_op of 'bt tuple_op
  | Struct_op of 'bt struct_op
  | Pointer_op of 'bt pointer_op
  | List_op of 'bt list_op
  | Set_op of 'bt set_op
  | CT_pred of 'bt ct_pred
  | Array_op of 'bt array_op

and 'bt term =
  | IT of 'bt term_ * 'bt





type typed = BT.t term
type untyped = unit term

type it = typed
type t = typed



let bt (IT (_, bt)) : BT.t = bt


let rec equal (IT (it, _)) (IT (it', _)) = 
  match it, it' with
  | Lit lit, Lit lit' -> 
     begin match lit, lit' with
     | Sym sym, Sym sym' -> Sym.equal sym sym'
     | Z n, Z n' -> Z.equal n n'
     | Q q, Q q' -> Q.equal q q'
     | Pointer p, Pointer p' -> Z.equal p p'
     | Bool b, Bool b' -> b = b'
     | Unit, Unit -> true
     | Default bt, Default bt' -> BT.equal bt bt'
     | Null, Null -> true
     | Sym _, _ -> false
     | Z _, _ -> false
     | Q _, _ -> false
     | Pointer _, _ -> false
     | Bool _, _ -> false
     | Unit, _ -> false
     | Default _, _ -> false
     | Null, _ -> false
     end
  | Arith_op arith_op, Arith_op arith_op' -> 
     begin match arith_op, arith_op' with
     | Add (t1,t2), Add (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Sub (t1,t2), Sub (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Mul (t1,t2), Mul (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Div (t1,t2), Div (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Exp (t1,t2), Exp (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Rem (t1,t2), Rem (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | Mod (t1,t2), Mod (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | LT (t1,t2), LT (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | LE (t1,t2), LE (t1',t2') -> equal t1 t1' && equal t2 t2' 
     | IntToReal t, IntToReal t' -> equal t t'
     | RealToInt t, RealToInt t' -> equal t t'
     | Add _, _ -> false
     | Sub _, _ -> false
     | Mul _, _ -> false 
     | Div _, _ -> false
     | Exp _, _ -> false
     | Rem _, _ -> false
     | Mod _, _ -> false
     | LT _, _ -> false
     | LE _, _ -> false
     | IntToReal _, _ -> false
     | RealToInt _, _ -> false
     end
  | Bool_op bool_op, Bool_op bool_op' -> 
     begin match bool_op, bool_op' with
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
     | EachI ((i1, s, i2), t), EachI ((i1', s', i2'), t') ->
        i1 = i1' && Sym.equal s s' && i2 = i2' && equal t t'
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
     | EachI _, _ ->
        false
     end
  | Tuple_op tuple_op, Tuple_op tuple_op' -> 
     begin match tuple_op, tuple_op' with
     | Tuple ts, Tuple ts' -> List.equal equal ts ts'
     | NthTuple (n,t), NthTuple (n',t') -> n = n' && equal t t' 
     | Tuple _, _ -> false
     | NthTuple _, _ -> false
     end
  | Struct_op struct_op, Struct_op struct_op' -> 
     begin match struct_op, struct_op' with
     | Struct (tag, members), Struct (tag2, members2) ->
        Sym.equal tag tag2 && 
          List.equal (fun (m,t) (m',t') -> Id.equal m m' && equal t t') 
            members members2
     | StructMember (t,member), StructMember (t',member') ->
        equal t t' && Id.equal member member'
     | Struct _, _ -> false
     | StructMember _, _ -> false
     end
  | Pointer_op pointer_op, Pointer_op pointer_op' -> 
     begin match pointer_op, pointer_op' with
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
     | AddPointer _, _ -> false
     | SubPointer _, _ -> false
     | MulPointer _, _ -> false
     | LTPointer _, _ -> false
     | LEPointer _, _ -> false
     | IntegerToPointerCast _, _ -> false
     | PointerToIntegerCast _, _ -> false
     | MemberOffset _, _ -> false
     | ArrayOffset _, _ -> false
     end
  | List_op list_op, List_op list_op' -> 
     begin match list_op, list_op' with
     | Nil, Nil -> true
     | Cons (t1,t2), Cons (t1',t2') -> equal t1 t1' && equal t2 t2'
     | List its, List its' -> List.equal equal its its'
     | Head t, Head t' -> equal t t'
     | Tail t, Tail t' -> equal t t'
     | NthList (n,t), NthList (n',t') -> n = n' && equal t t'
     | Nil, _ -> false
     | Cons _, _ -> false
     | List _, _ -> false
     | Head _, _ -> false
     | Tail _, _ -> false
     | NthList _, _ -> false
     end
  | Set_op set_op, Set_op set_op' -> 
     begin match set_op, set_op' with
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
     end
  | CT_pred ct_pred, CT_pred ct_pred' -> 
     begin match ct_pred, ct_pred' with
     | Aligned (t, ct), Aligned (t', ct') ->
        equal t t' && CT.equal ct ct'
     | AlignedI t1, AlignedI t2 ->
        equal t1.t t2.t && equal t1.align t2.align
     | Representable (rt, t), Representable (rt', t') ->
        CT.equal rt rt' && equal t t'
     | Good (rt, t), Good (rt', t') ->
        CT.equal rt rt' && equal t t'
     | Aligned _, _ -> false
     | AlignedI _, _ -> false
     | Representable _, _ -> false
     | Good _, _ -> false
     end
  | Array_op array_op, Array_op array_op' -> 
     begin match array_op, array_op' with
     | Const (bt, t), Const (bt', t') ->
        BT.equal bt bt' && equal t t'
     | Set (t1,t2,t3), Set (t1',t2',t3') ->
        equal t1 t1' && equal t2 t2' && equal t3 t3'
     | Get (t, args), Get (t', args') ->
        equal t t' && equal args args'
     | Def ((s, abt), body), Def ((s', abt'), body') ->
        Sym.equal s s' && BT.equal abt abt' && equal body body'
     | Const _, _ -> false
     | Set _, _ -> false
     | Get _, _ -> false
     | Def _, _ -> false
     end
  | Lit _, _ -> false
  | Arith_op _, _ -> false
  | Bool_op _, _ -> false
  | Tuple_op _, _ -> false
  | Struct_op _, _ -> false
  | Pointer_op _, _ -> false
  | List_op _, _ -> false
  | Set_op _, _ -> false
  | CT_pred _, _ -> false
  | Array_op _, _ -> false






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
       | IntToReal t ->
          c_app !^"intToReal" [aux false t]
       | RealToInt t ->
          c_app !^"realToInt" [aux false t]
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
          mparens (!^"not" ^^^ aux true o1)
       | ITE (o1,o2,o3) -> 
          mparens (flow (break 1) [aux true o1; !^"?"; aux true o2; colon; aux true o3])
       | EQ (o1,o2) -> 
          mparens (flow (break 1) [aux true o1; equals ^^ equals; aux true o2])
       | EachI ((i1, s, i2), t) ->
          mparens (c_app ((c_app !^"foreach" [!^(string_of_int i1); Sym.pp s; !^(string_of_int i2)])) [aux false t])
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
          c_app !^"union" (List.map (aux false) (List1.to_list ts))
       | SetIntersection ts ->
          c_app !^"intersection" (List.map (aux false) (List1.to_list ts))
       | SetDifference (t1, t2) ->
          c_app !^"difference" [aux false t1; aux false t2]
       | Subset (t1, t2) ->
          c_app !^"subset" [aux false t1; aux false t2]
       end
    | Array_op array_op -> 
       begin match array_op with
       | Const (_, t) ->
          braces (aux false t)
       | Set (t1,t2,t3) ->
          mparens (aux true t1 ^^ lbracket ^^ aux false t2 ^^^ equals ^^^ aux false t3 ^^ rbracket)
       | Get (t, args) ->
          mparens ((aux true t) ^^ brackets (aux false args))
       | Def ((s, abt), body) ->
          braces (BT.pp abt ^^^ Sym.pp s ^^^ !^"->" ^^^ aux false body)
       end
  in
  fun (it : 'bt term) -> aux false it



let rec free_vars : 'bt. 'bt term -> SymSet.t =
  fun (IT (it, _)) ->
  match it with
  | Lit lit -> 
     begin match lit with
     | Sym symbol -> SymSet.singleton symbol
     | Z _ -> SymSet.empty
     | Q _ -> SymSet.empty
     | Pointer _ -> SymSet.empty
     | Bool _ -> SymSet.empty
     | Unit -> SymSet.empty
     | Default _ -> SymSet.empty
     | Null -> SymSet.empty
     end
  | Arith_op arith_op -> 
     begin match arith_op with
     | Add (it, it') -> free_vars_list [it; it']
     | Sub (it, it') -> free_vars_list [it; it']
     | Mul (it, it') -> free_vars_list [it; it']
     | Div (it, it') -> free_vars_list [it; it']
     | Exp (it, it') -> free_vars_list [it; it']
     | Rem (it, it') -> free_vars_list [it; it']
     | Mod (it, it') -> free_vars_list [it; it']
     | LT (it, it') -> free_vars_list [it; it']
     | LE (it, it') -> free_vars_list [it; it']
     | IntToReal t -> free_vars t
     | RealToInt t -> free_vars t
     end
  | Bool_op bool_op ->
     begin match bool_op with
     | And its -> free_vars_list its
     | Or its -> free_vars_list its
     | Impl (it, it') -> free_vars_list [it; it']
     | Not it -> free_vars it
     | ITE (it,it',it'') -> free_vars_list [it;it';it'']
     | EQ (it, it') -> free_vars_list [it; it']
     | EachI ((_, s, _), t) -> SymSet.remove s (free_vars t)
     end
  | Tuple_op tuple_op -> 
     begin match tuple_op with
     | Tuple its -> free_vars_list its
     | NthTuple ( _, it) -> free_vars it
     end
  | Struct_op struct_op -> 
     begin match struct_op with
     | Struct (_tag, members) -> free_vars_list (map snd members)
     | StructMember (it, s) -> free_vars_list [it;it]
     end
  | Pointer_op pointer_op ->
     begin match pointer_op with
     | AddPointer (it, it') -> free_vars_list [it; it']
     | SubPointer (it, it') -> free_vars_list [it; it']
     | MulPointer (it, it') -> free_vars_list [it; it']
     | LTPointer (it, it')  -> free_vars_list [it; it']
     | LEPointer (it, it') -> free_vars_list [it; it']
     | IntegerToPointerCast t -> free_vars t
     | PointerToIntegerCast t -> free_vars t
     | MemberOffset (_, _) -> SymSet.empty
     | ArrayOffset (_, t) -> free_vars t
     end
  | CT_pred ct_pred ->
     begin match ct_pred with
     | Aligned (t, _rt) -> free_vars t
     | AlignedI t -> free_vars_list [t.t; t.align]
     | Representable (_rt,t) -> free_vars t
     | Good (_rt,t) -> free_vars t
     end
  | List_op list_op ->
     begin match list_op with
     | Nil  -> SymSet.empty
     | Cons (it, it') -> free_vars_list [it; it']
     | List its -> free_vars_list its
     | Head it -> free_vars it
     | Tail it -> free_vars it
     | NthList (_,it) -> free_vars it
     end
  | Set_op set_op ->
     begin match set_op with
     | SetMember (t1,t2) -> free_vars_list [t1;t2]
     | SetUnion ts -> free_vars_list (List1.to_list ts)
     | SetIntersection ts -> free_vars_list (List1.to_list ts)
     | SetDifference (t1, t2) -> free_vars_list [t1;t2]
     | Subset (t1, t2) -> free_vars_list [t1;t2]
     end
  | Array_op array_op -> 
     begin match array_op with
     | Const (_, t) -> free_vars t
     | Set (t1,t2,t3) -> free_vars_list [t1;t2;t3]
     | Get (t, arg) -> free_vars_list ([t; arg])
     | Def ((s, _), body) -> SymSet.remove s (free_vars body)
     end

and free_vars_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (free_vars sym)
    ) SymSet.empty l



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
       | IntToReal it -> IntToReal (subst su it)
       | RealToInt it -> RealToInt (subst su it)
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
       | AddPointer (it, it') -> 
          AddPointer (subst su it, subst su it')
       | SubPointer (it, it') -> 
          SubPointer (subst su it, subst su it')
       | MulPointer (it, it') -> 
          MulPointer (subst su it, subst su it')
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
       | SetUnion ts -> SetUnion (List1.map (subst su) ts)
       | SetIntersection ts -> SetIntersection (List1.map (subst su) ts)
       | SetDifference (t1, t2) -> SetDifference (subst su t1, subst su t2)
       | Subset (t1, t2) -> Subset (subst su t1, subst su t2)
     in
     IT (Set_op set_op, bt)
  | Array_op array_op -> 
     let array_op = match array_op with
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
     IT (Array_op array_op, bt)





let rec size (IT (it_, bt)) =
  match it_ with
  | Lit _ -> 1
  | Arith_op arith_op ->
     begin match arith_op with
     | Add (it, it')
     | Sub (it, it')
     | Mul (it, it')
     | Div (it, it')
     | Exp (it, it')
     | Rem (it, it')
     | Mod (it, it')
     | LT (it, it')
     | LE (it, it') 
       -> 1 + size it + size it'
     | IntToReal it
     | RealToInt it ->
        1 + size it
     end
  | Bool_op bool_op ->
     begin match bool_op with
     | And its -> 1 + size_list its
     | Or its -> 1 + size_list its
     | Impl (it, it') -> 1 + size it + size it'
     | Not it -> 1 + size it
     | ITE (it, it', it'') -> 1 + size_list [it; it'; it'']
     | EQ (it, it') -> 1 + size it + size it'
     | EachI (_, it) -> 1 + size it
     end
  | Tuple_op tuple_op ->
     begin match tuple_op with
     | Tuple its -> 1 + size_list its
     | NthTuple (_, it) -> 1 + size it
     end
  | Struct_op struct_op ->
     begin match struct_op with
     | Struct (_, members) -> 1 + size_list (List.map snd members)
     | StructMember (it, _) -> 1 + size it
     end
  | Pointer_op pointer_op ->
     begin match pointer_op with
     | AddPointer (it, it')
     | SubPointer (it, it')
     | MulPointer (it, it')
     | LTPointer (it, it')
     | LEPointer (it, it') ->
        1 + size it + size it'
     | IntegerToPointerCast it -> 1 + size it
     | PointerToIntegerCast it -> 1 + size it
     | MemberOffset _ -> 1
     | ArrayOffset (_, it) -> 1 + size it
     end
  | List_op list_op ->
     begin match list_op with
     | Nil -> 1
     | Cons (it, it') -> 1 + size it + size it'
     | List its -> 1 + size_list its
     | Head it -> 1 + size it
     | Tail it -> 1 + size it
     | NthList (_, it) -> 1 + size it
     end
  | Set_op set_op ->
     begin match set_op with
     | SetMember (it, it') -> 1 + size it + size it'
     | SetUnion its -> 1 + size_list (List1.to_list its)
     | SetIntersection its -> 1 + size_list (List1.to_list its)
     | SetDifference (it, it') -> 1 + size it + size it'
     | Subset (it, it') -> 1 + size it + size it'
     end
  | CT_pred ct_pred ->
     begin match ct_pred with
     | Representable (_, it) -> 1 + size it
     | Good (_, it) -> 1 + size it
     | AlignedI a -> 1 + size a.t + size a.align
     | Aligned (it, _) -> 1 + size it
     end
  | Array_op array_op ->
     begin match array_op with
     | Const (_, it) -> 1 + size it
     | Set (it, it', it'') -> 1 + size_list [it;it';it'']
     | Get (it, it') -> 1 + size it + size it'
     | Def (_, it) -> 1 + size it
     end

and size_list its = 
  List.fold_right (fun it acc -> acc + size it) its 0




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

let is_app = function
  | IT (Array_op (Get (f,arg)), _) -> Some (f, arg)
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
let not_ it = IT (Bool_op (Not it), BT.Bool)
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
let exp_ (it, it') = IT (Arith_op (Exp (it, it')), bt it)
let rem_ (it, it') = IT (Arith_op (Rem (it, it')), BT.Integer)
let mod_ (it, it') = IT (Arith_op (Mod (it, it')), BT.Integer)
let rem_t___ (it, it') = rem_ (it, it')
let rem_f___ (it, it') = rem_ (it, it')
let min_ (it, it') = ite_ (le_ (it, it'), it, it')
let max_ (it, it') = ite_ (ge_ (it, it'), it, it')
let intToReal_ it = IT (Arith_op (IntToReal it), BT.Real)
let realToInt_ it = IT (Arith_op (RealToInt it), BT.Integer)

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
let null_ = IT (Lit Null, BT.Loc)
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
let good_ (t, it) = 
  IT (CT_pred (Good (t, it)), BT.Bool)
let aligned_ (t, it) = 
  IT (CT_pred (Aligned (t, it)), BT.Bool)
let alignedI_ ~t ~align = 
  IT (CT_pred (AlignedI {t; align}), BT.Bool)

let const_ index_bt t = 
  IT (Array_op (Const (index_bt, t)), BT.Array (index_bt, bt t))
let set_ t1 (t2, t3) = 
  IT (Array_op (Set (t1, t2, t3)), bt t1)
let get_ v arg = 
  match bt v with
  | BT.Array (_, rbt) ->
     IT (Array_op (Get (v, arg)), rbt)
  | _ -> Debug_ocaml.error "illtyped index term"
let array_def_ (s, abt) body = 
  IT (Array_op (Def ((s, abt), body)), BT.Array (abt, bt body))



let (%@) it it' = get_ it it'






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
  | Arith_op _ -> 1
  | Bool_op _ -> 2
  | Tuple_op _ -> 3
  | Struct_op _ -> 4
  | Pointer_op _ -> 5
  | CT_pred _ -> 6
  | List_op _ -> 7
  | Set_op _ -> 8
  | Array_op _ -> 9
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




let in_pointer_range pointer =
  let pointer_bits = Memory.size_of_pointer * Memory.bits_per_byte in
  and_ [lePointer_ (pointer_ Z.zero, pointer); 
        ltPointer_ (pointer, pointer_ (Z.pow (Z.of_int 2) pointer_bits))]

let value_check_pointer alignment ~pointee_ct about = 
  let pointee_size = match pointee_ct with
    | Sctypes.Sctype (_, Void) -> 1
    | Sctypes.Sctype (_, Function _) -> 1
    | _ -> Memory.size_of_ctype pointee_ct 
  in
  and_ [in_pointer_range about;
        in_pointer_range (subPointer_ (addPointer_ (about, int_ pointee_size), int_ 1));
        if alignment then aligned_ (about, pointee_ct) else bool_ true]

let value_check alignment (struct_layouts : Memory.struct_decls) ct about =
  let open Sctypes in
  let open Memory in
  let rec aux (Sctype (_, ct_) : Sctypes.t) about = 
    match ct_ with
    | Void -> 
       bool_ true
    | Integer it -> 
       in_range about (z_ (min_integer_type it), z_ (max_integer_type it))
    | Array (it, None) -> 
       Debug_ocaml.error "todo: 'representable' for arrays with unknown length"
    | Array (ict, Some n) -> 
       let i_s, i = fresh BT.Integer in
       eachI_ (0, i_s, n - 1) (aux ict (get_ about i))
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



