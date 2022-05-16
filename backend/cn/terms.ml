type lit = 
  | Sym of Sym.t
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
  | Min of 'bt term * 'bt term
  | Max of 'bt term * 'bt term
  | IntToReal of 'bt term
  | RealToInt of 'bt term
  | XOR of Sctypes.IntegerTypes.t * 'bt term * 'bt term

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
  | Struct of BaseTypes.tag * (BaseTypes.member * 'bt term) list
  | StructMember of 'bt term * BaseTypes.member
  | StructUpdate of ('bt term * BaseTypes.member) * 'bt term

and 'bt record_op =
  | Record of (Sym.t * 'bt term) list
  | RecordMember of 'bt term * Sym.t
  | RecordUpdate of ('bt term * Sym.t) * 'bt term

and 'bt pointer_op = 
  | LTPointer of 'bt term * 'bt term
  | LEPointer of 'bt term * 'bt term
  | IntegerToPointerCast of 'bt term
  | PointerToIntegerCast of 'bt term
  | MemberOffset of BaseTypes.tag * Id.t
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
  | SetUnion of ('bt term) list
  | SetIntersection of ('bt term) list
  | SetDifference of 'bt term * 'bt term
  | Subset of 'bt term * 'bt term

and 'bt ct_pred = 
  | Representable of Sctypes.t * 'bt term
  | Good of Sctypes.t * 'bt term
  | AlignedI of {t : 'bt term; align : 'bt term}
  | Aligned of 'bt term * Sctypes.t

and 'bt map_op = 
  | Const of BaseTypes.t * 'bt term
  | Set of 'bt term * 'bt term * 'bt term
  | Get of 'bt term * 'bt term
  | Def of (Sym.t * BaseTypes.t) * 'bt term

and 'bt term_ =
  | Lit of lit
  | Arith_op of 'bt arith_op
  | Bool_op of 'bt bool_op
  | Tuple_op of 'bt tuple_op
  | Struct_op of 'bt struct_op
  | Record_op of 'bt record_op
  | Pointer_op of 'bt pointer_op
  | List_op of 'bt list_op
  | Set_op of 'bt set_op
  | CT_pred of 'bt ct_pred
  | Map_op of 'bt map_op
  | Info of string * ('bt term) list
  | Pred of string * ('bt term) list

and 'bt term =
  | IT of 'bt term_ * 'bt
[@@deriving eq, ord]


let equal = equal_term
let compare = compare_term
