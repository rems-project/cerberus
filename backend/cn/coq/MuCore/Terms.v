Require Import ZArith.
Require Import String.
Require Import List.
Require Import QArith.
Require Import Symbol.
Require Import BaseTypes.
Require Import Location.
Require Import SCtypes.
Require Import IntegerType.
(* Constants *)
Inductive const : Type :=
  | Z : Z -> const
  | Bits : (BaseTypes.sign * nat) * Z -> const
  | Q : Q -> const  (* Note: Q needs to be defined or imported *)
  | MemByte : Z * Z -> const  (* alloc_id * value *)
  | Pointer : Z * Z -> const  (* alloc_id * addr *)
  | Alloc_id : Z -> const
  | Bool : bool -> const
  | Unit : const
  | Null : const
  | CType_const : Type -> const  (* simplified from ctype *)
  | Default : BaseTypes.t -> const.

(* Unary operators *)
Inductive unop : Type :=
  | Not : unop
  | Negate : unop
  | BW_CLZ_NoSMT : unop
  | BW_CTZ_NoSMT : unop
  | BW_FFS_NoSMT : unop
  | BW_FLS_NoSMT : unop
  | BW_Compl : unop.

(* Binary operators *)
Inductive binop : Type :=
  | And : binop
  | Or : binop
  | Implies : binop
  | Add : binop
  | Sub : binop
  | Mul : binop
  | MulNoSMT : binop
  | Div : binop
  | DivNoSMT : binop
  | Exp : binop
  | ExpNoSMT : binop
  | Rem : binop
  | RemNoSMT : binop
  | Mod : binop
  | ModNoSMT : binop
  | BW_Xor : binop
  | BW_And : binop
  | BW_Or : binop
  | ShiftLeft : binop
  | ShiftRight : binop
  | LT : binop
  | LE : binop
  | Min : binop
  | Max : binop
  | EQ : binop
  | LTPointer : binop
  | LEPointer : binop
  | SetUnion : binop
  | SetIntersection : binop
  | SetDifference : binop
  | SetMember : binop
  | Subset : binop.

(* Patterns *)
Inductive pattern_ (bt : Type) : Type :=
  | PSym : sym -> pattern_ bt
  | PWild : pattern_ bt
  | PConstructor : sym -> list (Symbol.identifier * pattern bt) -> pattern_ bt

with pattern (bt : Type) : Type :=
  | Pat : pattern_ bt -> bt -> Location_t -> pattern bt.

(* Terms *)
Inductive term (bt : Type) : Type :=
  | Const : const -> term bt
  | Sym : sym -> term bt
  | Unop : unop -> annot bt -> term bt
  | Binop : binop -> annot bt -> annot bt -> term bt
  | ITE : annot bt -> annot bt -> annot bt -> term bt
  | EachI : (nat * (sym * BaseTypes.t) * nat) -> annot bt -> term bt
  | Tuple : list (annot bt) -> term bt
  | NthTuple : nat -> annot bt -> term bt
  | Struct : sym -> list (Symbol.identifier * annot bt) -> term bt
  | StructMember : annot bt -> Symbol.identifier -> term bt
  | StructUpdate :  (annot bt * Symbol.identifier) -> annot bt -> term bt
  | Record : list (Symbol.identifier * annot bt) -> term bt
  | RecordMember : annot bt -> Symbol.identifier -> term bt
  | RecordUpdate :  (annot bt * Symbol.identifier) -> annot bt -> term bt
  | Constructor : sym -> list (Symbol.identifier * annot bt) -> term bt
  | MemberShift : annot bt -> sym -> Symbol.identifier -> term bt
  | ArrayShift : annot bt -> Type -> annot bt -> term bt  (* base * ct * index *)
  | CopyAllocId : annot bt -> annot bt -> term bt  (* addr * loc *)
  | HasAllocId : annot bt -> term bt
  | SizeOf : SCtypes.t -> term bt 
  | OffsetOf : sym -> Symbol.identifier -> term bt
  | Nil : BaseTypes.t -> term bt
  | Cons : annot bt -> annot bt -> term bt
  | Head : annot bt -> term bt
  | Tail : annot bt -> term bt
  | NthList : annot bt -> annot bt -> annot bt -> term bt
  | ArrayToList : annot bt -> annot bt -> annot bt -> term bt
  | Representable : SCtypes.t -> annot bt -> term bt  
  | Good : SCtypes.t -> annot bt -> term bt  
  | Aligned : annot bt -> annot bt -> term bt  (* t * align *)
  | WrapI : IntegerType.t  -> annot bt -> term bt 
  | MapConst : BaseTypes.t -> annot bt -> term bt
  | MapSet : annot bt -> annot bt -> annot bt -> term bt
  | MapGet : annot bt -> annot bt -> term bt
  | MapDef : (sym * BaseTypes.t) -> annot bt -> term bt
  | Apply : sym -> (list  (annot bt)) -> term bt
  | Let : (sym * annot bt) -> annot bt -> term bt
  | _Match : annot bt -> list (pattern bt * annot bt) -> term bt
  | Cast : BaseTypes.t -> annot bt -> term bt

with annot (bt : Type) : Type :=
  | IT : term bt -> bt -> Location_t -> annot bt. 