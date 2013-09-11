Require Import BinPos.
Require Import String.

(* Strings (constants, identifiers, pragmas), stored in Ocaml data
   structure. *)
Definition atom := string.

(* Context information. *)
Definition cabsloc := positive.

Inductive typeSpecifier := (* Merge all specifiers into one type *)
  | Tvoid                 (* Type specifier ISO 6.7.2 *)
  | Tchar
  | Tshort
  | Tint
  | Tlong
  | Tfloat
  | Tdouble
  | Tsigned
  | Tunsigned
  | T_Bool
  | Tnamed : atom -> typeSpecifier
  (* each of the following three kinds of specifiers contains a field
   * or list item iff it corresponds to a definition (as opposed to
   * a forward declaration or simple reference to the type).
   * They also have a list of __attribute__s that appeared between the
   * keyword and the type name (definitions only) *)
  | Tatomic : (list spec_elem * decl_type) -> typeSpecifier
  | Tstruct : option atom -> option (list field_group) -> list attribute -> typeSpecifier
  | Tunion : option atom -> option (list field_group) -> list attribute -> typeSpecifier
  | Tenum : option atom -> option (list (atom * option expression * cabsloc)) -> list attribute -> typeSpecifier

with storage :=
  AUTO | STATIC | EXTERN | REGISTER | THREAD_LOCAL | TYPEDEF

with cvspec :=
  CV_CONST | CV_VOLATILE | CV_RESTRICT | CV_ATOMIC

(* Type specifier elements. These appear at the start of a declaration *)
(* Everywhere they appear in this file, they appear as a 'list spec_elem', *)
(* which is not interpreted by cabs -- rather, this "word soup" is passed *)
(* on to the compiler.  Thus, we can represent e.g. 'int long float x' even *)
(* though the compiler will of course choke. *)
with spec_elem :=
  | SpecCV : cvspec -> spec_elem            (* const/volatile *)
  | SpecAttr : attribute -> spec_elem
  | SpecStorage : storage -> spec_elem
  | SpecInline
  | SpecType : typeSpecifier -> spec_elem

(* Declarator type. They modify the base type given in the specifier. Keep
 * them in the order as they are printed (this means that the top level
 * constructor for ARRAY and PTR is the inner-level in the meaning of the
 * declared type) *)
with decl_type :=
 | JUSTBASE
 | ARRAY : decl_type -> list cvspec -> list attribute -> option expression -> decl_type
 | PTR : list cvspec -> list attribute -> decl_type -> decl_type
(* The bool is true for variable length parameters. *)
 | PROTO : decl_type -> list parameter * bool -> decl_type

with parameter :=
  | PARAM : list spec_elem -> option atom -> decl_type -> list attribute -> cabsloc -> parameter

(* The optional expression is the bitfield *)
with field_group := 
  | Field_group : list spec_elem -> list (option name * option expression) -> cabsloc -> field_group

(* The decl_type is in the order in which they are printed. Only the name of
 * the declared identifier is pulled out. *)
(* e.g: in "int *x", "*x" is the declarator; "x" will be pulled out as *)
(* the atom, and decl_type will be PTR([], JUSTBASE) *)
with name := 
  | Name : atom -> decl_type -> list attribute -> cabsloc -> name

(* A variable declarator ("name") with an initializer *)
with init_name := 
  | Init_name : name -> init_expression -> init_name

(*
** Expressions
*)
with binary_operator :=
  | ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | BAND | BOR | XOR | SHL | SHR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
  | COMMA

with unary_operator :=
  | MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

with expression :=
  | UNARY : unary_operator -> expression -> expression
  | BINARY : binary_operator -> expression -> expression -> expression
  | QUESTION : expression -> expression -> expression -> expression

    (* A CAST can actually be a constructor expression *)
  | CAST : (list spec_elem * decl_type) -> init_expression -> expression
  
  (* NOTE: we extend the syntax with builtin C11 atomic operation (the way clang does) *)
  | C11_ATOMIC_INIT : expression -> expression -> expression
  | C11_ATOMIC_STORE : expression -> expression -> expression -> expression
  | C11_ATOMIC_LOAD : expression -> expression -> expression
  | C11_ATOMIC_EXCHANGE : expression -> expression -> expression -> expression
  | C11_ATOMIC_COMPARE_EXCHANGE_STRONG : expression -> expression -> expression -> expression -> expression -> expression
  | C11_ATOMIC_COMPARE_EXCHANGE_WEAK : expression -> expression -> expression -> expression -> expression -> expression
  | C11_ATOMIC_FETCH_KEY : expression -> expression -> expression -> expression
  
  | CALL : expression -> list expression -> expression
  | BUILTIN_VA_ARG : expression -> list spec_elem * decl_type -> expression
  | CONSTANT : constant -> expression
  | VARIABLE : atom -> expression
  | EXPR_SIZEOF : expression -> expression
  | TYPE_SIZEOF : (list spec_elem * decl_type) -> expression
  | ALIGNOF : (list spec_elem * decl_type) -> expression
  | INDEX : expression -> expression -> expression
  | MEMBEROF : expression -> atom -> expression
  | MEMBEROFPTR : expression -> atom -> expression
  | OFFSETOF : (list spec_elem * decl_type) -> atom -> expression

with integer_suffix :=
  | SUFFIX_UNSIGNED
  | SUFFIX_UNSIGNED_LONG
  | SUFFIX_UNSIGNED_LONG_LONG
  | SUFFIX_LONG
  | SUFFIX_LONG_LONG

with character_prefix :=
  | PREFIX_L
  | PREFIX_u
  | PREFIX_U

with encoding_prefix :=
  | ENCODING_u8
  | ENCODING_u
  | ENCODING_U
  | ENCODING_L

with constant :=
  (* The atom is the textual representation of the constant in
     the source code. It does include quotes. *)
  | CONST_INT : atom -> option integer_suffix -> constant
  | CONST_FLOAT : atom -> constant
  | CONST_CHAR : option character_prefix -> atom -> constant
  | CONST_STRING : (* TODO: option encoding_prefix -> *) atom -> constant

with init_expression :=
  | NO_INIT
  | SINGLE_INIT : expression -> init_expression
  | COMPOUND_INIT : list (list initwhat * init_expression) -> init_expression

with initwhat :=
  | INFIELD_INIT : atom -> initwhat
  | ATINDEX_INIT : expression -> initwhat

with attribute :=
  | ATTR : atom -> list expression -> attribute.

(* like name_group, except the declared variables are allowed to have initializers *)
(* e.g.: int x=1, y=2; *)
Definition init_name_group := (list spec_elem * list init_name)%type.

(* The base type and the storage are common to all names. Each name might
 * contain type or storage modifiers *)
(* e.g.: int x, y; *)
Definition name_group := (list spec_elem * list name)%type.

(*
** Declaration definition (at toplevel)
*)
Inductive definition :=
 | FUNDEF           : list spec_elem -> name -> statement -> cabsloc -> definition
 | DECDEF           : init_name_group -> cabsloc -> definition  (* global variable(s), or function prototype *)
 | PRAGMA           : atom -> cabsloc -> definition

(*
** statements
*)

with statement :=
 | NOP : cabsloc -> statement
 | COMPUTATION : expression -> cabsloc -> statement
 | BLOCK : list statement -> cabsloc -> statement
 | If : expression -> statement -> option statement -> cabsloc -> statement
 | WHILE : expression -> statement -> cabsloc -> statement
 | DOWHILE : expression -> statement -> cabsloc -> statement
 | FOR : option for_clause -> option expression -> option expression -> statement -> cabsloc -> statement
 | BREAK : cabsloc -> statement
 | CONTINUE : cabsloc -> statement
 | RETURN : option expression -> cabsloc -> statement
 | SWITCH : expression -> statement -> cabsloc -> statement
 | CASE : expression -> statement -> cabsloc -> statement
 | DEFAULT : statement -> cabsloc -> statement
 | LABEL : atom -> statement -> cabsloc -> statement
 | GOTO : atom -> cabsloc -> statement
 | DEFINITION : definition -> statement (*definition or declaration of a variable or type*)
 | PAR : list statement -> cabsloc -> statement (* TODO: this is a fake syntax for thread creation (with direct join) *)

with for_clause :=
 | FC_EXP : expression -> for_clause
 | FC_DECL : definition -> for_clause.
