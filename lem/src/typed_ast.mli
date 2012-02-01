(* Sets of Names *)
module NameSet : Set.S with type elt = Name.t and type t = Set.Make(Name).t

(* Name keyed finite maps *)
module Nfmap : Finite_map.Fmap with type k = Name.t

type name_l = Name.lskips_t * Ast.l

(* Whitespace, comments, and newlines *)
type lskips = Ast.lex_skips

type 'a lskips_seplist = ('a, lskips) Seplist.t

(* The empty lskip *)
val no_lskips : lskips

(* A space lskip *)
val space : lskips

(* Get only the comments (and a trailing space) *)
val lskips_only_comments : lskips list -> lskips

val ast_target_compare : Ast.target -> Ast.target -> int

type target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex

val target_compare : target -> target -> int

(* target keyed finite maps *)
module Targetmap : Finite_map.Fmap with type k = target

val target_to_string : target -> string
val target_to_output : Output.id_annot -> Ast.target -> Output.t
val target_to_mname : target -> Name.t

(* What kind of top-level definition a particular constant is *)
type kind = 
  (* A (data) constructor *)
  | K_ctor

  (* A class method *)
  | K_method

  (* A val specification *)
  | K_spec

  (* A definition *)
  | K_let

  (* A target-specific definition *)
  | K_target of target

(* Sets of kinds *)
module Kset : Set.S with type elt = kind

type ('a,'b) annot = { term : 'a; locn : Ast.l; typ : Types.t; rest : 'b }
val annot_to_typ : ('a,'b) annot -> Types.t

(* Represents a (data) constructor *)
type constr_descr = 
  { 
    (* The path to the constructor's definition *)
    constr_binding : Path.t; 
    
    (* Its type parameters *)
    constr_tparams : Tyvar.t list; 
    
    (* The types of the constructor's arguments (can refer to the above type
     * parameters) *)
    constr_args : Types.t list; 
    
    (* The type constructor that the constructors value has.  Implicitly
    * parameterized by the above type parameters *)
    constr_tconstr : Path.t;
    
    (* The names of the other (data) constructors of the same type *)
    constr_names : NameSet.t; 
  }

(* Represents a field *)
type field_descr = 
    {
      (* The path to the field's definition *)
      field_binding : Path.t;

      (* Its type parameters *)
      field_tparams : Tyvar.t list;

      (* The type constructor of the record that the field belongs to.
      * Implicitly parameterized by the above type parameters *)
      field_tconstr : Path.t;

      (* The type of the field (can refer to the above type parameters) *)
      field_arg : Types.t;

      (* The names of the other fields of the same record type *)
      field_names : NameSet.t;
    }

type p_env = Path.t Nfmap.t

(* Represents a usage of an 'a (usually in constr_descr, field_descr,
 * const_descr) *)
type 'a id = 
    { 
      (* The identifier as written at the usage point *)
      id_path : Ident.t; 

      (* The location of the usage point *)
      id_locn : Ast.l;

      (* A description of the binding that the usage refers to *)
      descr : 'a; 

      (* The usage site instantiation of the type parameters of the definition *)
      instantiation : Types.t list;
    }


(* The AST.  lskips appear in the types wherever concrete syntactic elements
 * would appear (e.g., a keyword), and represent the comments and whitespace
 * that preceded that concrete element.  They do not represent the element
 * itself *)

and src_t = (src_t_aux,unit) annot

and src_t_aux = 
 | Typ_wild of lskips
 | Typ_var of lskips * Tyvar.t
 | Typ_fn of src_t * lskips * src_t
 | Typ_tup of src_t lskips_seplist
 | Typ_app of lskips * src_t lskips_seplist * lskips * Path.t id
 | Typ_paren of lskips * src_t * lskips

type lit = (lit_aux,unit) annot

and lit_aux =
  | L_true of lskips
  | L_false of lskips
  | L_num of lskips * int
  | L_string of lskips * string
  | L_unit of lskips * lskips

type pat = (pat_aux,pat_annot) annot
and pat_annot = { pvars : Types.t Nfmap.t }

and pat_aux = 
  | P_wild of lskips
  | P_as of pat * lskips * name_l
  | P_typ of lskips * pat * lskips * src_t * lskips
  | P_var of Name.lskips_t
  | P_constr of constr_descr id * pat list
  | P_record of lskips * (field_descr id * lskips * pat) lskips_seplist * lskips
  | P_tup of lskips * pat lskips_seplist * lskips
  | P_list of lskips * pat lskips_seplist * lskips
  | P_paren of lskips * pat * lskips
  | P_cons of pat * lskips * pat
  | P_lit of lit
  (* A type-annotated pattern variable.  This is redundant with the combination
  * of the P_typ and P_var cases above, but useful as a macro target. *)
  | P_var_annot of Name.lskips_t * src_t

(* The description of a top-level definition *)
and const_descr = 
  { 
    (* The path to the definition *)
    const_binding : Path.t;

    (* Its type parameters.  Must have length 1 for class methods. *)
    const_tparams : Tyvar.t list;

    (* Its class constraints (must refer to above type parameters).  Must have
     * length 1 for class methods *)
    const_class : (Path.t * Tyvar.t) list;

    (* Its type *)
    const_type : Types.t; 

    (* What kind of definition it is.  Must not contain K_ctor.  Must be a
    * singleton { K_method } or not contain K_method. 
    * TODO: add other invariants about the other cases *)
    kinds : Kset.t;

    (* The location for the first occurrence of a definition/specification of
     * this constant *)
    spec_l : Ast.l;

    (* Target-specific substitutions to use for this constant *)
    substitutions : ((Name.t,unit) annot list * exp) Targetmap.t; 
  }

and val_descr = 
  | Constr of constr_descr
  | Val of const_descr

and v_env = val_descr Nfmap.t

and f_env = field_descr Nfmap.t
and m_env = env Nfmap.t
and env = { m_env : m_env; p_env : p_env; f_env : f_env; v_env : v_env; }

and mod_descr = { mod_env : env; }

and exp
and exp_subst =
  | Sub of exp
  | Sub_rename of Name.t

and exp_aux = private
  | Var of Name.lskips_t
  | Constant of const_descr id
  | Constructor of constr_descr id
  | Tup_constructor of constr_descr id * lskips * exp lskips_seplist * lskips
  | Fun of lskips * pat list * lskips * exp
  | Function of lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | App of exp * exp
  (* The middle exp must be a Var, Constant, or Constructor *) 
  | Infix of exp * exp * exp
  | Record of lskips * fexp lskips_seplist * lskips
  | Record_coq of name_l * lskips * fexp lskips_seplist * lskips
  | Recup of lskips * exp * lskips * fexp lskips_seplist * lskips
  | Field of exp * lskips * field_descr id
  | Case of lskips * exp * lskips * (pat * lskips * exp * Ast.l) lskips_seplist * lskips
  | Typed of lskips * exp * lskips * src_t * lskips
  | Let of lskips * letbind * lskips * exp
  | Tup of lskips * exp lskips_seplist * lskips
  | List of lskips * exp lskips_seplist * lskips
  | Paren of lskips * exp * lskips
  | Begin of lskips * exp * lskips
  | If of lskips * exp * lskips * exp * lskips * exp
  | Lit of lit
  | Set of lskips * exp lskips_seplist * lskips
  | Setcomp of lskips * exp * lskips * exp * lskips * NameSet.t
  (* true for list comprehensions, false for set comprehensions *)
  | Comp_binding of bool * lskips * exp * lskips * lskips * quant_binding list * lskips * exp * lskips
  | Quant of Ast.q * quant_binding list * lskips * exp


and fexp = field_descr id * lskips * exp * Ast.l

and name_lskips_annot = (Name.lskips_t,unit) annot

and quant_binding = 
  | Qb_var of name_lskips_annot
  (* true for list quantifiers, false for set quantifiers *)
  | Qb_restr of bool * lskips * pat * lskips * exp * lskips

and funcl_aux = name_lskips_annot * pat list * (lskips * src_t) option * lskips * exp

and letbind = letbind_aux * Ast.l

and letbind_aux =
  | Let_val of pat * (lskips * src_t) option * lskips * exp
  | Let_fun of funcl_aux

type tyvar = lskips * BatRope.t * Ast.l

type texp = 
  | Te_opaque
  | Te_abbrev of lskips * src_t
  | Te_record of lskips * lskips * (name_l * lskips * src_t) lskips_seplist * lskips
  | Te_record_coq of lskips * name_l * lskips * (name_l * lskips * src_t) lskips_seplist * lskips
  | Te_variant of lskips * (name_l * lskips * src_t lskips_seplist) lskips_seplist
  | Te_variant_coq of lskips * (name_l * lskips * src_t lskips_seplist * name_l * tyvar lskips_seplist) lskips_seplist

type constraints = 
  | Cs_list of (lskips * Ident.t * tyvar * lskips) list * lskips

type constraint_prefix =
  | Cp_forall of lskips * tyvar list * lskips * constraints option

type typschm = constraint_prefix option * src_t

type instschm = constraint_prefix option * lskips * Ident.t * src_t * lskips

type val_spec = lskips * name_l * lskips * typschm

type class_val_spec = lskips * name_l * lskips * src_t

type targets_opt = (lskips * Ast.target lskips_seplist * lskips) option

type val_def = 
  | Let_def of lskips * targets_opt * letbind
  | Rec_def of lskips * lskips * targets_opt * funcl_aux lskips_seplist

type def = (def_aux * lskips option) * Ast.l

and def_aux =
  | Type_def of lskips * ((* ( *) lskips * 
                       tyvar lskips_seplist * 
                       (* ) *) lskips * 
                       name_l * texp) lskips_seplist
  (* The TVset contains the type variables that the definition is parameterized
   * over *)
  | Val_def of val_def * Types.TVset.t
  | Module of lskips * name_l * lskips * lskips * def list * lskips
  | Rename of lskips * name_l * lskips * mod_descr id
  | Open of lskips * mod_descr id
  | Indreln of lskips * targets_opt * 
               (lskips * name_lskips_annot list * lskips * exp * lskips * name_lskips_annot * exp list) lskips_seplist
  | Val_spec of val_spec
  | Subst of lskips * lskips * Ast.target * lskips * name_lskips_annot * name_lskips_annot list * lskips * exp
  | Class of lskips * lskips * name_l * tyvar * lskips * class_val_spec list * lskips
  | Instance of lskips * instschm * val_def list * lskips * v_env * Name.t

  (* Does not appear in the source, used to comment out definitions for certain
  * backends *)
  | Comment of def

val empty_env : env

val exp_to_locn : exp -> Ast.l
val exp_to_typ : exp -> Types.t

(* append_lskips adds new whitespace/newline/comments to the front of an
 * expression (before any existing whitespace/newline/comments in front of the
 * expression) *)
val append_lskips : lskips -> exp -> exp 
val pat_append_lskips : lskips -> pat -> pat

(* alter_init_lskips finds all of the whitespace/newline/comments preceding an
 * expression and passes it to the supplied function in a single invocation.
 * The preceding whitespace/newline/comments are replaced with the fst of the
 * function's result, and the snd of the function's result is returned from
 * alter_init_lskips *)
val pat_alter_init_lskips : (lskips -> lskips * lskips) -> pat -> pat * lskips
val alter_init_lskips : (lskips -> lskips * lskips) -> exp -> exp * lskips
val def_alter_init_lskips : (lskips -> lskips * lskips) -> def -> def * lskips

val unsat_constraint_err : Ast.l -> (Path.t * Tyvar.t) list -> unit
val pp_env : Format.formatter -> env -> unit
val pp_instances : Format.formatter -> Types.instance list Types.Pfmap.t -> unit

type checked_module =
    { filename : string;
      module_name : string;
      predecessor_modules : string list;
      untyped_ast : Ast.defs * Ast.lex_skips;
      typed_ast : def list * Ast.lex_skips; }

type var_avoid_f = (Name.t -> bool) * (BatRope.t -> (Name.t -> bool) -> Name.t)

module type Exp_context = sig
  (* Whether the constructor functions should do type checking too *)
  val check : Types.type_defs option
    (* Avoiding certain names for local variables.  Given a name and a set of
     * names that must be avoided, choose a new name if necessary *)
  val avoid : var_avoid_f option

end

module Exps_in_context(C : Exp_context) : sig
  val exp_subst : (Types.t Types.TVfmap.t * exp_subst Nfmap.t) -> exp -> exp
  val push_subst : (Types.t Types.TVfmap.t * exp_subst Nfmap.t) -> pat list -> exp -> pat list * exp
  val exp_to_term : exp -> exp_aux
  val exp_to_free : exp -> Types.t Nfmap.t
  val type_eq : Ast.l -> Types.t -> Types.t -> unit
  val mk_lnum : Ast.l -> lskips -> int -> Types.t option -> lit
  val mk_twild : Ast.l -> lskips -> Types.t -> src_t
  val mk_tvar : Ast.l -> lskips -> Tyvar.t -> Types.t -> src_t
  val mk_tfn : Ast.l -> src_t -> lskips -> src_t -> Types.t option -> src_t
  val mk_ttup : Ast.l -> src_t lskips_seplist -> Types.t option -> src_t
  val mk_tapp : Ast.l -> lskips -> src_t lskips_seplist -> lskips -> Path.t id -> Types.t option -> src_t
  val mk_tparen : Ast.l -> lskips -> src_t -> lskips -> Types.t option -> src_t

  val mk_pwild : Ast.l -> lskips -> Types.t -> pat
  val mk_pas : Ast.l -> pat -> lskips -> name_l -> Types.t option -> pat
  val mk_ptyp : Ast.l -> lskips -> pat -> lskips -> src_t -> lskips -> Types.t option -> pat
  val mk_pvar : Ast.l -> Name.lskips_t -> Types.t -> pat
  val mk_pconstr : Ast.l -> constr_descr id -> pat list -> Types.t option -> pat
  val mk_precord : Ast.l -> lskips -> (field_descr id * lskips * pat) lskips_seplist -> lskips -> Types.t option -> pat
  val mk_ptup : Ast.l -> lskips -> pat lskips_seplist -> lskips -> Types.t option -> pat
  val mk_plist : Ast.l -> lskips -> pat lskips_seplist -> lskips -> Types.t -> pat
  val mk_pparen : Ast.l -> lskips -> pat -> lskips -> Types.t option -> pat
  val mk_pcons : Ast.l -> pat -> lskips -> pat -> Types.t option -> pat
  val mk_plit : Ast.l -> lit -> Types.t option -> pat 
  val mk_pvar_annot : Ast.l -> Name.lskips_t -> src_t -> Types.t option -> pat 

  val mk_var : Ast.l -> Name.lskips_t -> Types.t -> exp
  val mk_const : Ast.l -> const_descr id -> Types.t option -> exp
  val mk_constr : Ast.l -> constr_descr id -> Types.t option -> exp
  val mk_tup_ctor : Ast.l -> constr_descr id -> lskips -> exp lskips_seplist -> lskips -> Types.t option -> exp
  val mk_fun : Ast.l -> lskips -> pat list -> lskips -> exp -> Types.t option -> exp
  val mk_function : Ast.l -> lskips -> (pat * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_app : Ast.l -> exp -> exp -> Types.t option -> exp
  val mk_infix : Ast.l -> exp -> exp -> exp -> Types.t option -> exp
  val mk_record : Ast.l -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp
  val mk_record_coq : Ast.l -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist-> lskips -> Types.t option -> exp
  val mk_recup : Ast.l -> lskips -> exp -> lskips -> (field_descr id * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_field : Ast.l -> exp -> lskips -> field_descr id -> Types.t option -> exp
  val mk_case : Ast.l -> lskips -> exp -> lskips -> (pat * lskips * exp * Ast.l) lskips_seplist -> lskips -> Types.t option -> exp
  val mk_typed : Ast.l -> lskips -> exp -> lskips -> src_t -> lskips -> Types.t option -> exp
  val mk_let_val : Ast.l -> pat -> (lskips * src_t) option -> lskips -> exp -> letbind
  val mk_let_fun : Ast.l -> name_lskips_annot -> pat list -> (lskips * src_t) option -> lskips -> exp -> letbind
  val mk_let : Ast.l -> lskips -> letbind -> lskips -> exp -> Types.t option -> exp
  val mk_tup : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t option -> exp
  val mk_list : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t -> exp
  val mk_paren : Ast.l -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_begin : Ast.l -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_if : Ast.l -> lskips -> exp -> lskips -> exp -> lskips -> exp -> Types.t option -> exp
  val mk_lit : Ast.l -> lit -> Types.t option -> exp
  val mk_set : Ast.l -> lskips -> exp lskips_seplist -> lskips -> Types.t -> exp
  val mk_setcomp : Ast.l -> lskips -> exp -> lskips -> exp -> lskips -> NameSet.t -> Types.t option -> exp
  val mk_comp_binding : Ast.l -> bool -> lskips -> exp -> lskips -> lskips -> quant_binding list -> lskips -> exp -> lskips -> Types.t option -> exp
  val mk_quant : Ast.l -> Ast.q -> quant_binding list -> lskips -> exp -> Types.t option -> exp
  val t_to_src_t : Types.t -> src_t
  val pat_subst : Types.t Types.TVfmap.t * Name.t Nfmap.t -> pat -> pat
  val delimit_exp : (Precedence.op -> Precedence.t) -> Precedence.context -> exp -> exp
  val exp_to_prec : (Precedence.op -> Precedence.t) -> exp -> Precedence.t
end

val single_pat_exhaustive : pat -> bool
val env_union : env -> env -> env
val delimit_pat : Precedence.pat_context -> pat -> pat
