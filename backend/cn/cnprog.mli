(* Module Cnprog -- Defines CN statements and CN let within a C function.

   CN statements are used to help with proof guidance and debugging *)

module BT = BaseTypes
module IT = IndexTerms
module Loc = Locations
module CF = Cerb_frontend
module RET = ResourceTypes
module LC = LogicalConstraints

type have_show =
  | Have
  | Show

type cn_extract = Id.t list * (Sym.t, Sctypes.t) IT.CF.Cn.cn_to_extract * IndexTerms.t

(* Type of CN statements that are allowed within C function and it's body *)
type cn_statement =
  | M_CN_pack_unpack of IT.CF.Cn.pack_unpack * ResourceTypes.predicate_type
  | M_CN_have of LogicalConstraints.t
  | M_CN_instantiate of (Sym.t, Sctypes.t) IT.CF.Cn.cn_to_instantiate * IndexTerms.t
  | M_CN_split_case of LogicalConstraints.t
  | M_CN_extract of cn_extract
  | M_CN_unfold of Sym.t * IndexTerms.t list
  | M_CN_apply of Sym.t * IndexTerms.t list
  | M_CN_assert of LogicalConstraints.t
  | M_CN_inline of Sym.t list
  | M_CN_print of IndexTerms.t

(* cn_load consists of a c type and pointer which is basetype term *)
type cn_load =
  { ct : Sctypes.t;
    pointer : IndexTerms.t
  }

(* Type of CN statements that are allowed within a function *)
type cn_prog =
  | M_CN_let of Loc.t * (Sym.t * cn_load) * cn_prog
  | M_CN_statement of Loc.t * cn_statement

(* Applies substitution to a CN_prog constructors *)
val subst : [ `Rename of Sym.t | `Term of IT.typed ] Subst.subst -> cn_prog -> cn_prog

(* Used within subst, it alpha renames a CN_prog constructor *)
val alpha_rename_ : from:Sym.t -> to_:Subst.SymSet.elt -> cn_prog -> Sym.t * cn_prog

val alpha_rename : Sym.t -> cn_prog -> Sym.t * cn_prog

val suitably_alpha_rename : Subst.SymSet.t -> Sym.t -> cn_prog -> Sym.t * cn_prog

(* Converts cn_prog constructors to decision tree ******************************************)

val dtree_of_to_instantiate
  :  (Cerb_frontend.Symbol.sym, Sctypes.ctype) Cerb_frontend.Cn.cn_to_instantiate ->
  Cerb_frontend.Pp_ast.doc_tree

val dtree_of_to_extract
  :  (Cerb_frontend.Symbol.sym, Sctypes.ctype) Cerb_frontend.Cn.cn_to_extract ->
  Cerb_frontend.Pp_ast.doc_tree

val dtree_of_cn_statement : cn_statement -> Cerb_frontend.Pp_ast.doc_tree

val dtree : cn_prog -> Cerb_frontend.Pp_ast.doc_tree
