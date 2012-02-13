open Typed_ast

exception Trans_error of Ast.l * string

val coq_synt_records : def list -> def list

type 'a macro = 'a -> 'a option

module Macros(I : Types.Global_defs)(E : sig val env : env end) : sig 
  val build_records : exp macro
  val remove_function : exp macro
  val remove_fun_pats : bool -> exp macro
  val remove_list_comprehension : exp macro
  val remove_set_restr_quant : exp macro
  val do_substitutions : target -> exp macro
  val hack : exp macro
  val tup_ctor : (exp -> exp) -> exp lskips_seplist -> exp macro
  val remove_sets : exp macro
  val remove_quant : exp macro
  val list_quant_to_set_quant : exp macro
  val remove_letfun : bool -> exp macro
  val remove_class_const : exp macro

  val peanoize_num_pats : bool -> pat macro
  val coq_type_annot_pat_vars : bool -> pat macro
end
