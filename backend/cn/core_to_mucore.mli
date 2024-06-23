(* Module Core_to_mucore - Translate Cerberus Core to CN Mucore *)

(* TODO: BCP: I'm sure there are a bunch of things here that don't need to be exported... *)

module CF = Cerb_frontend
module CA = Cerb_frontend.Cabs_to_ail
module CAE = Cerb_frontend.Cabs_to_ail_effect
module BT = BaseTypes
module SBT = SurfaceBaseTypes
module Mu = Mucore
module Loc = Locations
module C = Compile
module IT = IndexTerms

(* TODO: BCP: In the .ml file this is just
     module Pmap = struct
       include Pmap
       let filter_map compare f map =
         Pmap.fold (fun key value acc ->
             match f key value with
             | Some value' -> Pmap.add key value' acc
             | None -> acc
           ) map (Pmap.empty compare)
     end
*)
module Pmap :
  sig
    type ('key, 'a) map = ('key, 'a) Pmap.map
    val empty : ('key -> 'key -> int) -> ('key, 'a) map
    val is_empty : ('key, 'a) map -> bool
    val mem : 'key -> ('key, 'a) map -> bool
    val add : 'key -> 'a -> ('key, 'a) map -> ('key, 'a) map
    val singleton : ('key -> 'key -> int) -> 'key -> 'a -> ('key, 'a) map
    val remove : 'key -> ('key, 'a) map -> ('key, 'a) map
    val merge :
      ('key -> 'a option -> 'b option -> 'c option) ->
      ('key, 'a) map -> ('key, 'b) map -> ('key, 'c) map
    val union : ('key, 'a) map -> ('key, 'a) map -> ('key, 'a) map
    val compare :
      ('a -> 'a -> int) -> ('key, 'a) map -> ('key, 'a) map -> int
    val equal :
      ('a -> 'a -> bool) -> ('key, 'a) map -> ('key, 'a) map -> bool
    val iter : ('key -> 'a -> unit) -> ('key, 'a) map -> unit
    val fold : ('key -> 'a -> 'b -> 'b) -> ('key, 'a) map -> 'b -> 'b
    val for_all : ('key -> 'a -> bool) -> ('key, 'a) map -> bool
    val exist : ('key -> 'a -> bool) -> ('key, 'a) map -> bool
    val filter : ('key -> 'a -> bool) -> ('key, 'a) map -> ('key, 'a) map
    val partition :
      ('key -> 'a -> bool) ->
      ('key, 'a) map -> ('key, 'a) map * ('key, 'a) map
    val cardinal : ('key, 'a) map -> int
    val bindings_list : ('key, 'a) map -> ('key * 'a) list
    val bindings :
      ('key * 'a -> 'key * 'a -> int) ->
      ('key, 'a) map -> ('key * 'a) Pset.set
    val domain : ('key, 'a) map -> 'key Pset.set
    val range : ('a -> 'a -> int) -> ('key, 'a) map -> 'a Pset.set
    val min_binding : ('key, 'a) map -> 'key * 'a
    val max_binding : ('key, 'a) map -> 'key * 'a
    val choose : ('key, 'a) map -> 'key * 'a
    val split :
      'key -> ('key, 'a) map -> ('key, 'a) map * 'a option * ('key, 'a) map
    val find : 'key -> ('key, 'a) map -> 'a
    val lookup : 'key -> ('key, 'a) map -> 'a option
    val map : ('a -> 'b) -> ('key, 'a) map -> ('key, 'b) map
    val mapi : ('key -> 'a -> 'b) -> ('key, 'a) map -> ('key, 'b) map
    val from_set : ('key -> 'v) -> 'key Pset.set -> ('key, 'v) map
    val filter_map :
      ('a -> 'a -> int) ->
      ('a -> 'b -> 'c option) -> ('a, 'b) Pmap.map -> ('a, 'c) Pmap.map
  end

module SymSet : Set.S with type elt = Sym.t
module SymMap : Map.S with type key = Sym.t
module IdMap : Map.S with type key = Id.t

val do_ail_desugar_op :
  'a ->
  ('a ->
   ('b * 'c, Locations.t * Cerb_frontend.Errors.cause)
   Cerb_frontend.Exception.exceptM) ->
  ('b * 'c) Resultat.t
val do_ail_desugar_rdonly :
  'a ->
  ('a ->
   ('b * 'c, Locations.t * Cerb_frontend.Errors.cause)
   Cerb_frontend.Exception.exceptM) ->
  'b Resultat.m
val register_new_cn_local :
  Cerb_frontend.Symbol.identifier ->
  Cerb_frontend.Cabs_to_ail_effect.state_with_markers ->
  (Cerb_frontend.Symbol.sym *
   Cerb_frontend.Cabs_to_ail_effect.state_with_markers)
  Resultat.t
type symbol = Cerb_frontend.Symbol.sym
type mu_pexpr = unit Mu.mu_pexpr
type mu_pexprs = mu_pexpr list
type mu_expr = unit Mu.mu_expr
exception ConversionFailed
val assert_error : Locations.t -> Pp.document -> 'a
val assertl :
  Locations.t ->
  bool -> Pp.document -> Pp.document Lazy.t -> unit
val convert_ct :
  Locations.t ->
  Cerb_frontend.Ctype.ctype -> Sctypes.ctype
val convert_core_bt_for_list :
  Locations.t -> Cerb_frontend.Core.core_base_type -> BT.basetype
val ensure_pexpr_ctype :
  Mu.loc ->
  Pp.document ->
  ('a, Cerb_frontend.Symbol.sym) Cerb_frontend.Core.generic_pexpr -> Mu.act
val core_to_mu__pattern :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  Cerb_frontend.Symbol.sym Cerb_frontend.Core.generic_pattern ->
  unit Mu.mu_pattern
val n_ov :
  Locations.t ->
  Cerb_frontend.Core.object_value -> unit Mu.mu_object_value
val n_lv :
  Locations.t ->
  Cerb_frontend.Core.loaded_value -> unit Mu.mu_object_value
val n_val :
  Locations.t -> Cerb_frontend.Core.value -> unit Mu.mu_value
val unit_pat : Mu.loc -> Cerb_frontend.Annot.annot list -> unit Mu.mu_pattern
val function_ids : (string * Mu.mu_function) list
val ity_act : Mu.loc -> Sctypes.IntegerTypes.integerType -> Mu.act
val n_pexpr :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  (unit, Mu.symbol) Cerb_frontend.Core.generic_pexpr -> mu_pexpr
val n_kill_kind :
  Locations.t -> Cerb_frontend.Core.kill_kind -> Mu.m_kill_kind
val n_action :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  ('a, unit, Cerb_frontend.Symbol.sym) Cerb_frontend.Core.generic_action ->
  unit Mu.mu_action
val n_paction :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  ('a, unit, Cerb_frontend.Symbol.sym) Cerb_frontend.Core.generic_paction ->
  unit Mu.mu_paction
val show_n_memop :
  Cerb_frontend.Symbol.sym Cerb_frontend.Mem_common.generic_memop -> string
val n_memop :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  Cerb_frontend.Symbol.sym Cerb_frontend.Mem_common.generic_memop ->
  (unit, Mu.symbol) Cerb_frontend.Core.generic_pexpr list -> unit Mu.mu_memop
val unsupported :
  Locations.t ->
  Cerb_pp_prelude.P.document -> 'a Resultat.t
val n_expr :
  inherit_loc:bool ->
  Resultat.Loc.t ->
  (Compile.env *
   Compile.LocalState.state Compile.StringMap.t) *
  ((int, CAE.state) Pmap.map *
   Cerb_frontend.Cn_desugaring.cn_desugaring_state) ->
  (Sym.S.sym * TypeErrors.CF.Ctype.ctype) list *
  (int, (Sym.S.sym * TypeErrors.CF.Ctype.ctype) list)
  Pmap.map ->
  ('a, unit, Mu.symbol) Cerb_frontend.Core.generic_expr ->
  mu_expr Resultat.m
module RT = ReturnTypes
module AT = ArgumentTypes
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
val arguments_of_at : ('a -> 'b) -> 'a AT.t -> 'b Mu.mu_arguments
type identifier_env = Cerb_frontend.Annot.identifier_env
val make_largs :
  (C.env -> C.LocalState.states -> 'a Resultat.m) ->
  C.env ->
  C.LocalState.states ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition
  list -> 'a Mu.mu_arguments_l Resultat.m
val make_largs_with_accesses :
  (C.env -> C.LocalState.states -> 'a Resultat.m) ->
  C.env ->
  C.LocalState.states ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype))
  list *
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition
  list -> 'a Mu.mu_arguments_l Resultat.m
val is_pass_by_pointer : Cerb_frontend.Core.pass_by_value_or_pointer -> bool
val check_against_core_bt :
  Locations.t ->
  Cerb_frontend.Core.core_base_type ->
  CoreTypeChecks.BT.basetype -> unit Resultat.t
val make_label_args :
  (C.env -> C.LocalState.states -> 'a Resultat.m) ->
  Locations.t ->
  C.env ->
  C.LocalState.states ->
  ((Sym.S.sym Option.t *
    (Cerb_frontend.Ctype.ctype * Cerb_frontend.Core.pass_by_value_or_pointer)) *
   (Sym.S.sym * Cerb_frontend.Core.core_base_type))
  list ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype))
  list *
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition
  list -> 'a Mu.mu_arguments Resultat.m
val make_function_args :
  ((Sym.S.sym * C.LocalState.c_variable_state) list ->
   C.env -> C.LocalState.states -> 'a Resultat.m) ->
  Locations.t ->
  C.env ->
  ((Sym.S.sym *
    (Sym.S.sym Option.t * Cerb_frontend.Ctype.ctype)) *
   (C.SymTable.key * Cerb_frontend.Core.core_base_type))
  list ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype))
  list *
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition
  list -> 'a Mu.mu_arguments Resultat.m
val make_fun_with_spec_args :
  (C.env -> C.LocalState.states -> 'a Resultat.m) ->
  Locations.t ->
  C.env ->
  ((C.SymTable.key * TypeErrors.CF.Symbol.sym C.CF.Cn.cn_base_type) *
   Cerb_frontend.Ctype.ctype)
  list ->
  (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition
  list -> 'a Mu.mu_arguments Resultat.m
val desugar_access :
  CAE.state_with_markers ->
  (Sym.S.sym * Cerb_frontend.Ctype.ctype) list ->
  Locations.t * Cerb_frontend.Symbol.identifier ->
  (Locations.t *
   (Cerb_frontend.Symbol.sym * Cerb_frontend.Ctype.ctype))
  Resultat.m
val desugar_cond :
  Cerb_frontend.Cabs_to_ail_effect.state_with_markers ->
  (Cerb_frontend.Symbol.identifier, Cerb_frontend.Cabs.type_name)
  Cerb_frontend.Cn.cn_condition ->
  ((Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype)
   Cerb_frontend.Cn.cn_condition *
   Cerb_frontend.Cabs_to_ail_effect.state_with_markers)
  Resultat.m
val desugar_conds :
  Cerb_frontend.Cabs_to_ail_effect.state_with_markers ->
  (Cerb_frontend.Symbol.identifier, Cerb_frontend.Cabs.type_name)
  Cerb_frontend.Cn.cn_condition list ->
  ((Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype)
   Cerb_frontend.Cn.cn_condition list *
   Cerb_frontend.Cabs_to_ail_effect.state_with_markers)
  Resultat.m
val normalise_label :
  inherit_loc:bool ->
  Cerb_frontend.Symbol.sym ->
  (int, CAE.state) Pmap.map * Cerb_frontend.Cn_desugaring.cn_desugaring_state ->
  (Sym.S.sym * TypeErrors.CF.Ctype.ctype) list *
  (int, (Sym.S.sym * TypeErrors.CF.Ctype.ctype) list)
  Pmap.map ->
  (Locations.t * (Sym.t * Cerb_frontend.Ctype.ctype))
  list *
  (Cerb_frontend.Annot.loop_id, int * Cerb_frontend.Annot.attributes)
  Pmap.map ->
  C.env ->
  C.LocalState.states ->
  'a ->
  'b Cerb_frontend.Milicore.mi_label_def ->
  unit Mu.mu_label_def Resultat.t
val add_spec_arg_renames :
  Locations.t ->
  (Sym.t * 'a) list ->
  Cerb_frontend.Ctype.ctype list ->
  (Cerb_frontend.Symbol.sym, Cerb_frontend.Ctype.ctype)
  Cerb_frontend.Cn.cn_fun_spec -> C.env -> C.env
val make_struct_decl :
  Locations.t ->
  (Cerb_frontend.Symbol.identifier *
   ('a * 'b * 'c * Cerb_frontend.Ctype.ctype))
  list -> Sym.t -> Memory.struct_piece list
val normalise_tag_definition :
  Sym.t ->
  Locations.t * Cerb_frontend.Ctype.tag_definition ->
  Mu.mu_tag_definition Resultat.t
val normalise_tag_definitions :
  (Sym.t,
   Locations.t * Cerb_frontend.Ctype.tag_definition)
  Pmap.map ->
  (Sym.t, Mu.mu_tag_definition) Pmap.map Resultat.m
val register_glob : C.env -> C.SymTable.key * 'a Mu.mu_globs -> C.env
val translate_datatype :
  Compile.env ->
  TypeErrors.CF.Symbol.sym Cerb_frontend.Cn.cn_datatype ->
  TypeErrors.CF.Symbol.sym * Mu.mu_datatype
val normalise_file :
  inherit_loc:bool ->
  CAE.fin_markers_env * 'a Cerb_frontend.AilSyntax.sigma ->
  ('b, unit) Cerb_frontend.Milicore.mi_file ->
  unit Mu.mu_file Resultat.m
type statements =
    (Locations.t * Cnprog.cn_prog list) list
type fn_spec_instrumentation =
    (ReturnTypes.t * statements) ArgumentTypes.t
type instrumentation = {
  fn : Sym.t;
  fn_loc : Resultat.Loc.t;
  internal : fn_spec_instrumentation option;
}
val rt_stmts_subst :
  [ `Rename of Sym.t | `Term of Cnprog.IT.typed ]
  Subst.t ->
  ReturnTypes.t * ('a * Cnprog.cn_prog list) list ->
  ReturnTypes.t * ('a * Cnprog.cn_prog list) list
val fn_spec_instrumentation_subst_at :
  [ `Rename of Sym.t
  | `Term of ArgumentTypes.LAT.LC.IT.typed ] Subst.t ->
  fn_spec_instrumentation -> fn_spec_instrumentation
val fn_spec_instrumentation_subst_lat :
  [ `Rename of Sym.t
  | `Term of LogicalArgumentTypes.LC.IT.typed ] Subst.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t
val fn_spec_instrumentation_sym_subst_at :
  Sym.t * ArgumentTypes.LAT.LC.IT.BT.t * Sym.t ->
  fn_spec_instrumentation -> fn_spec_instrumentation
val fn_spec_instrumentation_sym_subst_lat :
  Sym.t * LogicalArgumentTypes.LC.IT.BT.t *
  Sym.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t
val fn_spec_instrumentation_sym_subst_lrt :
  Sym.t * LogicalConstraints.IT.BT.t * Sym.t ->
  LRT.t -> LRT.t
val concat2 : 'a list * 'b list -> 'a list * 'b list -> 'a list * 'b list
val concat2_map : ('a -> 'b list * 'c list) -> 'a list -> 'b list * 'c list
val stmts_in_expr :
  'a Mu.mu_expr ->
  (Mu.loc *
   (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement
   list)
  list * (Mu.loc * Cnprog.cn_prog list) list
val stmts_in_largs : ('a -> 'b) -> 'a Mu.mu_arguments_l -> 'b
val stmts_in_args : ('a -> 'b) -> 'a Mu.mu_arguments -> 'b
val stmts_in_labels :
  ('a, 'b Mu.mu_label_def) Pmap.map ->
  (Mu.loc *
   (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement
   list)
  list * (Mu.loc * Cnprog.cn_prog list) list
val stmts_in_function :
  ('a Mu.mu_expr * ('b, 'c Mu.mu_label_def) Pmap.map * 'd) Mu.mu_arguments ->
  (Mu.loc *
   (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement
   list)
  list * (Mu.loc * Cnprog.cn_prog list) list
val collect_instrumentation :
  'a Mu.mu_file -> instrumentation list * C.SBT.t C.SymTable.t
