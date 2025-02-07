module CF = Cerb_frontend
module A = Executable_spec_utils.A
module C = Executable_spec_utils.C

val cn_ghost_state_sym : Sym.t

val cn_ghost_state_struct_type : Executable_spec_utils.C.ctype

val get_cn_stack_depth_sym : Sym.t

val cn_stack_depth_ctype : C.ctype

val cn_stack_depth_incr_sym : Sym.t

val cn_stack_depth_decr_sym : Sym.t

val c_add_ownership_fn_sym : Sym.t

val c_remove_ownership_fn_sym : Sym.t

val c_declare_and_map_local_sym : Sym.t

val c_declare_init_and_map_local_sym : Sym.t

val get_start_loc : ?offset:int -> Cerb_location.t -> Cerb_location.t

val get_end_loc : ?offset:int -> Cerb_location.t -> Cerb_location.t

val get_ownership_global_init_stats
  :  unit ->
  Cerb_frontend.GenTypes.genTypeCategory A.statement_ list

val generate_c_local_ownership_entry_fcall
  :  A.ail_identifier * Executable_spec_utils.C.ctype ->
  Cerb_frontend.GenTypes.genTypeCategory Executable_spec_utils.A.expression

val gen_loop_ownership_entry_decls
  :  (Sym.t * ('a * 'b * 'c * Executable_spec_utils.C.ctype)) list ->
  (Sym.t
  * Cerb_frontend.GenTypes.genTypeCategory Executable_spec_utils.A.expression option)
    list ->
  (Sym.t
  * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
    * 'd option
    * Executable_spec_utils.C.qualifiers
    * Executable_spec_utils.C.ctype))
    list
  * (Sym.t
    * Cerb_frontend.GenTypes.genTypeCategory Executable_spec_utils.A.expression option)
      list

val generate_c_local_ownership_entry_inj
  :  bool ->
  Cerb_location.t ->
  (Sym.t * Cerb_frontend.GenTypes.genTypeCategory A.expression option) list ->
  (Sym.t * ('a * 'b * 'c * Executable_spec_utils.C.ctype)) list ->
  (Cerb_location.t
  * (Sym.t
    * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
      * 'd option
      * Executable_spec_utils.C.qualifiers
      * Executable_spec_utils.C.ctype))
      list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val generate_c_local_ownership_exit
  :  A.ail_identifier * Executable_spec_utils.C.ctype ->
  Cerb_frontend.GenTypes.genTypeCategory A.statement_

val get_c_local_ownership_checking
  :  (A.ail_identifier * Executable_spec_utils.C.ctype) list ->
  Cerb_frontend.GenTypes.genTypeCategory A.statement_ list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list

val collect_visibles
  :  (Sym.t * ('a * 'b * 'c * 'd)) list ->
  'e A.statement list ->
  (Sym.t * 'd) list

val take : int -> 'a list -> 'a list

val get_c_control_flow_block_unmaps_aux
  :  (A.ail_identifier * Executable_spec_utils.C.ctype) list ->
  (A.ail_identifier * Executable_spec_utils.C.ctype) list ->
  (A.ail_identifier * Executable_spec_utils.C.ctype) list ->
  (A.ail_identifier
  * ((Cerb_location.t * A.storageDuration * bool)
    * Executable_spec_utils.C.alignment option
    * Executable_spec_utils.C.qualifiers
    * Executable_spec_utils.C.ctype))
    list ->
  'a A.statement ->
  (Cerb_location.t
  * 'a A.expression option option
  * 'b list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val get_c_control_flow_block_unmaps
  :  'a A.statement ->
  (Cerb_location.t
  * 'a A.expression option option
  * 'b list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val get_c_block_entry_exit_injs_aux
  :  A.bindings ->
  Cerb_frontend.GenTypes.genTypeCategory A.statement ->
  (Cerb_location.t
  * (Sym.t
    * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
      * 'a option
      * Executable_spec_utils.C.qualifiers
      * Executable_spec_utils.C.ctype))
      list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val get_c_block_entry_exit_injs
  :  Cerb_frontend.GenTypes.genTypeCategory A.statement ->
  (Cerb_location.t
  * 'a option
  * (Sym.t
    * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
      * 'b option
      * Executable_spec_utils.C.qualifiers
      * Executable_spec_utils.C.ctype))
      list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val combine_injs_over_location
  :  Cerb_location.t ->
  (Cerb_location.t * 'a * 'b * 'c) list ->
  ('a * 'b * 'c) list

val get_return_expr_opt : 'a option list -> 'a option

val remove_duplicates
  :  Cerb_location.t list ->
  Cerb_location.t list ->
  Cerb_location.t list

val get_c_block_local_ownership_checking_injs
  :  Cerb_frontend.GenTypes.genTypeCategory A.statement ->
  (Cerb_location.t
  * Cerb_frontend.GenTypes.genTypeCategory A.expression option option
  * (Sym.t
    * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
      * 'a option
      * Executable_spec_utils.C.qualifiers
      * Executable_spec_utils.C.ctype))
      list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    list

val get_c_fn_local_ownership_checking_injs
  :  Sym.t ->
  Cerb_frontend.GenTypes.genTypeCategory Executable_spec_utils.A.sigma ->
  (Cerb_frontend.GenTypes.genTypeCategory A.statement_ list
  * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
    option
  * (Cerb_location.t
    * Cerb_frontend.GenTypes.genTypeCategory A.expression option option
    * (Sym.t
      * ((Cerb_location.t * Executable_spec_utils.A.storageDuration * bool)
        * 'a option
        * Executable_spec_utils.C.qualifiers
        * Executable_spec_utils.C.ctype))
        list
    * Cerb_frontend.GenTypes.genTypeCategory A.statement_ list)
      list
