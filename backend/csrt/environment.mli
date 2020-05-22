open Cerb_frontend

module Loc = Locations


type struct_decl = 
  {typ : (((string, VarTypes.t) Binders.t) list);
   mcl: Memory.mcl}



module Global : sig

  type t

  val empty : 
    t

  val add_struct_decl : 
    t -> 
    BaseTypes.struct_type -> 
    struct_decl ->
    t

  val add_fun_decl : 
    t -> 
    Sym.t -> 
    (Loc.t * FunctionTypes.t * Sym.t) -> 
    t

  val add_impl_fun_decl : 
    t -> 
    Implementation.implementation_constant -> 
    FunctionTypes.t -> 
    t

  val add_impl_constant : 
    t -> 
    Implementation.implementation_constant -> 
    BaseTypes.t -> 
    t

  val get_struct_decl : 
    Loc.t ->
    t -> 
    BaseTypes.struct_type -> 
    (struct_decl, Loc.t * TypeErrors.type_error) Except.m


  val get_fun_decl : 
    Loc.t ->
    t -> 
    Sym.t -> 
    ((Loc.t * FunctionTypes.t * Sym.t), Loc.t * TypeErrors.type_error) Except.m

  val get_impl_fun_decl : 
    Loc.t ->
    t -> 
    Implementation.implementation_constant -> 
    (FunctionTypes.t, Loc.t * TypeErrors.type_error) Except.m

  val get_impl_constant : 
    Loc.t ->
    t -> 
    Implementation.implementation_constant -> 
    (BaseTypes.t, Loc.t * TypeErrors.type_error) Except.m

  val get_names : 
    t -> 
    NameMap.t
  
  val record_name : 
    t -> 
    Loc.t -> 
    string -> 
    Sym.t -> 
    t

  val record_name_without_loc : 
    t -> 
    string -> 
    Sym.t -> 
    t

  val pp_items :
    t ->
    (int * PPrint.document) list

  val pp : 
    t -> 
    PPrint.document

end



module Local : sig

  type t

  val empty :
    t

  val pp : 
    t -> 
    PPrint.document

  val add_var : 
    t ->
    (Sym.t,VarTypes.t) Binders.t ->
    t

  val remove_var :
    t -> 
    Sym.t ->
    t

end



module Env : sig

  type t = { global: Global.t; local: Local.t}

  val with_fresh_local :
    Global.t ->
    t

  val add_var : 
    t ->
    (Sym.t,VarTypes.t) Binders.t ->
    t

  val remove_var :
    t -> 
    Sym.t ->
    t

  val get_Avar : 
    Loc.t ->
    t ->
    Sym.t ->
    (BaseTypes.t * t, Loc.t * TypeErrors.type_error) Except.m

  val get_Lvar : 
    Loc.t ->
    t ->
    Sym.t ->
    (LogicalSorts.t * t, Loc.t * TypeErrors.type_error) Except.m

  val get_Rvar : 
    Loc.t ->
    t ->
    Sym.t ->
    (Resources.t * t, Loc.t * TypeErrors.type_error) Except.m

  val get_Cvar : 
    Loc.t ->
    t ->
    Sym.t ->
    (LogicalConstraints.t * t, Loc.t * TypeErrors.type_error) Except.m

  val get_var : 
    Loc.t ->
    t ->
    Sym.t ->
    (VarTypes.t * t, Loc.t * TypeErrors.type_error) Except.m

  val filter_vars : 
    (Sym.t -> VarTypes.t -> bool) ->
    t ->
    Sym.t list

  val resources_associated_with :
    t ->
    Sym.t ->
    Sym.t list


  (* val resources_for_loc :
   *   Loc.t ->
   *   t ->
   *   Sym.t ->
   *   (Sym.t option, Loc.t * TypeErrors.type_error) Except.m *)


  val get_all_constraints :
    t ->
    LogicalConstraints.t list


  (* val get_constraints_about :
   *   t ->
   *   Sym.t ->
   *   LogicalConstraints.t list *)

  (* val is_struct_open :
   *   t ->
   *   Sym.t ->
   *   (Sym.t * Resources.open_struct) option *)

end
