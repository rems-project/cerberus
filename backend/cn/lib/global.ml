open Pp
module IdMap = Map.Make (Id)
module RT = ReturnTypes
module AT = ArgumentTypes

type t =
  { struct_decls : Memory.struct_decls;
    datatypes : BaseTypes.dt_info Sym.Map.t;
    datatype_constrs : BaseTypes.constr_info Sym.Map.t;
    datatype_order : Sym.t list list option;
    fun_decls : (Locations.t * AT.ft option * Sctypes.c_concrete_sig) Sym.Map.t;
    resource_predicates : Definition.Predicate.t Sym.Map.t;
    logical_functions : Definition.Function.t Sym.Map.t;
    lemmata : (Locations.t * AT.lemmat) Sym.Map.t
  }

let empty =
  { struct_decls = Sym.Map.empty;
    datatypes = Sym.Map.empty;
    datatype_constrs = Sym.Map.empty;
    datatype_order = None;
    fun_decls = Sym.Map.empty;
    resource_predicates = Sym.Map.(empty |> add Alloc.Predicate.sym Definition.alloc);
    logical_functions = Sym.Map.empty;
    lemmata = Sym.Map.empty
  }


let get_resource_predicate_def global id = Sym.Map.find_opt id global.resource_predicates

let get_logical_function_def global id = Sym.Map.find_opt id global.logical_functions

let get_fun_decl global sym = Sym.Map.find_opt sym global.fun_decls

let get_lemma global sym = Sym.Map.find_opt sym global.lemmata

let get_struct_decl global sym = Sym.Map.find_opt sym global.struct_decls

let get_datatype global sym = Sym.Map.find_opt sym global.datatypes

let get_datatype_constr global sym = Sym.Map.find_opt sym global.datatype_constrs

let sym_map_from_bindings xs =
  List.fold_left (fun m (nm, x) -> Sym.Map.add nm x m) Sym.Map.empty xs


module type Reader = sig
  type global = t

  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  type state

  val get : unit -> state t

  val to_global : state -> global
end

module type Lifted = sig
  type 'a t

  val get_resource_predicate_def : Sym.t -> Definition.Predicate.t option t

  val get_logical_function_def : Sym.t -> Definition.Function.t option t

  val get_fun_decl
    :  Sym.t ->
    (Cerb_location.t * AT.ft option * Sctypes.c_concrete_sig) option t

  val get_lemma : Sym.t -> (Cerb_location.t * AT.lemmat) option t

  val get_struct_decl : Sym.t -> Memory.struct_layout option t

  val get_datatype : Sym.t -> BaseTypes.dt_info option t

  val get_datatype_constr : Sym.t -> BaseTypes.constr_info option t
end

module Lift (M : Reader) : Lifted with type 'a t := 'a M.t = struct
  let lift f sym =
    let ( let@ ) = M.bind in
    let@ state = M.get () in
    let global = M.to_global state in
    M.return (f global sym)


  let get_resource_predicate_def = lift get_resource_predicate_def

  let get_logical_function_def = lift get_logical_function_def

  let get_fun_decl = lift get_fun_decl

  let get_lemma = lift get_lemma

  let get_struct_decl = lift get_struct_decl

  let get_datatype = lift get_datatype

  let get_datatype_constr = lift get_datatype_constr
end

let pp_struct_layout (tag, layout) =
  item
    ("struct " ^ plain (Sym.pp tag) ^ " (raw)")
    (separate_map
       hardline
       (fun Memory.{ offset; size; member_or_padding } ->
         item "offset" (Pp.int offset)
         ^^ comma
         ^^^ item "size" (Pp.int size)
         ^^ comma
         ^^^ item
               "content"
               (match member_or_padding with
                | Some (member, sct) -> typ (Id.pp member) (Sctypes.pp sct)
                | None -> parens (!^"padding" ^^^ Pp.int size)))
       layout)


let pp_struct_decls decls = Pp.list pp_struct_layout (Sym.Map.bindings decls)

let pp_fun_decl (sym, (_, t, _)) =
  item (plain (Sym.pp sym)) (Pp.option (AT.pp RT.pp) "(no spec)" t)


let pp_fun_decls decls = flow_map hardline pp_fun_decl (Sym.Map.bindings decls)

let pp_resource_predicate_definitions defs =
  separate_map
    hardline
    (fun (name, def) -> item (Sym.pp_string name) (Definition.Predicate.pp def))
    (Sym.Map.bindings defs)


let pp global =
  pp_struct_decls global.struct_decls
  ^^ hardline
  ^^ pp_fun_decls global.fun_decls
  ^^ hardline
  ^^ pp_resource_predicate_definitions global.resource_predicates


let mutual_datatypes (global : t) tag =
  let deps tag =
    let info = Sym.Map.find tag global.datatypes in
    info.all_params |> List.filter_map (fun (_, bt) -> BaseTypes.is_datatype_bt bt)
  in
  let rec seek tags = function
    | [] -> tags
    | new_tag :: new_tags ->
      if Sym.Set.mem new_tag tags then
        seek tags new_tags
      else
        seek (Sym.Set.add new_tag tags) (deps new_tag @ new_tags)
  in
  seek Sym.Set.empty [ tag ] |> Sym.Set.elements
