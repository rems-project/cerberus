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
    resource_predicates : ResourcePredicates.definition Sym.Map.t;
    logical_functions : LogicalFunctions.definition Sym.Map.t;
    lemmata : (Locations.t * AT.lemmat) Sym.Map.t
  }

let empty =
  { struct_decls = Sym.Map.empty;
    datatypes = Sym.Map.empty;
    datatype_constrs = Sym.Map.empty;
    datatype_order = None;
    fun_decls = Sym.Map.empty;
    resource_predicates =
      Sym.Map.(empty |> add Alloc.Predicate.sym ResourcePredicates.alloc);
    logical_functions = Sym.Map.empty;
    lemmata = Sym.Map.empty
  }


let get_resource_predicate_def global id = Sym.Map.find_opt id global.resource_predicates

let get_logical_function_def global id = Sym.Map.find_opt id global.logical_functions

let get_fun_decl global sym = Sym.Map.find_opt sym global.fun_decls

let get_lemma global sym = Sym.Map.find_opt sym global.lemmata

let sym_map_from_bindings xs =
  List.fold_left (fun m (nm, x) -> Sym.Map.add nm x m) Sym.Map.empty xs


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
    (fun (name, def) -> item (Sym.pp_string name) (ResourcePredicates.pp_definition def))
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
