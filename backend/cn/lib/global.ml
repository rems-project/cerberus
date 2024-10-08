open Pp
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module IdMap = Map.Make (Id)
module RT = ReturnTypes
module AT = ArgumentTypes

type t =
  { struct_decls : Memory.struct_decls;
    datatypes : BaseTypes.dt_info SymMap.t;
    datatype_constrs : BaseTypes.constr_info SymMap.t;
    datatype_order : Sym.t list list option;
    fun_decls : (Locations.t * AT.ft option * Sctypes.c_concrete_sig) SymMap.t;
    resource_predicates : ResourcePredicates.definition SymMap.t;
    logical_functions : LogicalFunctions.definition SymMap.t;
    lemmata : (Locations.t * AT.lemmat) SymMap.t
  }

let empty =
  { struct_decls = SymMap.empty;
    datatypes = SymMap.empty;
    datatype_constrs = SymMap.empty;
    datatype_order = None;
    fun_decls = SymMap.empty;
    resource_predicates =
      SymMap.(empty |> add Alloc.Predicate.sym ResourcePredicates.alloc);
    logical_functions = SymMap.empty;
    lemmata = SymMap.empty
  }


let get_resource_predicate_def global id = SymMap.find_opt id global.resource_predicates

let get_logical_function_def global id = SymMap.find_opt id global.logical_functions

let get_fun_decl global sym = SymMap.find_opt sym global.fun_decls

let get_lemma global sym = SymMap.find_opt sym global.lemmata

let sym_map_from_bindings xs =
  List.fold_left (fun m (nm, x) -> SymMap.add nm x m) SymMap.empty xs


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


let pp_struct_decls decls = Pp.list pp_struct_layout (SymMap.bindings decls)

let pp_fun_decl (sym, (_, t, _)) =
  item (plain (Sym.pp sym)) (Pp.option (AT.pp RT.pp) "(no spec)" t)


let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp_resource_predicate_definitions defs =
  separate_map
    hardline
    (fun (name, def) -> item (Sym.pp_string name) (ResourcePredicates.pp_definition def))
    (SymMap.bindings defs)


let pp global =
  pp_struct_decls global.struct_decls
  ^^ hardline
  ^^ pp_fun_decls global.fun_decls
  ^^ hardline
  ^^ pp_resource_predicate_definitions global.resource_predicates


let mutual_datatypes (global : t) tag =
  let deps tag =
    let info = SymMap.find tag global.datatypes in
    info.all_params |> List.filter_map (fun (_, bt) -> BaseTypes.is_datatype_bt bt)
  in
  let rec seek tags = function
    | [] -> tags
    | new_tag :: new_tags ->
      if SymSet.mem new_tag tags then
        seek tags new_tags
      else
        seek (SymSet.add new_tag tags) (deps new_tag @ new_tags)
  in
  seek SymSet.empty [ tag ] |> SymSet.elements
