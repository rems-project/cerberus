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
    resource_predicate_order : Sym.t list list option;
    logical_functions : Definition.Function.t Sym.Map.t;
    logical_function_order : Sym.t list list option;
    lemmata : (Locations.t * AT.lemmat) Sym.Map.t
  }

let empty =
  { struct_decls = Sym.Map.empty;
    datatypes = Sym.Map.empty;
    datatype_constrs = Sym.Map.empty;
    datatype_order = None;
    fun_decls = Sym.Map.empty;
    resource_predicates = Sym.Map.(empty |> add Alloc.Predicate.sym Definition.alloc);
    resource_predicate_order = None;
    logical_functions = Sym.Map.empty;
    logical_function_order = None;
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


type error =
  | Unknown_function of Sym.t
  | Unknown_struct of Sym.t
  | Unknown_datatype of Sym.t
  | Unknown_datatype_constr of Sym.t
  | Unknown_resource_predicate of
      { id : Sym.t;
        logical : bool
      }
  | Unknown_logical_function of
      { id : Sym.t;
        resource : bool
      }
  | Unknown_lemma of Sym.t
  | Unexpected_member of Id.t list * Id.t (** TODO replace with actual terms *)

type global_t_alias_do_not_use = t

module type ErrorReader = sig
  type 'a t

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val get_global : unit -> global_t_alias_do_not_use t

  val fail : Locations.t -> error -> 'a t
end

module type Lifted = sig
  type 'a t

  val get_resource_predicate_def : Locations.t -> Sym.t -> Definition.Predicate.t t

  val get_logical_function_def : Locations.t -> Sym.t -> Definition.Function.t t

  val get_fun_decl
    :  Locations.t ->
    Sym.t ->
    (Cerb_location.t * AT.ft option * Sctypes.c_concrete_sig) t

  val get_lemma : Locations.t -> Sym.t -> (Cerb_location.t * AT.lemmat) t

  val get_struct_decl : Locations.t -> Sym.t -> Memory.struct_layout t

  val get_member_type : Locations.t -> Id.t -> Memory.struct_piece list -> Sctypes.ctype t

  val get_datatype : Locations.t -> Sym.t -> BaseTypes.dt_info t

  val get_datatype_constr : Locations.t -> Sym.t -> BaseTypes.constr_info t
end

module Lift (M : ErrorReader) : Lifted with type 'a t := 'a M.t = struct
  let lift f loc sym msg =
    let ( let@ ) = M.bind in
    let@ global = M.get_global () in
    match f global sym with Some x -> M.return x | None -> M.fail loc (msg global)


  let get_logical_function_def_opt id = get_logical_function_def id

  let get_logical_function_def loc id =
    lift get_logical_function_def loc id (fun global ->
      let res = get_resource_predicate_def global id in
      Unknown_logical_function { id; resource = Option.is_some res })


  let get_resource_predicate_def loc id =
    lift get_resource_predicate_def loc id (fun global ->
      let log = get_logical_function_def_opt global id in
      Unknown_resource_predicate { id; logical = Option.is_some log })


  let get_fun_decl loc fsym = lift get_fun_decl loc fsym (fun _ -> Unknown_function fsym)

  let get_lemma loc lsym = lift get_lemma loc lsym (fun _ -> Unknown_lemma lsym)

  let get_struct_decl loc tag = lift get_struct_decl loc tag (fun _ -> Unknown_struct tag)

  let get_member_type loc member layout =
    let member_types = Memory.member_types layout in
    match List.assoc_opt Id.equal member member_types with
    | Some membertyp -> M.return membertyp
    | None -> M.fail loc (Unexpected_member (List.map fst member_types, member))


  let get_datatype loc tag =
    lift get_datatype loc tag (fun _ -> Unknown_datatype_constr tag)


  let get_datatype_constr loc tag =
    lift get_datatype_constr loc tag (fun _ -> Unknown_datatype_constr tag)
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
