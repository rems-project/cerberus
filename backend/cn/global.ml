module CF = Cerb_frontend
open Pp
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
module StringMap = Map.Make(String)
module RT = ReturnTypes
module AT = ArgumentTypes

module ImplMap = 
  Map.Make (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
    end)


type t = 
  { struct_decls : Memory.struct_decls; 
    fun_decls : (Locations.t * AT.ft * CF.Mucore.trusted) SymMap.t;
    impl_fun_decls : AT.ft ImplMap.t;
    impl_constants : RT.t ImplMap.t;
    resource_predicates : ResourcePredicates.definition StringMap.t;
    logical_predicates : LogicalPredicates.definition StringMap.t;
  } 

let empty = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
    resource_predicates = StringMap.empty;
    logical_predicates = StringMap.empty;
  }


let get_resource_predicate_def global id = StringMap.find_opt id global.resource_predicates
let get_logical_predicate_def global id = StringMap.find_opt id global.logical_predicates
let get_fun_decl global sym = SymMap.find_opt sym global.fun_decls
let get_impl_fun_decl global i = ImplMap.find i global.impl_fun_decls
let get_impl_constant global i = ImplMap.find i global.impl_constants



let pp_struct_layout (tag,layout) = 
  item ("struct " ^ plain (Sym.pp tag) ^ " (raw)") 
    (separate_map hardline (fun Memory.{offset; size; member_or_padding} -> 
         item "offset" (Pp.int offset) ^^ comma ^^^
           item "size" (Pp.int size) ^^ comma ^^^
             item "content" 
               begin match member_or_padding with 
               | Some (member, sct) -> 
                  typ (Id.pp member) (Sctypes.pp sct)
               | None ->
                  parens (!^"padding" ^^^ Pp.int size)
               end
       ) layout
    )


let pp_struct_decls decls = 
  Pp.list pp_struct_layout (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t, _)) = item (plain (Sym.pp sym)) (AT.pp RT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp_resource_predicate_definitions defs =
  separate_map hardline (fun (name, def) ->
      item name (ResourcePredicates.pp_definition def))
    (StringMap.bindings defs)

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls ^^ hardline ^^
  pp_resource_predicate_definitions global.resource_predicates





