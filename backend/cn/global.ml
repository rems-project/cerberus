open Pp
(* open Resultat
 * open TypeErrors *)

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
module StringMap = Map.Make(String)
module CF = Cerb_frontend
module LC = LogicalConstraints
module RE = Resources.RE
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = ArgumentTypes.Make(RT)
open Memory



open Predicates













(* Auxiliaries *)

module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)




let impl_lookup (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None ->
     Debug_ocaml.error
       ("Unbound implementation defined constant " ^
          (CF.Implementation.string_of_implementation_constant i))
  | Some v -> v








type t = 
  { struct_decls : struct_decls; 
    fun_decls : (Locations.t * FT.t) SymMap.t;
    impl_fun_decls : FT.t ImplMap.t;
    impl_constants : RT.t ImplMap.t;
    (* stdlib_funs : FT.t SymMap.t; *)
    resource_predicates : predicate_definition StringMap.t;
  } 

let empty = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
    (* stdlib_funs = SymMap.empty; *)
    resource_predicates = StringMap.empty;
  }





let get_predicate_def global predicate_name = 
  let open Resources in
  match predicate_name with
  | Id id -> 
     StringMap.find_opt id global.resource_predicates
  | Ctype ct ->
     let layouts tag = SymMap.find_opt tag global.struct_decls in
     let opred = ctype_predicate layouts ct in
     Option.map (ctype_predicate_to_predicate ct) opred

let get_fun_decl global sym = SymMap.find_opt sym global.fun_decls
let get_impl_fun_decl global i = impl_lookup global.impl_fun_decls i
let get_impl_constant global i = impl_lookup global.impl_constants i



let pp_struct_layout (tag,layout) = 
  item ("struct " ^ plain (Sym.pp tag) ^ " (raw)") 
    (separate_map hardline (fun {offset; size; member_or_padding} -> 
         item "offset" (Z.pp offset) ^^ comma ^^^
           item "size" (Z.pp size) ^^ comma ^^^
             item "content" 
               begin match member_or_padding with 
               | Some (member, sct) -> 
                  typ (Id.pp member) (Sctypes.pp sct)
               | None ->
                  parens (!^"padding" ^^^ Z.pp size)
               end
       ) layout
    )


let pp_struct_decls decls = 
  Pp.list pp_struct_layout (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp_predicate_definitions defs =
  separate_map hardline (fun (name, def) ->
      item name
        (pp_predicate_definition def))
    (StringMap.bindings defs)

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls ^^ hardline ^^
  pp_predicate_definitions global.resource_predicates





