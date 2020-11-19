open Pp
(* open Resultat
 * open TypeErrors *)

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
module CF = Cerb_frontend
module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = ArgumentTypes.Make(RT)



(* Auxiliaries *)

module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)




let impl_lookup (loc : Loc.t) (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None ->
    Debug_ocaml.error
      ("Unbound implementation defined constant " ^
         (CF.Implementation.string_of_implementation_constant i))
  | Some v -> v


type closed_stored_predicate_definition =
  { value_arg: Sym.t;
    clause: IT.t -> RT.l; }


type struct_decl = 
  { members: (BT.member * (Sctypes.t * BT.t)) list;
    (* sizes: (BT.member * RE.size) list;
     * offsets: (BT.member * Z.t) list;
     * representable: IT.t -> LC.t; *)
    (* closed: RT.t;  *)
    closed_stored: RT.t;
    closed_stored_predicate_definition: 
      closed_stored_predicate_definition
  }

type struct_decls = struct_decl SymMap.t

type resource_predicate = 
  { arguments : (Sym.t * LS.t) list;
    clauses : IT.t -> (RT.l list);
  }

type t = 
  { struct_decls : struct_decls; 
    fun_decls : (Loc.t * FT.t) SymMap.t;
    impl_fun_decls : (FT.t) ImplMap.t;
    impl_constants : BT.t ImplMap.t;
    stdlib_funs : SymSet.t;
    resource_predicates : resource_predicate IdMap.t;
  } 

let empty = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
    stdlib_funs = SymSet.empty;
    resource_predicates = IdMap.empty;
  }

let get_predicate_def loc global predicate_name = 
  let open Resources in
  let open TypeErrors in
  let open Resultat in
  match predicate_name with
  | Id id -> 
     begin match IdMap.find_opt id global.resource_predicates with
     | Some def -> return def
     | None -> fail loc (Missing_predicate id)
     end
  | Tag tag ->
     let* decl = match SymMap.find_opt tag global.struct_decls with
       | Some decl -> return decl
       | None -> fail loc (Missing_struct tag)
     in
     let {value_arg; clause} = 
       decl.closed_stored_predicate_definition in
     let def = 
       { arguments = [(value_arg, LS.Base (BT.Struct tag))]; 
         clauses = fun it -> [clause it] }
     in
     return def


let get_fun_decl loc global sym = SymMapM.lookup loc global.fun_decls sym
let get_impl_fun_decl loc global i = impl_lookup loc global.impl_fun_decls i
let get_impl_constant loc global i = impl_lookup loc global.impl_constants i



let pp_struct_decl (sym,decl) = 
  item ("struct " ^ plain (Sym.pp sym) ^ " (raw)") 
       (Pp.list (fun (m, (ct, bt)) -> 
            typ (Id.pp m) (BT.pp true bt)) decl.members) 
  ^/^
  item ("struct " ^ plain (Sym.pp sym) ^ " (closed stored)") 
       (RT.pp decl.closed_stored)
  ^/^
  item ("struct " ^ plain (Sym.pp sym) ^ " (predicate)") 
    (RT.pp_l 
       (decl.closed_stored_predicate_definition.clause
          (IT.S (Sym.fresh_named "struct_pointer"))))

let pp_struct_decls decls = Pp.list pp_struct_decl (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls


