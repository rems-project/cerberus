open Pp
open Resultat
open TypeErrors

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
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
     let err = 
       !^"Unbound implementation defined constant" ^^^
         !^(CF.Implementation.string_of_implementation_constant i)
     in
     fail loc (Internal err)
  | Some v -> return v


type struct_decl = 
  { raw: (BT.member * BT.t) list;
    sizes: (BT.member * RE.size) list;
    ranges: (BT.member * (IT.t -> LC.t)) list;
    closed: RT.t; 
    closed_stored: RT.t;
    closed_stored_aux: IT.t -> RT.l;
  }

type struct_decls = struct_decl SymMap.t

type t = 
  { tagDefs : CF.Core.core_tag_definitions;
    struct_decls : struct_decls; 
    fun_decls : (Loc.t * FT.t) SymMap.t;
    impl_fun_decls : (FT.t) ImplMap.t;
    impl_constants : BT.t ImplMap.t;
  } 

let empty tagDefs = 
  { tagDefs = tagDefs;
    struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
  }

let get_struct_decl loc struct_decls (BT.Tag s) = 
  match SymMap.find_opt s struct_decls with
  | Some decl -> return decl 
  | None -> 
     let err = !^"struct" ^^^ BT.pp_tag (BT.Tag s) ^^^ !^"not defined" in
     fail loc (Generic err)

let get_fun_decl loc global sym = SymMapM.lookup loc global.fun_decls sym
let get_impl_fun_decl loc global i = impl_lookup loc global.impl_fun_decls i
let get_impl_constant loc global i = impl_lookup loc global.impl_constants i

let pp_struct_decl (sym,decl) = 
  item ("struct " ^ plain (Sym.pp sym) ^ " (raw)") 
       (pp_list (fun (BT.Member m, bt) -> typ !^m (BT.pp true bt)) decl.raw) 
  ^/^
  item ("struct " ^ plain (Sym.pp sym) ^ " (closed)") 
       (RT.pp decl.closed)
  ^/^
  item ("struct " ^ plain (Sym.pp sym) ^ " (closed stored)") 
       (RT.pp decl.closed_stored)

let pp_struct_decls decls = pp_list pp_struct_decl (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls


