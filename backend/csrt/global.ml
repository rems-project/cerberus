open Pp
open List
open Except
open TypeErrors
open Tools

module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = FunctionTypes



(* Auxiliaries *)

module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)




let impl_lookup (loc : Loc.t) (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None -> fail loc (Unbound_impl_const i)
  | Some v -> return v


type struct_sig = { sbinder: Sym.t; souter: RT.l }

type struct_decl = 
  { raw: (BT.member * BT.t) list;
    ctypes: (BaseTypes.member * CF.Ctype.ctype) list;
    open_type: struct_sig;
    closed_type: struct_sig; 
  }

type struct_decls = struct_decl SymMap.t

type t = 
  { struct_decls : struct_decls; 
    fun_decls : (Loc.t * FT.t) SymMap.t;
    impl_fun_decls : FT.t ImplMap.t;
    impl_constants : BT.t ImplMap.t;
  } 

let empty = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty;
    impl_fun_decls = ImplMap.empty;
    impl_constants = ImplMap.empty;
  }

let get_struct_decl loc struct_decls (BT.Tag s) = 
  match SymMap.find_opt s struct_decls with
  | Some decl -> return decl 
  | None -> fail loc (Struct_not_defined (BT.Tag s))

let get_fun_decl loc global sym = symmap_lookup loc global.fun_decls sym
let get_impl_fun_decl loc global i = impl_lookup loc global.impl_fun_decls i
let get_impl_constant loc global i = impl_lookup loc global.impl_constants i

let pp_struct_decl (sym,decl) = 
  let tag = BT.Tag sym in
  let open_typ = 
    RT.Computational ((decl.open_type.sbinder, BT.Struct tag), 
                      decl.open_type.souter) 
  in
  let closed_typ = 
    RT.Computational ((decl.closed_type.sbinder, BT.Struct tag), 
                      decl.closed_type.souter) 
  in
  item (plain (Sym.pp sym) ^ " (raw)") 
       (pp_list (fun (BT.Member m, bt) -> typ !^m (BT.pp true bt)) decl.raw) 
  ^/^
  item (plain (Sym.pp sym) ^ " (open)") (RT.pp open_typ) 
  ^/^
  item (plain (Sym.pp sym) ^ " (closed)") 
       (RT.pp closed_typ)

let pp_struct_decls decls = pp_list pp_struct_decl (SymMap.bindings decls) 

let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

let pp_items global = 
  [ (1, h2 "Structs")
  ; (1, pp_struct_decls global.struct_decls)
  ; (1, h2 "Functions")
  ; (1, pp_fun_decls global.fun_decls)
  ]

let pp global = separate (break 1) (map snd (pp_items global))

