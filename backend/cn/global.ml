open Pp
(* open Resultat
 * open TypeErrors *)

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
module StringMap = Map.Make(String)
module CF = Cerb_frontend
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = ArgumentTypes.Make(RT)
open Memory



open Predicates





let early = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "EarlyAlloc" in
  let start_s = Sym.fresh () in
  let start_t = sym_ (start_s, Loc) in
  let end_s = Sym.fresh () in
  let end_t = sym_ (end_s, Loc) in
  let iargs = [(end_s, BT.Loc)] in
  let oargs = [] in
  let block = 
    Resources.char_region 
      (start_t)
      (add_ (sub_ (pointerToIntegerCast_ end_t, pointerToIntegerCast_ start_t), int_ 1))
      (q_ (1, 1))
  in
  let lrt =
    LRT.Resource (block, 
    LRT.Constraint (IT.good_pointer start_t (Sctypes.Sctype ([], Void)),
    LRT.Constraint (IT.good_pointer end_t (Sctypes.Sctype ([], Void)),
    LRT.I)))
  in
  let predicate = {
      pointer = start_s;
      iargs; 
      oargs; 
      clauses = [Clause {condition = lrt; outputs = []}]; 
    } 
  in
  (id, predicate)



let zero_region = 
  let open Resources in
  let open BT in
  let open IT in
  let id = "ZeroRegion" in
  let pointer_s = Sym.fresh () in
  let pointer_t = sym_ (pointer_s, Loc) in
  let length_s = Sym.fresh () in
  let length_t = sym_ (length_s, Integer) in
  let iargs = [(length_s, BT.Integer)] in
  let oargs = [] in
  let array = 
    RE.array pointer_t length_t (Z.of_int 1)
      (fun q -> int_ 0) (q_ (1,1))
  in
  let lrt =
    LRT.Resource (array, 
    LRT.Constraint (IT.good_pointer pointer_t (Sctypes.Sctype ([], Void)),
    LRT.I))
  in
  let predicate = {
      pointer = pointer_s;
      iargs; 
      oargs; 
      clauses = [(Clause {condition=lrt; outputs=[]})]; 
    } 
  in
  (id, predicate)







let builtin_predicates_list = [
    early;
    zero_region;
  ]

let builtin_predicates =
  List.fold_left (fun acc (name,def) -> StringMap.add name def acc) 
    StringMap.empty builtin_predicates_list
  




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







type struct_decls = struct_layout SymMap.t


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
    resource_predicates = builtin_predicates;
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

let pp global = 
  pp_struct_decls global.struct_decls ^^ hardline ^^
  pp_fun_decls global.fun_decls





