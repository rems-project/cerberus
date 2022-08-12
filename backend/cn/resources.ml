open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints
module LCSet = Set.Make(LC)



open ResourceTypes

let value_sym = Sym.fresh_named "value"

let size_sym = Sym.fresh_named "size"


let owned_iargs _ct = []
let owned_oargs_list ct = [(value_sym, BT.of_sct ct)]
let owned_oargs ct = BT.Record (owned_oargs_list ct)

let q_owned_iargs _ct = []    
let q_owned_oargs_list ct = [(value_sym, BT.Map (Integer, BT.of_sct ct))]
let q_owned_oargs ct = BT.Record (q_owned_oargs_list ct)

let block_iargs = []
let block_oargs_list = []
let block_oargs = BT.Record block_oargs_list

let q_block_iargs = [(value_sym, BT.Integer)]    
let q_block_oargs_list = []
let q_block_oargs = BT.Record q_block_oargs_list
    


type oargs = O of IT.t
let pp_oargs (O t) = IT.pp t


type resource = resource_type * oargs

type t = resource

let request (r, _oargs) = r

let oargs_bt (_re, O oargs) = IT.bt oargs


let pp (r, oargs) = ResourceTypes.pp r ^^ parens(pp_oargs oargs)


let json re : Yojson.Safe.t = `String (Pp.plain (pp re))


let subst substitution ((r, O oargs) : t) = 
  (ResourceTypes.subst substitution r,
   O (IT.subst substitution oargs))


let free_vars (r, O oargs) = 
  SymSet.union (ResourceTypes.free_vars r) (IT.free_vars oargs)
    


(* assumption: the resource is owned *)
let derived_lc1 = function
  | _ -> []


(* assumption: both resources are owned at the same *)
(* todo, depending on how much we need *)
let derived_lc2 resource resource' =
  match resource, resource' with
  | _ -> []


let pointer_facts =
  let rec aux acc = function
    | [] -> acc
    | r :: rs ->
       let acc = derived_lc1 r @ (List.concat_map (derived_lc2 r) rs) @ acc in 
       aux acc rs
  in
  fun resources -> aux [] resources







