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
let init_sym = Sym.fresh_named "init"

let owned_iargs _ct = []
let owned_oargs ct = 
  [(value_sym, BT.of_sct ct);
   (init_sym, BT.Bool)]
let q_owned_oargs ct = 
  [(value_sym, BT.Map (Integer, BT.of_sct ct));
   (init_sym, BT.Map (Integer, BT.Bool))]


type oarg = Sym.t * IT.t
type oargs = oarg list

let pp_oarg (s, oarg) = Sym.pp s ^^^ equals ^^^ IT.pp oarg
let pp_oargs oargs = flow_map (comma ^^ space) pp_oarg oargs



type t = resource_type * oargs


let request (r, _oargs) = r

let pp (r, oargs) = ResourceTypes.pp r ^^^ !^"where" ^^^ pp_oargs oargs


let json re : Yojson.Safe.t = `String (Pp.plain (pp re))


let subst substitution ((r, oargs) : t) = 
  (ResourceTypes.subst substitution r,
   List.map_snd (IT.subst substitution) oargs)


let free_vars (r, oargs) = 
  SymSet.union (ResourceTypes.free_vars r)
    (IT.free_vars_list (List.map snd oargs))
    


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







