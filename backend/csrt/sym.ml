(* open Cerb_frontend *)
open Except
open Cerb_frontend

module StringMap = Map.Make(String)

type t = Symbol.sym

let fresh = Symbol.fresh
let fresh_pretty = Symbol.fresh_pretty
let pp = Pp_symbol.to_string_pretty

let of_asym (s : 'bty Mucore.asym) = 
  let (Annotated (_, _, sym)) = s in sym

let lof_asym (s : 'bty Mucore.asym) = 
  let (Annotated (annots, _, sym)) = s in 
  (sym, Annot.get_loc_ annots)

let compare = Symbol.symbol_compare

let parse loc (names : (t * Location_ocaml.t) StringMap.t) name = 
  match StringMap.find_opt name names with
  | Some (sym,_) -> return sym
  | None -> Except.fail (Printf.sprintf "%s. Unbound variable %s" (Location.pp loc) name)



