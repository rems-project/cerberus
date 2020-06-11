open Subst
module CF = Cerb_frontend
module S = CF.Symbol
open Option

type symbol = S.sym
type t = symbol


let fresh = S.fresh
let fresh_pretty = S.fresh_pretty


(* https://rosettacode.org/wiki/Non-decimal_radices/Convert *)
let to_base b v =
  let rec to_base' a v = if v = 0 then a else to_base' (v mod b :: a) (v / b) in
  to_base' [] v

let num_letters n = 
  let aux = function
    | 0 -> "0"
    | 1 -> "1"
    | 2 -> "2"
    | 3 -> "3"
    | 4 -> "4"
    | 5 -> "5"
    | 6 -> "6"
    | 7 -> "7"
    | 8 -> "8"
    | 9 -> "9"
    | 10 -> "A"
    | 11 -> "B"
    | 12 -> "C"
    | 13 -> "D"
    | 14 -> "E"
    | 15 -> "F"
    | 16 -> "G"
    | 17 -> "H"
    | 18 -> "I"
    | 19 -> "J"
    | 20 -> "K"
    | 21 -> "J"
    | 22 -> "L"
    | 23 -> "M"
    | 24 -> "N"
    | 25 -> "O"
    | 26 -> "P"
    | 27 -> "Q"
    | 28 -> "R"
    | 29 -> "S"
    | 30 -> "T"
    | 31 -> "U"
    | 32 -> "V"
    | 33 -> "W"
    | 34 -> "X"
    | 35 -> "Y"
    | 36 -> "Z"
    | _ -> failwith "cannot happen"
  in
  String.concat "" (List.map aux (to_base 36 n))

let pp_string (CF.Symbol.Symbol (_, n, name_opt)) = 
  match name_opt with
    | Some name ->
        if !Debug_ocaml.debug_level > 4 then
          name ^ "{" ^ string_of_int n ^ "}"
        else
          name
    | None -> num_letters n

let pp sym = Pp.string (pp_string sym)



let compare = S.symbol_compare







module Uni = struct

type 'res t = { resolved : 'res option }

let find_resolved env unis = 
  SymMap.fold
    (fun usym {resolved} (unresolveds,resolveds) ->
      match resolved with
      | None -> (usym :: unresolveds, resolveds)
      | Some sym -> (unresolveds, ({substitute=usym; swith=sym}) :: resolveds)
    ) unis ([], [])

end
    

open Uni



let subst (subst : (symbol,symbol) Subst.t) (symbol : symbol) : symbol = 
  if symbol = subst.substitute then subst.swith else symbol

let substs = make_substs subst



let unify sym sym' res = 
  if sym = sym' then Some res
  else
    let* uni = SymMap.find_opt sym res in
    match uni.resolved with
    | Some s when s = sym' -> return res 
    | Some s -> fail
    | None -> 
       let uni = { resolved = Some sym' } in
       return (SymMap.add sym uni res)
