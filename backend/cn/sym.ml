module CF = Cerb_frontend
module S = CF.Symbol
include S

let executable_spec_enabled = ref false

type t = S.sym

type sym = t

let equal = S.symbolEquality

let compare = S.symbol_compare

type description = S.symbol_description

let description (s : t) : description = S.symbol_description s

let dest = function CF.Symbol.Symbol (digest, nat, oname) -> (digest, nat, oname)

let pp_string sym =
  if !executable_spec_enabled then
    CF.Pp_symbol.to_string_pretty sym
  else
    CF.Pp_symbol.to_string_pretty_cn sym


let pp sym = Pp.string (pp_string sym)

let pp_debug sym = Pp.string (CF.Symbol.show_raw_less sym)

let num = S.symbol_num

let fresh () = S.fresh ()

let fresh_pretty = fresh_cn

let fresh_named = fresh_cn

let fresh_description = S.fresh_description

let fresh_same (s : t) : t = fresh_description (S.symbol_description s)

let has_id = function
  | CF.Symbol.Symbol (_digest, _nat, SD_Id str) -> Some str
  | _ -> None


let has_id_with f sym = match has_id sym with None -> false | Some str -> f str

let has_cn_id_with f = function
  | CF.Symbol.Symbol (_, _, SD_CN_Id str) -> f str
  | _ -> false


module StringHash = Hashtbl.Make (struct
    type t = String.t

    let equal = String.equal

    let hash = Hashtbl.hash
  end)

let name_uses = StringHash.create 20

let name_make_uniq str =
  let next = match StringHash.find_opt name_uses str with None -> 0 | Some i -> i + 1 in
  StringHash.add name_uses str next;
  str ^ string_of_int next


let fresh_make_uniq name = fresh_named (name_make_uniq name)

let fresh_make_uniq_kind ~prefix name = fresh_named (name_make_uniq prefix ^ "_" ^ name)

let json sym = `String (pp_string sym)

let hash = num
