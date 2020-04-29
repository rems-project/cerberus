open PPrint
open Except
open List
open Utils


type t = Binders.t list

let pp ts = flow_map (space ^^ comma ^^ break 1) Binders.pp ts

let parse_sexp loc (names : NameMap.t) s = 
  let open Sexplib in
  let rec aux names acc ts = 
    match ts with
    | [] -> return (rev acc, names)
    | b :: bs ->
       Binders.parse_sexp loc names b >>= fun (b, names) ->
       aux names (b :: acc) bs
  in
  match s with
  | Sexp.List ts -> aux names [] ts
  | t -> parse_error loc "binders" t

let subst sym with_sym bs = 
  map (Binders.subst sym with_sym) bs

let names t = List.map (fun {Binders.name; _} -> name) t

let rename newname t = 
  match t with
  | [] -> print_endline "\n\nempty return type\n\n"; []
  | {Binders.name; _} :: _ -> subst name newname t



