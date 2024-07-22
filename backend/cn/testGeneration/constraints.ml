module IT = IndexTerms
open Utils
module CF = Cerb_frontend
open CF

type variables = (Symbol.sym * (Ctype.ctype * IT.t)) list

let string_of_variables (vars : variables) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, (ty, e)) ->
           codify_sym x
           ^ " -> ("
           ^ string_of_ctype ty
           ^ ", "
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ")")
         vars)
  ^ " }"


type locations = (IT.t * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (e, x) ->
           "(*" ^ Pp_utils.to_plain_pretty_string (IT.pp e) ^ ") -> " ^ codify_sym x)
         locs)
  ^ " }"


(** Tracks indirection for a struct's member [name],
    where [carrier] carries its value of type [cty].
    **)
type member =
  { name : string; (** The name of the member *)
    carrier : Sym.sym; (** The name of the carrier*)
    cty : Ctype.ctype (** The type of the member *)
  }

let string_of_member (m : member) : string =
  "." ^ m.name ^ ": " ^ string_of_ctype m.cty ^ " = " ^ codify_sym m.carrier


type members = (Symbol.sym * member list) list

let string_of_members (ms : members) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, ms) ->
           codify_sym x ^ " -> {" ^ String.concat ", " (List.map string_of_member ms))
         ms)
  ^ " }"


type constraints = IT.t list

let string_of_constraints (cs : constraints) : string =
  "{ "
  ^ String.concat "; " (List.map (fun e -> Pp_utils.to_plain_pretty_string (IT.pp e)) cs)
  ^ " }"


type goal = variables * members * locations * constraints

let string_of_goal ((vars, ms, locs, cs) : goal) : string =
  "Vars: "
  ^ string_of_variables vars
  ^ "\n"
  ^ "Ms: "
  ^ string_of_members ms
  ^ "\n"
  ^ "Locs: "
  ^ string_of_locations locs
  ^ "\n"
  ^ "Cs: "
  ^ string_of_constraints cs
  ^ "\n"


