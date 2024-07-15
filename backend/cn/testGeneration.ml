module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend
open CF

let _weak_sym_equal s1 s2 =
  String.equal (Pp_symbol.to_string_pretty s1) (Pp_symbol.to_string_pretty s2)
;;

let string_of_ctype (ty : Ctype.ctype) : string =
  Cerb_colour.do_colour := false;
  let tmp = String_ail.string_of_ctype ~is_human:true Ctype.no_qualifiers ty ^ " " in
  Cerb_colour.do_colour := true;
  tmp
;;

type variables = (Symbol.sym * (Ctype.ctype * IT.t)) list

let string_of_variables (vars : variables) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, (ty, e)) ->
           Pp_symbol.to_string_pretty x
           ^ " -> ("
           ^ string_of_ctype ty
           ^ ", "
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ")")
         vars)
  ^ " }"
;;

type locations = (IT.t * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (e, x) ->
           "(*"
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ") -> "
           ^ Pp_symbol.to_string_pretty x)
         locs)
  ^ " }"
;;

type members = (Symbol.sym * (string * (Ctype.ctype * Symbol.sym)) list) list

let string_of_members (ms : members) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, ms) ->
           Pp_symbol.to_string_pretty x
           ^ " -> {"
           ^ String.concat
               ", "
               (List.map
                  (fun (y, (ty, z)) ->
                    "."
                    ^ y
                    ^ ": "
                    ^ string_of_ctype ty
                    ^ " = "
                    ^ Pp_symbol.to_string_pretty z)
                  ms))
         ms)
  ^ " }"
;;

type constraints = IT.t list

let string_of_constraints (cs : constraints) : string =
  "{ "
  ^ String.concat "; " (List.map (fun e -> Pp_utils.to_plain_pretty_string (IT.pp e)) cs)
  ^ " }"
;;

type goal = variables * members * locations * constraints

let _string_of_goal ((vars, ms, locs, cs) : goal) : string =
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
;;

type test_framework = GTest

let main
  (_output_dir : string)
  (_filename : string)
  (_max_depth : int)
  (_sigma : _ AilSyntax.sigma)
  (_prog5 : unit Mucore.mu_file)
  (_tf : test_framework)
  : unit
  =
  ()
;;
