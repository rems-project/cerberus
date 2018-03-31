open Prelude

(* execution mode *)
type exec_mode =
  | Random
  | Exhaustive

let string_of_exec_mode = function
  | Random -> "random"
  | Exhaustive -> "exhaustive"

(* user configuration per instance *)
type conf =
  { rewrite: bool;
  }

(* NOTE: the execution tree is a pair of node and edges lists
 * this encoding works better in the client side (js libraries)
 * than functional AST for trees *)

type node =
  | Branch of int * string * Json.json * Location_ocaml.t option
      (* id * label * serialised memory * location *)
  | Leaf of int * string * string (* id * label * marshalled state *)

type edge =
  | Edge of int * int (* from -> to *)

type exec_tree = node list * edge list

type ast_result =
  { cabs: string option;
    ail:  string option;
    core: string option;
  }

type elaboration_result =
  { pp: ast_result;
    ast: ast_result;
    locs: Json.json;
  }

type result =
  | Elaboration of elaboration_result
  | Execution of string
  | Interaction of string option * exec_tree
  | Failure of string

module type Instance = sig
  val name: string
  val elaborate: conf -> string -> result
  val execute: conf -> string -> exec_mode -> result
  val step: conf -> string -> (string * int) option -> result
end

(* handle multiple instances *)

(*
let instances : (string * (module Instance)) list ref =
  ref []
   *)

let current: (unit -> (module Instance)) ref =
  ref (fun () -> failwith "no model loaded")

(*
let add_model m =
  let s = string_of_mem_switch () in
  print_endline ("linking " ^ s);
  instances := (string_of_mem_switch (), m) :: !instances
   *)

let name () =
  let module Model = (val !current()) in Model.name

let check_model s =
  let module Model = (val !current()) in Model.name = s

(*
let set_model s =
  print_endline ("Trying to change to " ^ name ());
  print_endline ("Currently at " ^ name ());
  if check_model s then
    print_endline ("Don't change model, continuing at " ^ s)
  else
  begin
    print_endline ("Changing to model " ^ s);
    match List.assoc_opt s !instances with
    | Some m -> current := fun () -> m
    | None -> failwith ("Unknown model " ^ s)
  end
*)

let set_model m =
  current := fun () -> m

(* easy API access *)


let elaborate conf fname =
  let module Model = (val !current()) in
  print_endline ("Accessing API " ^ Model.name);
  Model.elaborate conf fname

let execute conf fname mode =
  let module Model = (val !current()) in Model.execute conf fname mode

let step conf fname active =
  let module Model = (val !current()) in
  print_endline ("Accessing " ^ Model.name);
  Model.step conf fname active
