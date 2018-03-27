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

type ast_result =
  { cabs: string option;
    ail:  string option;
    core: string option;
  }

type elaboration_result =
  { pp: ast_result;
    ast: ast_result;
    locs: Yojson.json;
  }

type result =
  | Elaboration of elaboration_result
  | Execution of string
  | Interaction of string option * string (* result * steps TODO *)
  | Failure of string

module type Instance = sig
  val name: string
  val elaborate: conf -> string -> result
  val execute: conf -> string -> exec_mode -> result
end

(* handle multiple instances *)

let instances : (string * (module Instance)) list ref =
  ref []

let current: (unit -> (module Instance)) ref =
  ref (fun () -> failwith "no model loaded")

let add_model m =
  let s = string_of_mem_switch () in
  print_endline ("linking " ^ s);
  instances := (string_of_mem_switch (), m) :: !instances

let set_model s =
  print_endline ("Changing to model " ^ s);
  match List.assoc_opt s !instances with
  | Some m -> current := fun () -> m
  | None -> failwith ("Unknown model " ^ s)

(* easy API access *)

let name () =
  let module Model = (val !current()) in Model.name

let elaborate conf fname =
  let module Model = (val !current()) in Model.elaborate conf fname

let execute conf fname mode =
  let module Model = (val !current()) in Model.execute conf fname mode
