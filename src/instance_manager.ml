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
    result: string;
  }

type result =
  | Elaboration of elaboration_result
  | Execution of string
  | Interaction of string option * exec_tree
  | Failure of string

type request =
  [ `Elaborate of conf * string
  | `Execute of conf * string * exec_mode
  | `Step of conf * string * (string * int) option ]

(*
module type Instance = sig
  val name: string
  val elaborate: conf -> string -> result
  val execute: conf -> string -> exec_mode -> result
  val step: conf -> string -> (string * int) option -> result
end
*)