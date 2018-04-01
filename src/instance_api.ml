(* API between web server and a cerberus instance *)

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

(* state * node id option *)
type active_node = (string * int)

type filename = string

(* input: request *)
type request =
  [ `Elaborate of conf * filename
  | `Execute of conf * filename * exec_mode
  | `Step of conf * filename * active_node ]

type node =
  | Branch of int * string * Json.json * Location_ocaml.t option
      (* id * label * serialised memory * location *)
  | Leaf of int * string * string (* id * label * marshalled state *)

type edge =
  | Edge of int * int (* from -> to *)

(* NOTE: the execution tree is a pair of node and edges lists
 * this encoding works better in the client side (js libraries)
 * than functional AST for trees *)
type exec_tree = node list * edge list

type ast_result =
  { cabs: string option;
    ail:  string option;
    core: string option;
  }

type elaboration_result =
  { pp: ast_result;
    ast: ast_result;
    locs: Json.json; (* TODO: change this to something else than json *)
    result: string;
  }

(* output: result *)
type result =
  | Elaboration of elaboration_result
  | Execution of string                      (* cerberus result *)
  | Interaction of string option * exec_tree (* maybe result * execution tree *)
  | Failure of string
