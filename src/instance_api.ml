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
  { rewrite_core: bool;       (* run rewriting step *)
    sequentialise_core: bool; (* sequentialise flag *)
    cpp_cmd: string;          (* cpp command used before parsing *)
    core_impl: string;        (* core implementation file *)
    cerb_debug_level: int;    (* Cerberus debug level (not include server) *)
    timeout: int;             (* instance execution timeout *)
    tagDefs: string;          (* marshalled tag defs *)
  }

type active_node =
  { last_id: int; (* used to feed node id generation in the current instance *)
    marshalled_state: string;
    active_id: int;
    tagDefs: string;
  }

type filename = string

(* input: request *)
type request =
  [ `Elaborate of conf * filename
  | `Execute of conf * filename * exec_mode
  | `Step of conf * filename * active_node option ]

type point = int * int
type range = point * point

type node =
  | Branch of int * string * Json.json * Location_ocaml.t option * string option * string
      (* id * label * serialised memory * (c location * uid * arena) *)
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
    locs: (range * range) list;
    result: string;
  }

(* output: result *)
type result =
  | Elaboration of elaboration_result
  | Execution of string               (* cerberus result *)
  | Interactive of string * (string * PPrint.range) list * exec_tree (* tagDefs * range list * execution tree *)
  | Step of string option * int * exec_tree (* maybe result * active node id * execution tree *)
  | Failure of string
