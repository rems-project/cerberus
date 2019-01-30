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
    link_libc: bool;          (* link core with libc *)
    cpp_cmd: string;          (* cpp command used before parsing *)
    core_impl: string;        (* core implementation file *)
    cerb_debug_level: int;    (* Cerberus debug level (not include server) *)
    timeout: int;             (* instance execution timeout *)
    tagDefs: string;          (* marshalled tag defs *)
    switches: string list;
    n1570: Yojson.Basic.json;
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
  [ `Elaborate of conf * filename * string
  | `Execute of conf * filename * string * exec_mode
  | `Step of conf * filename * string * active_node option 
  | `BMC of conf * filename * string ]

type point = int * int
type range = point * point

type step_info =
  { step_kind: string; (* kind of step/transition *)
    step_debug: string; (* debug string *)
    step_file: string option; (* from file *)
    step_error_loc: Location_ocaml.t option;
  }

type node =
  { node_id: int;
    node_info: step_info; (* TODO: this might need to be in the edge *)
    memory: Json.json;
    c_loc: Location_ocaml.t;
    core_uid: string option;
    arena: string;
    env: string; (* maybe an associate list ? *)
    next_state: string option; (* marshalled state *)
    outp: string; (* stdout output *)
  }

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
  | BMC of [ `Satisfiable of (string * string list) | `Unsatisfiable of (string * string list) | `Unknown of string ]
  | Failure of string
