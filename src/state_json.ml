open Json


(* WARN: Serialising just location *)
module ThreadStateJSON: (JSON with type t = Core_run.thread_state) =
struct
  open Core_run
  type t = thread_state
  let serialise st = LocationJSON.serialise (st.current_loc)
  let parse _ = failwith "thread state"
end

(*
(* TODO *)
module CoreStateJSON: (JSON with type t = Core_run.core_state) =
struct
  open Core_run
  type t = core_state
  let serialise_
  let serialise st =**)
