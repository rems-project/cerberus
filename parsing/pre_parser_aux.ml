(* This file is from Jacques-Henri Jourdan's parser *)
type identifier_type =
  | VarId
  | TypedefId
  | OtherId

let push_context:(unit -> unit) ref= ref (fun () -> assert false)
let pop_context:(unit -> unit) ref = ref (fun () -> assert false)

let declare_varname:(string -> unit) ref = ref (fun _ -> assert false)
let declare_typename:(string -> unit) ref = ref (fun _ -> assert false)
