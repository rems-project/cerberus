type identifier_type =
  | VarId
  | TypedefId
  | OtherId of string

let push_context:(unit -> unit) ref= ref (fun () -> assert false)
let pop_context:(unit -> unit) ref = ref (fun () -> assert false)

let declare_varname:(Cabs.cabs_identifier -> unit) ref = ref (fun _ -> assert false)
let declare_typename:(Cabs.cabs_identifier -> unit) ref = ref (fun _ -> assert false)
