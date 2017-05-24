type identifier_type =
  | VarId
  | TypedefId
  | OtherId of string

(* TODO debug *)
let string_of_typ = function
  | VarId ->
      "varId"
  | TypedefId ->
      "typedefId"
  | OtherId str ->
      "otherId(" ^ str ^ ")"

let push_context:(unit -> unit) ref= ref (fun () -> assert false)
let pop_context:(unit -> unit) ref = ref (fun () -> assert false)

let declare_varname:(string -> unit) ref = ref (fun _ -> assert false)
let declare_typename:(string -> unit) ref = ref (fun _ -> assert false)


exception PreParser_undeclared_identifier of string * Location_ocaml.t
