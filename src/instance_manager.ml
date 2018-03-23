open Prelude

module type Instance = sig
  val name: string
  val translate: (string, Symbol.sym) Pmap.map
                    * (unit, unit) Translation.C.generic_fun_map
                 -> unit Translation.C.generic_impl
                 -> Symbol.sym UniqueId.supply
                    * (Symbol.sym option
                       * GenTypes.genTypeCategory Translation.A.sigma)
                 -> Symbol.sym * (unit, unit) Core.generic_file
end

let models : (string * (module Instance)) list ref =
  ref []

let current: (unit -> (module Instance)) ref =
  ref (fun () -> failwith "no model loaded")

let add_model m =
  let s = string_of_mem_switch () in
  print_endline ("linking " ^ s);
  models := (string_of_mem_switch (), m) :: !models

let set_model s =
  match List.assoc_opt s !models with
  | Some m -> current := fun () -> m
  | None -> failwith ("Unknown model " ^ s)

(* API *)

let name () =
  let module Model = (val !current()) in Model.name

let translate () =
  let module Model = (val !current()) in Model.translate

