open Cerb_frontend
open Rc_annot

(* temporarily imported from refined C *)
(* LICENCE: https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/LICENSE *)



(* SOURCE: https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/frontend/coq_ast.ml *)
let coq_locs : Location.Pool.t = Location.Pool.make ()


(* SOURCE: https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/frontend/ail_to_coq.ml *)
type loc       = Location_ocaml.t



(* SOURCE: https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/frontend/ail_to_coq.ml *)
let id_to_str : Symbol.identifier -> string =
  fun Symbol.(Identifier(_,id)) -> id

let register_loc : Location.Pool.t -> loc -> Location.t = fun p loc ->
  match Location_ocaml.(get_filename loc, to_cartesian loc) with
  | (Some(f), Some((l1,c1),(0 ,0 ))) -> Location.make f l1 c1 l1 c1 p
  | (Some(f), Some((l1,c1),(l2,c2))) -> Location.make f l1 c1 l2 c2 p
  | (_      , _                    ) -> Location.none coq_locs

let register_str_loc : Location.Pool.t -> loc -> Location.t = fun p loc ->
  match Location_ocaml.(get_filename loc, to_cartesian loc) with
  | (Some(f), Some((l1,c1),(l2,c2))) -> Location.make f l1 (c1+1) l2 (c2-1) p
  | (_      , _                    ) -> Location.none coq_locs

let mkloc elt loc = Location.{ elt ; loc }


let collect_rc_attrs : Annot.attributes -> rc_attr list =
  let fn acc Annot.{attr_ns; attr_id; attr_args} =
    match Option.map id_to_str attr_ns with
    | Some("rc") ->
        let rc_attr_id =
          let Symbol.(Identifier(loc, id)) = attr_id in
          mkloc id (register_loc rc_locs loc)
        in
        let rc_attr_args =
          let fn (loc, s) = mkloc s (register_str_loc rc_locs loc) in
          List.map fn attr_args
        in
        {rc_attr_id; rc_attr_args} :: acc
    | _          -> acc
  in
  fun (Annot.Attrs(attrs)) -> List.fold_left fn [] attrs
