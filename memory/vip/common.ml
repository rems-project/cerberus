(* Things mostly taken unchanged from the concrete memory model that
   we might want to put in a common module *)
open Ctype

let offsetsof = Ocaml_implementation.offsetsof
(* TODO(state-removal) *)
let sizeof ?(tagDefs= Tags.tagDefs ()) ty = Ocaml_implementation.sizeof tagDefs ty
let alignof ?(tagDefs= Tags.tagDefs ()) ty = Ocaml_implementation.alignof tagDefs ty

let ity_max ity =
  let open Z in
  match (Ocaml_implementation.get ()).sizeof_ity ity with
    | Some n ->
        let signed_max =
          sub (pow (of_int 2) Stdlib.(8*n-1)) one in
        let unsigned_max =
          sub (pow (of_int 2) Stdlib.(8*n)) one in
        let ity = match ity with
          | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
          | _ -> ity
        in
        begin match ity with
          | Char ->
              if (Ocaml_implementation.get ()).is_signed_ity Char then
                signed_max
              else
                unsigned_max
          | Bool ->
              (* TODO: not sure about this (maybe it should be 1 and not 255? *)
              unsigned_max
          | Size_t
          | Wchar_t (* TODO: it is implementation defined if unsigned *)
          | Unsigned _ ->
              unsigned_max
          | Ptrdiff_t
          | Wint_t (* TODO *)
          | Signed _ ->
              signed_max
          |  Ptraddr_t ->
              unsigned_max
          | Enum nm ->
              assert false
        end
    | None ->
        failwith "the VIP memory model requires a complete implementation MAX"

let ity_min ity =
  let open Z in
  let ity = match ity with
    | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
    | _ -> ity
  in
  match ity with
    | Char ->
        if (Ocaml_implementation.get ()).is_signed_ity Char then
          neg (pow (of_int 2) Stdlib.(8-1))
        else
          zero
    | Bool
    | Size_t
    | Wchar_t (* TODO: it is implementation defined if unsigned *)
    | Wint_t
    | Unsigned _ ->
        (* all of these are unsigned *)
        zero
    | Ptrdiff_t
    | Signed _ ->
        (* and all of these are signed *)
        begin match (Ocaml_implementation.get ()).sizeof_ity ity with
          | Some n ->
              neg (pow (of_int 2) Stdlib.(8*n-1))
          | None ->
              failwith "the VIP memory model requires a complete implementation MIN"
        end
    | Ptraddr_t -> zero
    | Enum _ ->
        assert false
