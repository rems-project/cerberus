open Pp_prelude
open Colour

module P = PPrint

type doc_tree =
  | Dleaf of P.document
  | Dnode of P.document * doc_tree list


(* TODO: move to utils *)
let map_with_last f_all f_last xs =
  let rec aux acc = function
    | [] ->
        acc
    | [x] ->
        f_last x :: acc
    | x::xs ->
        aux (f_all x :: acc) xs
  in
  List.rev (aux [] xs)

let pp_doc_tree dtree =
  let to_space = function
    | '|'
      -> "|"
    | _
      -> " " in
  let pp_prefix pref =
    !^ (ansi_format [Blue] pref) in
  let rec aux (pref, (current : char)) = function
    | Dleaf doc ->
        pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc
    | Dnode (doc, []) ->
        pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc ^^^ !^ "EMPTY"
        (* TODO: do a failwith ? *)
    | Dnode (doc, dtrees) ->
        P.separate P.hardline begin
          (pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc) ::
          map_with_last
            (aux (pref ^ to_space current ^ " ", '|'))
            (aux (pref ^ to_space current ^ " ", '`'))
            dtrees
        end
  in
  begin match dtree with
    | Dleaf doc ->
        doc
    | Dnode (doc, dtrees) ->
        doc ^^ P.hardline ^^
        P.separate P.hardline begin
          map_with_last
            (aux ("", '|'))
            (aux ("", '`'))
            dtrees
        end
  end

let pp_ctor k =
  !^ (ansi_format [Bold; Cyan] k)

let pp_stmt_ctor k =
  !^ (ansi_format [Bold; Magenta] k)
