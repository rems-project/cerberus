module Loc = Locations

type label = Cerb_frontend.Annot.label_annot

type section =
  | Label of
      { loc : Loc.t;
        label : label
      }
  | Body

let label_prefix =
  let open Cerb_frontend.Annot in
  function
  | LAreturn -> "return"
  | LAloop_break _ -> "break"
  | LAloop_continue _ -> "continue"
  | LAloop _ -> "loop"
  | LAswitch -> "switch"
  | LAcase -> "case"
  | LAdefault -> "default"
  | LAactual_label -> "label"


let pp_section =
  let open Pp in
  function
  | Body -> !^"body"
  | Label l ->
    !^(label_prefix l.label) ^^ parens !^(fst (Locations.head_pos_of_location l.loc))


type t =
  { fnction : Sym.t option;
    section : section option;
    statement : Loc.t option;
    expression : Loc.t option
  }

let empty = { fnction = None; section = None; statement = None; expression = None }

let set_function (fnction : Sym.t) (_w : t) =
  { fnction = Some fnction; section = None; statement = None; expression = None }


let set_section (section : section) (w : t) =
  { w with section = Some section; statement = None; expression = None }


let set_statement (statement : Loc.t) (w : t) =
  { w with statement = Some statement; expression = None }


let set_expression (expression : Loc.t) (w : t) = { w with expression = Some expression }
