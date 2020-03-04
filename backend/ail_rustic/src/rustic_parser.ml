open Opal
open Rustic_types

let var =
  letter >>= fun c ->
  many (letter <|> digit <|> exactly '_') >>= fun s ->
  let s = implode (c :: s) in
  return s
(*  if List.mem s keywords then mzero
  else return s*)

let spaces = many space

let ownership =
  (exactlys "read" >> return RC_read) <|>
  (exactlys "write" >> return RC_write)

let make_sym s =
  Symbol.Symbol (Fresh.digest (), 0, Some s) (* TODO: is this the right thing? *)

let rec ty s =
  (spaces >>
   ptr_ty <|> struct_ty <|> scalar_ty)
   s
and scalar_ty =
  exactlys "scalar" >>
  return RC_scalar
and ptr_ty s =
  (exactlys "ptr" >>
  exactlys "[" >>
  ownership >>= fun o ->
  exactlys "]" >>
  exactlys "(" >>
  ty >>= fun t ->
  exactlys ")" >>
  return (RC_ptr (o, t))) s
and struct_ty =
  exactlys "struct" >>
  space >>
  spaces >>
  var >>= fun s ->
  exactlys "[" >>
  ownership >>= fun o ->
  exactlys "]" >>
  return (RC_struct (make_sym s, o))

let arg_unchanged =
  exactlys "-|" >> return RC_unchanged

let arg_change =
  exactlys "->" >>
  spaces >>
  ty >>= fun t ->
  return (RC_changed t)

let arg_change =
  arg_unchanged <|> arg_change

let arg_spec =
  spaces >>
  var >>= fun x ->
  spaces >>
  exactlys ":" >>
  spaces >>
  ty >>= fun t1 ->
  spaces >>
  arg_change >>= fun t2 ->
  return (x, (t1, t2))

let fun_spec =
  exactlys "(" >>
  sep_by arg_spec (exactlys ",") >>= fun xs ->
  exactlys ")" >>
  spaces >>
  exactlys ":" >>
  spaces >>
  ty >>= fun retty ->
  return (xs, retty)