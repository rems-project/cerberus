open Earley_core
open Earley
open Extra

(** {3 Combinators and tokens} *)

(** [well_bracketed c_op c_cl] is a grammar that accepts strings starting with
    character [c_op], and ending with character [c_cl]. Moreover, strings with
    non-well-bracketed occurences of [c_op] and [c_cl] are rejected. The input
    ["(aa(b)(c))"] is hence accepted by [well_bracketed '(' ')'], and this has
    the effect of producing ["aa(b)(c)"] as semantic action. However, with the
    same parameters the input ["(aa(b)(c)"] would be rejected. *)
let well_bracketed : char -> char -> string Earley.grammar = fun c_op c_cl ->
  let fn buf pos =
    let str = Buffer.create 20 in
    let rec loop nb_op buf pos =
      let c = Input.get buf pos in
      if c = '\255' then
        Earley.give_up ()
      else if c = c_op then
        (Buffer.add_char str c; loop (nb_op + 1) buf (pos+1))
      else if c = c_cl then
        if nb_op = 1 then (buf, pos+1) else
        (Buffer.add_char str c; loop (nb_op - 1) buf (pos+1))
      else
        (Buffer.add_char str c; loop nb_op buf (pos+1))
    in
    let (buf, pos) = loop 1 buf (pos + 1) in
    (Buffer.contents str, buf, pos)
  in
  let name = Printf.sprintf "<%cwell-bracketed%c>" c_op c_cl in
  Earley.black_box fn (Charset.singleton c_op) false name

let list_sep : char -> 'a Earley.grammar -> 'a list Earley.grammar =
  fun c gr -> parser {e:gr es:{_:CHR(c) gr}* -> e::es}?[[]]

type ident     = string
type iris_term = string
type coq_term  = string

(** Identifier token (regexp ["[A-Za-z_]+"]). *)
let ident : ident Earley.grammar =
  let cs_first = Charset.from_string "A-Za-z_" in
  let cs = Charset.from_string "A-Za-z_0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem cs (Input.get buf (pos + !nb)) do incr nb done;
    (String.sub (Input.line buf) pos !nb, buf, pos + !nb)
  in
  Earley.black_box fn cs_first false "<ident>"

(** Arbitrary ("well-bracketed") string delimited by ['['] and [']']. *)
let iris_term : iris_term Earley.grammar =
  well_bracketed '[' ']'

(** Arbitrary ("well-bracketed") string delimited by ['{'] and ['}']. *)
let coq_term : coq_term Earley.grammar =
  well_bracketed '{' '}'

(** {3 Main grammars} *)

type coq_expr =
  | Coq_ident of string
  | Coq_all   of string

type constr =
  | Constr_Iris  of string
  | Constr_exist of string * constr
  | Constr_own   of string * type_expr
  | Constr_Coq   of coq_expr

and ptr_kind = Own | Shr | Frac of type_expr

and type_expr =
  | Ty_refine of coq_expr * type_expr
  | Ty_ptr    of ptr_kind * type_expr
  | Ty_opt1   of type_expr
  | Ty_opt2   of type_expr * type_expr
  | Ty_dots
  | Ty_exists of ident * type_expr
  | Ty_constr of type_expr * constr
  | Ty_params of ident * type_expr list
  | Ty_direct of ident
  | Ty_Coq    of coq_expr

let type_void : type_expr = Ty_direct "void"

let parser coq_expr =
  | x:ident    -> Coq_ident(x)
  | s:coq_term -> Coq_all(s)

let parser constr =
  | s:iris_term                                   -> Constr_Iris(s)
  | "∃" x:ident "." c:constr                      -> Constr_exist(x,c)
  | x:ident "@" "&own<" ty:type_expr ">"          -> Constr_own(x,ty)
  | c:coq_expr                                    -> Constr_Coq(c)

and parser type_expr =
  | c:coq_expr ty:{"@" type_expr}?                ->
      begin
        match (c, ty) with
        | (Coq_ident(x), None    ) -> Ty_direct(x)
        | (_           , None    ) -> Ty_Coq(c)
        | (_           , Some(ty)) -> Ty_refine(c,ty)
      end
  | "&own<" ty:type_expr ">"                      -> Ty_ptr(Own, ty)
  | "&shr<" ty:type_expr ">"                      -> Ty_ptr(Shr, ty)
  | "&frac<" l:type_expr "," ty:type_expr ">"     -> Ty_ptr(Frac(l), ty)
  | "..."                                         -> Ty_dots
  | "∃" x:ident "." ty:type_expr                  -> Ty_exists(x,ty)
  | ty:type_expr "&" c:constr                     -> Ty_constr(ty,c)
  | id:ident "<" tys:(list_sep ',' type_expr) ">" -> Ty_params(id,tys)

(** {3 Entry points} *)

(** {4 Annotations on type definitions} *)

let parser annot_parameter : (ident * coq_expr) Earley.grammar =
  | id:ident ":" s:coq_expr

let parser annot_refine : (ident * coq_expr) Earley.grammar =
  | id:ident ":" s:coq_expr

let parser annot_ptr_type : (ident * type_expr) Earley.grammar =
  | id:ident ":" ty:type_expr

let parser annot_type : ident Earley.grammar =
  | id:ident

(** {4 Annotations on structs} *)

let parser annot_size : ident Earley.grammar =
  | id:ident

let parser annot_exist : (ident * coq_expr) Earley.grammar =
  | id:ident ":" s:coq_expr

let parser annot_constr : constr Earley.grammar =
  | c:constr

(** {4 Annotations on fields} *)

let parser annot_field : type_expr Earley.grammar =
  | ty:type_expr

(** {4 Annotations on functions} *)

let parser annot_arg : type_expr Earley.grammar =
  | ty:type_expr

let parser annot_requires : constr Earley.grammar =
  | c:constr

let parser annot_returns : type_expr Earley.grammar =
  | ty:type_expr

let parser annot_ensures : constr Earley.grammar =
  | c:constr

(** {4 Annotations on statement expressions (ExprS)} *)

(*
let parser annot : ... Earley.grammar =
*)

(** {4 Annotations on blocks} *)

let parser annot_inv : constr Earley.grammar =
  | c:constr

(** {3 Parsing of attributes} *)

type annot =
  | Annot_parameters of (ident * coq_expr) list
  | Annot_refined_by of (ident * coq_expr) list
  | Annot_ptr_type   of (ident * type_expr)
  | Annot_type       of ident
  | Annot_size       of ident
  | Annot_exist      of (ident * coq_expr) list
  | Annot_constraint of constr list
  | Annot_immovable
  | Annot_tunion
  | Annot_field      of type_expr
  | Annot_args       of type_expr list
  | Annot_requires   of constr list
  | Annot_returns    of type_expr
  | Annot_ensures    of constr list
  | Annot_annot      of string
  | Annot_inv        of constr

exception Invalid_annot of string

type rc_attr =
  { rc_attr_id   : string
  ; rc_attr_args : string list }

let parse_attr : rc_attr -> annot = fun attr ->
  let {rc_attr_id = id; rc_attr_args = args} = attr in
  let error msg =
    raise (Invalid_annot (Printf.sprintf "annotation [%s] %s" id msg))
  in

  let parse : type a.a grammar -> string -> a = fun gr s ->
    let parse_string = Earley.parse_string gr Blanks.default in
    try parse_string s with Earley.Parse_error(_,i) ->
      let msg =
        Printf.sprintf  "no parse in annotation \"%s\" at position %i" s i
      in
      raise (Invalid_annot msg)
  in

  let single_arg : type a.a grammar -> (a -> annot) -> annot = fun gr c ->
    match args with
    | [s] -> c (parse gr s)
    | _   -> error "should have exactly one argument"
  in

  let many_args : type a.a grammar -> (a list -> annot) -> annot = fun gr c ->
    match args with
    | [] -> error "should have at least one argument"
    | _  -> c (List.map (parse gr) args)
  in

  let raw_single_arg : (string -> annot) -> annot = fun c ->
    match args with
    | [s] -> c s
    | _   -> error "should have exactly one argument"
  in

  let no_args : annot -> annot = fun c ->
    match args with
    | [] -> c
    | _  -> error "should not have arguments"
  in

  match id with
  | "parameters" -> many_args annot_parameter (fun l -> Annot_parameters(l))
  | "refined_by" -> many_args annot_refine (fun l -> Annot_refined_by(l))
  | "ptr_type"   -> single_arg annot_ptr_type (fun e -> Annot_ptr_type(e))
  | "type"       -> single_arg annot_type (fun e -> Annot_type(e))
  | "size"       -> single_arg annot_size (fun e -> Annot_size(e))
  | "exist"      -> many_args annot_exist (fun l -> Annot_exist(l))
  | "constraints"-> many_args annot_constr (fun l -> Annot_constraint(l))
  | "immovable"  -> no_args Annot_immovable
  | "tunion"     -> no_args Annot_tunion
  | "field"      -> single_arg annot_field (fun e -> Annot_field(e))
  | "args"       -> many_args annot_arg (fun l -> Annot_args(l))
  | "requires"   -> many_args annot_requires (fun l -> Annot_requires(l))
  | "returns"    -> single_arg annot_returns (fun e -> Annot_returns(e))
  | "ensures"    -> many_args annot_ensures (fun l -> Annot_ensures(l))
  | "annot"      -> raw_single_arg (fun e -> Annot_annot(e))
  | "inv"        -> single_arg annot_inv (fun e -> Annot_inv(e))
  | _            -> error "undefined"

(** {3 High level parsing of attributes} *)

type function_annot =
  { fa_parameters : (ident * coq_expr) list
  ; fa_args       : type_expr list
  ; fa_returns    : type_expr
  ; fa_exists     : (ident * coq_expr) list
  ; fa_requires   : constr list
  ; fa_ensures    : constr list }

let function_annot : rc_attr list -> function_annot = fun attrs ->
  let parameters = ref [] in
  let args = ref [] in
  let exists = ref [] in
  let returns = ref None in
  let requires = ref [] in
  let ensures = ref [] in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      raise (Invalid_annot (Printf.sprintf "annotation [%s] %s" id msg))
    in
    match (parse_attr attr, !returns) with
    | (Annot_parameters(l), _   ) -> parameters := !parameters @ l
    | (Annot_args(l)      , _   ) -> args := !args @ l
    | (Annot_returns(ty)  , None) -> returns := Some(ty)
    | (Annot_returns(_)   , _   ) -> error "already specified"
    | (Annot_requires(l)  , _   ) -> requires := !requires @ l
    | (Annot_ensures(l)   , _   ) -> ensures := !ensures @ l
    | (Annot_exist(l)     , _   ) -> exists := !exists @ l
    | (_                  , _   ) -> error "is invalid for a function"
  in
  List.iter handle_attr attrs;

  { fa_parameters = !parameters
  ; fa_args       = !args
  ; fa_returns    = Option.get type_void !returns
  ; fa_exists     = !exists
  ; fa_requires   = !requires
  ; fa_ensures    = !ensures }

let field_annot : rc_attr list -> type_expr = fun attrs ->
  let field = ref None in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      raise (Invalid_annot (Printf.sprintf "annotation [%s] %s" id msg))
    in
    match (parse_attr attr, !field) with
    | (Annot_field(ty), None) -> field := Some(ty)
    | (Annot_field(_) , _   ) -> error "already specified"
    | (_              , _   ) -> error "is invalid for a field"
  in
  List.iter handle_attr attrs;

  match !field with
  | None     -> raise (Invalid_annot "a field annotation is required")
  | Some(ty) -> ty

type expr_annot = string option

let expr_annot : rc_attr list -> expr_annot = fun attrs ->
  let error msg =
    raise (Invalid_annot (Printf.sprintf "expression annotation %s" msg))
  in
  match attrs with
  | []      -> None
  | _::_::_ -> error "carries more than one attributes"
  | [attr]  ->
  match parse_attr attr with
  | Annot_annot(s) -> Some(s)
  | _              -> error "is invalid (wrong kind)"

type struct_annot = annot list (* FIXME *)

let struct_annot : rc_attr list -> struct_annot = fun attrs ->
  List.map parse_attr attrs (* FIXME *)

type block_annot = constr option

let block_annot : rc_attr list -> block_annot = fun attrs ->
  let error msg =
    raise (Invalid_annot (Printf.sprintf "block annotation %s" msg))
  in
  match attrs with
  | []      -> None
  | _::_::_ -> error "carries more than one attributes"
  | [attr]  ->
  match parse_attr attr with
  | Annot_inv(c) -> Some(c)
  | _            -> error "is invalid (wrong kind)"
