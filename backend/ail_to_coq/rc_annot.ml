open Earley_core
open Earley
open Extra

(** {3 Combinators and utilities} *)

type 'a quot_elt =
  | Quot_plain of string
  | Quot_anti  of 'a

type 'a quoted = 'a quot_elt list

(** [well_bracketed c_op c_cl anti_gr] is a grammar accepting strings starting
    with character [c_op], and ending with character [c_cl]. Moreover, strings
    with non-well-bracketed occurences of characters [c_op] / [c_cl] and ['{']
    / ['}'] are rejected. A sequence of the form ["!{text}"] is interpreted as
    an antiquotation. Its contents (here, ["text"]) is parsed using [anti_gr],
    an it should itself be well-bracketed in terms of ['{'] / ['}']. Note that
    the produced semantic value is a list of elements that can be either plain
    text (using the [Quot_plain(s)] constructor) or an anti-quotation (using a
    [Quot_anti(e)] constructor). *)
let well_bracketed : char -> char -> 'a grammar -> 'a quoted grammar =
    fun c_op c_cl anti_gr ->
  let fn buf pos =
    let elts = ref [] in
    let str = Buffer.create 20 in
    let flush_plain () =
      elts := (Quot_plain(Buffer.contents str)) :: !elts;
      Buffer.clear str
    in
    let flush_anti () =
      (*Printf.eprintf "PARSING ANTIQUOTATION\n%!";*)
      let text = Buffer.contents str in
      let anti =
        let parse = Earley.parse_string anti_gr Blanks.default in
        try parse text with Earley.Parse_error(_,_) ->
          assert false (* FIXME fail correctly *)
      in
      elts := (Quot_anti(anti)) :: !elts;
      Buffer.clear str
    in
    let rec loop state buf pos =
      let (c, next_buf, next_pos) = Input.read buf pos in
      (*
      begin
        Printf.eprintf "READING [%c] IN STATE " c;
        match state with
        | `Init(i)   -> Printf.eprintf "Init(%i)\n%!" i
        | `Bang(i)   -> Printf.eprintf "Bang(%i)\n%!" i
        | `Anti(k,i) -> Printf.eprintf "Anti(%i,%i)\n%!" k i
      end;
      *)
      match (c, state) with
      | ('\255', _       )               -> (* EOF, error. *)
          Earley.give_up ()
      | ('\\'  , _       )               -> (* Escape sequence. *)
          let c = Input.get next_buf next_pos in
          if not (List.mem c ['\255'; '"'; '\\']) then Earley.give_up ();
          (* We only need to remove the [`\\`] here. *)
          loop state next_buf next_pos;
      | (_     , `Init(i)  ) when c = c_op -> (* Normal mode opening. *)
          Buffer.add_char str c; loop (`Init(i+1)) next_buf next_pos
      | (_     , `Init(1)  ) when c = c_cl -> (* Normal mode final closing. *)
          flush_plain (); (next_buf, next_pos)
      | (_     , `Init(i)  ) when c = c_cl -> (* Normal mode closing. *)
          Buffer.add_char str c; loop (`Init(i-1)) next_buf next_pos
      | ('!'   , `Init(i)  )               -> (* Potential antiquotation. *)
          loop (`Bang(i)) next_buf next_pos
      | ('{'   , `Bang(i)  )               -> (* Actual antiquotation. *)
          flush_plain (); loop (`Anti(1,i)) next_buf next_pos
      | (_     , `Bang(i)  )               -> (* No antiquot. after all. *)
          Buffer.add_char str '!'; loop (`Init(i)) buf pos
      | ('{'   , `Anti(k,i))               -> (* Antiquot. operning. *)
          Buffer.add_char str c; loop (`Anti(k+1,i)) next_buf next_pos
      | ('}'   , `Anti(1,i))               -> (* Antiquot. final closing. *)
          flush_anti (); loop (`Init(i)) next_buf next_pos
      | ('}'   , `Anti(k,i))               -> (* Antiquot. closing. *)
          Buffer.add_char str '}'; loop (`Anti(k-1,i)) next_buf next_pos
      | (_     , _         )               -> (* Normal character. *)
          Buffer.add_char str c; loop state next_buf next_pos
    in
    let (buf, pos) = loop (`Init(1)) buf (pos + 1) in
    (List.rev !elts, buf, pos)
  in
  let name = Printf.sprintf "<%cwell-bracketed%c>" c_op c_cl in
  Earley.black_box fn (Charset.singleton c_op) false name

(** {3 Annotations AST} *)

type ident   = string
type pattern = ident list

type coq_term  = type_expr quoted

and  iris_term = type_expr quoted

and coq_expr =
  | Coq_ident of string
  | Coq_all   of coq_term

and constr =
  | Constr_Iris  of iris_term
  | Constr_exist of string * coq_expr option * constr
  | Constr_own   of string * ptr_kind * type_expr
  | Constr_Coq   of coq_expr

and ptr_kind = Own | Shr | Frac of coq_expr

and type_expr =
  | Ty_refine of coq_expr * type_expr
  | Ty_ptr    of ptr_kind * type_expr
  | Ty_dots
  | Ty_exists of pattern * coq_expr option * type_expr
  | Ty_constr of type_expr * constr
  | Ty_params of ident * type_expr_arg list
  | Ty_Coq    of coq_expr

and type_expr_arg =
  | Ty_arg_expr   of type_expr
  | Ty_arg_lambda of pattern * coq_expr option * type_expr_arg

type annot_arg = int * int * coq_expr

(** {3 Main grammar defintions} *)

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

(** Integer token (regexp ["[0-9]+"]). *)
let integer : int Earley.grammar =
  let cs = Charset.from_string "0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem cs (Input.get buf (pos + !nb)) do incr nb done;
    (int_of_string (String.sub (Input.line buf) pos !nb), buf, pos + !nb)
  in
  Earley.black_box fn cs false "<integer>"

let parser pattern =
  | "(" ")"                         -> []
  | x:ident                         -> [x]
  | "(" x:ident xs:{"," ident}+ ")" -> x :: xs

(** Arbitrary ("well-bracketed") string delimited by ['{'] and ['}']. *)
let parser coq_term  = (well_bracketed '{' '}' (type_expr `Full))

(** Arbitrary ("well-bracketed") string delimited by ['['] and [']']. *)
and parser iris_term = (well_bracketed '[' ']' (type_expr `Full))

and parser coq_expr =
  | x:ident    -> Coq_ident(x)
  | s:coq_term -> Coq_all(s)

and parser constr =
  | s:iris_term                                   -> Constr_Iris(s)
  | "∃" x:ident a:{":" coq_expr}? "." c:constr    -> Constr_exist(x,a,c)
  | x:ident "@" (k,ty):ptr_type                   -> Constr_own(x,k,ty)
  | c:coq_expr                                    -> Constr_Coq(c)

and parser ptr_type =
  | "&own<" ty:(type_expr `Full) ">"                 -> (Own    , ty)
  | "&shr<" ty:(type_expr `Full) ">"                 -> (Shr    , ty)
  | "&frac<" e:coq_expr "," ty:(type_expr `Full) ">" -> (Frac(e), ty)

and parser type_expr @(p : [`Atom | `Cstr | `Full]) =
  | c:coq_expr ty:{"@" (type_expr `Atom)}?
      when p >= `Atom ->
        begin
          match (c, ty) with
          | (Coq_ident(x), None    ) -> Ty_params(x,[])
          | (_           , None    ) -> Ty_Coq(c)
          | (_           , Some(ty)) -> Ty_refine(c,ty)
        end
  | (k,ty):ptr_type
      when p >= `Atom -> Ty_ptr(k, ty)
  | id:ident "<" tys:type_args ">"
      when p >= `Atom -> Ty_params(id,tys)
  | "..."
      when p >= `Atom -> Ty_dots
  | "∃" p:pattern a:{":" coq_expr}? "." ty:(type_expr `Full)
      when p >= `Full -> Ty_exists(p,a,ty)
  | ty:(type_expr `Cstr) "&" c:constr
      when p >= `Cstr -> Ty_constr(ty,c)
  | "(" ty:(type_expr `Full) ")"
      when p >= `Atom -> ty

and parser type_expr_arg =
  | ty:(type_expr `Full)
      -> Ty_arg_expr(ty)
  | "λ" p:pattern a:{":" coq_expr}? "." tya:type_expr_arg
      -> Ty_arg_lambda(p,a,tya)

and parser type_args =
  | EMPTY                                   -> []
  | e:type_expr_arg es:{"," type_expr_arg}* -> e::es

let type_expr = type_expr `Full

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

let parser annot_size : coq_expr Earley.grammar =
  | c:coq_expr

let parser annot_exist : (ident * coq_expr) Earley.grammar =
  | id:ident ":" s:coq_expr

let parser annot_constr : constr Earley.grammar =
  | c:constr

(** {4 Annotations on tagged unions} *)

type tag_spec = string * (string * coq_expr) list

let tagged_union : coq_expr Earley.grammar = coq_expr

let parser union_tag : tag_spec Earley.grammar =
  | c:ident l:{"(" ident ":" coq_expr ")"}*

(** {4 Annotations on fields} *)

let parser annot_field : type_expr Earley.grammar =
  | ty:type_expr

(** {4 Annotations on global variables} *)

let parser annot_global : type_expr Earley.grammar =
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

let parser annot_args : annot_arg Earley.grammar =
  | integer ":" integer coq_expr

type manual_proof = string * string * string (* Load path, module, lemma. *)

let parser annot_manual : manual_proof Earley.grammar =
  | f:ident fs:{"." ident}* ":" file:ident "," thm:ident ->
      (String.concat "." (f :: fs), file, thm)

(** {4 Annotations on statement expressions (ExprS)} *)

(*
let parser annot : ... Earley.grammar =
*)

(** {4 Annotations on blocks} *)

let parser annot_inv_var : (ident * type_expr) Earley.grammar =
  | id:ident ":" ty:type_expr

(** {4 Type definition (in comments)} *)

type typedef = string * (string * coq_expr option) list * type_expr

let parser typedef_arg = ident {":" coq_expr}?

let parser typedef_args =
  | EMPTY                                   -> []
  | arg:typedef_arg args:{"," typedef_arg}* -> arg :: args

let parser typedef : typedef Earley.grammar =
  | id:ident args:{"<" typedef_args ">"}?[[]] "≔" ty:type_expr

(** {3 Parsing of attributes} *)

type annot =
  | Annot_parameters   of (ident * coq_expr) list
  | Annot_refined_by   of (ident * coq_expr) list
  | Annot_ptr_type     of (ident * type_expr)
  | Annot_size         of coq_expr
  | Annot_exist        of (ident * coq_expr) list
  | Annot_constraint   of constr list
  | Annot_immovable
  | Annot_tagged_union of coq_expr
  | Annot_union_tag    of tag_spec
  | Annot_field        of type_expr
  | Annot_global       of type_expr
  | Annot_args         of type_expr list
  | Annot_requires     of constr list
  | Annot_returns      of type_expr
  | Annot_ensures      of constr list
  | Annot_annot        of string
  | Annot_inv_vars     of (ident * type_expr) list
  | Annot_annot_args   of annot_arg list
  | Annot_tactics      of string list
  | Annot_trust_me
  | Annot_skip
  | Annot_manual       of manual_proof
  | Annot_block
  | Annot_full_block

let annot_lemmas : string list -> string list =
  List.map (Printf.sprintf "all: try by apply: %s; solve_goal.")

let rc_locs : Location.Pool.t = Location.Pool.make ()

exception Invalid_annot of Location.t * string

let invalid_annot : type a. Location.t -> string -> a = fun loc msg ->
  raise (Invalid_annot(loc, msg))

let invalid_annot_no_pos : type a. string -> a = fun msg ->
  invalid_annot (Location.none rc_locs) msg

type rc_attr =
  { rc_attr_id   : string Location.located
  ; rc_attr_args : string Location.located list }

let parse_attr : rc_attr -> annot = fun attr ->
  let {rc_attr_id = id; rc_attr_args = args} = attr in
  let error msg =
    invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
  in

  let parse : type a.a grammar -> string Location.located -> a = fun gr s ->
    let parse_string = Earley.parse_string gr Blanks.default in
    try parse_string s.elt with Earley.Parse_error(buf,pos) ->
      let msg =
        let i = Input.utf8_col_num buf pos in
        Printf.sprintf "No parse in annotation at position %i." i
      in
      invalid_annot s.loc msg
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
    | [s] -> c s.elt
    | _   -> error "should have exactly one argument"
  in

  let raw_many_args : (string list -> annot) -> annot = fun c ->
    match args with
    | [] -> error "should have at least one argument"
    | _  -> c (List.map (fun a -> Location.(a.elt)) args)
  in

  let no_args : annot -> annot = fun c ->
    match args with
    | [] -> c
    | _  -> error "should not have arguments"
  in

  match id.elt with
  | "parameters"   -> many_args annot_parameter (fun l -> Annot_parameters(l))
  | "refined_by"   -> many_args annot_refine (fun l -> Annot_refined_by(l))
  | "ptr_type"     -> single_arg annot_ptr_type (fun e -> Annot_ptr_type(e))
  | "size"         -> single_arg annot_size (fun e -> Annot_size(e))
  | "exists"       -> many_args annot_exist (fun l -> Annot_exist(l))
  | "constraints"  -> many_args annot_constr (fun l -> Annot_constraint(l))
  | "immovable"    -> no_args Annot_immovable
  | "tagged_union" -> single_arg tagged_union (fun e -> Annot_tagged_union(e))
  | "union_tag"    -> single_arg union_tag (fun t -> Annot_union_tag(t))
  | "field"        -> single_arg annot_field (fun e -> Annot_field(e))
  | "global"       -> single_arg annot_global (fun e -> Annot_global(e))
  | "args"         -> many_args annot_arg (fun l -> Annot_args(l))
  | "requires"     -> many_args annot_requires (fun l -> Annot_requires(l))
  | "returns"      -> single_arg annot_returns (fun e -> Annot_returns(e))
  | "ensures"      -> many_args annot_ensures (fun l -> Annot_ensures(l))
  | "annot"        -> raw_single_arg (fun e -> Annot_annot(e))
  | "inv_vars"     -> many_args annot_inv_var (fun l -> Annot_inv_vars(l))
  | "annot_args"   -> many_args annot_args (fun l -> Annot_annot_args(l))
  | "tactics"      -> raw_many_args (fun l -> Annot_tactics(l))
  | "lemmas"       -> raw_many_args (fun l -> Annot_tactics(annot_lemmas l))
  | "trust_me"     -> no_args Annot_trust_me
  | "skip"         -> no_args Annot_skip
  | "manual_proof" -> single_arg annot_manual (fun e -> Annot_manual(e))
  | "block"        -> no_args Annot_block
  | "full_block"   -> no_args Annot_full_block
  | _              -> error "undefined"

(** {3 High level parsing of attributes} *)

type proof_kind =
  | Proof_normal
  | Proof_skipped (* Not even a spec is generated. *)
  | Proof_trusted
  | Proof_manual of manual_proof

type function_annot =
  { fa_parameters : (ident * coq_expr) list
  ; fa_args       : type_expr list
  ; fa_returns    : type_expr
  ; fa_exists     : (ident * coq_expr) list
  ; fa_requires   : constr list
  ; fa_ensures    : constr list
  ; fa_tactics    : string list
  ; fa_proof_kind : proof_kind }

let function_annot : rc_attr list -> function_annot = fun attrs ->
  let parameters = ref [] in
  let args = ref [] in
  let exists = ref [] in
  let returns = ref None in
  let requires = ref [] in
  let ensures = ref [] in
  let tactics = ref [] in
  let proof = ref Proof_normal in

  let nb_attrs = ref 0 in
  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
    in
    incr nb_attrs;
    match (parse_attr attr, !returns) with
    | (_                  , _   ) when !proof = Proof_skipped ->
        error "a skipped function should not have other annotations";
    | (Annot_skip         , _   ) ->
        if !proof <> Proof_normal then error "proof mode already specified";
        if !nb_attrs <> 1 then error "other annotations are given";
        proof := Proof_skipped
    | (Annot_trust_me     , _   ) ->
        if !proof <> Proof_normal then error "proof mode already specified";
        proof := Proof_trusted
    | (Annot_manual(cfg)  , _   ) ->
        if !proof <> Proof_normal then error "proof mode already specified";
        proof := Proof_manual(cfg)
    | (Annot_parameters(l), _   ) -> parameters := !parameters @ l
    | (Annot_args(l)      , _   ) -> args := !args @ l
    | (Annot_returns(ty)  , None) -> returns := Some(ty)
    | (Annot_returns(_)   , _   ) -> error "already specified"
    | (Annot_requires(l)  , _   ) -> requires := !requires @ l
    | (Annot_ensures(l)   , _   ) -> ensures := !ensures @ l
    | (Annot_exist(l)     , _   ) -> exists := !exists @ l
    | (Annot_annot_args(_), _   ) -> () (* Handled separately. *)
    | (Annot_tactics(l)   , _   ) -> tactics := !tactics @ l
    | (_                  , _   ) -> error "is invalid for a function"
  in
  List.iter handle_attr attrs;

  (* When no annotations are given, the function is skipped. *)
  if !nb_attrs = 0 then proof := Proof_skipped;

  { fa_parameters = !parameters
  ; fa_args       = !args
  ; fa_returns    = Option.get (Ty_params("void", [])) !returns
  ; fa_exists     = !exists
  ; fa_requires   = !requires
  ; fa_ensures    = !ensures
  ; fa_tactics    = !tactics
  ; fa_proof_kind = !proof }

let function_annot_args : rc_attr list -> annot_arg list = fun attrs ->
  let annot_args = ref [] in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    if id.elt <> "annot_args" then () else
    match parse_attr attr with
    | Annot_annot_args(l) -> annot_args := !annot_args @ l
    | _                   -> assert false (* Unreachable. *)
  in
  List.iter handle_attr attrs;

  !annot_args

type member_annot =
  | MA_none
  | MA_field of type_expr
  | MA_utag  of tag_spec

let member_annot : rc_attr list -> member_annot = fun attrs ->
  let annot = ref MA_none in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
    in
    match (parse_attr attr, !annot) with
    | (Annot_field(ty)   , MA_none) -> annot := MA_field(ty)
    | (Annot_field(_)    , _      ) -> error "already specified"
    | (Annot_union_tag(s), MA_none) -> annot := MA_utag(s)
    | (Annot_union_tag(_), _      ) -> error "already specified"
    | (_                 , _      ) -> error "is invalid for a field"
  in
  List.iter handle_attr attrs; !annot

type expr_annot = string option

let expr_annot : rc_attr list -> expr_annot = fun attrs ->
  let error msg =
    invalid_annot_no_pos (Printf.sprintf "Expression annotation %s." msg)
  in
  match attrs with
  | []      -> None
  | _::_::_ -> error "carries more than one attributes"
  | [attr]  ->
  match parse_attr attr with
  | Annot_annot(s) -> Some(s)
  | _              -> error "is invalid (wrong kind)"

type basic_struct_annot =
  { st_parameters : (ident * coq_expr) list
  ; st_refined_by : (ident * coq_expr) list
  ; st_exists     : (ident * coq_expr) list
  ; st_constrs    : constr list
  ; st_size       : coq_expr option
  ; st_ptr_type   : (ident * type_expr) option
  ; st_immovable  : bool }

let default_basic_struct_annot : basic_struct_annot =
  { st_parameters = []
  ; st_refined_by = []
  ; st_exists     = []
  ; st_constrs    = []
  ; st_size       = None
  ; st_ptr_type   = None
  ; st_immovable  = false }

type struct_annot =
  | SA_union
  | SA_basic    of basic_struct_annot
  | SA_tagged_u of coq_expr

let struct_annot : rc_attr list -> struct_annot = fun attrs ->
  let parameters = ref [] in
  let refined_by = ref [] in
  let exists = ref [] in
  let constrs = ref [] in
  let size = ref None in
  let ptr = ref None in
  let immovable = ref false in
  let tagged_union = ref None in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
    in
    let check_and_set r v =
      if !r <> None then error "already specified";
      r := Some(v)
    in
    match (parse_attr attr, !tagged_union) with
    (* Tagged union stuff. *)
    | (Annot_tagged_union(e), None   ) -> tagged_union := Some(e)
    | (Annot_tagged_union(e), Some(_)) -> error "already specified"
    (* Normal struct stuff. *)
    | (Annot_parameters(l)  , None   ) -> parameters := !parameters @ l
    | (Annot_refined_by(l)  , None   ) -> refined_by := !refined_by @ l
    | (Annot_exist(l)       , None   ) -> exists := !exists @ l
    | (Annot_constraint(l)  , None   ) -> constrs := !constrs @ l
    | (Annot_size(s)        , None   ) -> check_and_set size s
    | (Annot_ptr_type(e)    , None   ) -> check_and_set ptr e
    | (Annot_immovable      , None   ) ->
        if !immovable then error "already specified";
        immovable := true
    | (Annot_parameters(_)  , _      )
    | (Annot_refined_by(_)  , _      )
    | (Annot_exist(_)       , _      )
    | (Annot_constraint(_)  , _      )
    | (Annot_size(_)        , _      )
    | (Annot_ptr_type(_)    , _      )
    | (Annot_immovable      , _      ) ->
        error "is invalid for tagged unions"
    | (_                    , _      ) ->
        error "is invalid for a struct or a tagged union"
  in
  List.iter handle_attr attrs;

  match !tagged_union with
  | Some(e) -> SA_tagged_u(e)
  | None    ->
  let basic_annot =
    { st_parameters = !parameters
    ; st_refined_by = !refined_by
    ; st_exists     = !exists
    ; st_constrs    = !constrs
    ; st_size       = !size
    ; st_ptr_type   = !ptr
    ; st_immovable  = !immovable }
  in
  SA_basic(basic_annot)

type loop_annot =
  { la_exists   : (ident * coq_expr) list
  ; la_constrs  : constr list
  ; la_inv_vars : (ident * type_expr) list
  ; la_full     : bool }

let no_loop_annot : loop_annot =
  { la_exists   = []
  ; la_constrs  = []
  ; la_inv_vars = []
  ; la_full     = true }

let loop_annot : rc_attr list -> loop_annot = fun attrs ->
  let exists = ref [] in
  let constrs = ref [] in
  let vars = ref [] in
  let full_block = ref None in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
    in
    let set_full_block b =
      match !full_block with
      | Some(_) -> error "mode already specified"
      | None    -> full_block := Some(b)
    in
    match parse_attr attr with
    | Annot_exist(l)      -> exists := !exists @ l
    | Annot_constraint(l) -> constrs := !constrs @ l
    | Annot_inv_vars(l)   -> vars := !vars @ l
    | Annot_block         -> set_full_block false
    | Annot_full_block    -> set_full_block true
    | _                   -> error "is invalid (wrong kind)"
  in
  List.iter handle_attr attrs;

  let la_full =
    match !full_block with
    | Some(b) -> b
    | None    -> no_loop_annot.la_full
  in

  {la_exists = !exists; la_constrs = !constrs; la_inv_vars = !vars; la_full}

type global_annot =
  { ga_parameters : (ident * coq_expr) list
  ; ga_type       : type_expr }

let global_annot : rc_attr list -> global_annot option = fun attrs ->
  let typ = ref None in
  let parameters = ref [] in

  let handle_attr ({rc_attr_id = id; _} as attr) =
    let error msg =
      invalid_annot id.loc (Printf.sprintf "Annotation [%s] %s." id.elt msg)
    in
    match (parse_attr attr, !typ) with
    | (Annot_global(e)    , None) -> typ := Some e
    | (Annot_parameters(l), _   ) -> parameters := !parameters @ l
    | (Annot_global(_)    , _   ) -> error "already specified"
    | (_                  , _   ) -> error "is invalid for a global"
  in
  List.iter handle_attr attrs;

  match !typ with
  | Some(ty) -> Some {ga_parameters = !parameters; ga_type = ty}
  | None -> None
