open Rustic_types
open Rustic_parser

(* TODO: end of share *)

type fn_decl =
  { fn_decl_quals : Ctype.qualifiers;
    fn_decl_retty : Ctype.ctype;
    fn_decl_argstys : (Ctype.qualifiers * Ctype.ctype * bool) list; }

let cvt_decl ((quals, retty), argstys) =
  { fn_decl_quals = quals;
    fn_decl_retty = retty;
    fn_decl_argstys = argstys; }

type 'a fn_def =
  { fn_def_attrs : Annot.attribute list;
    fn_def_ids : AilSyntax.ail_identifier list;
    fn_def_sts : 'a AilSyntax.statement; }

let cvt_def (loc, Annot.Attrs attrs, ids, sts) =
  { fn_def_attrs = attrs; 
    fn_def_ids = ids;
    fn_def_sts = sts; }

open AilSyntax

let string_of_identifier (Symbol.Identifier (_, s)) = s

let plop2 = function
| [] -> ""
| _ :: _ as l -> "(" ^ String.concat ", " l ^ ")"

let string_of_attr attr =
  string_of_identifier attr.Annot.attr_id ^ plop2 attr.Annot.attr_args

let string_of_attrs attrs =
  String.concat ", " (List.map string_of_attr attrs)

let string_of_fun_wo_args sym fn_def =
  string_of_sym sym ^ ": " ^ string_of_attrs fn_def.fn_def_attrs

let string_of_ty = function
| Ctype.Ctype _ -> "?"

let string_of_annots annots =
  let annots =
    map_option
      (let open Annot in function
      | Astd x -> None
      | Aloc loc -> None
      | Auid _ -> None
      | Abmc _ -> None
      | Aattrs (Attrs attrs) -> Some attrs)
      annots in
  let annots = List.concat annots in
  String.concat " " (List.map string_of_attr annots)

let rec string_of_ctype = let open Ctype in function
| Ctype (annots, cty_) ->
  string_of_annots annots ^ string_of_ctype_ cty_
and string_of_ctype_ = function
| Void -> "void"
| Basic x -> "int" (* TODO: lies *)
| Array (cty, sz) -> "array(" ^ string_of_ctype cty ^ ")"
| Function _ -> "function"
| Pointer (qls, cty) -> string_of_ctype cty ^ "*"
| Atomic cty -> "atomic(" ^ string_of_ctype cty ^ ")"
| Struct name -> string_of_sym name
| Union name -> string_of_sym name

let string_of_arg (ty, id) =
  match ty with
  | (_, cty, _) ->
    string_of_sym id ^ " : " ^ string_of_ctype cty

let string_of_args args =
  String.concat "," (List.map string_of_arg args)

let string_of_fun_w_args sym fn_decl fn_def =
  let args = List.combine fn_decl.fn_decl_argstys fn_def.fn_def_ids in
  string_of_sym sym ^ ":" ^ (match fn_def.fn_def_attrs with | [] -> "" | _::_ -> " " ^ string_of_attrs fn_def.fn_def_attrs) ^ " (" ^ string_of_args args ^ ")"

let string_of_fun = function
| (x, (Some ty, Some bod)) -> string_of_fun_w_args x ty bod
| (x, (_, Some bod)) -> string_of_fun_wo_args x bod
| (_, (None, None)) -> assert false (* ? *)
| (x, _)-> string_of_sym x ^ " no body"

let add_left id x m =
  let id = string_of_sym id in
  match String_map.find_opt id m with
  | None -> String_map.add id (Some x, None) m
  | Some (_, y) -> String_map.add id (Some x, y) m

let add_right id y m =
  let id = string_of_sym id in
  match String_map.find_opt id m with
  | None -> String_map.add id (None, Some y) m
  | Some (x, _) -> String_map.add id (x, Some y) m

let collect_functions s =
  let ds = map_option (function (id, (_, Decl_function (a, b, c, d, e, f))) -> Some (id, (b, c)) | (_, (_, Decl_object _)) -> None) s.declarations in
  let fs = s.function_definitions in
  let m = String_map.empty in
  (* this may discard stuff *)
  let m = List.fold_left (fun m (id, d) -> add_left id (cvt_decl d) m) m ds in
  let m = List.fold_left (fun m (id, f) -> add_right id (cvt_def f) m) m fs in
  m

type ('b) gamma_ty = ((rc_type * rc_type) String_map.t * 'b) list

let rec lookup_in_gamma x = function
| [] -> None
| (bds, sts) :: gamma ->
  (match String_map.find_opt x bds with
   | None -> lookup_in_gamma x gamma
   | Some ty -> Some ty)

let rc_ownership_of_annot = function
| Annot.Aattrs (Attrs attrs) ->
  let f a =
    match a.Annot.attr_ns with
    | None -> None
    | Some x ->
      if string_of_identifier x = "rc" then
        (match string_of_identifier a.Annot.attr_id with
         | "read" -> Some RC_read
         | "write" -> Some RC_write
         | _ -> failwith "unknown attr")
      else None
    in
  (match map_option f attrs with
  | [x] -> Some x
  | _ -> failwith "?")
| _ -> None

let rc_ownership_of_annots annots =
  match map_option rc_ownership_of_annot annots with
  | [rcow] -> rcow
  | [] -> RC_bad
  | _ :: _ :: _ -> failwith "ambiguous annotations"

(*
let rec rc_type_of_cty = function
| Ctype.Ctype (_, Void) -> RC_scalar
| Ctype.Ctype (_, Basic _) -> RC_scalar
| Ctype.Ctype (_, Array _) -> failwith "array"
| Ctype.Ctype (_, Function _) -> failwith "function"
| Ctype.Ctype (annots, Pointer (_, cty)) -> RC_ptr (rc_ownership_of_annots annots, rc_type_of_cty cty)
| Ctype.Ctype (_, Atomic cty) -> RC_atomic (rc_type_of_cty cty)
| Ctype.Ctype (annots, Struct s) -> RC_struct (s, rc_ownership_of_annots annots)
| Ctype.Ctype (_, Union _) -> failwith "union"

let rc_type_pair_of_cty cty =
  let rcty = rc_type_of_cty cty in
  (* TODO: this is a hack because we don't have annotations yet *)
  (rcty, rcty)

let type_of_fun (f : fn_decl) =
  (List.map (fun (_, b, _) -> rc_type_of_cty b) f.fn_decl_argstys, rc_type_of_cty f.fn_decl_retty)
  *)

type fun_spec_t = (string * (Rustic_types.rc_type * Rustic_types.rc_type)) list * Rustic_types.rc_type

let expand_rcty = function
| (ty1, RC_unchanged) -> (ty1, ty1)
| (ty1, RC_changed ty2) -> (ty1, ty2)

let fun_spec_of def  : fun_spec_t option =
  let x =
    Rustic_types.map_option
      (fun a ->
        match a.Annot.attr_ns with
        | None -> None
        | Some ns ->
          if string_of_identifier ns = "rc" && string_of_identifier a.Annot.attr_id = "fun_spec" then
            (match a.Annot.attr_args with
             | [s] ->
               (match Opal.parse_string Rustic_parser.fun_spec s with
               | Some s -> Some s
               | None -> print_string "couldn't parse spec :-("; None)
             | _ -> None)
          else None)
      def.fn_def_attrs in
  match x with
  | [] -> None
  | [(param, ret)] ->
    let fun_spec = (List.map (fun (x, ty) -> (x, expand_rcty ty)) param, ret) in
    Some fun_spec
  | _ :: _ :: _ -> None (* TODO: fail more gracefully *)

let collect_function_types fs =
  (* TODO: probably needs something better *)
  let hh _ = function
  | (_, Some fn_def) -> fun_spec_of fn_def
  | _ -> None in
  String_option_map.map hh fs

let zap = function
| RC_scalar -> RC_scalar
| RC_ptr (_, rcty) -> RC_ptr (RC_zap, rcty)
| RC_struct (id, _) -> RC_struct (id, RC_zap)

let own_rank = function
| RC_read -> 0
| RC_write -> 1
| RC_zap -> 2
| RC_bad -> 3

(*
let sub_own t1 t2 =
  own_rank t1 <= own_rank t2

let rec sub_rcty t1 t2 = match (t1, t2) with
| (RC_scalar, RC_scalar) -> true
| (RC_scalar, _) | (_, RC_scalar) -> false
| (RC_ptr (o1, t1), RC_ptr (o2, t2)) -> sub_own o1 o2 && sub_rcty t1 t2
| (RC_ptr _, _) | (_, RC_ptr _) -> false
| (RC_struct (_, o1), RC_struct (_, o2)) -> true
*)

module Type_error = struct
type t =
| TE_general of string
| TE_todo of string
| TE_expected_but_got of Location_ocaml.t * rc_type * rc_type
| TE_function_expected_but_got of Location_ocaml.t * rc_type * rc_type
| TE_internal_error of string

let string_of = function
| TE_general s -> s
| TE_todo s -> "TODO: " ^ s
| TE_expected_but_got (loc, t1, t2) -> Location_ocaml.location_to_string loc ^ ": expected `" ^ string_of_rc_type t1 ^ "` but got `" ^ string_of_rc_type t2 ^ "`"
| TE_function_expected_but_got (loc, t1, t2) -> Location_ocaml.location_to_string loc ^ ": function expected `" ^ string_of_rc_type t1 ^ "` but got `" ^ string_of_rc_type t2 ^ "`"
| TE_internal_error s -> "internal error: " ^ s
end
module TE_either = Either_fixed.Make(Type_error)

let loc_of_expression = function
| AnnotatedExpression (_, _, loc, _) -> loc

let rec check_expression stys (ftys : fun_spec_t Rustic_types.String_map.t) (gamma : 'b gamma_ty) (AnnotatedExpression (_, _, loc, e)) : (rc_type * rc_type) TE_either.t =
  check_expression_ stys ftys gamma loc e
and check_expression_ stys ftys gamma loc = function
| AilEident x ->
  (match lookup_in_gamma (string_of_sym x) gamma with
  | None -> TE_either.mzero (TE_general "unbound variable")
  | Some ty -> TE_either.return ty)
| AilEassign (e1, e2) ->
  TE_either.bind
    (check_expression stys ftys gamma e1)
    (function
      | (RC_scalar, _) -> TE_either.return (RC_scalar, RC_scalar)
      | (RC_ptr (o, t) as ty1, ty2) ->
        (*print_string (string_of_rc_type ty ^ "\n");*)
        if RC_write = o then TE_either.return (RC_placeholder "=1", RC_placeholder "=2")
        else TE_either.mzero (Type_error.TE_expected_but_got (loc, RC_ptr (RC_write, t), ty1))
      | _ -> TE_either.mzero (Type_error.TE_internal_error "writing to a non-ptr?"))
| AilEcall (AnnotatedExpression (_, _, _, AilEfunction_decay (AnnotatedExpression (_, _, _, AilEident f))), [e]) ->
  (match String_map.find_opt (string_of_sym f) ftys with
   | None -> TE_either.mzero (TE_general ("unbound function " ^ string_of_sym f))
   | Some ([(_, paramty)], retty) ->
     TE_either.bind
     (check_expression stys ftys gamma e)
      (fun (_, argty) ->
        if Rustic_types.RC_type.compare argty (fst paramty) = 0 then TE_either.return (failwith "???", retty)
        else TE_either.mzero (TE_function_expected_but_got (loc_of_expression e, fst paramty, retty)))
    | _ -> failwith "TODO: allow multiple args")
| AilEcall _ -> failwith "TODO: other AilEcall"
| AilEunary (Address, e) ->
  TE_either.bind
    (check_expression stys ftys gamma e)
    (fun (ty1, ty2) -> TE_either.return (RC_ptr (RC_read, ty1), RC_placeholder "&"))
| AilEunary (Indirection, e) ->
  TE_either.bind
    (check_expression stys ftys gamma e)
    (function
    | (RC_ptr (_, t), ty2) -> TE_either.return (t, ty2 (* ???*))
    | _ -> TE_either.mzero (Type_error.TE_internal_error "derefing a non-pointer?"))
| AilEunary ((Plus|Minus|Bnot|PostfixIncr|PostfixDecr), e) -> check_expression stys ftys gamma e
| AilEbinary _ -> failwith "TODO: binary"
| AilEcompoundAssign _ -> failwith "TODO: compound assign"
| AilEcond _ -> failwith "TODO: cond"
| AilEcast (_, _, e) -> check_expression stys ftys gamma e
| AilEconst e -> TE_either.return (RC_scalar, RC_scalar)
| AilEmemberof _ -> failwith "TODO: memberof"
| AilEfunction_decay _ -> TE_either.mzero (Type_error.TE_internal_error "non-directly-applied functions are not handled")
| AilEannot _ -> failwith "TODO: annot"
| AilEassert _ -> TE_either.return (RC_scalar, RC_scalar)
| AilEcompound _ -> failwith "TODO: compound"
| AilErvalue e ->
  TE_either.bind
    (check_expression stys ftys gamma e)
    (function
    | (RC_ptr (_, t), ty2) -> TE_either.return (t, ty2 (* ???*))
    | _ -> TE_either.mzero (Type_error.TE_general "rvalue?"))
| AilEmemberofptr (e, p) ->
  TE_either.bind
    (check_expression stys ftys gamma e)
    (function
     | (RC_struct (s, o), ty2) ->
         (match String_map.find_opt (string_of_sym s) stys with
         | None -> TE_either.mzero (TE_general ("unknown struct `" ^ string_of_sym s ^ "`"))
         | Some sty ->
           (match String_map.find_opt (string_of_identifier p) sty with
           | None -> TE_either.mzero (TE_general "unknown struct field")
           | Some ty -> TE_either.return (RC_ptr (o, ty), RC_placeholder "->")))
     | _ -> TE_either.mzero (TE_internal_error "memberofptr on non-struct"))
| _ -> failwith "TODO: unhandled expression"

(* TODO: this is completely wrong, it's just a skeleton *)
let rec check_statements stys (ftys : fun_spec_t Rustic_types.String_map.t) (gamma : 'b gamma_ty) : 'a -> unit TE_either.t = function
| [] -> pop stys ftys gamma
| AnnotatedStatement (_, AilSskip) :: sts -> check_statements stys ftys gamma sts
| AnnotatedStatement (_, AilSexpr e) :: sts ->
  TE_either.bind
    (check_expression stys ftys gamma e)
    (fun _ -> check_statements stys ftys gamma sts)
| AnnotatedStatement (_, AilSblock (bds, sts1)) :: sts ->
  (match String_map_aux.of_list (List.map (fun (x, v) -> (string_of_sym x, v)) bds) with
  | None -> assert false
  | Some bds ->
    let bds = String_map.map (fun (_, _, cty) -> (fun (ty1, ty2) -> (zap ty1, zap ty2)) (failwith "TODO: need annotations")) bds in
    check_statements stys ftys ((bds, sts) :: gamma) sts1)
| AnnotatedStatement (_, AilSif (_, s1, s2)) :: sts ->
  TE_either.bind
    (check_statements stys ftys ((String_map.empty, sts) :: gamma) [s1])
    (fun () -> check_statements stys ftys ((String_map.empty, sts) :: gamma) [s2])
| AnnotatedStatement (_, AilSreturnVoid) :: sts ->
  pop stys ftys gamma
| AnnotatedStatement (_, AilSdeclaration [(x, e)]) :: sts ->
  check_statements stys ftys gamma sts (* TODO: ? *)
| AnnotatedStatement (_, s) :: sts -> failwith "TODO: unhandled statement"
and pop stys ftys = function
| [] -> TE_either.return ()
| (_, sts) :: gamma -> check_statements stys ftys gamma sts

let should_typecheck_of (def : 'a fn_def) =
  let should_not_typecheck = 
  List.exists
    (fun a ->
      match a.Annot.attr_ns with
      | None -> false
      | Some ns ->
        string_of_identifier ns = "rc" && string_of_identifier a.Annot.attr_id = "should_not_typecheck")
    def.fn_def_attrs in
  not should_not_typecheck

let collect_structs s =
  let g xs =
    let xs = List.map (fun (id, (_, cty)) -> (string_of_identifier id, failwith "TODO: need annotations!")) xs in
    match String_map_aux.of_list xs with
    | None -> assert false
    | Some xs -> xs in
  let s =
    Rustic_types.map_option
      (function
      | (id, Ctype.StructDef xs) -> Some (string_of_sym id, g xs)
      | (_, Ctype.UnionDef _) -> None)
     s.tag_definitions in
  match Rustic_types.String_map_aux.of_list s with
  | None -> assert false
  | Some s -> s

type rc_outcome2 =
| RC_typechecks_as_expected
| RC_unexpectedly_typechecks
| RC_fails_to_typecheck of Type_error.t
| RC_rejected_as_expected

type rc_outcome =
| RC_skip
| RC_consider of rc_outcome2

let check_function stys (ftys : fun_spec_t Rustic_types.String_map.t) (id : string) = function
| (Some dcl, Some def) ->
  let should_typecheck = should_typecheck_of def in
  (match fun_spec_of def with
  | None -> RC_skip
  | Some (args_spec, retty) ->
    let m = List.combine def.fn_def_ids (List.map snd args_spec) in
    let m =
      (match Rustic_types.String_map_aux.of_list (List.map (fun (x, v) -> (string_of_sym x, v)) m) with
      | None -> assert false
      | Some m -> m) in
    RC_consider
      (match check_statements stys ftys [(m, [])] [def.fn_def_sts] with
      | TE_either.Left err ->
        if should_typecheck then RC_fails_to_typecheck err else RC_rejected_as_expected
      | TE_either.Right () ->
        if should_typecheck then RC_typechecks_as_expected else RC_unexpectedly_typechecks))
| _ -> RC_skip