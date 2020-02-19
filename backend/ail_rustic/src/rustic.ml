(* TODO: shared with BMC functors *)

module Map_of_list (X : Map.S) = struct
  let of_list (l : 'a) =
    List.fold_left
      (fun mo (x, v) ->
        match mo with
        | None -> None
        | Some m ->
          (match X.find_opt x m with
          | None -> Some (X.add x v m)
          | Some _ -> None))
      (Some X.empty)
      l
end

let rec map_option_aux f acc = function
  | [] -> List.rev acc
  | x :: xs ->
    (match f x with
     | None -> map_option_aux f acc xs
     | Some y -> map_option_aux f (y :: acc) xs)

let map_option f xs = map_option_aux f [] xs

module Option_map (X : Map.S) = struct
  module Z = Map_of_list(X)

  let map (f : X.key -> 'a -> 'b option) (s : 'a X.t) =
    let m = Z.of_list (map_option (fun (k, v) -> match f k v with None -> None | Some v' -> Some (k, v')) (X.bindings s)) in
    match m with
    | None -> (* it came from a map, and entries can only be deleted, so it is still functional *) assert false
    | Some m' -> m'
end

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

let string_of_sym (Symbol.Symbol (_, _, Some id)) = id

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

let print_funs fs =
  List.iter (fun f -> print_string (string_of_fun f ^ "\n")) fs

module Ail_identifier = struct
  type t = AilSyntax.ail_identifier
  let compare (x : t) y = Symbol.symbol_compare x y
end

module Ail_identifier_map = Map.Make(Ail_identifier)
module Ail_identifier_option_map = Option_map(Ail_identifier_map)
module Ail_identifier_map_aux = Map_of_list(Ail_identifier_map)

module String_map = Map.Make(String)
module String_map_aux = Map_of_list(String_map)

let add_left id x m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (Some x, None) m
  | Some (_, y) -> Ail_identifier_map.add id (Some x, y) m

let add_right id y m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (None, Some y) m
  | Some (x, _) -> Ail_identifier_map.add id (x, Some y) m

let collect_functions s =
  let ds = map_option (function (id, (_, Decl_function (a, b, c, d, e, f))) -> Some (id, (b, c)) | (_, (_, Decl_object _)) -> None) s.declarations in
  let fs = s.function_definitions in
  let m = Ail_identifier_map.empty in
  (* this may discard stuff *)
  let m = List.fold_left (fun m (id, d) -> add_left id (cvt_decl d) m) m ds in
  let m = List.fold_left (fun m (id, f) -> add_right id (cvt_def f) m) m fs in
  m

type rc_ownership = RC_read | RC_write | RC_zap

type rc_type =
| RC_basic
| RC_ptr of rc_ownership * rc_type
| RC_struct of Symbol.sym * rc_ownership
| RC_atomic of rc_type

type ('b) gamma_ty = (rc_type Ail_identifier_map.t * 'b) list

let rec lookup_in_gamma x = function
| [] -> None
| (bds, sts) :: gamma ->
  (match Ail_identifier_map.find_opt x bds with
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
  | _ -> failwith "?"
  )
| _ -> None

let rc_ownership_of_annots annots =
  match map_option rc_ownership_of_annot annots with
  | [rcow] -> rcow
  | _ -> RC_zap

let rec rc_type_of_cty = function
| Ctype.Ctype (_, Void) -> RC_basic
| Ctype.Ctype (_, Basic _) -> RC_basic
| Ctype.Ctype (_, Array _) -> failwith "array"
| Ctype.Ctype (_, Function _) -> failwith "function"
| Ctype.Ctype (annots, Pointer (_, cty)) -> RC_ptr (rc_ownership_of_annots annots, rc_type_of_cty cty)
| Ctype.Ctype (_, Atomic cty) -> RC_atomic (rc_type_of_cty cty)
| Ctype.Ctype (annots, Struct s) -> RC_struct (s, rc_ownership_of_annots annots)
| Ctype.Ctype (_, Union _) -> failwith "union"

let type_of_fun (f : fn_decl) =
  (List.map (fun (_, b, _) -> rc_type_of_cty b) f.fn_decl_argstys, rc_type_of_cty f.fn_decl_retty)

let collect_function_types fs =
  (* TODO: probably needs something better *)
  let hh _ = function
  | (Some fn_decl, _) -> Some (type_of_fun fn_decl)
  | _ -> None in
  Ail_identifier_option_map.map hh fs

let zap = function
| RC_basic -> RC_basic
| RC_ptr (_, rcty) -> RC_ptr (RC_zap, rcty)
| RC_struct (id, _) -> RC_struct (id, RC_zap)

let sub_own t1 t2 = match (t1, t2) with
| (RC_zap, RC_zap) -> true
| (RC_zap, _) -> false
| (_, RC_zap) -> true
| (_, RC_read) -> true
| (RC_write, RC_write) -> true
| (RC_read, RC_write) -> false

let rec sub_rcty t1 t2 = match (t1, t2) with
| (RC_basic, RC_basic) -> true
| (RC_basic, _) | (_, RC_basic) -> false
| (RC_ptr (o1, t1), RC_ptr (o2, t2)) -> sub_own o1 o2 && sub_rcty t1 t2
| (RC_ptr _, _) | (_, RC_ptr _) -> false
| (RC_struct (_, o1), RC_struct (_, o2)) -> true

let rec check_expression stys ftys gamma (AnnotatedExpression (_, _, _, e)) : 'a option =
  check_expression_ stys ftys gamma e
and check_expression_ stys ftys gamma = function
| AilEident x -> lookup_in_gamma x gamma
| AilEassign (AnnotatedExpression (_, _, _, AilEunary (Indirection, AnnotatedExpression (_, _, _, AilEident x))), e2) ->
  (match lookup_in_gamma x gamma with
  | None -> failwith "can't find variable"
  | Some cty ->
    (match cty with
     | RC_ptr (RC_write, _) -> failwith "TODO: ptr"
     | _ -> failwith "type violation?"))
| AilEassign _ -> None (* TODO *)
| AilEcall (AnnotatedExpression (_, _, _, AilEfunction_decay (AnnotatedExpression (_, _, _, AilEident f))), [e]) ->
  (match Ail_identifier_map.find_opt f ftys with
   | None -> None
   | Some ([paramty], retty) ->
     (match check_expression stys ftys gamma e with
      | None -> None
      | Some argty -> if sub_rcty argty paramty then Some retty else None)
    | _ -> failwith "multiple args")
| AilEcall _ -> failwith "TODO: other AilEcall"
| AilEunary (Address, e) ->
  Option2.map_post
    (check_expression stys ftys gamma e)
    (fun ty -> RC_ptr (RC_read, ty))
| AilEmemberofptr (e, p) ->
  Option2.bind
    (check_expression stys ftys gamma e)
    (function
     | RC_struct (s, o) ->
       Option2.bind
         (Ail_identifier_map.find_opt s stys)
         (fun sty ->
           Option2.map_post
             (String_map.find_opt (string_of_identifier p) sty)
             (fun x -> x))
     | _ -> None)
| _ -> failwith "TODO: unhandled expression"

(* TODO: this is completely wrong, it's just a skeleton *)
let rec check_statements stys ftys (gamma : 'b gamma_ty) = function
| [] -> pop stys ftys gamma
| AnnotatedStatement (_, AilSskip) :: sts -> check_statements stys ftys gamma sts
| AnnotatedStatement (_, AilSexpr e) :: sts ->
  check_expression stys ftys gamma e <> None && (* TODO: this is wrong: gamma can change! *)
  check_statements stys ftys gamma sts
| AnnotatedStatement (_, AilSblock (bds, sts1)) :: sts ->
  (match Ail_identifier_map_aux.of_list bds with
  | None -> assert false
  | Some bds ->
    let bds = Ail_identifier_map.map (fun (_, _, cty) -> zap (rc_type_of_cty cty)) bds in
    check_statements stys ftys ((bds, sts) :: gamma) sts1)
| AnnotatedStatement (_, AilSif (_, s1, s2)) :: sts ->
  check_statements stys ftys ((Ail_identifier_map.empty, sts) :: gamma) [s1] &&
  check_statements stys ftys ((Ail_identifier_map.empty, sts) :: gamma) [s2]
| AnnotatedStatement (_, AilSreturnVoid) :: sts ->
  pop stys ftys gamma
| AnnotatedStatement (_, AilSdeclaration [(x, e)]) :: sts ->
  true
| AnnotatedStatement (_, s) :: sts -> failwith "TODO: unhandled statement"
and pop stys ftys = function
| [] -> true
| (_, sts) :: gamma -> check_statements stys ftys gamma sts

let check_function stys ftys id = function
| (Some dcl, Some def) ->
  print_string (string_of_sym id);
  flush stdout;
  let m =
    let m = List.combine def.fn_def_ids (List.map (fun (_, cty, _) -> rc_type_of_cty cty) dcl.fn_decl_argstys) in
    (match Ail_identifier_map_aux.of_list m with
    | None -> assert false
    | Some m -> m) in
  let r = check_statements stys ftys [(m, [])] [def.fn_def_sts] in
  if r then print_string (": happy\n")
  else print_string (": sad\n")
| _ -> print_string (": skipped\n")

let collect_structs s =
  let g xs =
    let xs = List.map (fun (id, (_, cty)) -> (string_of_identifier id, rc_type_of_cty cty)) xs in
    match String_map_aux.of_list xs with
    | None -> assert false
    | Some xs -> xs in
  let s =
    map_option
      (function
      | (id, Ctype.StructDef xs) -> Some (id, g xs)
      | (_, Ctype.UnionDef _) -> None)
     s.tag_definitions in
  match Ail_identifier_map_aux.of_list s with
  | None -> assert false
  | Some s -> s

let run_rustic (id, s) =
  let fs = collect_functions s in
  let stys = collect_structs s in
  print_funs (Ail_identifier_map.bindings fs); flush stdout;
  let ftys = collect_function_types fs in
  Ail_identifier_map.iter (check_function stys ftys) fs;
  ()