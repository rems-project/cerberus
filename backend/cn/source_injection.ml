open Cerb_frontend

module Pos = struct
  type t = {
    line: int;
    col: int;
  }

  let v line col =
    { line; col }

  let of_location loc =
    match Cerb_location.to_cartesian loc with
      | None ->
          Error (__FUNCTION__ ^ ": failed to get line/col positions")
      | Some ((start_line, start_col), (end_line, end_col)) ->
          Ok (v (start_line+1) (start_col+1), v (end_line+1) (end_col+1))
end


type state = {
  input: Stdlib.in_channel;
  output: Stdlib.out_channel;
  current_pos: Pos.t;
  last_indent: int;
}


let ident_of_line str =
  let rec aux i =
    match String.get str i with
      | ' ' | '\t' ->
          aux (i+1)
      | exception (Invalid_argument _)
      | _ ->
        i
  in aux 0

let with_debug = false

let decorate_indent str =
  if with_debug then
    "\x1b[30;41m" ^ str ^ "\x1b[0m"
  else
    str

let decorate_injection str =
  if with_debug then
    "\x1b[33m" ^ str ^ "\x1b[0m"
  else
    str


let move_to ?(print=true) ?(no_ident=false) st pos =
  let open Pos in
  assert (pos.line > 0);
  assert (pos.line >= st.current_pos.line);
  let ident_of_line st str =
    if st.current_pos.col > 1 then
      st.last_indent
    else
      ident_of_line str in
  let rec aux last_indent st =
    if st.current_pos.line = pos.line then
      let len = pos.col - st.current_pos.col in
      let str =
        if len = 0 && not no_ident then
          ""
        else
          Stdlib.really_input_string st.input len in
      if print then begin
        Stdlib.output_string st.output (decorate_indent str)
      end;
      let last_indent = ident_of_line st str in
      ({ st with current_pos= pos; last_indent; }, str)
    else match Stdlib.input_line st.input with
      | str ->
          let last_indent = ident_of_line st str in
            if print then begin
              Stdlib.output_string st.output (str ^ "\n");
            end;
            aux last_indent
              { st with current_pos= { line= st.current_pos.line + 1; col= 1 } }
      | exception End_of_file -> begin
          Printf.fprintf stderr "st.line= %d\npos.line= %d\n"
            st.current_pos.line pos.line;
          failwith "end of file"
      end in
  aux st.last_indent st

type injection_kind =
  | InStmt of string
  | Return of (Pos.t * Pos.t) option
  | Pre of string list * Cerb_frontend.Ctype.ctype
  | Post of string list * Cerb_frontend.Ctype.ctype

type injection = {
  start_pos: Pos.t;
  end_pos: Pos.t;
  kind: injection_kind;
}

(* start (1, 1) and end (1, 1) for include headers *)
let inject st inj =
  (* let open Cerb_frontend in *)
  let do_output st str = Stdlib.output_string st.output (decorate_injection str); st in
  let (st, _) = move_to st inj.start_pos in
  let st = begin match inj.kind with
    | InStmt str ->
        let (st, _) = move_to ~no_ident:true ~print:false st {inj.end_pos with col= inj.end_pos.col } in
        do_output st (String.escaped str)
    | Return None ->
        do_output st ""
        (* do_output st ("__CN_RETURN_VOID;") *)
    | Return (Some (start_pos, end_pos)) ->
        let st = do_output st "__cn_ret = " in
        let (st, _) = move_to ~print:false st start_pos in
        let (st, _) = move_to ~no_ident:true st end_pos in
        do_output st ";"
    | Pre (strs, ret_ty) ->
        let indent = String.make st.last_indent ' ' in
        let indented_strs = List.map (fun str -> str ^ indent) strs in
        let str = List.fold_left (^) "" indented_strs in
        do_output st begin
          begin if AilTypesAux.is_void ret_ty then
            ""
          else
            String_ail.string_of_ctype Ctype.no_qualifiers ret_ty ^ " __cn_ret;\n" ^ indent
          end ^
          (* "__CN_PRE(__cn_id_" ^ str ^ ");\n"  *)
          str
          (* ^ indent *)
        end
    | Post (strs, ret_ty) ->
        let indent = String.make st.last_indent ' ' in
        let indented_strs = List.map (fun str -> "\n" ^ indent ^ str) strs in
        let str = List.fold_left (^) "" indented_strs in
        do_output st begin
          str
          ^

          (* "\n__cn_epilogue:\n" ^ *)
          (* "\n" ^
          indent ^ 
          str  *)
          (* "__CN_POST(__cn_id_" ^ str ^ ");" ^ *)
          begin if Cerb_frontend.AilTypesAux.is_void ret_ty then
            ""
          else
            "\n" ^ indent ^ "return __cn_ret;"
          end 
        end
  end in
  fst (move_to ~print:false st inj.end_pos)

let sort_injects xs =
  let cmp inj1 inj2 =
    let open Pos in
    Stdlib.compare (inj1.start_pos.line, inj1.start_pos.col) (inj2.start_pos.line, inj2.start_pos.col) in
  List.sort cmp xs

let inject_all oc filename xs =
  let st = {
    input= Stdlib.open_in filename;
    output= oc;
    current_pos= { line= 1; col= 1 };
    last_indent= 0;
  } in
  let st =
    List.fold_left (fun st m ->
      inject st m
    ) st (sort_injects xs) in
  let rec aux () =
    match Stdlib.input_line st.input with
      (* | Some str -> *)
    | str ->
       Stdlib.output_string st.output (str ^ "\n");
       aux ()
      (* | None -> *)
    | exception End_of_file ->
       st
  in
  aux ()

open Cerb_frontend
module A = AilSyntax

let collect_return_locations stmt =
  let rec aux acc (A.AnnotatedStatement (loc, _, stmt_)) =
    match stmt_ with
      | AilSskip
      | AilSexpr _
      | AilSbreak
      | AilScontinue
      | AilSgoto _
      | AilSdeclaration _
      | AilSreg_store _ ->
          acc
      | AilSreturnVoid ->
          (loc, None) :: acc
      | AilSreturn e ->
          (loc, Some e) :: acc
      | AilSblock (_, ss)
      | AilSpar ss ->
        List.fold_left aux acc ss
      | AilSif (_, s1, s2) ->
          aux (aux acc s1) s2
      | AilSwhile (_, s, _)
      | AilSdo (s, _, _)
      | AilSswitch (_, s)
      | AilScase (_, s)
      | AilScase_rangeGNU (_, _, s)
      | AilSdefault s
      | AilSlabel (_, s, _)
      | AilSmarker (_, s) ->
          aux acc s in
  aux [] stmt

let posOf_expr expr =
  let loc = A.instance_Loc_Located_AilSyntax_expression_dict.locOf_method expr in
  Pos.of_location loc

let posOf_stmt stmt =
  let loc = A.instance_Loc_Located_AilSyntax_statement_dict.locOf_method stmt in
  Pos.of_location loc

let (let*) = Result.bind
let rec mapM f xs =
  match xs with
  | [] -> Ok []
  | x :: xs ->
     let* y = f x in
     let* ys = mapM f xs in
     Ok (y :: ys)

let in_stmt_injs xs num_headers =
  mapM (fun (loc, str) ->
    let* (start_pos, end_pos) = Pos.of_location loc in
    let num_headers = if (num_headers != 0) then (num_headers + 1) else num_headers in
    Ok
      { start_pos= { col= start_pos.col; line= start_pos.line + num_headers }
      ; end_pos= {col= end_pos.col + 6; line= end_pos.line + num_headers }
      ; kind= InStmt str }
  ) xs

(* build the injections for the pre/post conditions of a C function *)
let pre_post_injs pre_post is_void (A.AnnotatedStatement (loc, _, stmt_)) =
  let* (pre_pos, post_pos) =
    match stmt_ with
      | AilSblock (bs, []) ->
          Pos.of_location loc
      | AilSblock (bs, ss) ->
          let first = List.hd ss in
          let last = Lem_list_extra.last ss in
          let* (pre_pos, _) = posOf_stmt first in
          let* (_, post_pos) = posOf_stmt last in
          Ok (pre_pos, post_pos)
      | _ ->
          Error (__FUNCTION__ ^ ": must be called on a function body statement") in
  Ok
    ( { start_pos= pre_pos; end_pos= pre_pos
      ; kind= Pre (fst pre_post, is_void) }
    , { start_pos= post_pos; end_pos= post_pos
      ; kind= Post (snd pre_post, is_void) } )

(* build the injections decorating the return statements in a statement (typically a function body) *)
let return_injs stmt =
  mapM (fun (loc, e_opt) ->
    let* (start_pos, end_pos) = Pos.of_location loc in
    let* z =
      match e_opt with
        | Some e -> let* z = posOf_expr e in Ok (Some z)
        | None -> Ok None in
    Ok { start_pos; end_pos; kind= Return z }
  ) (collect_return_locations stmt)


(* EXTERNAL *)
type 'a cn_injection = {
  filename: string;
  sigm: 'a A.sigma;
  pre_post: (Symbol.sym * (string list * string list)) list;
  in_stmt: (Cerb_location.t * string) list;
}

let output_injections oc cn_inj =
  Cerb_colour.without_colour begin fun () ->
  let* injs =
    List.fold_left (fun acc_ (fun_sym, (_, _, _, _, stmt)) ->
      match List.assoc_opt Symbol.equal_sym fun_sym cn_inj.pre_post with
        | Some pre_post_strs ->
            begin match acc_, List.assoc Symbol.equal_sym fun_sym cn_inj.sigm.A.declarations with
              | Ok acc, (_, _, A.Decl_function (_, (_, ret_ty), _, _, _, _)) ->
                  let* (pre, post) = pre_post_injs pre_post_strs ret_ty stmt in
                  let* rets = return_injs stmt in
                  Ok (pre :: post ::  rets @ acc)
              | _ ->
                  assert false
            end
        | None ->
            acc_
    ) (Ok []) cn_inj.sigm.A.function_definitions in

    let* in_stmt = in_stmt_injs cn_inj.in_stmt 0 in
    let injs = in_stmt @ injs in
    ignore (inject_all oc cn_inj.filename injs);
    Ok ()
  end ()



open Cerb_frontend
let get_magics_of_statement stmt =
  let open AilSyntax in
  let rec aux acc (AnnotatedStatement (loc, Annot.Attrs xs, stmt_)) =
    let acc =
      List.fold_left (fun acc attr ->
        let open Annot in
        match (attr.attr_ns, attr.attr_id, attr.attr_args) with
          | (Some (Symbol.Identifier (_, "cerb")), Symbol.Identifier (_, "magic"), xs) ->
              List.map (fun (loc, str, _) -> (loc, str)) xs :: acc
         | _ ->
            acc
      ) acc xs in
    match stmt_ with
      | AilSskip
      | AilSexpr _
      | AilSbreak
      | AilScontinue
      | AilSreturnVoid
      | AilSreturn _
      | AilSgoto _
      | AilSdeclaration _
      | AilSreg_store _ ->
          acc

      | AilSblock (_, ss)
      | AilSpar ss ->

          List.fold_left aux acc ss
      | AilSif (_, s1, s2) ->
          aux (aux acc s1) s2
      | AilSwhile (_, s, _)
      | AilSdo (s, _, _)
      | AilSswitch (_, s)
      | AilScase (_, s)
      | AilScase_rangeGNU (_, _, s)
      | AilSdefault s
      | AilSlabel (_, s, _)
      | AilSmarker (_, s) ->
        aux acc s
  in aux [] stmt
