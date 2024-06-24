open Cerb_frontend

module Pos : sig
  type t = private {
    line: int;
    col: int;
  }
  val compare: t -> t -> int
  val v: int -> int -> t
  val initial: t
  val newline: t -> t
  val offset_col: off:int -> t -> (t, string) result
  val increment_line: t -> int -> t
  val of_location: Cerb_location.t -> (t * t, string) result
  val[@warning "-unused-value-declaration"] to_string: t -> string
end = struct
  type t = {
    line: int;
    col: int;
  }

  let compare pos1 pos2 =
    Stdlib.compare (pos1.line, pos1.col) (pos2.line, pos2.col)

  let to_string pos =
    Printf.sprintf "{line: %d, col: %d}" pos.line pos.col

  let v line col =
    { line; col }

  let initial =
    v 1 1

  let newline pos =
    { line= pos.line + 1; col= 1 }

  let offset_col ~off pos =
    if pos.col + off < 0 then
      Error (__FUNCTION__ ^ ": pos.col < off")
    else
      Ok { pos with col= pos.col+off}
  let increment_line pos n =
    { pos with line= pos.line + n }

  let of_location loc =
    (* if not (Cerb_location.from_main_file loc) then
      Printf.fprintf stderr "\x1b[31mHEADER LOC: %s\x1b[0m\n" (Option.value ~default:"<unknown>" (Cerb_location.get_filename loc))
    ; *)
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

(* TODO: why isn't no_ident used? *)
(*
let [@warning "-27"] move_to_line ?(print=true) ?(no_ident=false) st line =
  assert (line > 0);
  assert (line >= st.current_pos.line);
  let rec aux st n =
    if n = 0 then
      st
    else match Stdlib.input_line st.input with
      | str ->
          if print then begin
            Stdlib.output_string st.output (str ^ "\n");
          end;
          aux { st with current_pos= Pos.newline st.current_pos } (n-1)
      | exception End_of_file -> begin
          Printf.fprintf stderr "st.line= %d --> line= %d [n: %d]\n"
            st.current_pos.line line n;
          failwith "end of file"
    end in
  aux st (line - st.current_pos.line)
*)


let move_to ?(print=true) ?(no_ident=false) st pos =
  let open Pos in
  (* Printf.fprintf stderr "MOVE_TO[%s] [off: %d] current_pos: %s --> %s\n"
    (if print then "print" else "\x1b[33m skip\x1b[0m")
    (Stdlib.pos_in st.input)
    (Pos.to_string st.current_pos)
    (Pos.to_string pos); *)
  assert (pos.line > 0);
  assert (pos.line >= st.current_pos.line);
  (* if not (pos.line >= st.current_pos.line) then begin
    Printf.fprintf stderr "pos.line: %d -- current_pos.line: %d\n"
      pos.line st.current_pos.line;
      failwith "BOOM"
  end ; *)
  let ident_of_line st str =
    if st.current_pos.col > 1 then
      st.last_indent
    else
      ident_of_line str in
  let rec aux st =
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
            if print then begin
              Stdlib.output_string st.output (str ^ "\n");
            end;
            aux
              { st with current_pos= Pos.newline st.current_pos (*{ line= st.current_pos.line + 1; col= 1 }*) }
      | exception End_of_file -> begin
          Printf.fprintf stderr "st.line= %d\npos.line= %d\n"
            st.current_pos.line pos.line;
          failwith "end of file"
      end in
  aux st

type injection_kind =
  | InStmt of int * string
  (* | Return of (Pos.t * Pos.t) option *)
  (* | Return of Pos.t option *)
  | Pre of string list * Cerb_frontend.Ctype.ctype * bool (* flag for whether injection is for main function *)
  | Post of string list * Cerb_frontend.Ctype.ctype

type injection_footprint = {
      start_pos: Pos.t;
      end_pos: Pos.t;
    }

type injection = {
  footprint: injection_footprint;
  kind: injection_kind;
}

(* let string_of_footprint {start_pos; end_pos} =
      Printf.sprintf "%s - %s"
        (Pos.to_string start_pos)
        (Pos.to_string end_pos) *)

(* start (1, 1) and end (1, 1) for include headers *)
let inject st inj =
  let do_output st str = Stdlib.output_string st.output (decorate_injection str); st in
  let (st, _) = move_to st inj.footprint.start_pos in
  let st = begin match inj.kind with
    | InStmt (_, str) ->
        let (st, _) = move_to ~no_ident:true ~print:false st inj.footprint.end_pos in
        do_output st str
    | Pre (strs, ret_ty, is_main) ->
        let indent = String.make (st.last_indent + 2) ' ' in
        let indented_strs = List.map ~f:(fun str -> str ^ indent) strs in
        let str = List.Old.fold_left (^) "" indented_strs in
        do_output st begin
          "\n" ^ indent ^ "/* EXECUTABLE CN PRECONDITION */" ^
          "\n" ^ indent ^
          begin if AilTypesAux.is_void ret_ty then
            ""
          else
             (let cn_ret_sym = Sym.fresh_pretty "__cn_ret"  in
              let ret_type_doc = Pp_ail.pp_ctype_declaration ~executable_spec:true (Pp_ail.pp_id_obj cn_ret_sym) Ctype.no_qualifiers ret_ty in
              let initialisation_str = if is_main then " = 0" else "" in
              Pp_utils.to_plain_pretty_string ret_type_doc ^ initialisation_str ^ ";\n" ^ indent)
          end ^
          str
        end
    | Post (strs, ret_ty) ->
        let indent = String.make st.last_indent ' ' in
        let epilogue_indent = String.make (st.last_indent + 2) ' ' in
        let indented_strs = List.map ~f:(fun str -> 
          let indent = if (String.contains str '{') then indent else epilogue_indent in
          "\n" ^ indent ^ str) 
        strs 
        in
        let str = List.Old.fold_left (^) "" indented_strs in
        do_output st begin
          "\n" ^ indent ^ "/* EXECUTABLE CN POSTCONDITION */" ^
          "\n__cn_epilogue:\n" ^
          str ^
          begin if Cerb_frontend.AilTypesAux.is_void ret_ty then
            indent ^ ";\n"
          else
            indent ^ "\nreturn __cn_ret;\n\n"
          end 
        end
  end in
  fst (move_to ~print:false st inj.footprint.end_pos)

let sort_injects xs =
  let cmp inj1 inj2 =
    let c = Pos.compare inj1.footprint.start_pos inj2.footprint.start_pos in
    if c = 0 then
      Pos.compare inj1.footprint.end_pos inj2.footprint.end_pos
    else
      c
  in
  let xs = List.Old.sort cmp xs in
  (* List.Old.iteri (fun i inj ->
    Printf.fprintf stderr "\x1b[35m[%d] -> %s @ %s\x1b[0\n"
      i
      begin match inj.kind with
        | InStmt (n,  str) ->
            "InStmt["^ string_of_int n ^ "] ==> '" ^ String.escaped str ^ "'"
        | Pre (strs, _, _) ->
            "Pre ==> [" ^ String.concat "," (List.map ~f:(fun s -> "\"" ^ String.escaped s ^ "\"" ) strs) ^ "]"
        | Post _ ->
            "Post"
      end
      (string_of_footprint inj.footprint)
  ) xs; *)
  xs

let inject_all oc filename xs =
  let st = {
    input= Stdlib.open_in filename;
    output= oc;
    current_pos= Pos.initial;
    last_indent= 0;
  } in
  let st =
    List.Old.fold_left (fun st m ->
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


let (let*) = Result.bind
let rec mapM f xs =
  match xs with
  | [] -> Ok []
  | x :: xs ->
     let* y = f x in
     let* ys = mapM f xs in
     Ok (y :: ys)


let _posOf_stmt stmt =
  let loc = A.instance_Loc_Located_AilSyntax_statement_dict.locOf_method stmt in
  Pos.of_location loc

let in_stmt_injs xs num_headers =
  mapM (fun (loc, strs) ->
    let* (start_pos, end_pos) = Pos.of_location loc in
    let num_headers = if (num_headers != 0) then (num_headers + 1) else num_headers in
    (* Printf.fprintf stderr "IN_STMT_INJS[%s], start: %s -- end: %s ---> [%s]\n"
      (Cerb_location.location_to_string loc)
      (Pos.to_string start_pos) (Pos.to_string end_pos)
      (String.concat "; " (List.map ~f:(fun str -> "'" ^ String.escaped str ^ "'") strs)); *)
    Ok
      { footprint=
          { start_pos= Pos.increment_line start_pos num_headers
          ; end_pos= Pos.v (end_pos.line + num_headers) end_pos.col }
      ; kind= InStmt (List.length strs, String.concat "\n" strs) }
  )
  xs
  (* (List.filter ~f:(fun (loc, _) -> Cerb_location.from_main_file loc) xs) *)

(* build the injections for the pre/post conditions of a C function *)
let pre_post_injs pre_post is_void is_main (A.AnnotatedStatement (loc, _, _)) =
  let* (pre_pos, post_pos) =
    let* (pre_pos, post_pos) = Pos.of_location loc in
    let* pre_pos = Pos.offset_col ~off:1 pre_pos in
    let* pos_pos = Pos.offset_col ~off:(-1) post_pos in
    Ok (pre_pos, pos_pos) in
    (* match stmt_ with
      | AilSblock (_bindings, []) ->
          Pos.of_location loc
      | AilSblock (_bindings, ss) ->
          let first = List.hd_exn ss in
          let last = Lem_list_extra.last ss in
          let* (pre_pos, _) = posOf_stmt first in
          let* (_, post_pos) = posOf_stmt last in
          Ok (pre_pos, post_pos)
      | _ ->
          Error (__FUNCTION__ ^ ": must be called on a function body statement") in *)
  (* Printf.fprintf stderr "\x1b[35mPRE[%s], pos: %s\x1b[0m\n"
    (Cerb_location.location_to_string loc)
    (Pos.to_string pre_pos);
  Printf.fprintf stderr "\x1b[35mPOST[%s], pos: %s\x1b[0m\n"
    (Cerb_location.location_to_string loc)
    (Pos.to_string post_pos); *)
  Ok
    ( { footprint= { start_pos= pre_pos; end_pos= pre_pos }
      ; kind= Pre (fst pre_post, is_void, is_main) }
    , { footprint= { start_pos= post_pos; end_pos= post_pos }
      ; kind= Post (snd pre_post, is_void) } )

(* build the injections decorating for all return statements *)
let return_injs xs =
  let rec aux acc = function
    | [] -> acc
    | (loc, e_opt, inj_strs) :: xs ->
        match acc with
          | Error _ -> acc
          | Ok acc ->
              let* (start_pos, end_pos) = Pos.of_location loc in
              let* acc' = match e_opt with
                | None -> Ok ({ footprint= {start_pos; end_pos}; kind= InStmt (1, String.concat "" inj_strs ^ "goto __cn_epilogue;\n") } :: acc)
                | Some e ->
                  let loc = A.instance_Loc_Located_AilSyntax_expression_dict.locOf_method e in
                  let* (e_start_pos, e_end_pos) = Pos.of_location loc in
                  Ok begin
                    { footprint= {start_pos; end_pos= e_start_pos}; kind= InStmt (1, "{ __cn_ret = ") } ::
                    { footprint= {start_pos=e_end_pos; end_pos}; kind= InStmt (1, "; " ^ String.concat "" inj_strs ^ "goto __cn_epilogue; }") } :: acc
                  end
              in aux (Ok acc') xs
  in aux (Ok []) xs

(* EXTERNAL *)
type 'a cn_injection = {
  filename: string;
  program: 'a A.ail_program;
  pre_post: (Symbol.sym * (string list * string list)) list;
  in_stmt: (Cerb_location.t * string list) list;
  returns: (Cerb_location.t * ('a AilSyntax.expression) option * string list) list;
}

let output_injections oc cn_inj =
  Cerb_colour.without_colour begin fun () ->
  let* injs =
    List.Old.fold_left (fun acc_ (fun_sym, (loc, _, _, _, stmt)) ->
      if not (Cerb_location.from_main_file loc) then
        (* let () = Printf.fprintf stderr "\x1b[31mSKIPPING ==> %s\x1b[0m\n" (Cerb_location.simple_location loc) in *)
        acc_
      else match List.Old.assoc_opt Symbol.equal_sym fun_sym cn_inj.pre_post with
        | Some pre_post_strs ->
            begin match acc_, List.Old.assoc Symbol.equal_sym fun_sym (snd cn_inj.program).A.declarations with
              | Ok acc, (_, _, A.Decl_function (_, (_, ret_ty), _, _, _, _)) ->
                  let is_main = match fst cn_inj.program with
                    | Some main_sym when Symbol.equal_sym main_sym fun_sym -> true
                    | _ -> false in
                  let* (pre, post) = pre_post_injs pre_post_strs ret_ty is_main stmt in
                  Ok (pre :: post :: acc)
              | _ ->
                  assert false
            end
        | None ->
            acc_
    ) (Ok []) (snd cn_inj.program).A.function_definitions in

    let* in_stmt = in_stmt_injs cn_inj.in_stmt 0 in
    let* rets = return_injs cn_inj.returns in
    let injs = in_stmt @ rets @ injs in
    ignore (inject_all oc cn_inj.filename injs);
    Ok ()
  end ()


open Cerb_frontend
let get_magics_of_statement stmt =
  let open AilSyntax in
  let rec aux acc (AnnotatedStatement (_loc, Annot.Attrs xs, stmt_)) =
    let acc =
      List.Old.fold_left (fun acc attr ->
        let open Annot in
        match (attr.attr_ns, attr.attr_id, attr.attr_args) with
          | (Some (Symbol.Identifier (_, "cerb")), Symbol.Identifier (_, "magic"), xs) ->
              List.map ~f:(fun (loc, str, _) -> (loc, str)) xs :: acc
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

          List.Old.fold_left aux acc ss
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
