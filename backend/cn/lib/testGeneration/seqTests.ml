module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module Utils = Executable_spec_utils
(* module Config = TestGenConfig *)
module SymSet = Set.Make (Sym)

type test_stats = {successes : int; failures : int; skipped: int}

let save ?(perm = 0o666) (output_dir : string) (filename : string) (doc : Pp.document)
: unit
=
let oc =
  Stdlib.open_out_gen
    [ Open_wronly; Open_creat; Open_trunc; Open_text ]
    perm
    (Filename.concat output_dir filename)
in
output_string oc (Pp.plain ~width:80 doc);
close_out oc

let rec pick 
  (distribution : (int * (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))) list) 
  (i : int)
  : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))
  =
  match distribution with
  | [] -> failwith "impossible case"
  | (score, f)::fs -> if i <= score then f else pick fs (i - score)

let callable 
  (ctx : (Sym.t * C.ctype) list) 
  ((_, (_, args)) : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))) 
  : bool 
  = 
  List.for_all (fun x -> x) (List.map (fun (_, (ty : C.ctype)) -> 
    (match ty with 
    | Ctype(_, ty) ->
      (match ty with
      | Basic(Integer(Char)) | Basic(Integer(Bool)) | Basic(Integer(Signed(_))) 
      | Basic(Integer(Unsigned(_))) | Basic(Floating(_)) | Void -> true
      | Pointer(_, ty) -> List.exists (fun (_, ct) -> C.ctypeEqual ty ct) ctx
      | _ -> false)) 
    || List.exists (fun (_, ct) -> C.ctypeEqual ty ct) ctx) 
    args)
     
let calc_score
  (ctx : (Sym.t * C.ctype) list) 
  (args : (Sym.t * C.ctype) list)
  : int
  =
  List.fold_left 
  (fun acc (_, ty) -> 
    if (List.exists (fun (_, ct) -> C.ctypeEqual ty ct) ctx) then acc + 10
    else acc) 
  1 args

let ctx_to_string 
  (ctx : (Sym.t * C.ctype) list)
  : string
  =
  List.fold_left (^) "" (
    List.map (
      fun (name, ty) ->
        "(" ^ (Sym.pp_string name) ^ ":" ^ (CF.String_core_ctype.string_of_ctype ty) ^ ")"
    ) ctx)

let gen_arg 
  (ctx : (Sym.t * C.ctype) list)  
  ((name, ty) : Sym.t * C.ctype) 
  : Pp.document
  =
  let open Pp in 
  let generated_base_ty = 
  (match ty with 
  | Ctype(_, ty1) ->
    (match ty1 with
    | Basic(Integer(Char))        -> [string "\'" ^^ char (char_of_int ((Random.int 96) + 32)) ^^ string "\'"]
    | Basic(Integer(Bool))        -> [if Random.int 2 = 1 then string "true" else string "false"]
    | Basic(Integer(Signed(_)))   -> let rand_int = Random.int 32767 in 
                                      [int (if Random.int 2 = 1 then (rand_int * -1) else rand_int)]
    | Basic(Integer(Unsigned(_))) -> [int (Random.int 65536)]
    | Basic(Floating(_))          -> [string (string_of_float (Random.float 65536.0))]
    | Void                        -> [empty]
    | _                           -> []))
    in
    let prev_call = 
        let prev_calls = 
          List.filter (
            fun (_, ct) -> 
              C.ctypeEqual ty ct || 
              (match ty with 
              | Ctype(_, Pointer(_, ty)) -> (C.ctypeEqual ty ct)
              | _ -> false
              )
          ) ctx in
        (match List.length prev_calls with
        | 0 -> []
        | n -> 
          let (name, ty') = List.nth prev_calls (Random.int n) in
          if not (C.ctypeEqual ty' ty) then (* only way they're not directly equal is if pointer*)
            [string "&" ^^ Sym.pp name]
          else
            [Sym.pp name])
    in
    let options = List.append generated_base_ty prev_call in
    match List.length options with
    | 0 -> failwith 
            ("unable to generate arg or reuse context for " 
            ^ (Sym.pp_string name) ^ " in context " ^ (ctx_to_string ctx))
    | n -> List.nth options (Random.int n)

let stmt_to_doc 
  (stmt: CF.GenTypes.genTypeCategory A.statement_)
  : Pp.document
  =
  (CF.Pp_ail.pp_statement ~executable_spec:true ~bs:[] 
      (Utils.mk_stmt 
        (stmt))) 

let create_test_file 
  (sequence : Pp.document) 
  (fun_decls : Pp.document)
  : Pp.document
  =
  let open Pp in
  string "#include "
  ^^ dquotes (string "cn.h")
  ^^ twice hardline
  ^^ fun_decls
  ^^ twice hardline
  (* need to add function signatures ex. void push_queue (int x, struct queue *q); *)
  ^^ string "int main"
  ^^ parens (string "int argc, char* argv[]")
  ^^ break 1
  ^^ braces 
      (nest 2 
        (hardline 
          ^^ 
          let init_ghost = Ownership_exec.get_ownership_global_init_stats () in
          separate_map hardline stmt_to_doc init_ghost 
          ^^ hardline
          ^^ sequence 
          ^^ hardline 
          ^^ (string "return 0;")) 
          ^^ hardline)

let out_to_list 
(command : string) 
=
  let chan = Unix.open_process_in command in
  let res = ref ([] : string list) in
  let rec go () =  
    let e = input_line chan in
    res := e::!res;
    go() in
  try go ()
  with End_of_file ->
    let status = Unix.close_process_in chan in (!res, status)

let rec gen_sequence 
  (funcs : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list)) list)
  (fuel : int)
  (max_retries : int)
  (stats : test_stats)
  (ctx : (Sym.t * C.ctype) list)
  (prev : int)
  (seq_so_far : Pp.document)
  (output_dir : string)
  (filename_base : string)
  (src_code : string list)
  (fun_decls : Pp.document)
  : (Pp.document * test_stats, Pp.document * test_stats) Either.either
  =           
    let open Pp 
    in 
    (match fuel with
    | 0 -> let unmap_stmts = List.map Ownership_exec.generate_c_local_ownership_exit ctx in
           let unmap_str = hardline ^^ separate_map hardline stmt_to_doc unmap_stmts in Right(seq_so_far ^^ unmap_str, stats)
    | n -> 
      let fs = List.map 
        (fun ((_, (_, args)) as f)  -> (calc_score ctx args, f))
      (List.filter (callable ctx) funcs) in
      let rec gen_test 
        (args_map : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))) 
        (retries_left : int)
        : (SymSet.elt * C.ctype) list * int * (document, document) Either.either
        =
        if retries_left = 0 then 
          ctx, prev, Either.Left(empty)
        else
        (match args_map with
        | (f, ((qualifiers, ret_ty), args)) -> 
          let (ctx', name, assign, prev) = 
          (match ret_ty with 
          | Ctype(_, Void) -> (ctx, None, empty, prev) (* attempted to use fresh_cn but did not work for some reason?*)
          | _ -> let name = Sym.fresh_named ("x" ^ string_of_int prev) in 
                ((name, ret_ty)::ctx, Some(name), separate space [CF.Pp_ail.pp_ctype qualifiers ret_ty; Sym.pp name; equals], prev+1))
          in
          let curr_test = 
            (assign ^^ Sym.pp f ^^ parens
            (separate
              (comma ^^ space)
              [ separate_map (comma ^^ space) (gen_arg ctx) args ])
            ^^ semi 
            ^^ hardline 
            ^^ (match name with 
            | None -> empty
            | Some(name) -> 
                stmt_to_doc(A.AilSexpr(Ownership_exec.generate_c_local_ownership_entry_fcall (name, ret_ty))) 
                ^^ hardline)
            ) 
          in
          let _ = save output_dir (filename_base ^ "_test.c") (create_test_file (seq_so_far ^^ curr_test) fun_decls) in
          let (output, status) = out_to_list (output_dir ^ "/run_tests.sh") in
          match status with
          | WEXITED(0) -> ctx', prev, Either.Right(curr_test)
          | _ -> 
            let violation_regex = Str.regexp {| +\^~+ .+\.c:\([0-9]+\):[0-9]+-[0-9]+|} in
            let is_post_regex = Str.regexp {|\(/\*@\)?[ \t]*ensures|} in
            let is_pre_regex = Str.regexp {|\(/\*@\)?[ \t]*requires|} in
            let rec get_violation_line test_output =
              match test_output with
              | [] -> 0
              | line::lines -> 
                  if Str.string_match violation_regex line 0 then
                    int_of_string (Str.matched_group 1 line)
                  else get_violation_line lines 
            in 
            let rec is_precond_violation code =
              match code with
              | [] -> true
              | line::lines -> 
                  if Str.string_match is_post_regex line 0 then false
                  else if Str.string_match is_pre_regex line 0 then true 
                  else is_precond_violation lines 
            in
            let drop n l = (* ripped from OCaml 5.3 *)
              let rec aux i = function
                | _x::l when i < n -> aux (i + 1) l
                | rest -> rest
              in
              if n < 0 then invalid_arg "List.drop";
              aux 0 l
            in 
            let violation_line_num = get_violation_line output in
            if is_precond_violation (drop (List.length src_code - violation_line_num) src_code) then
              gen_test (pick fs (Random.int (List.fold_left (+) 1 (List.map fst fs)))) (retries_left - 1)
            else
              (ctx', prev,
              Either.Left(
                string 
                  (Printf.sprintf "/* violation of post-condition at line number %d in %s detected on this call: */" 
                    violation_line_num (filename_base ^ ".c")) 
                ^^ hardline 
                ^^ curr_test)
              )
        )
      in
      (match (List.length fs) with
      | 0 -> Left(seq_so_far ^^ (string "/* unable to generate call at this point */"), {stats with failures = stats.failures + 1})
      | _ -> 
        (match gen_test (pick fs (Random.int (List.fold_left (+) 1 (List.map fst fs)))) max_retries with
        | ctx', prev, Either.Right(test) -> gen_sequence funcs (n - 1) max_retries {stats with successes = stats.successes + 1} ctx' prev (seq_so_far ^^ test) output_dir filename_base src_code fun_decls
        | _, prev, Either.Left(err) -> 
          (if is_empty err then 
            gen_sequence funcs (n - 1) max_retries {stats with skipped = stats.skipped + 1} ctx prev seq_so_far output_dir filename_base src_code fun_decls
          else 
            Either.Left(seq_so_far ^^ err, {stats with failures = 1}))))
    )

let compile_sequence 
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (insts : Executable_spec_extract.instrumentation list)
  (num_samples : int)
  (max_retries : int)
  (output_dir : string)
  (filename_base : string)
  (src_code : string list)
  (fun_decls : Pp.document)
  : (Pp.document * test_stats, Pp.document * test_stats) Either.either
  = 
  let fuel = num_samples in
  let declarations : A.sigma_declaration list =
    insts
    |> List.map (fun (inst : Executable_spec_extract.instrumentation) ->
      (inst.fn, List.assoc Sym.equal inst.fn sigma.declarations))
  in
  let args_map : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list)) list =
    List.map
      (fun (inst : Executable_spec_extract.instrumentation) ->
        ( inst.fn,
          let _, _, _, xs, _ = List.assoc Sym.equal inst.fn sigma.function_definitions in
          match List.assoc Sym.equal inst.fn declarations with
          | _, _, Decl_function (_, (qual, ret), cts, _, _, _) ->
            ((qual, ret), List.combine xs (List.map (fun (_, ct, _) -> ct) cts))
          | _ ->
            failwith
              (String.concat
                  " "
                  [ "Function declaration not found for";
                    Sym.pp_string inst.fn;
                    "@";
                    __LOC__
                  ]) )) insts in
      gen_sequence args_map fuel max_retries {successes = 0; failures = 0; skipped = 0} [] 0 Pp.empty output_dir filename_base src_code fun_decls

let generate
  ~(output_dir : string)
  ~(filename : string)
  (num_samples : int)
  (max_retries : int)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  : unit
  =
  let insts =
    prog5
    |> Executable_spec_extract.collect_instrumentation
    |> fst
    |> List.filter (fun (inst : Executable_spec_extract.instrumentation) ->
      Option.is_some inst.internal)
  in
  if List.is_empty insts then failwith "No testable functions";
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let test_file = filename_base ^ "_test.c" in
  let script_doc = BuildScript.generate ~output_dir ~filename_base in
  let src_code, _ = out_to_list ("cat " ^ filename) in
  save ~perm:0o777 output_dir "run_tests.sh" script_doc;
  let fun_to_decl (inst : Executable_spec_extract.instrumentation) =
    CF.Pp_ail.pp_function_prototype
         ~executable_spec:true
         inst.fn
         (let _, _, decl = List.assoc Sym.equal inst.fn sigma.declarations in
          decl)
    in 
    let open Pp in
  let fun_decls = separate_map (hardline) fun_to_decl insts in
  let compiled_seq = compile_sequence sigma insts num_samples max_retries output_dir filename_base src_code fun_decls in
  let seq, output_msg = match compiled_seq with
  | Left(seq, stats) -> 
      seq, (Printf.sprintf 
              "Testing Summary:\n\
              %d tests succeeded\n\
              POST-CONDITION VIOLATION DETECTED.\n\
              See %s/%s for details"
            stats.successes output_dir test_file)
  | Right(seq, stats) ->
      seq, (Printf.sprintf 
              "Testing Summary:\n\
              passed: %d, failed: %d, skipped: %d" 
            stats.successes stats.failures stats.skipped)
  in
  let tests_doc = create_test_file seq fun_decls in
  print_endline output_msg;
  save output_dir test_file tests_doc;
  ()
