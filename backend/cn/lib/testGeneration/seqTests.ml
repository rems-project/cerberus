module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module ESpecInternal = Executable_spec_internal
module Config = TestGenConfig
module SymSet = Set.Make (Sym)

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

let gen_arg 
  (ctx : (Sym.t * C.ctype) list)  
  ((_, ty) : Sym.t * C.ctype) 
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
        let prev_calls = List.filter (fun (_, ct) -> C.ctypeEqual ty ct) ctx in
        (match List.length prev_calls with
        | 0 -> []
        | n -> let (name, _) = List.nth prev_calls (Random.int n) in [Sym.pp name])
    in
    let options = List.append generated_base_ty prev_call in
    match List.length options with
    | 0 -> failwith "unable to generate arg or reuse context"
    | n -> List.nth options (Random.int n)

let gen_test 
  (ctx : (Sym.t * C.ctype) list)  
  (args_map : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))) 
  (prev : int)
  =
  let open Pp in 
  (match args_map with
  | (f, ((qualifiers, ret_ty), args)) -> 
    let (ctx', assign) = 
    (match ret_ty with 
    | Ctype(_, Void) -> (ctx, empty) (* attempted to use fresh_cn but did not work for some reason?*)
    | _ -> let name = Sym.fresh_named ("x" ^ string_of_int prev) in 
          ((name, ret_ty)::ctx, separate space [CF.Pp_ail.pp_ctype qualifiers ret_ty; Sym.pp name; equals]))
    in 
    (ctx', assign ^^ Sym.pp f ^^ parens
    (separate
      (comma ^^ space)
      [ separate_map (comma ^^ space) (gen_arg ctx) args ])
      ^^ semi ^^ hardline))

(* let rec dist_to_str
(distribution : (int * (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list))) list) =
match distribution with
[] -> " "
| (score, (f, (_, _)))::l -> string_of_int score ^ "," ^ (Sym.pp_string f) ^  "; " ^ dist_to_str l *)

let rec gen_sequence 
  (args_map : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list)) list)
  (fuel : int)
  (ctx : (Sym.t * C.ctype) list)
  (prev : int)
  : Pp.document
  = 
    let open Pp in 
    (match fuel with
    | 0 -> empty
    | n -> 
      let fs = List.map 
        (fun ((_, (_, args)) as f)  -> (calc_score ctx args, f))
      (List.filter (callable ctx) args_map) in
      let (ctx', curr_test) =
      (match (List.length fs) with
      | 0 -> (ctx, string "unable to generate call at this point")
      | _ -> gen_test ctx (pick fs (Random.int (List.fold_left (+) 1 (List.map fst fs)))) prev )
      in
      curr_test ^^ gen_sequence args_map (n - 1) ctx' (prev + 1))

let compile_sequence 
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (insts : Core_to_mucore.instrumentation list)
  (num_samples : int)
  : Pp.document
  = 
  let fuel = num_samples in
  let declarations : A.sigma_declaration list =
    insts
    |> List.map (fun (inst : Core_to_mucore.instrumentation) ->
      (inst.fn, List.assoc Sym.equal inst.fn sigma.declarations))
  in
  let args_map : (Sym.t * ((C.qualifiers * C.ctype) * (Sym.t * C.ctype) list)) list =
    List.map
      (fun (inst : Core_to_mucore.instrumentation) ->
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
      gen_sequence args_map fuel [] 0

let compile_tests
(filename_base : string)
(sigma : CF.GenTypes.genTypeCategory A.sigma)
(insts : Core_to_mucore.instrumentation list)
(num_samples : int)
=
  let sequence = compile_sequence sigma insts num_samples in
  let open Pp in
  string "#include "
  ^^ dquotes (string (filename_base ^ ".c"))
  ^^ twice hardline
  ^^ string "int main"
  ^^ parens (string "int argc, char* argv[]")
  ^^ break 1
  ^^ braces (nest 2 (hardline ^^ sequence ^^ hardline ^^ (string "return 0;")) ^^ hardline)

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

let generate
~(output_dir : string)
~(filename : string)
(num_samples : int)
(sigma : CF.GenTypes.genTypeCategory A.sigma)
(prog5 : unit Mucore.file)

: unit
=
  let insts =
    prog5
    |> Core_to_mucore.collect_instrumentation
    |> fst
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      Option.is_some inst.internal)
  in
  if List.is_empty insts then failwith "No testable functions";
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let tests_doc =
    compile_tests filename_base sigma insts num_samples
  in
  let test_file = filename_base ^ "_test.c" in
  save output_dir test_file tests_doc;
  ()
