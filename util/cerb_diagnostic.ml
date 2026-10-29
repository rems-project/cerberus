open Cerb_colour

type error_verbosity =
  | Basic    (* similar to a normal compiler *)
  | RefStd   (* add an std reference to Basic *)
  | QuoteStd (* print a full quote of the std text *)

type config = {
  verbosity: error_verbosity;
  n1570: Yojson.Basic.t option;
}

let err_count = ref 0
let wrn_count = ref 0
let log_warn = Logs.Src.create "Cerb_diagnostic.warn"
let conf = ref { verbosity= QuoteStd; n1570= None }


let init ~verbosity ?n1570 () =
  let n1570 = match n1570 with
  | None ->
      if verbosity <> QuoteStd then
        None
      else Some (Lazy.force N1570.data)
  | Some x -> x in
  conf := { verbosity; n1570 }

let exit code =
  if !wrn_count > 0 then Printf.eprintf "%d warning generated.\n" !wrn_count;
  if !err_count > 0 then Printf.eprintf "%d error generated.\n" !err_count;
  exit code

let get_verbosity () =
  !conf.verbosity

let get_std_quote ref =
  let key =
    String.split_on_char ',' ref |> List.hd (* remove everything after ',' *)
  in
  match !conf.n1570 with
  | Some (`Assoc xs) ->
    begin match List.assoc_opt key xs with
      | Some (`String b) -> "\n" ^ b
      | _ -> "(ISO C11 quote not found)"
    end
  | _ -> "(Missing N1507 file)"


exception Internal_error of string

let internal_error msg =
  Printf.eprintf "%s%s\n"
    (ansi_format ~err:true [Bold; Red] "internal error: ")
    msg;
  raise (Internal_error msg)

let fatal ?(code = 1) msg =
  incr err_count;
  prerr_endline
    (ansi_format ~err:true [Bold; Red] "error: " ^ ansi_format ~err:true [Bold] msg);
  let code = if code = 0 then 1 else code in
  exit code

let warn msg =
  incr wrn_count;
  Logs.warn ~src:log_warn (fun m -> m "%s" (msg ()))
