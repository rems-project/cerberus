(* Exercise an actual Lem-generated caller, including its __FUNCTION__ name
   and debug_enabled guard. Symbol identity ignores its descriptive label. *)
open Cerb_frontend

let () =
  let digest = Digest.string "logging-test" in
  let left = Symbol.Symbol (digest, 0, Symbol.SD_Id "left") in
  let right = Symbol.Symbol (digest, 0, Symbol.SD_Id "right") in
  let events = ref [] in
  Logs.set_reporter {Logs.report = fun src level ~over k msgf ->
    msgf (fun ?header:_ ?tags:_ fmt -> Format.kasprintf (fun message ->
      events := (Logs.Src.name src, level, message) :: !events;
      over (); k ()) fmt)};
  Cerb_log_auto.configure (Some Logs.Warning) [];
  assert (Symbol.equal_sym left right);
  assert (!events = []);
  Cerb_log_auto.configure (Some Logs.Warning) ["Symbol.symbolEquality"];
  assert (Symbol.equal_sym left right);
  (match !events with
   | [("Symbol.symbolEquality", Logs.Debug, message)] ->
       assert (String.starts_with ~prefix:"[Symbol.symbolEqual] suspicious equality" message)
   | _ -> failwith "Lem extraction lost the caller's function name or message");
  Cerb_log_auto.configure None ["all"];
  assert (Symbol.equal_sym left right);
  assert (List.length !events = 1);
  Logs.set_reporter Logs.nop_reporter;
  print_endline "Lem-generated caller: automatic name, filtering and unchanged result passed"
