(* Exercise an actual Lem-generated caller, including its __FUNCTION__ name
   and conditional emission. Symbol identity ignores its descriptive label. *)
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
  Cerb_log.configure (Some Logs.Warning) [];
  assert (Symbol.equal_sym left right);
  assert (!events = []);
  Cerb_log.configure (Some Logs.Warning) ["Symbol.symbolEquality"];
  assert (Symbol.equal_sym left left);
  assert (!events = []);
  assert (Symbol.equal_sym left right);
  (match !events with
   | [("Symbol.symbolEquality", Logs.Debug, message)] ->
       assert (String.starts_with ~prefix:"[Symbol.symbolEqual] suspicious equality" message)
   | _ -> failwith "Lem extraction lost the caller's function name or message");
  let warning () =
    assert (Translation.floating_conversion_TODO Ctype.void Ctype.void 7 = 7) in
  let error () =
    let _action = Translation_effect.record_error "logging test error" in () in
  events := [];
  Cerb_log.configure (Some Logs.Warning) [];
  warning (); error ();
  (match List.rev !events with
   | [("Translation.floating_conversion_TODO", Logs.Warning, message);
      ("Translation_effect.record_error", Logs.Error, "logging test error")] ->
       assert (String.starts_with ~prefix:"casts between floating types" message)
   | _ -> failwith "Lem warning/error extraction lost automatic names or severities");
  Logs.set_reporter Logs.nop_reporter;
  print_endline "Lem-generated callers: automatic Debug/Warning/Error names and filtering passed"
