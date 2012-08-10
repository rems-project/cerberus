include BatPervasives

exception BUG
exception ERROR

let raise_bug msg = CpLogger.bug (fun x -> x) msg; raise BUG
let raise_error msg = CpLogger.error (fun x -> x) msg; raise ERROR

let (%>) v f =
  match v with
  | Some value -> f value
  | None -> None
