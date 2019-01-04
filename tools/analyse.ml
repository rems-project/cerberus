type date =
  { sec: int option;
    min: int option;
    hour: int option;
    day: int option;
    mon: int option;
    year: int option;
  }

module DayMap = Map.Make(struct
    type t = date
    let compare d1 d2 =
      match compare d1.year d2.year with
      | 0 ->
        begin match compare d1.mon d2.mon with
          | 0 -> compare d1.day d2.day
          | n -> n
        end
      | n -> n
end)

module StringMap = Map.Make(struct
    type t = string
    let compare = compare
  end)

type entry =
  { ip: string;
    date: date;
    act_model: string;
    source: string;
  }

let parse_tm date time =
  Scanf.sscanf date "%d/%d/%d" (fun day mon year ->
      Scanf.sscanf time "%d:%d:%d" (fun hour min sec ->
          { sec = Some sec;
            min = Some min;
            hour = Some hour;
            day = Some day;
            mon = Some mon;
            year = Some year } ) )

let parse_line l =
  match String.split_on_char ' ' l with
  | ip :: date :: [time] ->
    let date = parse_tm date time in
    Some { ip; date; act_model = ""; source = "" }
  | ip :: date :: time :: act_model :: source_0 :: source_n ->
    if String.get source_0 0 <> '"' then begin
      prerr_endline @@ "Error parsing: " ^ l;
      None
    end else begin
      let date = parse_tm date time in
      let source = String.concat " " (source_0::source_n) in
      Some { ip; date; act_model; source }
    end
  | _ ->
    prerr_endline @@ "Error parsing: " ^ l;
    None

let parse logfile =
  let ic = open_in logfile in
  let rec loop acc =
    try
      match parse_line @@ input_line ic with
      | Some e -> loop @@ e :: acc
      | None -> loop acc
    with End_of_file -> acc
  in
  let entries = loop [] in
  close_in ic;
  entries

let analyse_per_day =
  List.fold_left (fun m entry ->
      match DayMap.find_opt entry.date m with
      | None -> DayMap.add entry.date [entry] m
      | Some es -> DayMap.add entry.date (entry::es) m
    )
    DayMap.empty

let print_date date =
  match date.day, date.mon, date.year with
  | Some day, Some mon, Some year ->
      Printf.printf "['%d/%d/%d'" day mon year
  | _ ->
      Printf.printf "unknown"

let print_map =
  DayMap.iter (fun date entries ->
      print_date date;
      Printf.printf ", %d],\n" (List.length entries)
    )

let whois ip =
  let ic = Unix.open_process_in @@ "whois " ^ ip in
  let rec loop () =
    try
      let l = input_line ic in
      if String.length l > 7 && String.lowercase_ascii @@ String.sub l 0 7 = "country" then
        match Str.split (Str.regexp "[ \t]+") l with
        | [_; country] ->
          print_endline @@ "Country: " ^ country;
          country
        | _ ->
          print_endline @@ "Unknown country: " ^ l;
          "<unknown>"
      else
        loop ()
    with End_of_file -> "<unknown>"
  in
  let country = loop () in
  ignore @@ Unix.close_process_in ic;
  country

let print_ip entries =
  let (_, countries) = List.fold_left (fun (countries, count) entry ->
      let (countries, k) = match StringMap.find_opt entry.ip countries with
        | Some country -> (countries, country)
        | None -> let k = whois entry.ip in (StringMap.add entry.ip k countries, k)
      in
      let n = match StringMap.find_opt k count with Some n -> n | None -> 0 in
      (countries, StringMap.add k (n+1) count)
    ) (StringMap.empty, StringMap.empty) entries
  in
  StringMap.iter (fun k n -> Printf.printf "['%s', %d]," k n) countries

let analyse debug_level logfiles =
  let entries =
    List.concat @@ List.fold_left
      (fun acc logfile -> parse logfile :: acc) [] logfiles in
  print_endline "let req_per_day = [
          ['Date', 'Requests'],";
  print_map @@ analyse_per_day entries;
  print_endline "];";
  print_endline "let countries = [";
  print_ip entries;
  print_endline "];"


(* Arguments *)

open Cmdliner

let logfiles =
  let doc = "Set log files to analyse" in
  Arg.(value & pos_all file [] & info [] ~docv:"FILE" ~doc)

let debug_level =
  let doc = "Set the debug message level $(docv) \
             (should range over [0-9])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let () =
  let analyse = Term.(pure analyse $ debug_level $ logfiles) in
  let doc  = "Analyse Cerberus server log." in
  let info = Term.info "Cerberus server analyser" ~doc in
  match Term.eval (analyse, info) with
  | `Error _ -> exit 1;
  | `Ok _
  | `Version
  | `Help -> exit 0
