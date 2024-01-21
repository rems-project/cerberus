type state_entry = {
    loc_e : Pp.doc option;
    loc_v : Pp.doc option;
    state : Pp.doc option;
  }


type var_entry = {
    var : Pp.doc;
    value : Pp.doc;
  }


type predicate_clause_entry = {
    cond : Pp.doc;
    clause : Pp.doc;
  }


type resource_entry = {
    res : Pp.doc;
    res_span : Pp.doc;
  }



type state_report = {
    location_trace: Pp.doc list;
    (* memory : state_entry list; *)
    variables : var_entry list;
    requested : resource_entry list;
    unproven : Pp.doc list;
    resources : resource_entry list;
    predicate_hints : predicate_clause_entry list;
    constraints: Pp.doc list;
    trace: Pp.doc list;
  }




type column = {
    classes : string list;
    content : string;
    colspan : int
  }
type row = {
    header : bool;
    classes : string list;
    columns : column list
  }

type p = {text : string}

type table = {
    rows : row list;
    column_info : string list
  }

type element =
  | P of p
  | Table of table

type body = {elements : element list}
type head = {style : string}
type html = {head : head; body : body}

let classes = function
  | [] -> ""
  | cs -> "class=\""^String.concat " " cs^"\""

let column header {classes = cs; content; colspan} =
  let tag = if header then "th" else "td" in
  "<"^tag^" "^classes cs^" colspan=\"" ^ string_of_int colspan ^ "\">" ^
    content ^
  "</"^tag^">"

let row {header; classes = cs; columns} =
  let content =
    "<tr "^classes cs^">" ^
      String.concat "" (List.map (column header) columns) ^
    "</tr>"
  in
  if header then "<thead>"^content^"</thead>" else content

let column_info column_class =
  "<col class = \""^column_class^"\">"

let table {rows; column_info = ci} =
  "<table>" ^
    String.concat "" (List.map row rows) ^
  "</table>"

let p {text} =
  "<p>" ^
    text ^
  "</p>"

let element = function
  | P pcontent -> p pcontent
  | Table tablecontent -> table tablecontent

let body {elements} =
  "<body>" ^
    String.concat "" (List.map element elements) ^
  "</body>"

let head {style} =
  "<head>" ^
    "<style>" ^
      style ^
    "</style>" ^
  "</head>"


let html {head = h; body = b} =
  "<html>" ^
    head h ^
    body b ^
  "</html>"


let to_html report =

  let sdoc doc = Pp.plain doc in

  (* let o_sdoc o_doc =  *)
  (*   match o_doc with *)
  (*   | Some doc -> sdoc doc *)
  (*   | None -> "" *)
  (* in *)

  (* let state_entry {loc_e; loc_v; state} = *)
  (*   { header = false; *)
  (*     classes = ["memory_entry"]; *)
  (*     columns = [ *)
  (*         { classes = ["loc_e"]; content = o_sdoc loc_e; colspan = 1}; *)
  (*         { classes = ["loc_v"]; content = o_sdoc loc_v; colspan = 1}; *)
  (*         { classes = ["state"]; content = o_sdoc state; colspan = 1}; *)
  (*       ] *)
  (*   } *)
  (* in *)

  let variable_entry {var; value} =
    { header = false;
      classes = ["variable_entry"];
      columns = [
          { classes = ["expression"]; content = sdoc var; colspan = 1 };
          { classes = ["value"]; content = sdoc value; colspan = 2 };
        ]
    }
  in

  let predicate_info_entry {cond; clause} =
    { header = false;
      classes = ["predicate_info_entry"];
      columns = [
          { classes = ["condition"]; content = sdoc cond; colspan = 1 };
          { classes = ["clause"]; content = sdoc clause; colspan = 2 };
        ]
    }
  in

  let resource_entry {res; res_span} =
    { header = false;
      classes = ["resource entry"];
      columns = [
          { classes = ["res"]; content = sdoc res; colspan = 2};
          { classes = ["span"]; content = sdoc res_span; colspan = 1};
        ]
    }
  in


  let full_row_entry nm doc =
    { header = false;
      classes = [nm ^ "_entry"];
      columns = [
          { classes = [nm]; content = sdoc doc; colspan = 3 };
        ]
    }
  in

  let constraint_entry = full_row_entry "constraint" in
  let location_entry = full_row_entry "location" in

  let header hds =
    let columns =
      List.map (fun (name, colspan) ->
          {classes = [];
           content = name;
           colspan = colspan}
        ) hds
    in
    { header = true;
      columns;
      classes = ["table_header"]}
  in

  let opt_header xs hds = if List.length xs = 0
    then [] else [header hds] in

  let table =
    { column_info = ["column1"; "column2"; "column3"];
      rows = (
        (* header [("pointer",1); ("addr",1); ("state",1)] :: *)
        (* List.map state_entry report.memory @ *)
        opt_header report.location_trace [("path to error",3)] @
          List.map location_entry report.trace @
        opt_header report.requested [("requested resource", 2); ("byte span", 1)] @
          List.map resource_entry report.requested @
        opt_header report.unproven [("unproven constraint", 3)] @
          List.map constraint_entry report.unproven @
        opt_header report.predicate_hints [("possibly relevant predicate clauses", 3)] @
          List.map predicate_info_entry report.predicate_hints @
        opt_header report.resources [("available resources", 2); ("byte span and match", 1)] @
          List.map resource_entry report.resources @
        header [("expression",1); ("value",2)] ::
          List.map variable_entry report.variables @
        header [("constraints",3)] ::
          List.map constraint_entry report.constraints 
    )}
  in

  { head = {style = Style.style};
    body = {elements = [Table table]} }


let print_report report = html (to_html report)
