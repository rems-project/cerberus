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

type intra_label_trace_item_report = { 
  stmt : Pp.doc; 
  within : Pp.doc list 
}
type per_label_trace_report = { 
  label : Pp.doc; 
  trace : intra_label_trace_item_report list;
}
type trace_report = per_label_trace_report list

type state_report = {
    variables : var_entry list;
    requested : resource_entry option;
    unproven : (Pp.doc * Pp.doc) option;
    resources : resource_entry list;
    predicate_hints : predicate_clause_entry list;
    constraints: Pp.doc list;
    trace: trace_report;
  }



let list elements = String.concat "" elements
let enclose tag what = "<"^tag^">" ^ what ^ "</"^tag^">"
let html elements = enclose "html" (list elements)
let head = enclose "head"
let style = enclose "style"
let body elements = enclose "body" (list elements)
let h i title body = list [enclose ("h"^string_of_int i) title; body]
let table_row cols = enclose "tr" (list (List.map (enclose "td") cols))
let table_head_row cols = enclose "tr" (list (List.map (enclose "th") cols))
let table_head cols = enclose "thead" (table_head_row cols)
let table_body rows = enclose "tbody" (list (List.map table_row rows))
let table head rows = enclose "table" (list [table_head head; table_body rows])
let table_without_head rows = enclose "table" (list [table_body rows])
let details summary more = enclose "details" (list [enclose "summary" summary; more])
let oguard o f = match o with None -> "" | Some x -> f x 
let lguard l f = match l with [] -> "" | _ -> f l
let details_with_table summary detail_list = details summary (table_without_head detail_list)

let make_per_stmt_trace {stmt; within} =
  match within with 
  | [] ->
     Pp.plain stmt
  | _ ->
    details_with_table (Pp.plain stmt) 
      (List.map (fun i -> [Pp.plain i]) within)

let make_per_label_trace {label; trace} = 
  match trace with
  | [] -> Pp.plain label
  | _ -> 
    details_with_table (Pp.plain label)
      (List.map (fun i -> [make_per_stmt_trace i]) trace)

let make_trace trace = 
  lguard trace (fun trace ->
    h 1 "Path to error" (
      table_without_head 
        (List.map (fun i -> [make_per_label_trace i]) trace)
    )
  )

let make_requested requested = 
  oguard requested (fun re ->
    h 1 "Requested resource" (
      table ["requested"; "byte span"]
        [[Pp.plain re.res; Pp.plain re.res_span]]
    )
  )

let make_unproven unproven = 
  oguard unproven (fun c ->
    h 1 "Unproven constraint" (
      table ["constraint"; "simplified constraint"]
        [[Pp.plain (fst c); Pp.plain (snd c)]]
    )
  )  

let make_predicate_hints predicate_hints =
  lguard predicate_hints (fun predicate_hints ->
    h 1 "Possibly relevant predicate clauses" (
      table ["condition"; "clause"]
        (List.map (fun pce -> [Pp.plain pce.cond; Pp.plain pce.clause]) predicate_hints)
    )
  )

let make_resources resources = 
  h 1 "Available resources" (
    match resources with
    | [] -> "(no available resources)"
    | _ ->
      table ["resource"; "byte span and match"]
        (List.map (fun re -> [Pp.plain re.res; Pp.plain re.res_span]) resources)
  )

let make_variables variables =
  h 1 "Variables" (
    match variables with
    | [] -> "(none)"
    | _ ->
      table ["variable"; "value"]
        (List.map (fun v -> [Pp.plain v.var; Pp.plain v.value]) variables)
  )

let make_constraints constraints = 
  h 1 "Constraints" (
    match constraints with
    | [] -> "(none)"
    | _ -> 
      table ["constraint"]
        (List.map (fun c -> [Pp.plain c]) constraints)
  )


let make report = 
  html [
    head (style Style.style); 
    body [
      make_trace report.trace;
      make_requested report.requested;
      make_unproven report.unproven;
      make_predicate_hints report.predicate_hints;
      make_resources report.resources;
      make_variables report.variables;
      make_constraints report.constraints;
    ]
  ] 






(*


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


type table = {
    rows : row list;
    column_info : string list
  }

type element =
  | H of int * string
  | P of string
  | UL of element list
  | Details of { summary : string; contents : element }
  | Table of table

type html = {style : string; body : element list}

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

let p text =
  "<p>" ^
    text ^
  "</p>"

let h i text = 
  "<h"^string_of_int i^">" ^
  text ^
  "</h"^string_of_int i^">" 

let ul l = 
  "<ul>" ^
  String.concat "" (List.map (fun i -> "<li>" ^ i ^ "</li>") l) ^ 
  "</ul>"

let details summary contents = 
  "<details>" ^
  "<summary>" ^ summary ^ "</summary>" ^
  contents

let rec element = function
  | H (i,text) -> h i text
  | P text-> p text
  | Details { summary; contents } -> details summary (element contents)
  | Table tablecontent -> table tablecontent



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
  let trace_item_entry = full_row_entry "trace_item" in

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
        make_trace report.trace 
        @
        opt_header report.requested [("requested resource", 2); ("byte span", 1)] @
        List.map resource_entry report.requested 
        @
        opt_header report.unproven [("unproven constraint", 3)] @
        List.map constraint_entry report.unproven 
        @
        opt_header report.predicate_hints [("possibly relevant predicate clauses", 3)] @
        List.map predicate_info_entry report.predicate_hints 
        @
        opt_header report.resources [("available resources", 2); ("byte span and match", 1)] @
        List.map resource_entry report.resources 
        @
        header [("expression",1); ("value",2)] ::
        List.map variable_entry report.variables 
        @
        header [("constraints",3)] ::
        List.map constraint_entry report.constraints 
    )}
  in

  let body = [

      Table table
    ]
  in

  { style = Style.style; body }


let print_report report = html (to_html report)

*)
