type state_entry = { 
    loc_e : Pp.doc option;
    loc_v : Pp.doc option;
    state : Pp.doc option;
  }


type var_entry = {
    var : Pp.doc;
    value : Pp.doc;
  }


type state_report = {
    memory : state_entry list;
    variables : var_entry list;
    constraints: Pp.doc list;
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
type head = {css_file : string}
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

let head {css_file} = 
  "<head>" ^
    "<link href=\""^css_file^"\" rel=\"stylesheet\">" ^
  "</head>"


let html {head = h; body = b} =
  "<html>" ^ 
    head h ^
    body b ^
  "</html>"


let to_html report = 

  let sdoc doc = Pp.plain doc in

  let o_sdoc o_doc = 
    match o_doc with
    | Some doc -> sdoc doc
    | None -> ""
  in

  let state_entry {loc_e; loc_v; state} =
    { header = false;
      classes = ["memory_entry"];
      columns = [
          { classes = ["loc_e"]; content = o_sdoc loc_e; colspan = 1};
          { classes = ["loc_v"]; content = o_sdoc loc_v; colspan = 1};
          { classes = ["state"]; content = o_sdoc state; colspan = 1};
        ]
    }
  in

  let variable_entry {var; value} =
    { header = false;
      classes = ["variable_entry"];
      columns = [ 
          { classes = ["expression"]; content = sdoc var; colspan = 1 };
          { classes = ["value"]; content = sdoc value; colspan = 2 };
        ]
    }
  in

  let constraint_entry constr =
    { header = false;
      classes = ["constraint_entry"];
      columns = [ 
          { classes = ["contraint"]; content = sdoc constr; colspan = 3 };
        ]
    }
  in


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

  let table = 
    { column_info = ["column1"; "column2"; "column3"];
      rows = (
        header [("pointer",1); ("addr",1); ("state",1)] ::
        List.map state_entry report.memory @
        header [("expression",1); ("value",2)] ::
        List.map variable_entry report.variables @
        header [("constraints",3)] ::
        List.map constraint_entry report.constraints
    )}
  in

  { head = {css_file = "style.css"};
    body = {elements = [Table table]} }
  

let print_report report = html (to_html report)
