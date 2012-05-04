open Core_run




module Print = struct
  module P = Pprint

  open Core
  open P.Operators
  
  
  let pp_symbol (n,str_opt) =
    match str_opt with
      | Some str -> !^ str
      | None     -> !^ ("\alpha_" ^ string_of_int n)
  let pp_number   n = !^ n
  
  
  let optional pp = function
    | Some x -> pp x
    | None   -> P.empty
  
  
  let pp_binop = function
    | OpAdd -> P.plus
    | OpSub -> P.minus
    | OpMul -> P.star
    | OpDiv -> P.slash
    | OpMod -> !^ "\%"
    | OpEq  -> P.equals
    | OpLt  -> P.langle
    | OpAnd -> !^ "\\wedge"
    | OpOr  -> !^ "\\vee"
  
  let rec pp_expr e =
    match e with
      | COMMENT (_, e)   -> pp_expr e
      | DEBUG str        -> !^ ""
      | Kconst n         -> pp_number (string_of_int n)
      | Ksym a           -> pp_symbol a
      | Kop (op, e1, e2) -> P.parens (pp_expr e1) ^^^ pp_binop op ^^^ P.parens (pp_expr e2)
      | Ktrue            -> !^ "\\text{true}"
      | Kfalse           -> !^ "\\text{false}"
      | Knot e           -> !^ "\\text{not}" ^^ P.parens (pp_expr e)
      | Kctype ty        -> Ail.Print.pp_type ty
      | Klet ([], e1, e2)   -> !^ "BUG: for now LET must have at least one symbol."
      | Klet ([a], e1, e2)  -> !^ "\\text{let}" ^^^ pp_symbol a ^^^ P.equals ^^ 
                           P.nest 2 (P.break1 ^^ pp_expr e1 ^^^ !^ "\\text{in}")
                           ^^ P.break1 ^^ pp_expr e2
      | Klet (_as, e1, e2)  -> !^ "\\text{let}" ^^^ (P.parens (P.sepmap P.comma pp_symbol _as)) ^^^ P.equals ^^^
                           P.nest 2 (P.break1 ^^ pp_expr e1 ^^^ !^ "\\text{in}")
                           ^^ P.break1 ^^ pp_expr e2
      | Kif (b, e1, e2)     -> !^ "\\text{if}" ^^^ pp_expr b ^^^ !^ "\\text{then}" ^^
                           P.nest 2 (P.break1 ^^ pp_expr e1) ^^ P.break1 ^^
                           !^ "\\text{else}" ^^ P.nest 2 (P.break1 ^^ pp_expr e2) ^^ P.break1
      | Kcall (a, es)      -> !^ "CALL" (* pp_symbol a ^^ P.parens (P.sepmap (P.comma ^^ P.space) pp_expr es) *)
(*      | Kundef          -> pp_keyword "undef" *)
(*      | Kerror          -> pp_keyword "error" *)
      | Kskip           -> !^ "\\textbf{\\textsf{skip}}"
(*      | Kseq ([], e1, e2)   -> pp_expr e1 ^^ P.semi ^^ P.break1 ^^ pp_expr e2
      | Kseq ([a], e1, e2)  -> pp_symbol a ^^^ !^ "<-" ^^
                           P.nest 2 (P.break1 ^^ pp_expr e1 ^^ P.semi)
                           ^^ P.break1 ^^ pp_expr e2
      | Kseq (_as, e1, e2)  -> (P.parens (P.sepmap P.comma pp_symbol _as)) ^^^ !^ "<-" ^^
                           P.nest 2 (P.break1 ^^ pp_expr e1 ^^ P.semi)
                           ^^ P.break1 ^^ pp_expr e2 *)
(*      | Kunseq []       -> !^ "BUG: UNSEQ must have at least two arguments (seen 0)"
      | Kunseq [_]      -> !^ "BUG: UNSEQ must have at least two arguments (seen 1)"
      | Kunseq es       ->  P.sepmap (pp_control "||") (fun x -> P.parens (pp_expr x)) es *)
(*      | Kindet e        -> P.brackets (pp_expr e) *)
(*      | Katom e         -> P.braces (pp_expr e) *)
(*      | Kcreate ty      -> pp_keyword "create" ^^ P.braces (Ail.Print.pp_type ty) *)
(*      | Kalloc e        -> pp_keyword "alloc" ^^^ pp_expr e *)
(*      | Kkill a         -> pp_keyword "kill" ^^^ pp_symbol a *)
(*      | Kstore (ty, e1, e2) -> pp_keyword "store" ^^ P.braces (Ail.Print.pp_type ty) ^^^ pp_expr e1 ^^^ pp_expr e2 *)
(*      | Kload (ty, e)      -> pp_keyword "load" ^^ P.braces (Ail.Print.pp_type ty) ^^^ pp_expr e *)
(*      | Ksame (a1, a2)     -> pp_keyword "same" ^^^ pp_symbol a1 ^^^ pp_symbol a2 *)
      | Kmax ty         -> !^ "\\text{max}" ^^ P.braces (Ail.Print.pp_type ty)
      | Kmin ty         -> !^ "\\text{min}" ^^ P.braces (Ail.Print.pp_type ty)
      | Ksizeof ty      -> !^ "\\text{sizeof}" ^^ P.braces (Ail.Print.pp_type ty)
      | Kalignof ty     -> !^ "\\text{alignof}" ^^ P.braces (Ail.Print.pp_type ty)
      | Koffsetof ty    -> !^ "\\text{offset}" ^^ P.braces (Ail.Print.pp_type ty)
      | Kshift (a, e)      -> !^ "\\text{shift}" ^^^ pp_symbol a ^^^ pp_expr e
      | Kconv (ty1, ty2, a) -> !^ "\\text{conv}" ^^ P.braces (Ail.Print.pp_type ty1 ^^ !^"\\" ^^ Ail.Print.pp_type ty2) ^^^ pp_symbol a
  
end


(* ------------------------------------------------ *)


(* TODO *)
let string_of_action = function
  | Aundef              -> "\\textbf{\\textsf{undef}}"
  | Aerror              -> "\\textbf{\\textsf{error}}"
  | Acreate ty          ->
      let p_ty = Document.to_plain_string (Ail.Print.pp_type ty) in
      "\\textbf{\\textsf{create}}_{\\text{" ^ p_ty ^ "}}"
  | Aalloc e            ->
      let p_e  = Document.to_plain_string (Print.pp_expr e) in
      "\\textbf{\\textsf{alloc}} \\ " ^ p_e
  | Akill a             ->
      let p_a  = Document.to_plain_string (Print.pp_symbol a) in
      "\\textbf{\\textsf{kill}} \\ " ^ p_a
  | Astore (ty, e1, e2) ->
      let p_ty = Document.to_plain_string (Ail.Print.pp_type ty)  in
      let p_e1 = Document.to_plain_string (Print.pp_expr e1) in
      let p_e2 = Document.to_plain_string (Print.pp_expr e2) in
      "\\textbf{\\textsf{store}}_{\\text{" ^ p_ty ^ "}} \\ " ^ p_e1 ^ " \\ " ^ p_e2
  | Aload (ty, e)       ->
      let p_ty = Document.to_plain_string (Ail.Print.pp_type ty) in
      let p_e  = Document.to_plain_string (Print.pp_expr e) in
      "\\textbf{\\textsf{load}}_{\\text{" ^ p_ty ^ "}} \\ " ^ p_e
  | Asame (a1, a2)      -> "same a1 a2"
  | Acall (f, args)     -> "f (arg1, ..., argn)"

let is_call = function
  | Acall _ -> true
  | _       -> false


(* generate a graphviz representation of a given graph.
   REMARK: doesn't take a graph of type 'a g as input. *)
let toDot n g =
  (* print a vertex (salmond if it is a function call, white otherwise) *)
  let printV vs =
    List.fold_left
      (fun s (id, v) ->
        let v_str = string_of_int id ^ ": " ^ string_of_action v in
        s ^ "\"" ^ v_str ^ (string_of_int n) ^ "\"" ^
            "[label=\"" ^ v_str ^ "\"" ^
            (if is_call v then "color=salmon" else "") ^ "];")
      "" vs in
  let style = function
    | Syntax       -> ""
    | Syntax_trans -> "[style=dashed]"
    | Indet        -> "[color=red]"
    | Indet_trans  -> "[color=salmon,style=dashed]" in
  (* print a edge with the colour corresponding to its "kind" *)
  let printE es =
    List.fold_left
      (fun s (x,y,k) -> s ^ "\"" ^ (string_of_int x ^ ": " ^ string_of_action (Pmap.find x g.Core_run.nodes)) ^ (string_of_int n) ^ "\"" ^
                            " -> \"" ^ (string_of_int y ^ ": " ^ string_of_action (Pmap.find y g.Core_run.nodes)) ^ (string_of_int n) ^ "\"" ^
                            (style k) ^ ";")
      "" es in
  (* paint the background of the order yellow if there is a cycle *)
  let boxColour = "lightgrey" (* if List.exists (fun v -> isAccessible es v v) vs then "yellow" else "lightgrey" *) in
  
  "subgraph cluster_"  ^ (string_of_int n) ^ "{style=filled;color=" ^ boxColour ^
  ";label=\"order nb " ^ (string_of_int n) ^ "\";" ^ printV (Pmap.bindings g.Core_run.nodes) ^ printE (simpl g.Core_run.edges) ^ "}"
