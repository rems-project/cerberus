open Bmc_utils
open Printf
open Util


(* ======== CAT SPECIFICATION ============ *)
module CatFile = struct
  type base_set =
    | BaseSet_U         (* all events *)
    | BaseSet_R         (* read events *)
    | BaseSet_W         (* write events *)
    | BaseSet_M         (* reads and writes *)
    | BaseSet_A         (* atomic events *)
    | BaseSet_I         (* initial events *)
    | BaseSet_F
    | BaseSet_NA
    | BaseSet_RLX
    | BaseSet_REL
    | BaseSet_ACQ
    | BaseSet_ACQ_REL
    | BaseSet_SC
    (* === Linux stuff ==== *)
    | BaseSet_Wmb
    | BaseSet_Rmb
    | BaseSet_Mb
    | BaseSet_RbDep
    | BaseSet_RcuLock
    | BaseSet_RcuUnlock
    | BaseSet_SyncRcu
    | BaseSet_LinuxAcquire
    | BaseSet_LinuxRelease

  type base_identifier =
    | BaseId_rf
    | BaseId_rf_inv
    | BaseId_co
    | BaseId_id
    | BaseId_asw
    | BaseId_po
    | BaseId_loc
    | BaseId_int (* internal: same thread *)
    | BaseId_ext (* external: same thread *)
    | BaseId_rfi
    | BaseId_rfe
    | BaseId_po_loc
    | BaseId_atomicloc    (* TODO: should be BaseSet *)
    | BaseId_nonatomicloc (* TODO: should be BaseSet *)
    | BaseId_addr_dep
    | BaseId_data_dep
    | BaseId_ctrl_dep

  type id =
    | Id of string (* TODO: only relations allowed currently *)
    | BaseId of base_identifier

  type set =
    | Set_base of base_set
    | Set_union of set * set
    | Set_intersection of set * set
    | Set_difference of set * set
    | Set_not of set

  type simple_expr =
    | Eid of id
    | Einverse of simple_expr
    | Eunion of simple_expr * simple_expr (* expr * expr *)
    | Eintersection of simple_expr * simple_expr
    | Esequence of simple_expr * simple_expr (* domain analysis *)
    | Edifference of simple_expr * simple_expr
    | Eset of set (*identity relation on set *)
    | Eprod of set * set (* cartesian product *)
    | Eoptional of simple_expr (* one or more, e? *)

  type expr =
    | Esimple of simple_expr
    | Eplus of simple_expr (* transitive closure *)
    | Estar of simple_expr (* reflexive, transitive closure *)

  type constraint_expr =
    | Irreflexive of simple_expr
    | Acyclic of simple_expr
    | Empty of simple_expr

  let mk_set_U = Set_base BaseSet_U
  let mk_set_R = Set_base BaseSet_R
  let mk_set_W = Set_base BaseSet_W
  let mk_set_M = Set_base BaseSet_M
  let mk_set_A = Set_base BaseSet_A
  let mk_set_I = Set_base BaseSet_I
  let mk_set_F = Set_base BaseSet_F
  let mk_set_NA = Set_base BaseSet_NA
  let mk_set_REL = Set_base BaseSet_REL
  let mk_set_RLX = Set_base BaseSet_RLX
  let mk_set_ACQ = Set_base BaseSet_ACQ
  let mk_set_ACQ_REL = Set_base BaseSet_ACQ_REL
  let mk_set_SC = Set_base BaseSet_SC
  let mk_set_Wmb = Set_base BaseSet_Wmb
  let mk_set_Rmb = Set_base BaseSet_Rmb
  let mk_set_Mb = Set_base BaseSet_Mb
  let mk_set_RbDep = Set_base BaseSet_RbDep
  let mk_set_RcuLock = Set_base BaseSet_RcuLock
  let mk_set_RcuUnlock = Set_base BaseSet_RcuUnlock
  let mk_set_SyncRcu = Set_base BaseSet_SyncRcu
  let mk_set_LinuxAcquire = Set_base BaseSet_LinuxAcquire
  let mk_set_LinuxRelease = Set_base BaseSet_LinuxRelease

  let mk_set_union (x: set) (y: set) =
    Set_union (x,y)
  let mk_set_diff (x: set) (y:set) =
    Set_difference (x,y)
  let mk_set_intersection (x: set) (y:set) =
    Set_intersection (x,y)
  let mk_set_not (x: set) =
    Set_not x


  let mk_po = Eid (BaseId BaseId_po)
  let mk_asw = Eid (BaseId BaseId_asw)
  let mk_loc = Eid (BaseId BaseId_loc)
  let mk_identity = Eid (BaseId BaseId_id)
  let mk_internal = Eid (BaseId BaseId_int)
  let mk_external = Eid (BaseId BaseId_ext)
  let mk_rfi = Eid (BaseId BaseId_rfi)
  let mk_rfe = Eid (BaseId BaseId_rfe)
  let mk_po_loc = Eid (BaseId BaseId_po_loc)
  let mk_atomicloc = Eid (BaseId BaseId_atomicloc)
  let mk_nonatomicloc = Eid (BaseId BaseId_nonatomicloc)
  let mk_addr_dep = Eid (BaseId BaseId_addr_dep)
  let mk_ctrl_dep = Eid (BaseId BaseId_ctrl_dep)
  let mk_data_dep = Eid (BaseId BaseId_data_dep)

  let mk_prod (x: set) (y: set) =
    Eprod(x,y)

  let mk_rf = (Eid (BaseId BaseId_rf))
  let mk_rf_inv = (Eid (BaseId BaseId_rf_inv))
  let mk_co = Eid (BaseId BaseId_co)
  let mk_id (s: string) =
    Eid (Id s)


  let mk_inverse (e : simple_expr) =
    Einverse e

  let mk_set_rel (s: set) =
    Eset s

  let mk_sequence (e1:simple_expr) (e2:simple_expr) =
    Esequence (e1,e2)

  let mk_plus (e: simple_expr) =
    Eplus e

  let mk_star (e: simple_expr) =
    Estar e

  let mk_optional (e: simple_expr) =
    Eoptional e

  let mk_diff (e1: simple_expr) (e2:simple_expr) =
    Edifference (e1,e2)

  let mk_union (e1,e2) = (* TODO: a * b -> c or a->b -> c?*)
    Eunion (e1,e2)

  let mk_intersection (e1: simple_expr) (e2: simple_expr) =
    Eintersection (e1,e2)

  let mk_simple (es: simple_expr) =
    Esimple es

  let mk_irreflexive (e: simple_expr) =
    Irreflexive e

  let mk_acyclic (e: simple_expr) =
    Acyclic e

  let mk_empty (e: simple_expr) =
    Empty e

  (* ====== pprinters ======== *)
  let wrap s =
    "(" ^ s ^ ")"

  let pprint_base_id = function
    | BaseId_rf -> "rf"
    | BaseId_rf_inv -> "rf^-1"
    | BaseId_co -> "co"
    | BaseId_id  -> "id"
    | BaseId_asw -> "asw"
    | BaseId_po  -> "po"
    | BaseId_loc -> "loc"
    | BaseId_int -> "int"
    | BaseId_ext -> "ext"
    | BaseId_rfi -> "rfi"
    | BaseId_rfe -> "rfe"
    | BaseId_po_loc -> "po-loc"
    | BaseId_atomicloc    -> "atomicloc"
    | BaseId_nonatomicloc -> "nonatomicloc"
    | BaseId_addr_dep -> "addr"
    | BaseId_ctrl_dep -> "ctrl"
    | BaseId_data_dep -> "data"

  let pprint_id = function
    | Id s -> "|" ^ s ^ "|"
    | BaseId id -> pprint_base_id id

  let pprint_base_set = function
    | BaseSet_U       -> "U"
    | BaseSet_R       -> "R"
    | BaseSet_W       -> "W"
    | BaseSet_M       -> "M"
    | BaseSet_A       -> "A"
    | BaseSet_I       -> "I"
    | BaseSet_F       -> "F"
    | BaseSet_NA      -> "NA"
    | BaseSet_RLX     -> "RLX"
    | BaseSet_REL     -> "REL"
    | BaseSet_ACQ     -> "ACQ"
    | BaseSet_ACQ_REL -> "ACQ_REL"
    | BaseSet_SC      -> "SC"
    | BaseSet_Rmb     -> "Rmb"
    | BaseSet_Wmb     -> "Wmb"
    | BaseSet_Mb      -> "Mb"
    | BaseSet_RbDep   -> "RbDep"
    | BaseSet_RcuLock -> "RcuLock"
    | BaseSet_RcuUnlock -> "RcuUnlock"
    | BaseSet_SyncRcu   -> "Sync-rcu"
    | BaseSet_LinuxAcquire -> "LinuxAcquire"
    | BaseSet_LinuxRelease -> "LinuxRelease"

  let rec pprint_set = function
    | Set_base base_set ->
        pprint_base_set base_set
    | Set_union (s1,s2) ->
        (wrap (pprint_set s1)) ^ " | " ^ (wrap (pprint_set s2))
    | Set_intersection (s1,s2) ->
        (wrap (pprint_set s1)) ^ " & " ^ (wrap (pprint_set s2))
    | Set_difference (s1,s2) ->
        (wrap (pprint_set s1)) ^ " \\ " ^ (wrap (pprint_set s2))
    | Set_not s ->
        "~" ^ (wrap (pprint_set s))

  let rec pprint_simple_expr = function
    | Eid id ->
        pprint_id id
    | Einverse se ->
        wrap (pprint_simple_expr se) ^ "^-1"
    | Eunion (se1, se2) ->
        wrap(pprint_simple_expr se1) ^ " | " ^ (wrap (pprint_simple_expr se2))
    | Eintersection (se1, se2) ->
        wrap(pprint_simple_expr se1) ^ " & " ^ (wrap (pprint_simple_expr se2))
    | Esequence (se1, se2) ->
        (wrap (pprint_simple_expr se1))
        ^ " ; "
        ^ (wrap (pprint_simple_expr se2))
    | Edifference (se1, se2) ->
        (wrap (pprint_simple_expr se1))
        ^ " \\ "
        ^ (wrap (pprint_simple_expr se2))
    | Eset s ->
        "[" ^ (wrap (pprint_set s)) ^ "]"
    | Eprod (s1,s2) ->
        (wrap (pprint_set s1)) ^ " * " ^ (wrap (pprint_set s2))
    | Eoptional se ->
        (wrap (pprint_simple_expr se)) ^ "?"

  let pprint_expr = function
    | Esimple se ->
        pprint_simple_expr se
    | Eplus se ->
        wrap (pprint_simple_expr se) ^ "+"
    | Estar se ->
        wrap (pprint_simple_expr se) ^ "*"
end

module type CatModel = sig
  (*val identifiers : string list*)
  val bindings   : (string
                    * (CatFile.set * CatFile.set)
                    * CatFile.expr) list
  val constraints : (string option * CatFile.constraint_expr) list

  val undefs_unless_empty :  string list (* TODO: support generic UBs *)

  val to_output : string list (* TODO: should be id? *)
end

module Partial_RC11Model : CatModel = struct
  open CatFile
  let bindings =
    [ ("sb", (mk_set_U, mk_set_U),
             mk_simple (mk_union
              (mk_po,mk_prod mk_set_I (mk_set_diff mk_set_M mk_set_I))))
    ; ("rf_star", (mk_set_W, mk_set_U),
             mk_star mk_rf)
    (*
    ; ("rs", (mk_set_W, mk_set_U),
             mk_sequence (mk_optional (mk_intersection (mk_id "sb") mk_loc))
             (mk_sequence (mk_id "rs")
             (mk_sequence mk_rf
             (mk_sequence () ()))))
    *)
    ; ("sw", (mk_set_U, mk_set_U),
             mk_simple mk_asw)
    ; ("hb", (mk_set_U, mk_set_U),
             mk_plus (mk_union (mk_id "sb", mk_id "sw"))) (* TODO: sw, asw *)
    ; ("mo", (mk_set_W, mk_set_W),
             mk_simple mk_co)
    ; ("fr", (mk_set_R, mk_set_W),
             mk_simple
               (mk_diff (mk_sequence mk_rf_inv (mk_id "mo")) mk_identity))
    ; ("eco", (mk_set_U, mk_set_U),
              mk_simple (
                mk_union (mk_rf,
                mk_union (mk_id "mo",
                mk_union (mk_id "fr",
                mk_union (mk_sequence (mk_id "mo") mk_rf,
                          mk_sequence (mk_id "fr") mk_rf))))))
    ]

  let constraints =
    [ (Some "coh", Irreflexive ((mk_sequence (mk_id "hb") (mk_id "eco"))))
    ; (Some "atomic1", Irreflexive (mk_id "eco"))
    ; (Some "atomic2", Irreflexive (mk_sequence (mk_id "fr") (mk_id "mo")))
    ; (Some "sb|rf", Acyclic ((mk_union (mk_id "sb", mk_rf))))
    ]

  let undefs_unless_empty = []

  let to_output = ["sw"]
end

module CatParser = struct
  open Angstrom
  open CatFile

  type instruction =
    | Binding of string * CatFile.expr
    | Constraint of string option * CatFile.constraint_expr
    | Undefined_unless_empty of string (* TODO: support Undefined_unless acyclic/irreflexive *)
    | Output of string
    | Skip of string

  let pprint_constraint (s_opt: string option) (constr : CatFile.constraint_expr) =
    let name =
        (if is_some s_opt then " as " ^ (Option.get s_opt) else "") in
    match constr with
    | Irreflexive se ->
        sprintf "irreflexive (%s)%s"
          (CatFile.pprint_simple_expr se) name
    | Acyclic se ->
        sprintf "acyclic (%s)%s"
          (CatFile.pprint_simple_expr se) name
    | Empty se ->
        sprintf "empty (%s)%s"
          (CatFile.pprint_simple_expr se) name

  let pprint_instruction = function
    | Binding (s, expr) ->
        sprintf "let %s = %s" s (CatFile.pprint_expr expr)
    | Constraint (s_opt, constr) ->
        pprint_constraint s_opt constr
    | Undefined_unless_empty s ->
        sprintf "undefined_unless empty %s" (s)
    | Output s ->
        sprintf "output %s" s
    | Skip s ->
        sprintf "skip: %s" s

  let is_space =
    function | ' ' | '\t' -> true | _ -> false

  (* TODO: rename *)
  let is_lower =
    function | 'a' .. 'z' |'0'..'9' | '_' | '-' -> true | _ -> false

  let spaces = take_while is_space
  let lowers = take_while1 is_lower

  let token p =
    p <* spaces

  let parens p = token (char '(') *> p <* token (char ')')

  let id =
    token lowers >>= fun s ->
    let ret =
           if s = "id"           then mk_identity
      else if s = "asw"          then mk_asw
      else if s = "po"           then mk_po
      else if s = "loc"          then mk_loc
      else if s = "rf"           then mk_rf
      else if s = "rf_inv"       then mk_rf_inv
      else if s = "co"           then mk_co
      else if s = "int"          then mk_internal
      else if s = "ext"          then mk_external
      else if s = "rfi"          then mk_rfi
      else if s = "rfe"          then mk_rfe
      else if s = "po-loc"       then mk_po_loc
      else if s = "atomicloc"    then mk_atomicloc
      else if s = "nonatomicloc" then mk_nonatomicloc
      else if s = "addr"         then mk_addr_dep
      else if s = "ctrl"         then mk_ctrl_dep
      else if s = "data"         then mk_data_dep
      else mk_id s
    in return ret

  let base_set : 'a Angstrom.t =
    choice[token (string "NA")      *> return mk_set_NA
          ;token (string "REL")     *> return mk_set_REL
          ;token (string "RLX")     *> return mk_set_RLX
          ;token (string "ACQ_REL") *> return mk_set_ACQ_REL
          ;token (string "ACQ")     *> return mk_set_ACQ
          ;token (string "LinuxAcquire") *> return mk_set_LinuxAcquire
          ;token (string "LinuxRelease") *> return mk_set_LinuxRelease
          ;token (string "Wmb")     *> return mk_set_Wmb
          ;token (string "Rmb")     *> return mk_set_Rmb
          ;token (string "Mb")      *> return mk_set_Mb
          ;token (string "RbDep")   *> return mk_set_RbDep
          ;token (string "RcuLock")   *> return mk_set_RcuLock
          ;token (string "RcuUnlock") *> return mk_set_RcuUnlock
          ;token (string "Sync-rcu")   *> return mk_set_SyncRcu
          ;token (string "SC")      *> return mk_set_SC
          ;token (string "U")       *> return mk_set_U
          ;token (string "R")       *> return mk_set_R
          ;token (string "W")       *> return mk_set_W
          ;token (string "M")       *> return mk_set_M
          ;token (string "A")       *> return mk_set_A
          ;token (string "I")       *> return mk_set_I
          ;token (string "F")       *> return mk_set_F
          ]

  let chainl1 e op =
    let rec go acc =
      (lift2 (fun f x -> f acc x) op e >>= go) <|> return acc in
    e >>= fun init -> go init

  let rec chainr1 e op =
    e  >>= fun x ->
    (op           >>= fun f ->
     chainr1 e op >>= fun y ->
     return (f x y))
    <|> return x

  let set =
    fix (fun set ->
      let base = (token base_set) in
      let negation term =
        token (char '~') *> term >>| mk_set_not in
      let intersect_op =
        token (char '&') *> return mk_set_intersection in
      let union_op =
        token (char '|') *> return mk_set_union in
      let diff_op =
        token (char '\\') *> return mk_set_diff in

      (* TODO: define function to handle operator precedence *)
      let term = parens set <|> base in
      let prefix = negation term <|> term in
      let prec1 = chainr1 prefix intersect_op in
      let prec2 = chainl1 prec1 diff_op in
      chainr1 prec2 union_op
    )

  let simple_expr =
    fix (fun se ->
      let eid = token id in
      (*let eset () = ((token set) >>= fun e -> return (Eset e)) in *)
      let eprod =
        token set >>= fun s1 ->
        token (char '*') *>
        token set >>= fun s2 ->
        return (mk_prod s1 s2) in
      let eset =
        token (char '[') *> token set <* token (char ']') >>| mk_set_rel in

      let postfix_invert e = e <* token (string "^-1") >>| mk_inverse in
      let postfix_option e = e <* token (string "?")   >>| mk_optional in

      let intersect_op = token (char '&')  *> return mk_intersection in
      let diff_op      = token (char '\\') *> return mk_diff in
      let sequence_op  = token (char ';')  *> return mk_sequence in
      let union_op =  token (char '|') *> return (fun x y -> mk_union (x,y)) in

      (* TODO: fix sequencing of precedence *)
      let term = parens se <|> eprod <|> eset <|> eid in
      let postfixed_term =
        postfix_invert term <|> postfix_option term <|> term in
      let prec1 = chainr1 postfixed_term intersect_op in
      let prec2 = chainr1 prec1 diff_op in
      let prec3 = chainr1 prec2 sequence_op in
      chainr1 prec3 union_op
    )

  let expr =
    simple_expr     >>= fun se ->
    choice [token (char '*') *> return (mk_star se)
           ;token (char '+') *> return (mk_plus se)
           ;return (mk_simple se)]

  let binding =
    token (string "let") *>
    token lowers         >>= fun id ->
    token (char '=')     *>
    token expr           >>= fun e ->
    end_of_input         *>
    return (Binding (id, e))

  let check =
    choice[token (string "acyclic") *> return mk_acyclic
          ;token (string "irreflexive") *> return mk_irreflexive
          ;token (string "empty") *> return mk_empty
          ]

  let constraint_expr =
    token check >>= fun constr_fn ->
    token simple_expr >>= fun e ->
    ((token (string "as") *> token lowers >>= fun s -> return (Some s))
    <|> return None) >>= fun s_opt ->
    return (Constraint(s_opt, constr_fn e))

  let undefined_expr =
    token (string "undefined_unless") *>
    token (string "empty") *>
    (*token check >>= fun constr_fn ->*)
    token lowers >>= fun e ->
    (*token simple_expr >>= fun e ->*)
    ((token (string "as") *> token lowers >>= fun s -> return (Some s))
    <|> return None) >>= fun s_opt ->
    return (Undefined_unless_empty e)

  let output =
    token (string "output") *>
    token lowers >>= fun s ->
    return (Output s)

  let empty_string =
    spaces >>= fun s ->
    return (Skip s)

  let comment =
    token (string "//") *>
    take_while (fun _ -> true) >>= fun s ->
    return (Skip ("//" ^ s))

  let instruction =
    choice [constraint_expr
           ;undefined_expr
           ;binding
           ;output
           ;comment
           ;empty_string
           ]
    <* end_of_input

  let get_domain_range_id (id: CatFile.base_identifier) : set * set =
    match id with
    | BaseId_rf     -> (mk_set_W, mk_set_R)
    | BaseId_rf_inv -> (mk_set_R, mk_set_W)
    | BaseId_co     -> (mk_set_W, mk_set_W)
    | BaseId_id     -> (mk_set_U, mk_set_U)
    | BaseId_asw    -> (mk_set_U, mk_set_U)
    | BaseId_po     -> (mk_set_U, mk_set_U)
    | BaseId_loc    -> (mk_set_M, mk_set_M)
    | BaseId_int    -> (mk_set_U, mk_set_U)
    | BaseId_ext    -> (mk_set_U, mk_set_U)
    | BaseId_rfi    -> (mk_set_W, mk_set_R)
    | BaseId_rfe    -> (mk_set_W, mk_set_R)
    | BaseId_po_loc -> (mk_set_M, mk_set_M)
    | BaseId_atomicloc    -> (mk_set_M, mk_set_M)
    | BaseId_nonatomicloc -> (mk_set_M, mk_set_M)
    | BaseId_addr_dep -> (mk_set_R, mk_set_M)
    | BaseId_data_dep -> (mk_set_R, mk_set_M)
    | BaseId_ctrl_dep -> (mk_set_R, mk_set_M)

  let rec get_domain_range_simple_expr (expr: CatFile.simple_expr)
                                       : set * set  =
    match expr with
    | Eid (Id str) -> (mk_set_U, mk_set_U)
    | Eid (BaseId base_id) ->
        get_domain_range_id base_id
    | Einverse e ->
        let (domain, range) = get_domain_range_simple_expr e in
        (range,domain)
    | Eunion (e1,e2) ->
        let (domain1, range1) = get_domain_range_simple_expr e1 in
        let (domain2, range2) = get_domain_range_simple_expr e2 in
        (mk_set_union domain1 domain2,
         mk_set_union range1 range2)
    | Eintersection (e1,e2) ->
        let (domain1, range1) = get_domain_range_simple_expr e1 in
        let (domain2, range2) = get_domain_range_simple_expr e2 in
        (mk_set_intersection domain1 domain2,
         mk_set_intersection range1 range2)
    | Esequence (e1,e2) ->
        let (domain1, _) = get_domain_range_simple_expr e1 in
        let (_, range2)  = get_domain_range_simple_expr e2 in
        (domain1, range2)
    | Edifference (e1,_) ->
        get_domain_range_simple_expr e1
    | Eset set ->
        (set, set)
    | Eprod (s1,s2) ->
        (s1, s2)
    | Eoptional _ ->
        (mk_set_U, mk_set_U)

  (* Given an expr, compute it's domain and range and return a simplified expr *)
  let get_domain_range_expr (expr: CatFile.expr) : set * set =
    match expr with
    | Esimple simple_expr ->
        get_domain_range_simple_expr simple_expr
    | _ ->
        (mk_set_U, mk_set_U)


  (* If sequence of expressions ending in a set, we can replace with
   * domain/range restrictions *)
  let rec strip_hd_set (expr: CatFile.simple_expr) : CatFile.simple_expr =
    match expr with
    | Esequence(Eset s, e2) ->
        e2
    | Esequence(e1, e2) ->
        Esequence (strip_hd_set e1, e2)
    | _ -> expr

  let rec strip_tl_set (expr: CatFile.simple_expr) : CatFile.simple_expr =
    match expr with
    | Esequence(e1, Eset s) ->
        e1
    | Esequence(e1, e2) ->
        Esequence(e1, strip_tl_set e2)
    | _ -> expr

  let simplify_sequenced_exprs (expr: CatFile.expr) : CatFile.expr =
    match expr with
    | Esimple simple_expr ->
        Esimple (strip_tl_set (strip_hd_set simple_expr))
    | _ -> expr

  let load_file filename =
    let lines = read_file filename in
    let (bindings, constraints, undefs_unless_empty, outputs) =
      List.fold_left (fun (binding, constraints, undefs_unless_empty, output) s ->
        let result = parse_string instruction s in
        match result with
        | Result.Ok v ->
            bmc_debug_print 5 (pprint_instruction v);
            begin match v with
            | Binding (s, expr) ->
                (* TODO: domain and range *)
                let (domain, range) = get_domain_range_expr expr in
                let simplified_expr = simplify_sequenced_exprs expr in
                bmc_debug_print 5 (CatFile.pprint_expr simplified_expr);
                ((s, (domain, range),simplified_expr)::binding, constraints, undefs_unless_empty, output)
            | Constraint (s_opt, expr) ->
                (binding, (s_opt, expr)::constraints, undefs_unless_empty, output)
            | Undefined_unless_empty s ->
                (binding, constraints, s::undefs_unless_empty, output)
            | Output s ->
                (binding, constraints, undefs_unless_empty, s::output)
            | Skip _ -> (binding, constraints, undefs_unless_empty, output)
            end
        | Result.Error msg ->
            printf "ERROR: %s (input: '%s')\n" msg s;
            (binding, constraints, undefs_unless_empty, output)
      ) ([],[], [], []) lines in
    (module struct
      let bindings = bindings
      let constraints = constraints
      let undefs_unless_empty = undefs_unless_empty
      let to_output = outputs
     end : CatModel)
end


(*let load_catfile filename =
  let m = CatParser.load_file filename in
  let module M = (val m) in *)
