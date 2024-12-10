open Pp
open List
module BT = BaseTypes
module Res = Resource
module LC = LogicalConstraints
module Loc = Locations
module IntMap = Map.Make (Int)

type l_info = Locations.t * Pp.document Lazy.t

let pp_l_info doc (l : l_info) =
  typ doc (Lazy.force (snd l) ^^ break 1 ^^ Locations.pp (fst l))


type basetype_or_value =
  | BaseType of BT.t
  | Value of IndexTerms.t

let bt_of = function BaseType bt -> bt | Value v -> IndexTerms.bt v

let has_value = function BaseType _ -> false | Value _ -> true

(* History information about the most recent read/write actions taken on a resource. These
   are used to check for and report on concurrent races. The history is kept in a separate
   map to the resource list, indexed by resource id, so that the final deletion of a
   resource remains in the history. *)
type resource_history =
  { last_written : Locations.t;
    reason_written : string;
    last_written_id : int;
    last_read : Locations.t;
    last_read_id : int
  }

type t =
  { computational : (basetype_or_value * l_info) Sym.Map.t;
    logical : (basetype_or_value * l_info) Sym.Map.t;
    resources : (Res.t * int) list * int;
    resource_history : resource_history IntMap.t;
    constraints : LC.Set.t;
    global : Global.t;
    where : Where.t
  }

let empty =
  let logical =
    let loc_str = __FILE__ ^ ":" ^ string_of_int __LINE__ in
    let l_info = (Locations.other loc_str, lazy (Pp.string loc_str)) in
    Sym.Map.(empty |> add Alloc.History.sym (BaseType Alloc.History.bt, l_info))
  in
  { computational = Sym.Map.empty;
    logical;
    resources = ([], 0);
    resource_history = IntMap.empty;
    constraints = LC.Set.empty;
    global = Global.empty;
    where = Where.empty
  }


let get_rs (ctxt : t) = List.map fst (fst ctxt.resources)

let pp_basetype_or_value = function
  | BaseType bt -> BaseTypes.pp bt
  | Value it -> IndexTerms.pp it


let pp_variable_bindings bindings =
  Pp.list
    (fun (sym, (binding, _)) -> typ (Sym.pp sym) (pp_basetype_or_value binding))
    (Sym.Map.bindings bindings)


let pp_constraints constraints =
  Pp.list
    (fun lc ->
      if !print_level >= 11 || Option.is_none (LC.is_sym_lhs_equality lc) then
        LC.pp lc
      else
        parens !^"...")
    (LC.Set.elements constraints)


let pp (ctxt : t) =
  item "computational" (pp_variable_bindings ctxt.computational)
  ^/^ item "logical" (pp_variable_bindings ctxt.logical)
  ^/^ item "resources" (Pp.list Res.pp (get_rs ctxt))
  ^/^ item "constraints" (pp_constraints ctxt.constraints)


let bound_a s ctxt = Sym.Map.exists (fun s' _ -> Sym.equal s s') ctxt.computational

let bound_l s ctxt = Sym.Map.exists (fun s' _ -> Sym.equal s s') ctxt.logical

let bound s ctxt = bound_a s ctxt || bound_l s ctxt

let get_a s ctxt =
  match Sym.Map.find_opt s ctxt.computational with
  | Some (bt_v, _) -> bt_v
  | None -> failwith ("Context.get_a: not found: " ^ Pp.plain (Sym.pp_debug s))


let get_l s ctxt =
  match Sym.Map.find_opt s ctxt.logical with
  | Some (bt_v, _) -> bt_v
  | None -> failwith ("Context.get_l: not found: " ^ Pp.plain (Sym.pp_debug s))


let add_a_binding s binding info ctxt =
  if bound s ctxt then failwith ("already bound: " ^ Sym.pp_string s);
  { ctxt with computational = Sym.Map.add s (binding, info) ctxt.computational }


let add_a s bt info ctxt = add_a_binding s (BaseType bt) info ctxt

let add_a_value s value info ctxt = add_a_binding s (Value value) info ctxt

let add_l_binding s binding info ctxt =
  if bound s ctxt then failwith ("already bound: " ^ Sym.pp_string s);
  { ctxt with logical = Sym.Map.add s (binding, info) ctxt.logical }


let add_l s bt info ctxt = add_l_binding s (BaseType bt) info ctxt

let add_l_value s value info ctxt = add_l_binding s (Value value) info ctxt

(* Move s from computational to logical world so we can keep the constraints that may be
   attached to s: s will still be bound "logically", but out of scope as far as the Core
   program goes. *)
let remove_a s ctxt =
  let binding, info = Sym.Map.find s ctxt.computational in
  add_l_binding
    s
    binding
    info
    { ctxt with computational = Sym.Map.remove s ctxt.computational }


let add_c c (ctxt : t) =
  let s = ctxt.constraints in
  if LC.Set.mem c s then
    ctxt
  else
    { ctxt with constraints = LC.Set.add c s }


let modify_where (f : Where.t -> Where.t) ctxt = { ctxt with where = f ctxt.where }

(* let add_label_to_trace label ctxt = *)
(*   { ctxt with trace = { label; trace = [] } :: ctxt.trace } *)

(* let modify_current_label_trace f ctxt =  *)
(*   let label, labels = match ctxt.trace with *)
(*     | hd::tl -> hd, tl *)
(*     | [] -> assert false *)
(*   in *)
(*   { ctxt with trace = f label :: labels }  *)

(* let add_trace_item_to_trace i ctxt = *)
(*   modify_current_label_trace (fun label -> *)
(*       { label with trace = i :: label.trace} *)
(*     ) ctxt *)

let pp_history h =
  Pp.braces
    (Pp.list
       (fun (nm, v) -> Pp.typ (Pp.string nm) v)
       [ ("last read", Pp.int h.last_read_id);
         ("last read at", Locations.pp h.last_read);
         ("last written", Pp.int h.last_written_id);
         ("last written at", Locations.pp h.last_written)
       ])


let set_map_history id h m =
  (* Pp.debug 10 (lazy (Pp.item ("setting resource history of " ^ Int.to_string id)
     (pp_history h))); *)
  IntMap.add id h m


let set_history id h (ctxt : t) =
  let m = set_map_history id h ctxt.resource_history in
  { ctxt with resource_history = m }


let add_r loc r (ctxt : t) =
  let rs, ix = ctxt.resources in
  let resources = ((r, ix) :: rs, ix + 1) in
  let h =
    { last_written = loc;
      reason_written = "created";
      last_written_id = ix;
      last_read = loc;
      last_read_id = ix
    }
  in
  set_history ix h { ctxt with resources }


let res_map_history m id =
  match IntMap.find_opt id m with
  | Some h -> h
  | None ->
    let here = Locations.other __FUNCTION__ in
    { last_written = here;
      reason_written = "unknown";
      last_written_id = id;
      last_read = here;
      last_read_id = id
    }


let res_history (ctxt : t) id = res_map_history ctxt.resource_history id

let res_read loc id (ix, m) =
  let h = { (res_map_history m id) with last_read = loc; last_read_id = ix } in
  (ix + 1, set_map_history id h m)


let res_written loc id reason (ix, m) =
  let h =
    { (res_map_history m id) with
      last_written_id = ix;
      last_written = loc;
      reason_written = reason
    }
  in
  (ix + 1, set_map_history id h m)


(* used during unfold, clone one history to a list of new ids *)
let clone_history id ids m =
  let h = res_map_history m id in
  List.fold_right (fun id2 m -> set_map_history id2 h m) ids m


let json (ctxt : t) : Yojson.Safe.t =
  let basetype_or_value = function
    | BaseType bt -> `Variant ("BaseType", Some (BT.json bt))
    | Value it -> `Variant ("Value", Some (IndexTerms.json it))
  in
  let computational =
    List.map
      (fun (sym, (binding, _)) ->
        `Assoc [ ("name", Sym.json sym); ("type", basetype_or_value binding) ])
      (Sym.Map.bindings ctxt.computational)
  in
  let logical =
    List.map
      (fun (sym, (binding, _)) ->
        `Assoc [ ("name", Sym.json sym); ("type", basetype_or_value binding) ])
      (Sym.Map.bindings ctxt.logical)
  in
  let resources = List.map Res.json (get_rs ctxt) in
  let constraints = List.map LC.json (LC.Set.elements ctxt.constraints) in
  let json_record =
    `Assoc
      [ ("computational", `List computational);
        ("logical", `List logical);
        ("resources", `List resources);
        ("constraints", `List constraints)
      ]
  in
  `Variant ("Context", Some json_record)


(* picks out universally quantified constraints, recursive functions,
   and resource predicates that will not be given to the solver *)
let not_given_to_solver ctxt =
  let global = ctxt.global in
  let constraints =
    filter LogicalConstraints.is_forall (LC.Set.elements ctxt.constraints)
  in
  let funs =
    Sym.Map.bindings
      (Sym.Map.filter
         (fun _ v -> not (LogicalFunctions.given_to_solver v))
         global.logical_functions)
  in
  let preds =
    Sym.Map.bindings
      (Sym.Map.filter
         (fun _ v -> not (ResourcePredicates.given_to_solver v))
         global.resource_predicates)
  in
  (constraints, funs, preds)
