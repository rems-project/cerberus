module IT=IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module TE = TypeErrors
module Loc = Locations
module LF = LogicalFunctions
module LC = LogicalConstraints

module IdSet = Set.Make(Id)
module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

module StringList = struct
  type t = string list
  let compare = List.compare String.compare
  let equal = List.equal String.equal
end
module StringListMap = Map.Make(StringList)
module IntMap = Map.Make(Int)

open Cerb_pp_prelude

(* Some things are defined on-demand, so this state monad stores the set
   of such things defined and the contents of the various setup sections
   they may be defined into. *)
module PrevDefs = struct
  type t = {present: (Sym.t list) StringListMap.t;
        defs: (Pp.doc list) IntMap.t;
        dt_params: (IT.t * Id.t * Sym.t) list;
        failures: TypeErrors.type_error list}
  let init_t = {present = StringListMap.empty; defs = IntMap.empty; dt_params = []; failures = []}
  type 'a m = t -> ('a * t, TypeErrors.t) Result.t
  let return (x : 'a) : 'a m = (fun st -> Result.Ok (x, st))
  let bind (x : 'a m) (f : 'a -> 'b m) : 'b m = (fun st ->
    match x st with
    | Result.Error e -> Result.Error e
    | Result.Ok (xv, st) -> f xv st
  )
  let get : t m = (fun st -> Result.Ok (st, st))
  let set (st : t) : unit m = (fun _ -> Result.Ok ((), st))
  let upd (f : t -> t) : unit m = bind get (fun st -> set (f st))

  let get_section section (st : t) =
    match IntMap.find_opt section st.defs with
      | None -> []
      | Some docs -> docs
  let add_to_section section doc (st : t) =
    let current = get_section section st in
    let defs = IntMap.add section (doc :: current) st.defs in
    {st with defs}

  let add_dt_param x = upd (fun st ->
    {st with dt_params = x :: st.dt_params})

  let get_dt_param it m_nm = bind get (fun st ->
    return (List.find_opt (fun (it2, m2, sym) -> IT.equal it it2 && Id.equal m_nm m2)
        st.dt_params |> Option.map (fun (_, _, sym) -> sym)))

  let debug_dt_params i = bind get (fun st ->
    Pp.debug i (lazy (Pp.item "dt params available"
        (Pp.brackets (Pp.list (fun (it, m, _) -> Pp.typ (IT.pp it) (Id.pp m)) st.dt_params))));
    return ())

end
module PrevMonad = Effectful.Make(PrevDefs)
open PrevDefs
open PrevMonad

let with_reset_dt_params f =
  let@ st = get in
  let@ x = f () in
  let@ st2 = get in
  let@ () = set {st2 with dt_params = st.dt_params} in
  return x

module Mu = Mucore





let emit_kind kinds k =
  StringSet.mem k kinds || StringSet.mem "all" kinds

let parse_directions directions =
  (directions, StringSet.singleton "all")

let header filename =
  let open Pp in
  !^"(*" ^^^ !^ filename ^^ !^": generated lemma specifications from CN *)"
  ^^ hardline ^^ hardline
  ^^ !^"Require Import ZArith Bool." ^^ hardline
  ^^ !^"Require CN_Lemmas.CN_Lib."
  ^^ hardline ^^ hardline

let fail msg details =
  let open Pp in
  print stdout (format [Bold; Red] msg ^^ colon ^^ space ^^ details);
  failwith msg

(* print the error message, but continue with a default value when possible *)
let fail_m rv loc msg =
  let err = TypeErrors.{loc; msg = Generic msg} in
  Pp.error loc msg [];
  let@ () = upd (fun st -> {st with failures = err :: st.failures}) in
  return rv

let fail_m_d = fail_m (!^ "<error>")
let fail_m_o = fail_m None

(* release stored failures as exceptions *)
let release_failures () =
  let@ st = get in
  match st.failures with
  | [] -> return ()
  | fs -> (fun _ -> Result.Error (List.hd (List.rev fs)))

(* set of functions with boolean return type that we want to use
   as toplevel propositions, i.e. return Prop rather than bool
   (computational) in Coq. *)
let prop_funs = StringSet.of_list
  ["page_group_ok"]

exception Cannot_Coerce

(* attempt to coerce out the resources in this function type.
   we can do this for some lemmas where resources are passed and
   returned unchanged as a way of passing their return values. *)
let try_coerce_res (ftyp : AT.lemmat) =
  let rec erase_res r t = match t with
    | LRT.Define (v, info, t) ->
       LRT.Define (v, info, erase_res r t)
    | LRT.Constraint (lc, info, t) ->
       LRT.Constraint (lc, info, erase_res r t)
    | LRT.Resource ((name, (re, bt)), ((loc, _) as info), t) ->
        let (arg_name, arg_re) = r in
        if ResourceTypes.alpha_equivalent arg_re re
        then begin
          Pp.debug 2 (lazy (Pp.item "erasing" (Sym.pp name)));
          LRT.subst (IT.make_subst [(name, IT.sym_ (arg_name, bt, loc))]) t
        end else LRT.Resource ((name, (re, bt)), info, erase_res r t)
    | LRT.I ->
        Pp.debug 2 (lazy (Pp.string "no counterpart found"));
        raise Cannot_Coerce (* did not find a matching resource *)
  in
  let erase_res2 r t =
    Pp.debug 2 (lazy (Pp.item "seeking to erase counterpart" (Sym.pp (fst r))));
    let res = LAT.map ((erase_res r)) t in
    res
  in
  let rec coerce_lat t = match t with
    | LAT.Resource ((name, (re, bt)), info, t) ->
       let computationals, t = coerce_lat (erase_res2 (name, re) t) in
       ((name, bt, info) :: computationals), t
    | LAT.Define (v, info, t) ->
       let computationals, t = coerce_lat t in
       computationals, LAT.Define (v, info, t)
    | LAT.Constraint (lc, info, t) ->
       let computationals, t = coerce_lat t in
       computationals, LAT.Constraint (lc, info, t)
    | LAT.I _ ->
       [], t
  in
  let rec coerce_at t = match t with
    | AT.Computational (v, info, t) ->
       AT.Computational (v, info, coerce_at t)
    | AT.L t ->
       let computationals, t = coerce_lat t in
       AT.mComputationals computationals (AT.L t)
  in
  try Some (coerce_at ftyp) with Cannot_Coerce -> None

type scan_res = {
    res: string option;
    res_coerce: AT.lemmat option
  }

let init_scan_res = {res = None; res_coerce = None}

(* recurse over a function type and detect resources (impureness),
   non-unit return types (non-lemma trusted functions), and the set
   of uninterpreted functions used. *)
let scan (ftyp : AT.lemmat) =
  let rec scan_lrt t = match t with
    | LRT.Define ((_, it), _, t) -> scan_lrt t
    | LRT.Resource ((name, _), _, t) -> {(scan_lrt t) with res = Some (Sym.pp_string name)}
    | LRT.Constraint (_, _, t) -> scan_lrt t
    | LRT.I -> init_scan_res
  in
  let rec scan_lat t = match t with
    | LAT.Define (_, _, t) -> scan_lat t
    | LAT.Resource ((name, _), _, t) -> {(scan_lat t) with res = Some (Sym.pp_string name)}
    | LAT.Constraint (_, _, t) -> scan_lat t
    | LAT.I t -> scan_lrt t
  in
  let rec scan_at t = match t with
    | AT.Computational (_, _, t) -> scan_at t
    | AT.L t -> scan_lat t
  in
  let x = scan_at ftyp in
  if Option.is_none x.res then x
  else
  begin
  Pp.debug 2 (lazy (Pp.item "attempting to coerce ftyp" (Pp.string "")));
  match try_coerce_res ftyp with
    | None -> x
    | Some ftyp2 ->
    let y = scan_at ftyp2 in
    if Option.is_none y.res
    then begin
      Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "succeeded")));
      {x with res_coerce = Some ftyp2}
    end else begin
      Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "failed")));
      {x with res = y.res}
    end
  end

let struct_layout_field_bts xs =
  let open Memory in
  let xs2 = List.filter (fun x -> Option.is_some x.member_or_padding) xs
    |> List.sort (fun (x : struct_piece) y -> Int.compare x.offset y.offset)
    |> List.filter_map (fun x -> x.member_or_padding)
  in
  (List.map fst xs2, List.map (fun x -> Memory.bt_of_sct (snd x)) xs2)

let get_struct_xs struct_decls tag = match SymMap.find_opt tag struct_decls with
  | Some def -> struct_layout_field_bts def
  | None -> fail "undefined struct" (Sym.pp tag)

let binop s x y =
  let open Pp in
  parens (flow (break 1) [x; !^ s; y])

let doc_fun_app sd xs =
  let open Pp in
  parens (flow (break 1) (sd :: xs))

let fun_app s xs =
  doc_fun_app (!^ s) xs

let tuple_coq_ty doc fld_tys =
  let open Pp in
  let rec stars = function
    | [] -> fail "tuple_coq_ty: empty" doc
    | [x] -> [x]
    | x :: xs -> x :: star :: stars xs
  in
  parens (flow (break 1) (stars fld_tys))

(* type conv_info = { *)
(*     global : Global.t; *)
(*     (\* pairs ('a, nm) if 'a list is monomorphised to datatype named nm *\) *)
(*     list_mono : (BT.t * Sym.t) list *)
(*   } *)

type list_mono = (BT.t * Sym.t) list


let add_list_mono_datatype (bt, nm) global =
  let open Global in
  let bt_name = Sym.pp_string (Option.get (BT.is_datatype_bt bt)) in
  let nil = Sym.fresh_named ("Nil_of_" ^ bt_name) in
  let cons = Sym.fresh_named ("Cons_of_" ^ bt_name) in
  let hd = Id.id ("hd_of_" ^ bt_name) in
  let tl = Id.id ("tl_of_" ^ bt_name) in
  let mems = [(hd, bt); (tl, BT.Datatype nm)] in
  let datatypes = SymMap.add nm
        BT.{dt_constrs = [nil; cons]; dt_all_params = mems} global.datatypes in
  let datatype_constrs = global.datatype_constrs
    |> SymMap.add nil BT.{c_params = []; c_datatype_tag = nm}
    |> SymMap.add cons BT.{c_params = mems; c_datatype_tag = nm}
  in
  {global with datatypes; datatype_constrs}

let mono_list_bt list_mono bt = Option.bind (BT.is_list_bt bt)
  (fun arg_bt -> Option.bind
    (List.find_opt (fun (bt2, _) -> BT.equal arg_bt bt2) list_mono)
    (fun (_, dt_sym) -> Some (BT.Datatype dt_sym)))

let monomorphise_dt_lists global =
  let dt_lists = function
    | BT.List (BT.Datatype sym) -> Some sym
    | _ -> None
  in
  let all_dt_types = SymMap.fold (fun _ dt_info ss ->
        List.filter_map dt_lists (List.map snd dt_info.BT.dt_all_params) @ ss)
    global.Global.datatypes [] in
  let uniq_dt_types = SymSet.elements (SymSet.of_list all_dt_types) in
  let new_sym sym = (sym, Sym.fresh_named ("list_of_" ^ Sym.pp_string sym)) in
  let new_syms = List.map new_sym uniq_dt_types in
  let list_mono = List.map (fun (s1, s2) -> (BT.Datatype s1, s2)) new_syms in
  let global = List.fold_right add_list_mono_datatype list_mono global in
  let map_bt bt = Option.value ~default:bt (mono_list_bt list_mono bt) in
  let map_mems = List.map (fun (nm, bt) -> (nm, map_bt bt)) in
  let datatypes = SymMap.map (fun info ->
    BT.{info with dt_all_params = map_mems info.dt_all_params}) global.Global.datatypes in
  let datatype_constrs = SymMap.map (fun info ->
    BT.{info with c_params = map_mems info.c_params}) global.Global.datatype_constrs in
  let global = Global.{global with datatypes; datatype_constrs} in
  (list_mono, global)

let rec new_nm s nms i =
  let s2 = s ^ "_" ^ Int.to_string i in
  if List.exists (String.equal s2) nms
  then new_nm s nms (i + 1)
  else s2

let alpha_rename_if_pp_same (s, bt, loc) body =
  let vs = IT.free_vars body in
  let other_nms = List.filter (fun sym -> not (Sym.equal sym s)) (SymSet.elements vs)
    |> List.map Sym.pp_string in
  if List.exists (String.equal (Sym.pp_string s)) other_nms
  then begin
    Pp.debug 6 (lazy (Pp.item "doing rename"
        (Pp.typ (Sym.pp s) (Pp.braces (Pp.list Pp.string other_nms)))));
    let s2 = Sym.fresh_named (new_nm (Sym.pp_string s) other_nms 0) in
    let body = IT.subst (IT.make_subst [(s, IT.sym_ (s2, bt, loc))]) body in
    (s2, body, IT.free_vars body)
  end
  else (s, body, vs)

let it_adjust (global : Global.t) it =
  let rec f t =
    let loc = IT.loc t in
    match IT.term t with
        | IT.Binop (And, x1, x2) ->
            let xs = List.map f [x1; x2] |> List.partition IT.is_true |> snd in
            IT.and_ xs loc
        | IT.Binop (Or, x1, x2) ->
            let xs = List.map f [x1; x2] |> List.partition IT.is_false |> snd in
            IT.or_ xs loc
        | IT.Binop (EQ, x, y) ->
            let x = f x in
            let y = f y in
            if IT.equal x y then IT.bool_ true loc else IT.eq__ x y loc
        | IT.Binop (Impl, x, y) ->
            let x = f x in
            let y = f y in
            if IT.is_false x || IT.is_true y then IT.bool_ true loc else IT.impl_ (x, y) loc
        | IT.EachI ((i1, (s, bt), i2), x) ->
            let x = f x in
            (* TODO revisit this location *)
            let (s, x, vs) = alpha_rename_if_pp_same (s, BT.Integer, loc) x in
            if not (SymSet.mem s vs)
            then (assert (i1 <= i2); x)
            else IT.eachI_ (i1, (s, bt), i2) x loc
    | IT.Apply (name, args) ->
        let open LogicalFunctions in
        let def = SymMap.find name global.logical_functions in
        begin match def.definition, def.emit_coq with
          | Def body, false -> f ((open_fun def.args body args))
          | _ -> t
        end
    | IT.Good (ct, t2) -> if Option.is_some (Sctypes.is_struct_ctype ct)
        then t else f (IT.good_value global.struct_decls ct t2 loc)
    | Representable (ct, t2) -> if Option.is_some (Sctypes.is_struct_ctype ct)
        then t else f (IT.representable global.struct_decls ct t2 loc)
    | Aligned t ->
        f (IT.divisible_ (IT.pointerToIntegerCast_ t.t loc, t.align) loc)
    | IT.Let ((nm, x), y) ->
        let x = f x in
        let y = f y in
        (* TODO revisit this location *)
        let (nm, y, vs) = alpha_rename_if_pp_same (nm, IT.bt x, loc) y in
        if Option.is_some (IT.is_sym x)
        then IT.subst (IT.make_subst [(nm, x)]) y
        else
        if not (SymSet.mem nm vs)
        then y
        else IT.let_ ((nm, x), y) loc
    | _ -> t
  in
  let res = f it in
  Pp.debug 9 (lazy (Pp.item "it_adjust" (binop "->" (IT.pp it) (IT.pp res))));
  f it

let fun_prop_ret (global : Global.t) nm =
  match SymMap.find_opt nm global.logical_functions with
  | None -> fail "fun_prop_ret: not found" (Sym.pp nm)
  | Some def ->
    let open LogicalFunctions in
    BaseTypes.equal BaseTypes.Bool def.return_bt
      && StringSet.mem (Sym.pp_string nm) prop_funs

let tuple_syn xs =
  let open Pp in
  parens (flow (comma ^^^ !^ "") xs)

let find_tuple_element (eq : 'a -> 'a -> bool) (x : 'a) (pp : 'a -> Pp.doc) (ys : 'a list) =
  let n_ys = List.mapi (fun i y -> (i, y)) ys in
  match List.find_opt (fun (i, y) -> eq x y) n_ys with
    | None -> fail "tuple element not found" (pp x)
    | Some (i, _) -> (i, List.length ys)

let tuple_element t (i, len) =
  let open Pp in
  let nm i = string ("x_t_" ^ Int.to_string i) in
  let lhs = string "'" ^^ tuple_syn (List.init len nm) in
  parens (!^ "let" ^^^ lhs ^^^ !^ ":=" ^^^ t ^^^ !^ "in" ^^ break 1 ^^ nm i)

let tuple_upd_element t (i, len) y =
  let open Pp in
  let nm i = string ("x_t_" ^ Int.to_string i) in
  let lhs = string "'" ^^ tuple_syn (List.init len nm) in
  let rhs = tuple_syn (List.init len (fun j -> if j = i then y else nm j)) in
  parens (!^ "let" ^^^ lhs ^^^ !^ ":=" ^^^ t ^^^ !^ "in" ^^ break 1 ^^ rhs)

let rets s = return (Pp.string s)
let build = function
  | [] -> fail "build" (Pp.string "empty")
  | xs ->
    let@ docs = ListM.mapM (fun x -> x) xs in
    return (Pp.flow (Pp.break 1) docs)
let parensM x =
    let@ xd = x in
    return (Pp.parens xd)
let f_appM nm xs = parensM (build (rets nm :: xs))

let defn nm args opt_ty rhs =
  let open Pp in
  let tyeq = match opt_ty with
    | None -> []
    | Some ty -> [colon; ty]
  in
  flow (break 1) ([!^"  Definition"; !^ nm] @ args @ tyeq @ [!^":="])
  ^^ hardline ^^ !^"    " ^^ rhs ^^ !^ "." ^^ hardline

let fun_upd_def =
  defn "fun_upd" (List.map Pp.string ["{A B : Type}"; "(eq : A -> A -> bool)";
        "(f : A -> B)"; "x"; "y"; "z"]) None
    (Pp.string "if eq x z then y else f z")

let gen_ensure section k doc xs =
  let@ st = get in
  match StringListMap.find_opt k st.present with
  | None ->
    Pp.debug 8 (lazy (Pp.item "finalising doc for section"
        (Pp.brackets (Pp.list Pp.string k))));
    let@ fin_doc = Lazy.force doc in
    (* n.b. finalising the rhs-s of definitions might change the state *)
    let@ st = get in
    let st = add_to_section section fin_doc st in
    set {st with present = StringListMap.add k xs st.present}
  | Some ys ->
    if List.equal Sym.equal xs ys
    then return ()
    else fail "gen_ensure: mismatch/redef" (Pp.list Pp.string k)

let ensure_fun_upd () =
  let k = ["predefs"; "fun_upd"] in
  gen_ensure 2 k (lazy (return fun_upd_def)) []

let rec bt_to_coq (global : Global.t) (list_mono : list_mono) loc_info =
  let open Pp in
  let open Global in
  let do_fail nm bt = fail_m_d (fst loc_info) (Pp.item ("bt_to_coq: " ^ nm)
        (BaseTypes.pp bt ^^^ !^ "in converting" ^^^ (snd loc_info))) in
  let rec f bt = match bt with
  | BaseTypes.Bool -> return (!^ "bool")
  | BaseTypes.Integer -> return (!^ "Z")
  | BaseTypes.Bits _ -> return (!^ "Z")
  | BaseTypes.Map (x, y) ->
    let@ enc_x = f x in
    let@ enc_y = f y in
    return (parens (binop "->" enc_x enc_y))
  | BaseTypes.Struct tag ->
    let (_, fld_bts) = get_struct_xs global.struct_decls tag in
    let@ enc_fld_bts = ListM.mapM f fld_bts in
    return (tuple_coq_ty (Sym.pp tag) enc_fld_bts)
  | BaseTypes.Record mems ->
    let@ enc_mem_bts = ListM.mapM f (List.map snd mems) in
    return (tuple_coq_ty (!^ "record") enc_mem_bts)
  | BaseTypes.Loc -> return (!^ "CN_Lib.Loc")
  | BaseTypes.Datatype tag ->
    let@ () = ensure_datatype global list_mono (fst loc_info) tag in
    return (Sym.pp tag)
  | BaseTypes.List bt2 -> begin match mono_list_bt list_mono bt with
    | Some bt3 -> f bt3
    | _ -> do_fail "polymorphic list" bt
  end
  | _ -> do_fail "unsupported" bt
  in
  f

and ensure_datatype (global : Global.t) (list_mono : list_mono) loc dt_tag =
  let family = Global.mutual_datatypes global dt_tag in
  let dt_tag = List.hd family in
  let inf = (loc, Pp.typ (Pp.string "datatype") (Sym.pp dt_tag)) in
  let bt_to_coq2 bt = match BT.is_datatype_bt bt with
    | Some dt_tag2 -> if List.exists (Sym.equal dt_tag2) family
      then return (Sym.pp dt_tag2)
      else bt_to_coq global list_mono inf bt
    | _ -> bt_to_coq global list_mono inf bt
  in
  gen_ensure 0 ["types"; "datatype"; Sym.pp_string dt_tag]
  (lazy (
      let open Pp in
      let cons_line dt_tag c_tag =
          let info = SymMap.find c_tag global.datatype_constrs in
          let@ argTs = ListM.mapM (fun (_, bt) -> bt_to_coq2 bt) info.c_params in
          return (!^ "    | " ^^ Sym.pp c_tag ^^^ colon ^^^
              flow (!^ " -> ") (argTs @ [Sym.pp dt_tag]))
      in
      let@ dt_eqs = ListM.mapM (fun dt_tag ->
          let info = SymMap.find dt_tag global.datatypes in
          let@ c_lines = ListM.mapM (cons_line dt_tag) info.dt_constrs in
          return (!^ "    " ^^ Sym.pp dt_tag ^^^ colon ^^^ !^"Type :=" ^^
              hardline ^^ flow hardline c_lines)
      ) family in
      return (flow hardline
          (List.mapi (fun i doc -> !^ (if i = 0 then "  Inductive" else "    with") ^^
              hardline ^^ doc) dt_eqs) ^^ !^ "." ^^ hardline)
  )) [dt_tag]

let ensure_datatype_member global list_mono loc dt_tag (mem_tag: Id.t) bt =
  let@ () = ensure_datatype global list_mono loc dt_tag in
  let op_nm = Sym.pp_string dt_tag ^ "_" ^ Id.pp_string mem_tag in
  let dt_info = SymMap.find dt_tag global.Global.datatypes in
  let inf = (loc, Pp.typ (Pp.string "datatype acc for") (Sym.pp dt_tag)) in
  let@ bt_doc = bt_to_coq global list_mono inf bt in
  let cons_line c =
    let c_info = SymMap.find c global.Global.datatype_constrs in
    let pats =
      List.map (fun (m2, _) ->
        if Id.equal mem_tag m2
        then Id.pp mem_tag
        else Pp.string "_"
      ) c_info.c_params
    in
    let open Pp in
    !^ "    |" ^^^ flow (!^ " ") (Sym.pp c :: pats) ^^^ !^"=>" ^^^
    if List.exists (Id.equal mem_tag) (List.map fst c_info.c_params)
    then Id.pp mem_tag
    else !^"default"
  in
  let@ () =
  gen_ensure 0 ["types"; "datatype acc"; Sym.pp_string dt_tag; Id.pp_string mem_tag]
    (lazy (
      let open Pp in
      let eline = [!^ "    end"] in
      return (defn op_nm [parens (typ (!^ "dt") (Sym.pp dt_tag)); !^ "default"] (Some bt_doc)
      (flow hardline (!^ "match dt with" :: List.map cons_line dt_info.dt_constrs @ eline)))
    )) [dt_tag]
  in
  return op_nm

let ensure_single_datatype_member global list_mono loc dt_tag (mem_tag: Id.t) bt =
  let@ () = ensure_datatype global list_mono loc dt_tag in
  let op_nm = Sym.pp_string dt_tag ^ "_" ^ Id.pp_string mem_tag in
  let dt_info = SymMap.find dt_tag global.Global.datatypes in
  let cons_line c =
    let c_info = SymMap.find c global.Global.datatype_constrs in
    let pats = List.map (fun (m2, _) -> if Id.equal mem_tag m2
        then Id.pp mem_tag else Pp.string "_") c_info.c_params in
    let open Pp in
    !^ "    |" ^^^ flow (!^ " ") (Sym.pp c :: pats) ^^^ !^"=>" ^^^ Id.pp mem_tag
  in
  let@ () = gen_ensure 0 ["types"; "datatype acc";
        Sym.pp_string dt_tag; Id.pp_string mem_tag]
  (lazy (
      let inf = (loc, Pp.typ (Pp.string "datatype acc for") (Sym.pp dt_tag)) in
      let@ bt_doc = bt_to_coq global list_mono inf bt in
      let open Pp in
      let eline = [!^ "    end"] in
      return (defn op_nm [parens (typ (!^ "dt") (Sym.pp dt_tag))] (Some bt_doc)
          (flow hardline (!^ "match dt with" :: List.map cons_line dt_info.dt_constrs @ eline)))
  )) [dt_tag]
  in
  return op_nm

let ensure_list global list_mono loc bt =
  let@ dt_bt = match mono_list_bt list_mono bt with
    | Some x -> return x
    | None -> fail ("ensure_list: not a monomorphised list") (BT.pp bt)
  in
  let dt_sym = Option.get (BT.is_datatype_bt dt_bt) in
  let dt_info = SymMap.find dt_sym global.Global.datatypes in
  let (nil_nm, cons_nm) = match dt_info.BT.dt_constrs with
    | [nil; cons] -> (nil, cons)
    | _ -> assert false
  in
  let open Pp in
  let cons = parens (!^ "fun x ->" ^^^ Sym.pp cons_nm ^^^ !^ "x") in
  let dest_op_nm = "dest_" ^ Sym.pp_string dt_sym in
  let@ () = gen_ensure 0 ["types"; "list destructor"; Sym.pp_string dt_sym]
  (lazy (
      let nil_line = !^ "    |" ^^^ Sym.pp nil_nm ^^^ !^ "=>" ^^^ !^"None" in
      let cons_line = !^ "    |" ^^^ Sym.pp cons_nm ^^^ !^ "y ys =>" ^^^ !^"Some (y, ys)" in
      return (defn dest_op_nm [parens (typ (!^ "xs") (Sym.pp dt_sym))] None
          (flow hardline [!^ "match xs with"; nil_line; cons_line; !^"    end"]))
  )) [dt_sym]
  in
  return (Sym.pp nil_nm, cons, Pp.string dest_op_nm)

let ensure_tuple_op is_upd nm (ix, l) =
  let ix_s = Int.to_string ix in
  let len_s = Int.to_string l in
  let dir_s = if is_upd then "upd" else "get" in
  let k = ["predefs"; "tuple"; dir_s; nm; ix_s; len_s] in
  let op_nm = dir_s ^ "_" ^ nm ^ "_" ^ ix_s ^ "_" ^ len_s in
  let doc = lazy (
    let open Pp in
    let ty i = !^ ("T_" ^ Int.to_string i) in
    let t_ty = tuple_coq_ty (!^ op_nm) (List.init l ty) in
    let t = parens (typ (!^ "t") t_ty) in
    let x = parens (typ (!^ "x") (ty ix)) in
    let infer = !^"{" ^^ flow (!^ " ") (List.init l ty) ^^ colon ^^^ !^"Type}" in
    return (if is_upd then defn op_nm [infer; t; x]
             None (tuple_upd_element t (ix, l) x)
        else defn op_nm [infer; t] None (tuple_element t (ix, l)))
  )
  in
  let@ () = gen_ensure 2 k doc [] in
  return op_nm

let ensure_pred global list_mono loc name aux =
  let open LogicalFunctions in
  let def = SymMap.find name global.Global.logical_functions in
  let inf = (loc, Pp.typ (Pp.string "pred") (Sym.pp name)) in
  begin match def.definition with
  | Uninterp -> gen_ensure 1 ["params"; "pred"; Sym.pp_string name]
    (lazy (
      let@ arg_tys = ListM.mapM (fun (_, bt) -> bt_to_coq global list_mono inf bt) def.args in
      let open Pp in
      let@ ret_ty = if fun_prop_ret global name then return (!^ "Prop")
        else bt_to_coq global list_mono inf def.return_bt in
      let ty = List.fold_right (fun at rt -> at ^^^ !^ "->" ^^^ rt) arg_tys ret_ty in
      return (!^ "  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^ "." ^^ hardline)
    )) []
  | Def body ->
     gen_ensure 2 ["predefs"; "pred"; Sym.pp_string name]
       (lazy (
         let@ rhs = aux (it_adjust global body) in
         let@ args = ListM.mapM (fun (sym, bt) ->
                 let@ coq_bt = bt_to_coq global list_mono inf bt in
                 return (Pp.parens (Pp.typ (Sym.pp sym) coq_bt)))
             def.args in
         return (defn (Sym.pp_string name) args None rhs)
       )) []
  | Rec_Def body ->
    fail_m () def.loc (Pp.item "rec-def not yet handled" (Sym.pp name))
  end

let ensure_struct_mem is_good global list_mono loc ct aux = match Sctypes.is_struct_ctype ct with
  | None -> fail "ensure_struct_mem: not struct" (Sctypes.pp ct)
  | Some tag ->
  let bt = BaseTypes.Struct tag in
  let nm = if is_good then "good" else "representable" in
  let k = ["predefs"; "struct"; Sym.pp_string tag; nm] in
  let op_nm = "struct_" ^ Sym.pp_string tag ^ "_" ^ nm in
  let@ () = gen_ensure 2 k
  (lazy (
      let@ ty = bt_to_coq global list_mono (loc, Pp.string op_nm) bt in
      let x = Pp.parens (Pp.typ (Pp.string "x") ty) in
      let loc = Locations.other __FUNCTION__ in
      let x_it = IT.sym_ (Sym.fresh_named "x", bt, loc) in
      let@ rhs = aux (it_adjust global (IT.good_value global.struct_decls ct x_it loc)) in
      return (defn op_nm [x] None rhs)
  )) [tag] in
  return op_nm

let rec unfold_if_possible global it =
  let open IT in
  let open LogicalFunctions in
  match it with
  | IT (IT.Apply (name, args), _, _) ->
     let def = Option.get (Global.get_logical_function_def global name) in
     begin match def.definition with
     | Rec_Def _ -> it
     | Uninterp -> it
     | Def body ->
        unfold_if_possible global
          ((open_fun def.args body args))
     end
  | _ ->
     it

let mk_forall global list_mono loc sym bt doc =
  let open Pp in
  let inf = (loc, !^"forall of" ^^^ Sym.pp sym) in
  let@ coq_bt = bt_to_coq global list_mono inf bt in
  return (!^ "forall" ^^^ parens (typ (Sym.pp sym) coq_bt)
      ^^ !^"," ^^ break 1 ^^ doc)

let add_dt_param_counted (it, (m_nm : Id.t)) =
  let@ st = get in
  let idx = List.length (st.dt_params) in
  let sym = Sym.fresh_named (Id.pp_string m_nm ^ "_" ^ Int.to_string idx) in
  let@ () = add_dt_param (it, m_nm, sym) in
  return sym

let mk_let sym rhs_doc doc =
  let open Pp in
  !^ "let" ^^^ Sym.pp sym ^^^ !^ ":=" ^^^ rhs_doc ^^^ !^ "in" ^^^ doc

let rec pat_to_coq = function
  | Terms.Pat (Terms.PSym sym, _) -> return (Sym.pp sym)
  | Terms.Pat (Terms.PWild, _) -> rets "_"
  | Terms.Pat (Terms.PConstructor (c_nm, id_ps), _) ->
    (* assuming here that the id's are in canonical order *)
    parensM (build ([return (Sym.pp c_nm)] @ List.map pat_to_coq (List.map snd id_ps)))

let enc_z z = if Z.leq Z.zero z then rets (Z.to_string z)
  else parensM (rets (Z.to_string z))

let norm_bv_op bt doc_f = match bt with
  | BT.Bits (sign, sz) ->
    let (minInt, maxInt) = BT.bits_range (sign, sz) in
    f_appM "CN_Lib.wrapI" [enc_z minInt; enc_z maxInt; doc_f]
  | _ -> doc_f

let it_to_coq loc global list_mono it =
  let open Pp in
  let eq_of = function
    | BaseTypes.Integer -> rets "Z.eqb"
    | bt -> fail_m_d loc (Pp.item "eq_of" (BaseTypes.pp bt))
  in
  let rec f comp_bool t =
    let do_fail msg = fail_m_d loc (Pp.item ("it_to_coq: unsupported " ^ msg) (IT.pp t)) in
    let fail_on_prop () = match comp_bool with
      | None -> return ()
      | Some (ctxt, reason) -> fail_m () loc
        (Pp.item ("it_to_coq: unsupported in computational (non-Prop) mode")
            (Pp.flow (Pp.comma ^^ Pp.break 1) [IT.pp t; !^ reason; !^ "context:"; IT.pp ctxt]))
    in
    let aux t = f comp_bool t in
    let abinop s x y = parensM (build [aux x; rets s; aux y]) in
    let enc_prop = Option.is_none comp_bool in
    let with_is_true x = if enc_prop && BaseTypes.equal (IT.bt t) BaseTypes.Bool
        then f_appM "Is_true" [x] else x
    in
    let enc_z z = if Z.leq Z.zero z then rets (Z.to_string z)
      else parensM (rets (Z.to_string z))
    in
    let check_pos t f =
      (* FIXME turning this off for now to test stuff
      let t = unfold_if_possible global t in
      match IT.is_z t with
      | Some i when Z.gt i Z.zero -> f
      | _ -> do_fail "divisor (not positive const)"
      *) f
    in
    match IT.term t with
    | IT.Sym sym -> return (Sym.pp sym)
    | IT.Const l -> begin match l with
        | IT.Bool b -> with_is_true (rets (if b then "true" else "false"))
        | IT.Z z -> enc_z z
        | IT.Bits (info, z) -> enc_z (BT.normalise_to_range info z)
        | _ -> do_fail "const"
    end
    | IT.Unop (op, x) -> norm_bv_op (IT.bt t) begin match op with
       | IT.Not -> f_appM (if enc_prop then "~" else "negb") [aux x]
       | IT.BWFFSNoSMT -> f_appM "CN_Lib.find_first_set_z" [aux x]
       | IT.BWCTZNoSMT -> f_appM "CN_Lib.count_trailing_zeroes_z" [aux x]
       | _ -> do_fail "unary op"
    end
    | IT.Binop (op, x, y) -> norm_bv_op (IT.bt t) begin match op with
       | Add  -> abinop "+" x y
       | Sub  -> abinop "-" x y
       | Mul  -> abinop "*" x y
       | MulNoSMT  -> abinop "*" x y
       | Div  -> check_pos y (abinop "/" x y)
       | DivNoSMT  -> check_pos y (abinop "/" x y)
       | Mod  -> check_pos y (abinop "mod" x y)
       | ModNoSMT  -> check_pos y (abinop "mod" x y)
       (* TODO: this can't be right: mod and rem aren't the same
            - maybe they have the same semantics as Coq Z.modulo/Z.rem *)
       | Rem  -> check_pos y (abinop "mod" x y)
       | RemNoSMT  -> check_pos y (abinop "mod" x y)
       | LT  -> abinop (if enc_prop then "<" else "<?") x y
       | LE  -> abinop (if enc_prop then "<=" else "<=?") x y
       | Exp  -> abinop "^" x y
       | ExpNoSMT -> abinop "^" x y
       | XORNoSMT -> f_appM "Z.lxor" [aux x; aux y]
       | BWAndNoSMT -> f_appM "Z.land" [aux x; aux y]
       | BWOrNoSMT -> f_appM "Z.lor" [aux x; aux y]
       | EQ ->
           let comp = Some (t, "argument of equality") in
           parensM (build [f comp x; rets (if enc_prop then "=" else "=?"); f comp y])
       | LEPointer -> abinop (if enc_prop then "<=" else "<=?") x y
       | LTPointer -> abinop (if enc_prop then "<" else "<?") x y
       | And -> abinop (if enc_prop then "/\\" else "&&") x y
       | Or -> abinop (if enc_prop then "\\/" else "||") x y
       | Impl -> abinop (if enc_prop then "->" else "implb") x y
       | _ -> do_fail "arith op"
       end
    | IT.Match (x, cases) ->
        let comp = Some (t, "case-discriminant") in
        let br (pat, rhs) = build ([rets "|"; pat_to_coq pat; rets "=>"; aux rhs]) in
        parensM (build ([rets "match"; f comp x; rets "with"]
            @ List.map br cases @ [rets "end"]))
    | IT.ITE (sw, x, y) ->
        let comp = Some (t, "if-condition") in
        parensM (build [rets "if"; f comp sw; rets "then"; aux x; rets "else"; aux y])
    | IT.EachI ((i1, (s, _), i2), x) ->
        let@ () = fail_on_prop () in
        let@ x = aux x in
        let@ enc = mk_forall global list_mono loc s BaseTypes.Integer
             (binop "->" (binop "/\\"
                 (binop "<=" (Pp.int i1) (Sym.pp s)) (binop "<=" (Sym.pp s) (Pp.int i2)))
             x) in
        return (parens enc)
    | IT.MapSet (m, x, y) ->
        let@ () = ensure_fun_upd () in
        let@ e = eq_of (IT.bt x) in
        f_appM "fun_upd" [return e; aux m; aux x; aux y]
    | IT.MapGet (m, x) -> parensM (build [aux m; aux x])
    | IT.RecordMember (t, m) ->
        let flds = BT.record_bt (IT.bt t) in
        if List.length flds == 1
        then aux t
        else
        let ix = find_tuple_element Id.equal m Id.pp (List.map fst flds) in
        let@ op_nm = ensure_tuple_op false (Id.pp_string m) ix in
        parensM (build [rets op_nm; aux t])
    | IT.RecordUpdate ((t, m), x) ->
        let flds = BT.record_bt (IT.bt t) in
        if List.length flds == 1
        then aux x
        else
        let ix = find_tuple_element Id.equal m Id.pp (List.map fst flds) in
        let@ op_nm = ensure_tuple_op true (Id.pp_string m) ix in
        parensM (build [rets op_nm; aux t; aux x])
    | IT.Record mems ->
        let@ xs = ListM.mapM aux (List.map snd mems) in
        parensM (return (flow (comma ^^ break 1) xs))
    | IT.StructMember (t, m) ->
        let tag = BaseTypes.struct_bt (IT.bt t) in
        let (mems, bts) = get_struct_xs global.struct_decls tag in
        let ix = find_tuple_element Id.equal m Id.pp mems in
        if List.length mems == 1
        then aux t
        else
        let@ op_nm = ensure_tuple_op false (Id.pp_string m) ix in
        parensM (build [rets op_nm; aux t])
    | IT.StructUpdate ((t, m), x) ->
        let tag = BaseTypes.struct_bt (IT.bt t) in
        let (mems, bts) = get_struct_xs global.struct_decls tag in
        let ix = find_tuple_element Id.equal m Id.pp mems in
        if List.length mems == 1
        then aux x
        else
        let@ op_nm = ensure_tuple_op true (Id.pp_string m) ix in
        parensM (build [rets op_nm; aux t; aux x])
    | IT.Cast (cbt, t) ->
        begin match IT.bt t, cbt with
        | Integer, Loc -> aux t
        | Loc, Integer -> aux t
        | source, target ->
            let source = Pp.plain (BT.pp source) in
            let target = Pp.plain (BT.pp target) in
            do_fail ("cast from " ^ source ^ " to " ^ target)
        end
    | IT.Apply (name, args) ->
        let prop_ret = fun_prop_ret global name in
        let body_aux = f (if prop_ret then None else Some (t, "fun-arg")) in
        let@ () = ensure_pred global list_mono loc name body_aux in
        let@ r = parensM (build ([return (Sym.pp name)] @ List.map body_aux args)) in
        if prop_ret then return r else with_is_true (return r)
    | IT.Good (ct, t2) when (Option.is_some (Sctypes.is_struct_ctype ct)) ->
        let@ () = fail_on_prop () in
        let@ op_nm = ensure_struct_mem true global list_mono loc ct aux in
        parensM (build [rets op_nm; aux t2])
    | IT.Representable (ct, t2) when (Option.is_some (Sctypes.is_struct_ctype ct)) ->
        let@ () = fail_on_prop () in
        let@ op_nm = ensure_struct_mem true global list_mono loc ct aux in
        parensM (build [rets op_nm; aux t2])
    | IT.Constructor (nm, id_args) ->
       let info = SymMap.find nm global.datatype_constrs in
       let comp = Some (t, "datatype contents") in
       let@ () = ensure_datatype global list_mono loc info.c_datatype_tag in
       (* assuming here that the id's are in canonical order *)
       parensM (build ([return (Sym.pp nm)] @ List.map (f comp) (List.map snd id_args)))
    | IT.NthList (n, xs, d) ->
       let@ (_, _, dest) = ensure_list global list_mono loc (IT.bt xs) in
       parensM (build [rets "CN_Lib.nth_list_z"; return dest;
                       aux n; aux xs; aux d])
    | IT.ArrayToList (arr, i, len) ->
       let@ (nil, cons, _) = ensure_list global list_mono loc (IT.bt t) in
       parensM (build [rets "CN_Lib.array_to_list"; return nil; return cons;
                       aux arr; aux i; aux len])
    | IT.WrapI (ity, arg) ->
       assert (not (Sctypes.IntegerTypes.equal ity Sctypes.IntegerTypes.Bool));
       let maxInt = Memory.max_integer_type ity in
       let minInt = Memory.min_integer_type ity in
       f_appM "CN_Lib.wrapI" [enc_z minInt; enc_z maxInt; aux arg]
    | IT.Let ((nm, x), y) ->
       let@ x = aux x in
       let@ y = aux y in
       parensM (return (mk_let nm x y))
    | IT.ArrayShift { base; ct; index } ->
      let size_of_ct = Z.of_int @@ Memory.size_of_ctype ct in
      f_appM "CN_Lib.array_shift" [aux base; enc_z size_of_ct; aux index]
    | _ -> do_fail "term kind"
  in
  f None it

let lc_to_coq_check_triv loc global list_mono = function
  | LC.T it -> let it = it_adjust global it in
    if IT.is_true it then return None
    else let@ v = it_to_coq loc global list_mono it in return (Some v)
  | LC.Forall ((sym, bt), it) -> let it = it_adjust global it in
    if IT.is_true it then return None
    else
      let@ v = it_to_coq loc global list_mono it in
      let@ enc = mk_forall global list_mono loc sym bt v in
      return (Some (Pp.parens enc))

let nth_str_eq n s ss = Option.equal String.equal (List.nth_opt ss n) (Some s)

let types_spec types =
  let open Pp in
  !^"Module Types."
  ^^ hardline ^^ hardline
  ^^ (if List.length types == 0
    then !^ "  (* no type definitions required *)" ^^ hardline
    else flow hardline types)
  ^^ hardline
  ^^ !^"End Types."
  ^^ hardline ^^ hardline

let param_spec params =
  let open Pp in
  !^"Module Type Parameters." ^^ hardline
  ^^ !^"  Import Types."
  ^^ hardline ^^ hardline
  ^^ (if List.length params == 0
    then !^ "  (* no parameters required *)" ^^ hardline
    else flow hardline params)
  ^^ hardline
  ^^ !^"End Parameters."
  ^^ hardline ^^ hardline


let ftyp_to_coq loc global list_mono (ftyp: AT.lemmat) =
  let open Pp in
  let lc_to_coq_c = lc_to_coq_check_triv loc global list_mono in
  let it_tc = it_to_coq loc global list_mono in
  (* FIXME: handle underdefinition in division *)
  let oapp f opt_x y = match opt_x with
    | Some x -> f x y
    | None -> y
  in
  let mk_and doc doc2 = doc ^^^ !^ "/\\" ^^^ doc2 in
  let mk_imp doc doc2 = doc ^^^ !^ "->" ^^^ doc2 in
  let omap_split f = Option.map (fun doc -> f (break 1 ^^ doc)) in
  let rec lrt_doc t = match t with
    | LRT.Constraint (lc, _, t) ->
    let@ d = lrt_doc t in
    let@ c = lc_to_coq_c lc in
    begin match d, c with
        | None, _ -> return c
        | _, None -> return d
        | Some dd, Some cd -> return (Some (mk_and cd dd))
    end
    | LRT.Define ((sym, it), _, t) ->
        let@ d = lrt_doc t in
        let@ l = it_tc it in
        return (omap_split (mk_let sym l) d)
    | LRT.I -> return None
    | _ -> fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LRT.pp t))
  in
  let rec lat_doc t = match t with
    | LAT.Define ((sym, it), _, t) ->
        let@ d = lat_doc t in
        let@ l = it_tc it in
        return (omap_split (mk_let sym l) d)
    | LAT.Resource _ ->
       fail_m_o loc (Pp.item "ftyp_to_coq: unsupported" (LAT.pp LRT.pp t))
    | LAT.Constraint (lc, _, t) ->
        let@ c = lc_to_coq_c lc in
        let@ d = lat_doc t in
        return (omap_split (oapp mk_imp c) d)
    | LAT.I t -> lrt_doc t
  in
  let rec at_doc t = match t with
    | AT.Computational ((sym, bt), _, t) ->
        let@ d = at_doc t in
        begin match d with
          | None -> return None
          | Some doc ->
            let@ doc2 = mk_forall global list_mono loc sym bt (break 1 ^^ doc) in
            return (Some doc2)
        end
    | AT.L t -> lat_doc t
  in
  let@ d = at_doc ftyp in
  match d with
  | Some doc -> return doc
  | None -> rets "Is_true true"

let convert_lemma_defs global list_mono lemma_typs =
  let lemma_ty (nm, (typ: AT.lemmat), loc, kind) =
    Pp.progress_simple ("converting " ^ kind ^ " lemma type") (Sym.pp_string nm);
    let@ rhs = ftyp_to_coq loc global list_mono typ in
    return (defn (Sym.pp_string nm ^ "_type") [] (Some (Pp.string "Prop")) rhs)
  in
  let@ tys = ListM.mapM lemma_ty lemma_typs in
  let@ st = get in
  Pp.debug 4 (lazy (Pp.item "saved conversion elements"
    (Pp.list (fun (ss, _) -> Pp.parens (Pp.list Pp.string ss))
        (StringListMap.bindings st.present))));
  return (tys, List.rev (get_section 0 st),
        List.rev (get_section 1 st), List.rev (get_section 2 st))

let defs_module aux_defs lemma_tys =
  let open Pp in
  !^"Module Defs (P : Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Import Types P." ^^ hardline
  ^^ !^"  Open Scope Z." ^^ hardline ^^ hardline
  ^^ flow hardline aux_defs
  ^^ hardline
  ^^ flow hardline lemma_tys
  ^^ hardline
  ^^ !^"End Defs."
  ^^ hardline ^^ hardline

let mod_spec lemma_nms =
  let open Pp in
  let lemma nm =
    !^"  Parameter" ^^^ typ (Sym.pp nm) (Sym.pp nm ^^ !^ "_type")
        ^^ !^ "." ^^ hardline
  in
  !^"Module Type Lemma_Spec (P : Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Module D := Defs(P)." ^^ hardline
  ^^ !^"  Import D." ^^ hardline ^^ hardline
  ^^ flow hardline (List.map lemma lemma_nms)
  ^^ hardline
  ^^ !^"End Lemma_Spec."
  ^^ hardline ^^ hardline

let convert_and_print channel global list_mono conv =
  let@ (conv_defs, types, params, defs) = convert_lemma_defs global list_mono conv in
  let@ () = release_failures () in
  Pp.print channel (types_spec types);
  Pp.print channel (param_spec params);
  Pp.print channel (defs_module defs conv_defs);
  Pp.print channel (mod_spec (List.map (fun (nm, _, _, _) -> nm) conv));
  return ()

let cmp_line_numbers = function
  | None, None -> 0
  | None, _ -> 1
  | _, None -> -1
  | Some (a, b), Some (c, d) ->
    let x = Int.compare a c in
    if x == 0 then Int.compare b d else x

let cmp_loc_line_numbers l1 l2 =
    cmp_line_numbers (Loc.line_numbers l1, Loc.line_numbers l2)

(* an experiment involving calling the Retype features again, this time
   with "CallByValue" set. this probably doesn't work, since the elaboration
   needs to be compatible
let do_re_retype mu_file trusted_funs prev_mode pred_defs pre_retype_mu_file =
  match prev_mode with
  | `CallByValue -> Ok mu_file
  | `CallByReference ->
  let prev_cut =
      let open Retype.Old in
      let info2 = Pmap.filter (fun fsym _ -> SymSet.mem fsym trusted_funs)
          pre_retype_mu_file.mu_funinfo in
      let funs2 = Pmap.filter (fun fsym _ -> SymSet.mem fsym trusted_funs)
          pre_retype_mu_file.mu_funs in
      { pre_retype_mu_file with mu_funs = funs2; mu_funinfo = info2 }
  in
  Retype.retype_file pred_defs `CallByValue prev_cut
*)

type scanned = {
    sym : Sym.t;
    loc: Loc.t;
    typ: AT.lemmat;
    scan_res: scan_res
  }



let generate (global : Global.t) directions (lemmata : (Sym.t * (Loc.t * AT.lemmat)) list) =
  (* let open Mu in *)
  let (filename, kinds) = parse_directions directions in
  let channel = open_out filename in
  Pp.print channel (header filename);
  Pp.debug 1 (lazy (Pp.item "lemmata generation"
    (Pp.braces (Pp.list Sym.pp (List.map fst lemmata)))));
  let scan_lemmata =
    List.map (fun (sym, (loc, typ)) ->
        {sym; loc; typ; scan_res = scan typ}
      ) lemmata
    |> List.sort (fun x (y : scanned) -> cmp_loc_line_numbers x.loc y.loc)
  in
  let (impure, pure) = List.partition (fun x -> Option.is_some x.scan_res.res) scan_lemmata in
  let (coerce, skip) = List.partition
        (fun x -> Option.is_some x.scan_res.res_coerce) impure in
  List.iter (fun x ->
    Pp.progress_simple "skipping trusted fun with resource"
        (Sym.pp_string x.sym ^ ": " ^ (Option.get x.scan_res.res))
  ) skip;
  (* let fun_info = List.fold_right (fun (s, def) m -> SymMap.add s def m) *)
  (*       mu_file.mu_logical_predicates SymMap.empty in *)
  (* let struct_decls = get_struct_decls mu_file in *)
  (* let global = Global.{ctxt.Context.global with struct_decls} in *)
  let (list_mono, global) = monomorphise_dt_lists global in
  (* let ci = {global; fun_info; list_mono} in *)
  let conv = List.map (fun x -> (x.sym, x.typ, x.loc, "pure")) pure
    @ List.map (fun x -> (x.sym, Option.get x.scan_res.res_coerce, x.loc, "coerced")) coerce in
  match convert_and_print channel global list_mono conv init_t with
  | Result.Ok _ -> Result.Ok ()
  | Result.Error e -> Result.Error e
