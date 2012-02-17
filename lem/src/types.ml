exception No_type of Ast.l * string

let raise_error l msg pp n =
  let pp ppf = Format.fprintf ppf "%s: %a" msg pp n in
    raise (No_type(l, Pp.pp_to_string pp))


module TVfmap = Finite_map.Fmap_map(Tyvar)
module TVset' = Set.Make(Tyvar)
module TVset = struct
  include TVset'
  let pp ppf tvset =
    Format.fprintf ppf "{@[%a@]}"
      (Pp.lst ",@ " Tyvar.pp)
      (TVset'.elements tvset)
end

module Pfmap = Finite_map.Fmap_map(Path)

type t = { mutable t : t_aux }
and t_aux =
  | Tvar of Tyvar.t
  | Tfn of t * t
  | Ttup of t list
  | Tapp of t list * Path.t
  | Tuvar of t_uvar
and t_uvar = { index : int; mutable subst : t option }

let free_vars t =
  let rec f t acc =
    match t.t with
      | Tvar(tv) -> TVset.add tv acc
      | Tfn(t1,t2) -> f t2 (f t1 acc)
      | Ttup(ts) -> 
          List.fold_left (fun acc t -> f t acc) acc ts
      | Tapp(ts,_) ->
          List.fold_left (fun acc t -> f t acc) acc ts
      | Tuvar _ -> TVset.empty
  in
    f t TVset.empty

let rec compare t1 t2 =
  if t1 == t2 then
    0
  else
    match (t1.t,t2.t) with
    | (Tvar(tv1), Tvar (tv2)) ->
        Tyvar.compare tv1 tv2
    | (Tvar _, _) -> 1
    | (_, Tvar _) -> -1
    | (Tfn(t1,t2), Tfn(t3,t4)) ->
        let c = compare t1 t3 in
          if c = 0 then
            compare t2 t4
          else
            c
    | (Tfn _, _) -> 1
    | (_, Tfn _) -> -1
    | (Ttup(ts1), Ttup(ts2)) ->
        Util.compare_list compare ts1 ts2
    | (Ttup _, _) -> 1
    | (_, Ttup _) -> -1
    | (Tapp(ts1,p1), Tapp(ts2,p2)) -> 
        let c = Util.compare_list compare ts1 ts2 in
          if c = 0 then
            Path.compare p1 p2
          else
            c
    | (Tapp _, _) -> 1
    | (_, Tapp _) -> -1
    | (Tuvar(u1), Tuvar(u2)) -> 
        if u1 == u2 then
          0
        else
          match (u1.subst, u2.subst) with
            | (Some(t1), Some(t2)) ->
                compare t1 t2
            | (Some _, None) -> 1
            | (None, Some _) -> -1
            | (None, None) -> 0

let multi_fun (ts : t list) (t : t) : t =
  List.fold_right (fun t1 t2 -> { t = Tfn(t1,t2); }) ts t

let rec type_subst_aux (substs : t TVfmap.t) (t : t) = 
  match t.t with
    | Tvar(s) ->
        (match TVfmap.apply substs s with
           | Some(t) -> Some(t)
           | None -> assert false)
    | Tfn(t1,t2) -> 
        begin
          match (type_subst_aux substs t1, type_subst_aux substs t2) with
            | (None,None) -> None
            | (Some(t),None) -> Some({ t = Tfn(t, t2) })
            | (None,Some(t)) -> Some({ t = Tfn(t1, t) })
            | (Some(t1),Some(t2)) -> Some({ t = Tfn(t1, t2) })
        end
    | Ttup(ts) -> 
        begin
          match Util.map_changed (type_subst_aux substs) ts with
            | None -> None
            | Some(ts) -> Some({ t = Ttup(ts) })
        end
    | Tapp(ts,p) -> 
        begin
          match Util.map_changed (type_subst_aux substs) ts with
            | None -> None
            | Some(ts) -> Some({ t = Tapp(ts,p) })
        end
    | Tuvar _ -> 
        assert false

let type_subst (substs : t TVfmap.t) (t : t) : t = 
  if TVfmap.is_empty substs then
    t
  else
    match type_subst_aux substs t with
      | None -> t
      | Some(t) -> t

let rec resolve_subst (t : t) : t = match t.t with
  | Tuvar({ subst=Some(t') } as u) ->
      let t'' = resolve_subst t' in
        (match t''.t with
           | Tuvar(_) ->
               u.subst <- Some(t'');
               t''
           | x -> 
               t.t <- x;
               t)
  | _ ->
      t

type tc_def = 
  | Tc_abbrev of Tyvar.t list * t option
  | Tc_class of Name.t list

type type_defs = tc_def Pfmap.t

type instance = Tyvar.t list * (Path.t * Tyvar.t) list * t * Name.t list

module IM = Map.Make(struct type t = int let compare = BatInt.compare end)
open Format
open Pp

let rec pp_type ppf t =
  pp_open_box ppf 0;
  (match t.t with
     | Tvar(tv) ->
         Tyvar.pp ppf tv
     | Tfn(t1,t2) ->
         fprintf ppf "(@[%a@])@ ->@ %a"
           pp_type t1
           pp_type t2
     | Ttup(ts) ->
         fprintf ppf "(@[%a@])"
           (lst "@ *@ " pp_type) ts
     | Tapp([],p) ->
         Path.pp ppf p
     | Tapp([t],p) ->
         fprintf ppf "%a@ %a"
           pp_type t
           Path.pp p
     | Tapp(ts,p) ->
         fprintf ppf "(@[%a@])@ %a"
           (lst ",@ " pp_type) ts
           Path.pp p
     | Tuvar(u) ->
         fprintf ppf "_");
         (*
         fprintf ppf "<@[%d,@ %a@]>" 
           u.index
           (opt pp_type) u.subst);
          *)
  pp_close_box ppf ()

let pp_tc ppf = function
  | Tc_abbrev(tvs, topt) ->
      begin
        match topt with
          | None -> fprintf ppf "%s" (string_of_int (List.length tvs))
          | Some(t) -> fprintf ppf "%a" pp_type t
      end
  | Tc_class _ ->
      (*TODO*)
      ()

let pp_tdefs ppf tds =
  Pfmap.pp_map Path.pp pp_tc ppf tds

let pp_class_constraint ppf (p, tv) =
  fprintf ppf "(@[%a@ %a@])"
    Path.pp p
    Tyvar.pp tv

let pp_instance_constraint ppf (p, t) =
  fprintf ppf "(@[%a@ %a@])"
    Path.pp p
    pp_type t

let pp_instance ppf (tyvars, constraints, t, p) =
  fprintf ppf "@[<2>forall@ (@[%a@]).@ @[%a@]@ =>@ %a@]@ (%a)"
    (lst ",@," Tyvar.pp) tyvars
    (lst "@ " pp_class_constraint) constraints
    pp_type t
    (lst "." Name.pp) p

let t_to_string t =
  pp_to_string (fun ppf -> pp_type ppf t)

let rec head_norm (d : type_defs) (t : t) : t = 
  let t = resolve_subst t in
    match t.t with
      | Tapp(ts,p) ->
          (match Pfmap.apply d p with
             | None ->
                 (*
                 Path.pp Format.std_formatter p;
                 Format.fprintf Format.std_formatter "@\n";
                 pp_tdefs Format.std_formatter d;
                 Format.fprintf Format.std_formatter "@\n";
                  *)
                 assert false
             | Some(Tc_abbrev(_,None)) -> t
             | Some(Tc_abbrev(tvs,Some(t))) ->
                 head_norm d (type_subst (TVfmap.from_list2 tvs ts) t)
             | Some(Tc_class _) ->
                 assert false)
      | _ -> 
          t

let t_to_tv t =
  match t.t with
    | Tvar(tv) -> tv
    | _ -> assert false

let types_match t_pat t =
  match (t_pat.t,t.t) with
    | (Tvar(tv), _) -> true
    | (Tfn(tv1,tv2), Tfn(t1,t2)) -> true
    | (Ttup(tvs), Ttup(ts)) ->
        List.length tvs = List.length ts
    | (Tapp(tvs,p), Tapp(ts,p')) ->
        Path.compare p p' = 0
    | (Tuvar _, _) -> assert false
    | _ -> false

let do_type_match t_pat t =
  match (t_pat.t,t.t) with
    | (Tvar(tv), _) -> TVfmap.from_list [tv,t]
    | (Tfn(tv1,tv2), Tfn(t1,t2)) ->
        TVfmap.from_list [(t_to_tv tv1,t1); (t_to_tv tv2,t2)]
    | (Ttup(tvs), Ttup(ts)) ->
        TVfmap.from_list2 (List.map t_to_tv tvs) ts
    | (Tapp(tvs,p), Tapp(ts,p')) ->
        TVfmap.from_list2 (List.map t_to_tv tvs) ts
    | _ -> assert false

let rec get_matching_instance d (p,t) instances = 
  let t = head_norm d t in 
    match Pfmap.apply instances p with
      | None -> None
      | Some(possibilities) ->
          try
            let (tvs,cs,t',p) = 
              List.find (fun (tvs,cs,t',p) -> types_match t' t) possibilities
            in
            let subst = do_type_match t' t in
              Some(p,
                   List.map (fun (p, tv) ->
                               (p, 
                                match TVfmap.apply subst tv with
                                  | Some(t) -> t
                                  | None -> assert false))
                     cs)
          with
              Not_found -> None

let type_mismatch l t1 t2 = 
  let t1 = t_to_string t1 in
  let t2 = t_to_string t2 in
    raise (No_type(l, "type mismatch:\n" ^ t1 ^ "\nand\n" ^ t2))

let rec assert_equal l (d : type_defs) (t1 : t) (t2 : t) : unit =
  if t1 == t2 then
    ()
  else
    let t1 = head_norm d t1 in
    let t2 = head_norm d t2 in
      match (t1.t,t2.t) with
        | (Tuvar _, _) -> type_mismatch l t1 t2
        | (_, Tuvar _) -> type_mismatch l t1 t2
        | (Tvar(s1), Tvar(s2)) ->
            if Tyvar.compare s1 s2 = 0 then
              ()
            else
              type_mismatch l t1 t2
        | (Tfn(t1,t2), Tfn(t3,t4)) ->
            assert_equal l d t1 t3;
            assert_equal l d t2 t4
        | (Ttup(ts1), Ttup(ts2)) -> 
            if List.length ts1 = List.length ts2 then
              assert_equal_lists l d ts1 ts2
            else 
              type_mismatch l t1 t2
        | (Tapp(args1,p1), Tapp(args2,p2)) ->
            if Path.compare p1 p2 = 0 && List.length args1 = List.length args2 then
              assert_equal_lists l d args1 args2
            else
              type_mismatch l t1 t2
        | _ -> 
            type_mismatch l t1 t2

and assert_equal_lists l d ts1 ts2 =
  List.iter2 (assert_equal l d) ts1 ts2

module type Constraint = sig
  val new_type : unit -> t
  val equate_types : Ast.l -> t -> t -> unit
  val add_constraint : Path.t -> t -> unit
  (*
  val equate_type_lists : Ast.l -> t list -> t list -> unit
   *)
  val add_tyvar : Tyvar.t -> unit 
  (*
  val same_types : Ast.l -> t list -> t
  val dest_fn_type : Ast.l -> t -> t * t
   *)
  val inst_leftover_uvars : Ast.l -> TVset.t * (Path.t * Tyvar.t) list
end

module type Global_defs = sig
  val d : type_defs 
  val i : (instance list) Pfmap.t 
end 

module Constraint (T : Global_defs) : Constraint = struct

  let next_uvar : int ref = ref 0
  let uvars : t list ref = ref []
  let tvars : TVset.t ref = ref TVset.empty

  let class_constraints : (Path.t * t) list ref = ref []

  let new_type () : t =
    let i = !(next_uvar) in
      incr next_uvar;
      let t = { t = Tuvar({ index=i; subst=None }); } in
        uvars := t::!uvars;
        t

  let add_tyvar (tv : Tyvar.t) : unit =
    tvars := TVset.add tv (!tvars)

  let rec occurs_check (t_box : t) (t : t) : unit =
    let t = resolve_subst t in
      if t_box == t then
        raise (No_type(Ast.Unknown, "Failed occurs check"))
      else
        match t.t with
          | Tfn(t1,t2) ->
              occurs_check t_box t1;
              occurs_check t_box t2
          | Ttup(ts) ->
              List.iter (occurs_check t_box) ts
          | Tapp(ts,_) ->
              List.iter (occurs_check t_box) ts
          | _ ->
              ()

  let prim_equate_types (t_box : t) (t : t) : unit =
    let t = resolve_subst t in
      if t_box == t then
        ()
      else
        (occurs_check t_box t;
         match t.t with
           | Tuvar(_) ->
               (match t_box.t with
                  | Tuvar(u) ->
                      u.subst <- Some(t)
                  | _ ->
                      assert false)
           | _ ->
               t_box.t <- t.t)

  let rec equate_types (l : Ast.l) (t1 : t) (t2 : t) : unit =
    if t1 == t2 then
      ()
    else
    let t1 = head_norm T.d t1 in
    let t2 = head_norm T.d t2 in
      match (t1.t,t2.t) with
        | (Tuvar _, _) -> 
            prim_equate_types t1 t2
        | (_, Tuvar _) -> 
            prim_equate_types t2 t1
        | (Tvar(s1), Tvar(s2)) ->
            if Tyvar.compare s1 s2 = 0 then
              ()
            else
              type_mismatch l t1 t2
        | (Tfn(t1,t2), Tfn(t3,t4)) ->
            equate_types l t1 t3;
            equate_types l t2 t4
        | (Ttup(ts1), Ttup(ts2)) -> 
            if List.length ts1 = List.length ts2 then
              equate_type_lists l ts1 ts2
            else 
              type_mismatch l t1 t2
        | (Tapp(args1,p1), Tapp(args2,p2)) ->
            if Path.compare p1 p2 = 0 && List.length args1 = List.length args2 then
              equate_type_lists l args1 args2
            else
              type_mismatch l t1 t2
        | _ -> 
            type_mismatch l t1 t2

  and equate_type_lists l ts1 ts2 =
    List.iter2 (equate_types l) ts1 ts2
(*
  let equate_types l t1 t2 =
    fprintf std_formatter "%a@ =@ %a@\n"
      pp_type t1
      pp_type t2;
    equate_types l t1 t2;
    fprintf std_formatter "%a@ =@ %a@\n@\n"
      pp_type t1
      pp_type t2
 *)

  let add_constraint p t =
    class_constraints := (p,t) :: (!class_constraints)

  let cur_tyvar = ref 0

  let rec get_next_tvar (i : int) : (int * Tyvar.t) =
    let tv = Tyvar.nth i in
      if TVset.mem tv (!tvars) then
        get_next_tvar (i + 1) 
      else
        (i,tv)

  let next_tyvar () : Tyvar.t =
    let (i,tv) = get_next_tvar !cur_tyvar in
      cur_tyvar := i+1;
      tv

  let rec solve_constraints instances unsolvable = function
    | [] -> unsolvable 
    | (p,t) :: constraints ->
        match get_matching_instance T.d (p,t) instances with
          | None ->
              solve_constraints instances ((p,t) :: unsolvable) constraints
          | Some((_,new_cs)) ->
              solve_constraints instances unsolvable (new_cs @ constraints)

  let check_constraint l (p,t) =
    match t.t with
      | Tvar(tv) -> (p,tv)
      | _ -> 
          let t1 = 
            Pp.pp_to_string (fun ppf -> pp_instance_constraint ppf (p, t))
          in 
            raise (No_type(l, "unsatisfied type class constraint:\n" ^ t1))

  let inst_leftover_uvars l =  
    let used_tvs = ref TVset.empty in
    let inst t =
      let t' = resolve_subst t in
        match t'.t with
          | Tuvar(u) ->
              let nt = next_tyvar () in
                used_tvs := TVset.add nt !used_tvs;
                t'.t <- Tvar(nt);
                ignore (resolve_subst t)
          | _ -> 
              ()
    in
      List.iter inst (!uvars);
      let cs = solve_constraints T.i [] !class_constraints in
        (TVset.union !tvars !used_tvs, List.map (check_constraint l) cs)
end

let rec ftvs (ts : t list) (acc : TVset.t) : TVset.t = match ts with
  | [] -> acc
  | t::ts -> ftvs ts (ftv t acc)
and ftv (t : t) (acc : TVset.t) : TVset.t = match t.t with
  | Tvar(x) -> 
      TVset.add x acc
  | Tfn(t1,t2) -> 
      ftv t2 (ftv t1 acc)
  | Ttup(ts) -> 
      ftvs ts acc
  | Tapp(ts,_) ->
      ftvs ts acc
  | Tuvar(_) -> 
      acc

