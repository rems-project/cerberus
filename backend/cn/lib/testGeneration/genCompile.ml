module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module RP = ResourcePredicates
module RET = ResourceTypes
module GBT = GenBaseTypes
module GT = GenTerms
module GD = GenDefinitions
module Config = TestGenConfig
module CtA = Cn_internal_to_ail
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)

type s = GD.context

type 'a t = s -> 'a * s

type 'a m = 'a t

let ( let@ ) (g : 'a m) (f : 'a -> 'b m) : 'b m =
  fun s ->
  let x, s' = g s in
  f x s'


let return (x : 'a) : 'a m = fun s -> (x, s)

let cn_return = Sym.fresh_named "cn_return"

let compile_oargs (ret_bt : BT.t) (iargs : (Sym.t * BT.t) list) : (Sym.t * BT.t) list =
  (cn_return, ret_bt) :: iargs


let compile_vars (generated : SymSet.t) (oargs : (Sym.t * GBT.t) list) (lat : IT.t LAT.t)
  : SymSet.t * (GT.t -> GT.t)
  =
  let backtrack_num = Config.get_max_backtracks () in
  let rec aux (xbts : (Sym.t * BT.t) list) : GT.t -> GT.t =
    match xbts with
    | (x, bt) :: xbts' ->
      let here = Locations.other __FUNCTION__ in
      let gt_gen = GT.arbitrary_ bt here in
      fun (gt : GT.t) ->
        let gt' = aux xbts' gt in
        GT.let_ (backtrack_num, (x, gt_gen), gt') here
    | [] -> fun gt -> gt
  in
  let xs, xbts =
    match lat with
    | Define ((x, it), _info, _) -> (SymSet.singleton x, IT.free_vars_bts it)
    | Resource ((x, ((P { name = Owned _; _ } as ret), bt)), _, _) ->
      (SymSet.singleton x, SymMap.add x bt (RET.free_vars_bts ret))
    | Resource ((x, (ret, _)), _, _) -> (SymSet.singleton x, RET.free_vars_bts ret)
    | Constraint (lc, _, _) -> (SymSet.empty, LC.free_vars_bts lc)
    | I it ->
      ( SymSet.empty,
        SymMap.union
          (fun _ bt1 bt2 ->
            assert (BT.equal bt1 bt2);
            Some bt1)
          (IT.free_vars_bts it)
          (oargs
           |> List.filter (fun (x, _) -> not (Sym.equal x cn_return))
           |> List.map_snd GBT.bt
           |> List.to_seq
           |> SymMap.of_seq) )
  in
  let xbts =
    xbts |> SymMap.filter (fun x _ -> not (SymSet.mem x generated)) |> SymMap.bindings
  in
  let generated =
    xbts |> List.map fst |> SymSet.of_list |> SymSet.union generated |> SymSet.union xs
  in
  (generated, aux xbts)


let rec compile_it_lat
  (preds : (Sym.t * RP.definition) list)
  (name : Sym.t)
  (generated : SymSet.t)
  (oargs : (Sym.t * GBT.t) list)
  (lat : IT.t LAT.t)
  : GT.t m
  =
  let backtrack_num = Config.get_max_backtracks () in
  (* Generate any free variables needed *)
  let generated, f_gt_init = compile_vars generated oargs lat in
  (* Compile *)
  let@ gt =
    match lat with
    | Define ((x, it), (loc, _), lat') ->
      let@ gt' = compile_it_lat preds name generated oargs lat' in
      return (GT.let_ (backtrack_num, (x, GT.return_ it (IT.loc it)), gt') loc)
    | Resource ((x, (P { name = Owned (ct, _); pointer; iargs = _ }, bt)), (loc, _), lat')
      ->
      let@ gt' = compile_it_lat preds name generated oargs lat' in
      let gt_asgn = GT.asgn_ ((pointer, ct), IT.sym_ (x, bt, loc), gt') loc in
      let gt_val =
        if SymSet.mem x generated then
          gt_asgn
        else
          GT.let_ (backtrack_num, (x, GT.arbitrary_ bt loc), gt_asgn) loc
      in
      return gt_val
    | Resource
        ((x, (P { name = PName fsym; pointer; iargs = args_its' }, bt)), (loc, _), lat')
      ->
      let here = Locations.other __LOC__ in
      let ret_bt = BT.Record [ (Identifier (here, "cn_return"), bt) ] in
      (* Recurse *)
      let@ gt' =
        compile_it_lat
          preds
          name
          generated
          oargs
          (LAT.subst
             IT.subst
             (IT.make_subst
                [ ( x,
                    IT.recordMember_
                      ~member_bt:bt
                      (IT.sym_ (x, ret_bt, here), Identifier (here, "cn_return"))
                      here )
                ])
             lat')
      in
      (* Get arguments *)
      let pred = List.assoc Sym.equal fsym preds in
      let arg_syms = pred.pointer :: fst (List.split pred.iargs) in
      let arg_its = pointer :: args_its' in
      let args = List.combine arg_syms arg_its in
      (* Add request *)
      let desired_iargs = List.map fst args in
      let gd : GD.t =
        { name = fsym;
          iargs =
            (pred.pointer, BT.Loc ()) :: pred.iargs
            |> List.filter (fun (x, _) -> List.mem Sym.equal x desired_iargs)
            |> List.map (fun (x, bt) -> (x, GBT.of_bt bt));
          oargs =
            compile_oargs
              pred.oarg_bt
              (pred.iargs
               |> List.filter (fun (x, _) -> not (List.mem Sym.equal x desired_iargs)))
            |> List.map (fun (x, bt) -> (x, GBT.of_bt bt));
          body = None
        }
      in
      (* Build [GT.t] *)
      let gt_call = GT.call_ (fsym, args) ret_bt loc in
      let gt_let = GT.let_ (backtrack_num, (x, gt_call), gt') loc in
      fun s -> (gt_let, GD.add_context gd s)
    | Resource
        ( ( x,
            ( Q
                { name = Owned (ct, _);
                  pointer;
                  q = q_sym, _;
                  q_loc;
                  step;
                  permission;
                  iargs = _
                },
              bt ) ),
          (loc, _),
          lat' ) ->
      let@ gt' = compile_it_lat preds name generated oargs lat' in
      let k_bt, v_bt = BT.map_bt bt in
      let gt_body =
        let sym_val = Sym.fresh () in
        let it_q = IT.sym_ (q_sym, k_bt, q_loc) in
        let it_p = IT.add_ (pointer, IT.mul_ (it_q, step) (IT.loc step)) loc in
        let gt_asgn =
          GT.asgn_
            ( (it_p, ct),
              IT.sym_ (sym_val, v_bt, loc),
              GT.return_ (IT.sym_ (sym_val, v_bt, loc)) loc )
            loc
        in
        GT.let_ (backtrack_num, (sym_val, GT.arbitrary_ v_bt loc), gt_asgn) loc
      in
      let gt_map = GT.map_ ((q_sym, k_bt, permission), gt_body) loc in
      let gt_let = GT.let_ (backtrack_num, (x, gt_map), gt') loc in
      return gt_let
    | Resource
        ( ( x,
            ( Q
                { name = PName fsym;
                  pointer;
                  q = q_sym, q_bt;
                  q_loc;
                  step;
                  permission;
                  iargs
                },
              bt ) ),
          (loc, _),
          lat' ) ->
      (* Recurse *)
      let@ gt' = compile_it_lat preds name generated oargs lat' in
      (* Get arguments *)
      let pred = List.assoc Sym.equal fsym preds in
      let arg_syms = pred.pointer :: fst (List.split pred.iargs) in
      let it_q = IT.sym_ (q_sym, q_bt, q_loc) in
      let it_p = IT.add_ (pointer, IT.mul_ (it_q, step) (IT.loc step)) loc in
      let arg_its = it_p :: iargs in
      let args = List.combine arg_syms arg_its in
      (* Add request *)
      let desired_iargs = List.map fst args in
      let gd : GD.t =
        { name = fsym;
          iargs =
            (pred.pointer, BT.Loc ()) :: pred.iargs
            |> List.filter (fun (x, _) -> List.mem Sym.equal x desired_iargs)
            |> List.map (fun (x, bt) -> (x, GBT.of_bt bt));
          oargs =
            compile_oargs
              pred.oarg_bt
              (pred.iargs
               |> List.filter (fun (x, _) -> not (List.mem Sym.equal x desired_iargs)))
            |> List.map (fun (x, bt) -> (x, GBT.of_bt bt));
          body = None
        }
      in
      (* Build [GT.t] *)
      let gt_body = GT.call_ (fsym, args) bt loc in
      let gt_map = GT.map_ ((q_sym, q_bt, permission), gt_body) loc in
      let gt_let = GT.let_ (backtrack_num, (x, gt_map), gt') loc in
      fun s -> (gt_let, GD.add_context gd s)
    | Constraint (lc, (loc, _), lat') ->
      let@ gt' = compile_it_lat preds name generated oargs lat' in
      return (GT.assert_ (lc, gt') loc)
    | I it ->
      let here = Locations.other __LOC__ in
      let conv_fn = List.map (fun (x, gbt) -> (x, IT.sym_ (x, GBT.bt gbt, here))) in
      let it_oargs =
        match oargs with
        | (sym, _) :: oargs' when Sym.equal sym cn_return ->
          (cn_return, it) :: conv_fn oargs'
        | _ -> conv_fn oargs
      in
      let it_ret =
        IT.record_ (List.map_fst (fun sym -> Id.id (Sym.pp_string sym)) it_oargs) here
      in
      return (GT.return_ it_ret (IT.loc it))
  in
  return (f_gt_init gt)


let rec compile_clauses
  (preds : (Sym.t * RP.definition) list)
  (name : Sym.t)
  (iargs : SymSet.t)
  (oargs : (Sym.t * GBT.t) list)
  (cls : RP.clause list)
  : GT.t m
  =
  match cls with
  | [ cl ] ->
    assert (IT.is_true cl.guard);
    compile_it_lat preds name iargs oargs cl.packing_ft
  | cl :: cls' ->
    let it_if = cl.guard in
    let@ gt_then = compile_it_lat preds name iargs oargs cl.packing_ft in
    let@ gt_else = compile_clauses preds name iargs oargs cls' in
    return (GT.ite_ (it_if, gt_then, gt_else) cl.loc)
  | [] -> failwith "unreachable"


let compile_pred
  (preds : (Sym.t * RP.definition) list)
  ({ name; iargs; oargs; body } : GD.t)
  : unit m
  =
  assert (Option.is_none body);
  let pred = List.assoc Sym.equal name preds in
  let@ gt =
    compile_clauses
      preds
      name
      (SymSet.of_list (List.map fst iargs))
      oargs
      (Option.get pred.clauses)
  in
  let gd : GD.t = { name; iargs; oargs; body = Some gt } in
  fun s -> ((), GD.add_context gd s)


let compile_spec (preds : (Sym.t * RP.definition) list) (name : Sym.t) (at : 'a AT.t)
  : unit m
  =
  let rec aux (at : 'a AT.t) =
    match at with
    | Computational ((x, bt), (loc, _), at') ->
      let acc, lat = aux at' in
      ((x, (bt, loc)) :: acc, lat)
    | L lat -> ([], lat)
  in
  let args, lat = aux at in
  let here = Locations.other __FUNCTION__ in
  let oargs = List.map_snd (fun (bt, _) -> GBT.of_bt bt) args in
  let@ gt =
    compile_it_lat preds name SymSet.empty oargs (LAT.map (fun _ -> IT.unit_ here) lat)
  in
  let gd : GD.t = { name; iargs = []; oargs; body = Some gt } in
  fun s -> ((), GD.add_context gd s)


let compile
  ?(ctx : GD.context option)
  (preds : (Sym.t * RP.definition) list)
  (insts : Core_to_mucore.instrumentation list)
  : GD.context
  =
  let context_specs =
    insts
    |> List.map (fun (inst : Core_to_mucore.instrumentation) ->
      compile_spec preds inst.fn (Option.get inst.internal))
    |> List.fold_left
         (fun ctx f ->
           let (), ctx' = f ctx in
           ctx')
         GD.empty_context
  in
  let context_preds (ctx : GD.context) : GD.context =
    List.fold_left
      (fun ctx' (_, iargs_defs) ->
        List.fold_left
          (fun ctx'' ((_, gd) : _ * GD.t) ->
            if Option.is_some gd.body then
              ctx''
            else (
              let (), ctx''' = compile_pred preds gd ctx'' in
              ctx'''))
          ctx'
          iargs_defs)
      ctx
      ctx
  in
  let rec loop (ctx : GD.context) : GD.context =
    let old_ctx = ctx in
    let new_ctx = context_preds ctx in
    if GD.equal_context old_ctx new_ctx then ctx else loop new_ctx
  in
  loop (Option.value ~default:context_specs ctx)
