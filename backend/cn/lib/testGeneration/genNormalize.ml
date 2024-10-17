module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module SymMap = Map.Make (Sym)

let rec arbitrary_of_sctype (sct : Sctypes.t) loc : GT.t =
  match sct with
  | Sctypes.Array (ct', Some len) ->
    let sym = Sym.fresh () in
    let bt = BT.Bits (Unsigned, 64) in
    GT.map_
      ( ( sym,
          bt,
          IT.and2_
            ( IT.le_ (IT.num_lit_ Z.zero bt loc, IT.sym_ (sym, bt, loc)) loc,
              IT.lt_ (IT.sym_ (sym, bt, loc), IT.num_lit_ (Z.of_int len) bt loc) loc )
            loc ),
        arbitrary_of_sctype ct' loc )
      loc
  | Array (_, None) ->
    failwith
      Pp.(
        plain
          (Sctypes.pp sct
           ^^ space
           ^^ at
           ^^ space
           ^^ Locations.pp loc
           ^^ space
           ^^ at
           ^^ space
           ^^ string __LOC__))
  | _ -> GT.arbitrary_ (Memory.bt_of_sct sct) loc


(* Should not have any primitive generators of structs *)
let destruct_struct_arbitrary (prog5 : unit Mucore.file) (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    match gt with
    (* This case is for when nested in a `map` due to needing an arbitrary array*)
    | GT (Arbitrary, Struct tag, loc_arb) ->
      (* Generate fresh vars for each member *)
      let members =
        match Pmap.find tag prog5.tagDefs with
        | StructDef pieces ->
          pieces
          |> List.filter_map (fun ({ member_or_padding; _ } : Memory.struct_piece) ->
            member_or_padding)
          |> List.map (fun (member, ct) -> (Sym.fresh (), (member, ct)))
        | _ -> failwith ("no struct " ^ Sym.pp_string tag ^ " found")
      in
      (* Assemble final struct *)
      let gt_struct =
        GT.return_
          (IT.struct_
             ( tag,
               List.map
                 (fun (y, (member, ct)) ->
                   (member, IT.sym_ (y, Memory.bt_of_sct ct, loc_arb)))
                 members )
             loc_arb)
          loc_arb
      in
      (* Generate appropriate generators for the members *)
      List.fold_left
        (fun gt'' (y, (_, sct)) ->
          let gt_arb = arbitrary_of_sctype sct loc_arb in
          (* NOTE: By construction, this should only be inside maps, so it'll never get backtracked to *)
          GT.let_ (0, (y, gt_arb), gt'') loc_arb)
        gt_struct
        members
    | GT (Let (backtracks, (x, GT (Arbitrary, Struct tag, loc_arb)), gt'), _, _) ->
      (* Generate fresh vars for each member *)
      let members =
        match Pmap.find tag prog5.tagDefs with
        | StructDef pieces ->
          pieces
          |> List.filter_map (fun ({ member_or_padding; _ } : Memory.struct_piece) ->
            member_or_padding)
          |> List.map (fun (member, ct) -> (Sym.fresh (), (member, ct)))
        | _ -> failwith ("no struct " ^ Sym.pp_string tag ^ " found")
      in
      (* Assemble final struct *)
      let gt_struct =
        GT.let_
          ( backtracks,
            ( x,
              GT.return_
                (IT.struct_
                   ( tag,
                     List.map
                       (fun (y, (member, ct)) ->
                         (member, IT.sym_ (y, Memory.bt_of_sct ct, loc_arb)))
                       members )
                   loc_arb)
                loc_arb ),
            gt' )
          loc_arb
      in
      (* Generate appropriate generators for the members *)
      List.fold_left
        (fun gt'' (y, (_, sct)) ->
          let gt_arb = arbitrary_of_sctype sct loc_arb in
          GT.let_ (backtracks, (y, gt_arb), gt'') loc_arb)
        gt_struct
        members
    | _ -> gt
  in
  GT.map_gen_pre aux gt


let normalize_gen (prog5 : unit Mucore.file) (gt : GT.t) : GT.t =
  let rec loop (gt : GT.t) : GT.t =
    let old_gt = gt in
    let new_gt = gt |> destruct_struct_arbitrary prog5 in
    if GT.equal old_gt new_gt then new_gt else loop new_gt
  in
  gt |> loop


let normalize_gen_def
  (prog5 : unit Mucore.file)
  ({ filename; recursive; name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { filename;
    recursive;
    name;
    iargs;
    oargs;
    body = Option.map (normalize_gen prog5) body
  }


let normalize (prog5 : unit Mucore.file) (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd (normalize_gen_def prog5)) ctx
