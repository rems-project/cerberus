module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module Config = TestGenConfig

let generated_size (bt : BT.t) : int =
  match bt with
  | Datatype _ -> failwith Pp.(plain (BT.pp bt ^^ space ^^ at ^^ space ^^ string __LOC__))
  | _ -> 0


let allocations (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, bt, loc)) = gt in
    let gt_ =
      match gt_ with
      | Arbitrary ->
        (match bt with
         | Loc () -> GT.Alloc (IT.num_lit_ Z.zero Memory.size_bt loc)
         | _ -> gt_)
      | _ -> gt_
    in
    GT (gt_, bt, loc)
  in
  GT.map_gen_pre aux gt


let apply_array_max_length (gt : GT.t) : GT.t =
  let rec aux (gt : GT.t) : GT.t =
    let (GT (gt_, _bt, here)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
    | Pick wgts -> GT.pick_ (List.map_snd aux wgts) here
    | Asgn ((it_addr, sct), it_val, gt') ->
      GT.asgn_ ((it_addr, sct), it_val, aux gt') here
    | Let (backtracks, (x, gt_inner), gt') ->
      GT.let_ (backtracks, (x, aux gt_inner), aux gt') here
    | Assert (lc, gt') -> GT.assert_ (lc, aux gt') here
    | ITE (it_if, gt_then, gt_else) -> GT.ite_ (it_if, aux gt_then, aux gt_else) here
    | Map ((i, i_bt, it_perm), gt') ->
      let _it_min, it_max = IndexTerms.Bounds.get_bounds (i, i_bt) it_perm in
      let loc = Locations.other __LOC__ in
      let it_max_min =
        IT.le_
          ( IT.num_lit_ (Z.of_int 0) (IT.bt it_max) loc,
            IT.add_ (it_max, IT.num_lit_ Z.one (IT.bt it_max) loc) loc )
          loc
      in
      let it_max_max =
        IT.lt_
          ( it_max,
            IT.num_lit_ (Z.of_int (Config.get_max_array_length ())) (IT.bt it_max) loc )
          loc
      in
      GT.assert_
        ( LC.T (IT.and2_ (it_max_min, it_max_max) loc),
          GT.map_ ((i, i_bt, it_perm), aux gt') here )
        loc
  in
  aux gt


let default_weights (gt : GT.t) : GT.t =
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, bt, loc)) = gt in
    let gt_ =
      match gt_ with
      | Arbitrary ->
        (match bt with
         | Map _ | Loc () ->
           failwith Pp.(plain (BT.pp bt ^^ space ^^ at ^^ space ^^ string __LOC__))
         | _ -> GT.Uniform (generated_size bt))
      | _ -> gt_
    in
    GT (gt_, bt, loc)
  in
  GT.map_gen_pre aux gt


let confirm_distribution (gt : GT.t) : GT.t =
  let rec aux (gt : GT.t) : Locations.t list =
    let (GT (gt_, _, loc)) = gt in
    match gt_ with
    | Arbitrary -> [ loc ]
    | Uniform _ | Alloc _ | Call _ | Return _ -> []
    | Pick wgts -> wgts |> List.map snd |> List.map aux |> List.flatten
    | Asgn (_, _, gt') | Assert (_, gt') | Map ((_, _, _), gt') -> aux gt'
    | Let (_, (_, gt1), gt2) | ITE (_, gt1, gt2) ->
      [ gt1; gt2 ] |> List.map aux |> List.flatten
  in
  let failures = aux gt in
  if List.is_empty failures then
    gt
  else
    failwith
      Pp.(
        plain
          (string "Distribute failure: `arbitrary` still remaining at following locations"
           ^^ space
           ^^ brackets (separate_map (comma ^^ break 1) Locations.pp failures)))


let distribute_gen (gt : GT.t) : GT.t =
  gt |> allocations |> apply_array_max_length |> default_weights |> confirm_distribution


let distribute_gen_def ({ filename; recursive; spec; name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { filename; recursive; spec; name; iargs; oargs; body = Option.map distribute_gen body }


let distribute (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd distribute_gen_def) ctx
