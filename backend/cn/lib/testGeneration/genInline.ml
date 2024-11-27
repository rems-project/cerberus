module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions

let unfold (ctx : GD.context) : GD.context =
  let rec loop (fuel : int option) (gd : GD.t) : GD.t =
    if Option.equal Int.equal fuel (Some 0) then
      gd
    else (
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _, _)) = gt in
        match gt_ with
        | Call (fsym, iargs) when List.non_empty iargs ->
          let gd' =
            ctx
            |> List.assoc Sym.equal fsym
            |> List.assoc (List.equal Sym.equal) (List.map fst iargs)
          in
          if gd'.recursive then
            gt
          else
            GT.subst (IT.make_subst iargs) (Option.get gd'.body)
        | _ -> gt
      in
      let gt = Option.get gd.body in
      let gt' = GT.map_gen_post aux gt in
      if GT.equal gt gt' then
        { gd with body = Some gt' }
      else
        loop (Option.map (fun x -> x - 1) fuel) { gd with body = Some gt' })
  in
  let unfolds = TestGenConfig.get_max_unfolds () in
  ctx
  |> List.map_snd (List.map_snd (loop unfolds))
  |> List.filter_map (fun (x, gds) ->
    if Option.is_some unfolds then
      Some (x, gds)
    else (
      match List.filter (fun ((_, gd) : _ * GD.t) -> gd.spec || gd.recursive) gds with
      | [] -> None
      | gds' -> Some (x, gds')))


let inline (ctx : GD.context) : GD.context = unfold ctx
