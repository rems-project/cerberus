module IT = IndexTerms
module GT = GenTerms
module GD = GenDefinitions

let unfold (ctx : GD.context) : GD.context =
  let rec loop (fuel : int) (gd : GD.t) : GD.t =
    if fuel <= 0 then
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
      loop (fuel - 1) { gd with body = Some (GT.map_gen_post aux (Option.get gd.body)) })
  in
  List.map_snd (List.map_snd (loop (TestGenConfig.get_max_unfolds ()))) ctx


let inline (ctx : GD.context) : GD.context = unfold ctx
