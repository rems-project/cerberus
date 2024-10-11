module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GA = GenAnalysis
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

type opt_pass =
  { name : string;
    transform : GT.t -> GT.t
  }

(** This pass performs various inlinings *)
module Inline = struct
  (** This pass inlines generators that just return a constant or symbol *)
  module Returns = struct
    let name = "inline_return"

    let transform (gt : GT.t) : GT.t =
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _, here)) = gt in
        match gt_ with
        | Let (_, (x, GT (Return it, _, loc_ret)), gt') ->
          let (IT (t_, _, _)) = it in
          (match t_ with
           (* Terms to inline *)
           | Const _ | Sym _ -> GT.subst (IT.make_subst [ (x, it) ]) gt'
           (* Otherwise, at least avoid pointless backtracking *)
           | _ -> GT.let_ (0, (x, GT.return_ it loc_ret), gt') here)
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  (* This pass inlines terms used a single time *)
  module SingleUse = struct
    module GenTerms = struct
      let name = "inline_single_use_gen"

      let subst (x : Sym.t) (gt_repl : GT.t) (gt : GT.t) : GT.t =
        let aux (gt : GT.t) : GT.t =
          let (GT (gt_, _, _)) = gt in
          match gt_ with
          | Return (IT (Sym y, _, _)) when Sym.equal x y -> gt_repl
          | _ -> gt
        in
        GT.map_gen_post aux gt


      let of_symset (s : SymSet.t) : bool SymMap.t =
        s |> SymSet.to_seq |> Seq.map (fun x -> (x, false)) |> SymMap.of_seq


      let union = SymMap.union (fun _ a b -> Some (not (a || b)))

      let rec transform_aux (gt : GT.t) : GT.t * bool SymMap.t =
        let (GT (gt_, _, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ -> (gt, SymMap.empty)
        | Pick wgts ->
          let wgts, only_ret =
            wgts
            |> List.map_snd transform_aux
            |> List.map (fun (a, (b, c)) -> ((a, b), c))
            |> List.split
          in
          (GT.pick_ wgts loc, List.fold_left union SymMap.empty only_ret)
        | Alloc it -> (gt, it |> IT.free_vars |> of_symset)
        | Call (_fsym, xits) ->
          ( gt,
            xits
            |> List.map snd
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty )
        | Asgn ((it_addr, sct), it_val, gt') ->
          let only_ret =
            [ it_addr; it_val ]
            |> List.map IT.free_vars
            |> List.map of_symset
            |> List.fold_left union SymMap.empty
          in
          let gt', only_ret' = transform_aux gt' in
          (GT.asgn_ ((it_addr, sct), it_val, gt') loc, union only_ret only_ret')
        | Let (backtracks, (x, gt_inner), gt') ->
          let gt', only_ret = transform_aux gt' in
          let only_ret = SymMap.remove x only_ret in
          if Option.equal Bool.equal (SymMap.find_opt x only_ret) (Some true) then
            (subst x gt_inner gt', only_ret)
          else (
            let gt_inner, only_ret' = transform_aux gt_inner in
            (GT.let_ (backtracks, (x, gt_inner), gt') loc, union only_ret only_ret'))
        | Return it ->
          ( gt,
            (match IT.is_sym it with
             | Some (x, _bt) -> SymMap.singleton x true
             | None -> it |> IT.free_vars |> of_symset) )
        | Assert (lc, gt') ->
          let only_ret = lc |> LC.free_vars |> of_symset in
          let gt', only_ret' = transform_aux gt' in
          (GT.assert_ (lc, gt') loc, union only_ret only_ret')
        | ITE (it_if, gt_then, gt_else) ->
          let only_ret = it_if |> IT.free_vars |> of_symset in
          let gt_then, only_ret' = transform_aux gt_then in
          let gt_else, only_ret'' = transform_aux gt_else in
          ( GT.ite_ (it_if, gt_then, gt_else) loc,
            [ only_ret; only_ret'; only_ret'' ] |> List.fold_left union SymMap.empty )
        | Map ((i, i_bt, it_perm), gt_inner) ->
          let only_ret = it_perm |> IT.free_vars |> SymSet.remove i |> of_symset in
          let gt_inner, only_ret' = transform_aux gt_inner in
          let only_ret' = only_ret' |> SymMap.remove i |> SymMap.map (fun _ -> false) in
          (GT.map_ ((i, i_bt, it_perm), gt_inner) loc, union only_ret only_ret')


      let transform (gt : GT.t) : GT.t = fst (transform_aux gt)

      let pass = { name; transform }
    end

    let passes = [ GenTerms.pass ]
  end

  let passes = Returns.pass :: SingleUse.passes
end

(** This pass breaks down constraints, so that
    other passes can optimize more *)
module SplitConstraints = struct
  module Conjunction = struct
    let name = "split_conjunction"

    let rec cnf_ (e : BT.t IT.term) : BT.t IT.term =
      match e with
      (* Double negation elimination *)
      | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) -> e
      (* Flip inequalities *)
      | Unop (Not, IT (Binop (LT, e1, e2), _, _)) -> Binop (LE, e2, e1)
      | Unop (Not, IT (Binop (LE, e1, e2), _, _)) -> Binop (LT, e2, e1)
      (* De Morgan's Law *)
      | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
        Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
      | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
        Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
      (* Distribute disjunction *)
      | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
      | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
        Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
      | _ -> e


    and cnf (e : IT.t) : IT.t =
      let (IT (e, info, loc)) = e in
      IT (cnf_ e, info, loc)


    let listify_constraints (it : IT.t) : IT.t list =
      let rec loop (c : IT.t) : IT.t list =
        match c with IT (Binop (And, e1, e2), _, _) -> loop e1 @ loop e2 | _ -> [ c ]
      in
      loop it


    let transform (gt : GT.t) : GT.t =
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Assert (T it, gt') ->
          it
          |> cnf
          |> listify_constraints
          |> List.fold_left (fun gt_rest it' -> GT.assert_ (LC.T it', gt_rest) loc) gt'
        | Assert (Forall ((i_sym, i_bt), it), gt') ->
          let its_in, its_out =
            it
            |> cnf
            |> listify_constraints
            |> List.partition (fun it' -> SymSet.mem i_sym (IT.free_vars it'))
          in
          let gt_forall =
            GT.assert_ (LC.Forall ((i_sym, i_bt), IT.and_ its_in loc), gt') loc
          in
          List.fold_left
            (fun gt_rest it' -> GT.assert_ (LC.T it', gt_rest) loc)
            gt_forall
            its_out
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  module Let = struct
    let name = "split_let"

    let transform (gt : GT.t) : GT.t =
      let aux (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Assert (T (IT (Let ((x, it_inner), it_rest), _, loc_let)), gt') ->
          GT.let_
            ( 0,
              (x, GT.return_ it_inner (IT.loc it_inner)),
              GT.assert_ (LC.T it_rest, gt') loc )
            loc_let
        | Assert (Forall ((_i_sym, _i_bt), IT (Let _, _, _)), _) ->
          (* TODO: Pull out lets that don't refer to `i_sym` *)
          gt
        | _ -> gt
      in
      GT.map_gen_pre aux gt


    let pass = { name; transform }
  end

  let passes = [ Conjunction.pass; Let.pass ]
end

(** This pass infers how much allocation is needed
    for each pointer given the current intraprocedural
    context *)
module InferAllocationSize = struct
  let name = "infer_alloc_size"

  let infer_size (vars : SymSet.t) (x : Sym.t) (gt : GT.t) : IT.t option =
    let merge loc oa ob =
      match (oa, ob) with
      | Some a, Some b -> Some (IT.max_ (a, b) loc)
      | Some a, _ | _, Some a -> Some a
      | None, None -> None
    in
    let rec aux (gt : GT.t) : IT.t option =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> None
      | Pick wgts ->
        wgts
        |> List.map snd
        |> List.map aux
        |> List.fold_left (merge (Locations.other __LOC__)) None
      | Asgn ((it_addr, sct), _it_val, gt') ->
        let oit_size =
          let (IT (_, _, loc)) = it_addr in
          let open Option in
          let@ psym, it_offset = GA.get_addr_offset_opt it_addr in
          if Sym.equal x psym && SymSet.subset (IT.free_vars it_offset) vars then
            return (IT.add_ (it_offset, IT.sizeOf_ sct loc) loc)
          else
            None
        in
        (merge (Locations.other __LOC__)) oit_size (aux gt')
      | Let (_, (y, gt_inner), gt') ->
        let oit = aux gt_inner in
        let gt' = if Sym.equal x y then snd (GT.alpha_rename_gen x gt') else gt' in
        (merge (Locations.other __LOC__)) oit (aux gt')
      | Assert (_, gt') -> aux gt'
      | ITE (_it_if, gt_then, gt_else) ->
        (merge (Locations.other __LOC__)) (aux gt_then) (aux gt_else)
      | Map ((i_sym, i_bt, it_perm), gt_inner) ->
        let j_sym, gt_inner =
          if Sym.equal x i_sym then GT.alpha_rename_gen x gt_inner else (i_sym, gt_inner)
        in
        let open Option in
        let@ it = aux gt_inner in
        if SymSet.mem j_sym (IT.free_vars it) then (
          let _, it_max = GA.get_bounds (i_sym, i_bt) it_perm in
          return (IT.subst (IT.make_subst [ (j_sym, it_max) ]) it))
        else
          return it
    in
    aux gt


  let transform (gd : GD.t) : GD.t =
    let rec aux (vars : SymSet.t) (gt : GT.t) : GT.t =
      let (GT (gt_, _bt, loc)) = gt in
      match gt_ with
      | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
      | Pick wgts -> GT.pick_ (List.map_snd (aux vars) wgts) loc
      | Asgn ((it_addr, sct), it_val, gt_rest) ->
        GT.asgn_ ((it_addr, sct), it_val, aux vars gt_rest) loc
      | Let (backtracks, (x, (GT (Alloc it_size, _bt, loc_alloc) as gt_inner)), gt_rest)
        ->
        let gt_rest = aux (SymSet.add x vars) gt_rest in
        (match infer_size vars x gt_rest with
         | Some it_size' ->
           let here = Locations.other __LOC__ in
           GT.let_
             ( backtracks,
               (x, GT.alloc_ (IT.max_ (it_size, it_size') here) loc_alloc),
               gt_rest )
             loc
         | None ->
           GT.let_
             (backtracks, (x, aux vars gt_inner), aux (SymSet.add x vars) gt_rest)
             loc)
      | Let (backtracks, (x, gt_inner), gt_rest) ->
        GT.let_ (backtracks, (x, aux vars gt_inner), aux (SymSet.add x vars) gt_rest) loc
      | Assert (lc, gt_rest) -> GT.assert_ (lc, aux vars gt_rest) loc
      | ITE (it_if, gt_then, gt_else) ->
        GT.ite_ (it_if, aux vars gt_then, aux vars gt_else) loc
      | Map ((i_sym, i_bt, it_perm), gt_inner) ->
        GT.map_ ((i_sym, i_bt, it_perm), aux (SymSet.add i_sym vars) gt_inner) loc
    in
    let body =
      Some (aux (gd.iargs |> List.map fst |> SymSet.of_list) (Option.get gd.body))
    in
    { gd with body }
end

(** This pass uses [Simplify] to rewrite [IndexTerms.t] *)
module TermSimplification = struct
  let name = "simplify_term"

  let transform (prog5 : unit Mucore.file) (gt : GT.t) : GT.t =
    let globals =
      { Global.empty with
        logical_functions = SymMap.of_seq (List.to_seq prog5.logical_predicates)
      }
    in
    let simp_it (it : IT.t) : IT.t =
      Simplify.IndexTerms.simp ~inline_functions:true (Simplify.default globals) it
    in
    let simp_lc (lc : LC.t) : LC.t =
      Simplify.LogicalConstraints.simp
        ~inline_functions:true
        (Simplify.default globals)
        lc
    in
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, bt, loc)) = gt in
      match gt_ with
      | Alloc it -> GT.alloc_ (simp_it it) loc
      | Call (fsym, iargs) -> GT.call_ (fsym, List.map_snd simp_it iargs) bt loc
      | Asgn ((it_addr, sct), it_val, gt') ->
        GT.asgn_ ((simp_it it_addr, sct), simp_it it_val, gt') loc
      | Return it -> GT.return_ (simp_it it) loc
      | Assert (lc, gt') -> GT.assert_ (simp_lc lc, gt') loc
      | Map ((i, i_bt, it_perm), gt') -> GT.map_ ((i, i_bt, simp_it it_perm), gt') loc
      | _ -> gt
    in
    GT.map_gen_pre aux gt


  let pass (prog5 : unit Mucore.file) = { name; transform = transform prog5 }
end

(** This pass removes unused variables *)
module RemoveUnused = struct
  let name = "remove_unused"

  let transform (gt : GT.t) : GT.t =
    let aux (gt : GT.t) : GT.t =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Let (_, (x, gt1), gt2)
        when GA.is_pure gt1 && not (SymSet.mem x (GT.free_vars gt2)) ->
        gt2
      | _ -> gt
    in
    GT.map_gen_post aux gt


  let passes = [ { name; transform } ]
end

let all_passes (prog5 : unit Mucore.file) =
  Inline.passes
  @ RemoveUnused.passes
  @ [ TermSimplification.pass prog5 ]
  @ SplitConstraints.passes


let optimize_gen (prog5 : unit Mucore.file) (passes : StringSet.t) (gt : GT.t) : GT.t =
  let passes =
    all_passes prog5
    |> List.filter_map (fun { name; transform } ->
      if StringSet.mem name passes then Some transform else None)
  in
  let opt (gt : GT.t) : GT.t = List.fold_left (fun gt pass -> pass gt) gt passes in
  let rec loop (fuel : int) (gt : GT.t) : GT.t =
    if fuel <= 0 then
      gt
    else (
      let old_gt = gt in
      let new_gt = opt gt in
      if GT.equal old_gt new_gt then new_gt else loop (fuel - 1) new_gt)
  in
  gt |> loop 5


let optimize_gen_def
  (prog5 : unit Mucore.file)
  (passes : StringSet.t)
  ({ name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { name; iargs; oargs; body = Option.map (optimize_gen prog5 passes) body }
  |> InferAllocationSize.transform


let optimize
  (prog5 : unit Mucore.file)
  ?(passes : StringSet.t option = None)
  (ctx : GD.context)
  : GD.context
  =
  let default = all_passes prog5 |> List.map (fun p -> p.name) |> StringSet.of_list in
  let passes = Option.value ~default passes in
  List.map_snd (List.map_snd (optimize_gen_def prog5 passes)) ctx
