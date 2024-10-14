module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GS = GenStatements
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
           | Const _ | Sym _ | Cast (_, IT (Const _, _, _)) | Cast (_, IT (Sym _, _, _))
             ->
             GT.subst (IT.make_subst [ (x, it) ]) gt'
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

(** This pass pulls asserts and assignments
    closer to the relevant variables *)
module Reordering = struct
  let name = "reordering"

  let get_statement_ordering (iargs : SymSet.t) (stmts : GS.t list) : GS.t list =
    let rec loop ((vars, res, stmts) : SymSet.t * GS.t list * GS.t list)
      : SymSet.t * GS.t list
      =
      if List.is_empty stmts then
        (vars, res)
      else (
        let res', stmts =
          List.partition
            (fun (stmt : GS.t) ->
              match stmt with
              | Asgn ((it_addr, _sct), it_val) ->
                SymSet.subset (IT.free_vars_list [ it_addr; it_val ]) vars
              | Assert lc -> SymSet.subset (LC.free_vars lc) vars
              | _ -> false)
            stmts
        in
        let res = res @ res' in
        let vars, res, stmts =
          match stmts with
          | (Let (_, (var, _)) as stmt) :: stmts' ->
            (SymSet.add var vars, res @ [ stmt ], stmts')
          | stmt :: _ -> failwith (Pp.plain (GS.pp stmt) ^ " @ " ^ __LOC__)
          | [] -> (vars, res, [])
        in
        loop (vars, res, stmts))
    in
    let _, res = loop (iargs, [], stmts) in
    res


  let reorder (iargs : SymSet.t) (gt : GT.t) : GT.t =
    let stmts, gt_last = GS.stmts_of_gt gt in
    let stmts = get_statement_ordering iargs stmts in
    GS.gt_of_stmts stmts gt_last


  let transform (gd : GD.t) : GD.t =
    let rec aux (iargs : SymSet.t) (gt : GT.t) : GT.t =
      let rec loop (iargs : SymSet.t) (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
        | Pick wgts -> GT.pick_ (List.map_snd (aux iargs) wgts) loc
        | Asgn ((it_addr, sct), it_val, gt_rest) ->
          GT.asgn_ ((it_addr, sct), it_val, loop iargs gt_rest) loc
        | Let (backtracks, (x, gt'), gt_rest) ->
          let iargs = SymSet.add x iargs in
          GT.let_ (backtracks, (x, (aux iargs) gt'), loop iargs gt_rest) loc
        | Assert (lc, gt_rest) -> GT.assert_ (lc, loop iargs gt_rest) loc
        | ITE (it_if, gt_then, gt_else) ->
          GT.ite_ (it_if, aux iargs gt_then, aux iargs gt_else) loc
        | Map ((i_sym, i_bt, it_perm), gt_inner) ->
          GT.map_ ((i_sym, i_bt, it_perm), aux (SymSet.add i_sym iargs) gt_inner) loc
      in
      gt |> reorder iargs |> loop iargs
    in
    let iargs = gd.iargs |> List.map fst |> SymSet.of_list in
    { gd with body = Some (aux iargs (Option.get gd.body)) }
end

module ConstraintPropagation = struct
  open Interval

  module IntRep = struct
    type t =
      { mult : Z.t;
        intervals : Intervals.t
      }
    [@@deriving eq, ord]

    let of_ (mult : Z.t) (intervals : Intervals.t) : t =
      let intervals =
        let open Z in
        let min = Option.get (Intervals.minimum intervals) in
        let min' = min / mult * mult in
        let max' = Z.succ (Option.get (Intervals.maximum intervals)) in
        let max =
          ((max' / mult) + if Z.equal (max' mod mult) Z.zero then Z.zero else Z.one)
          * mult
        in
        let mult_interval = Interval.range (Z.max min min') (Z.min max max') in
        Intervals.intersect (Intervals.of_interval mult_interval) intervals
      in
      { mult; intervals }


    let rec of_bt (bt : BT.t) : t option =
      match bt with
      | Loc () -> of_bt Memory.uintptr_bt
      | Bits (sgn, bits) ->
        let to_interval =
          match sgn with Signed -> Interval.sint | Unsigned -> Interval.uint
        in
        let interval = to_interval bits in
        Some (of_ Z.one (Intervals.of_interval interval))
      | _ -> None


    let of_mult (mult : Z.t) : t =
      { mult; intervals = Intervals.of_interval Interval.int }


    let of_intervals (intervals : Intervals.t) : t = { mult = Z.one; intervals }

    let of_interval (interval : Interval.t) : t =
      of_intervals (Intervals.of_interval interval)


    let const (n : Z.t) : t = of_interval (Interval.const n)

    let ne (n : Z.t) : t =
      of_intervals (Intervals.complement (Intervals.of_interval (Interval.const n)))


    let lt (n : Z.t) : t = of_interval (Interval.lt n)

    let leq (n : Z.t) : t = of_interval (Interval.leq n)

    let gt (n : Z.t) : t = of_interval (Interval.gt n)

    let geq (n : Z.t) : t = of_interval (Interval.geq n)

    let intersect ({ mult = m1; intervals = i1 } : t) ({ mult = m2; intervals = i2 } : t)
      : t
      =
      let mult = Z.lcm m1 m2 in
      let intervals = Intervals.intersect i1 i2 in
      of_ mult intervals


    let is_const (r : t) : Z.t option = Intervals.is_const r.intervals

    let minimum (r : t) : Z.t = Option.get (Intervals.minimum r.intervals)

    let maximum (r : t) : Z.t = Option.get (Intervals.maximum r.intervals)
  end

  module Domain = struct
    type t = Int of IntRep.t [@@deriving eq, ord]

    let hash = Hashtbl.hash

    let rec of_it (it : IT.t) : (bool * (Sym.t * t)) option =
      let (IT (it_, _, _)) = it in
      let open Option in
      match it_ with
      | Binop (op, IT (Sym x, x_bt, _), IT (Const (Bits (_, n)), _, _)) ->
        let@ bt_rep = IntRep.of_bt x_bt in
        (match op with
         | EQ -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.const n))))
         | LT -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.lt n))))
         | LE -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.leq n))))
         | _ -> None)
      | Binop (op, IT (Const (Bits (_, n)), _, _), IT (Sym x, x_bt, _)) ->
        let@ bt_rep = IntRep.of_bt x_bt in
        (match op with
         | EQ -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.const n))))
         | LT -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.gt n))))
         | LE -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.geq n))))
         | _ -> None)
      | Binop
          ( op,
            IT (Const (Bits (_, n)), _, _),
            IT (Binop (Add, IT (Sym x, x_bt, _), IT (Const (Bits (_, m)), _, _)), _, _) )
      | Binop
          ( op,
            IT (Const (Bits (_, n)), _, _),
            IT (Binop (Add, IT (Const (Bits (_, m)), _, _), IT (Sym x, x_bt, _)), _, _) )
        when Z.equal m Z.one ->
        let@ bt_rep = IntRep.of_bt x_bt in
        (match op with
         | LT -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.geq n))))
         | _ -> None)
      | Binop
          ( op,
            IT (Binop (Sub, IT (Sym x, x_bt, _), IT (Const (Bits (_, m)), _, _)), _, _),
            IT (Const (Bits (_, n)), _, _) )
        when Z.equal m Z.one ->
        let@ bt_rep = IntRep.of_bt x_bt in
        (match op with
         | LT -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.leq n))))
         | _ -> None)
      | Binop
          ( op,
            IT (Const (Bits (_, n)), _, _),
            IT (Binop (Sub, IT (Sym x, x_bt, _), IT (Const (Bits (_, m)), _, _)), _, _) )
        when Z.equal m Z.one ->
        let@ bt_rep = IntRep.of_bt x_bt in
        (match op with
         | LE -> Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.gt n))))
         | _ -> None)
      | Binop
          ( op,
            IT (Binop (Add, IT (Sym x, bt, _), IT (Sym y, _, _)), _, _),
            IT (Const (Bits (_, n)), _, _) )
      | Binop
          ( op,
            IT
              ( Binop
                  ( Add,
                    IT (Cast (_, IT (Sym x, bt, _)), _, _),
                    IT (Cast (_, IT (Sym y, _, _)), _, _) ),
                _,
                _ ),
            IT (Const (Bits (_, n)), _, _) )
        when Sym.equal x y ->
        let loc = Locations.other __LOC__ in
        (match op with
         | EQ | LT | LE ->
           of_it
             (IT.arith_binop
                op
                (IT.sym_ (x, bt, loc), IT.num_lit_ (Z.div n (Z.of_int 2)) bt loc)
                loc)
         | _ -> None)
        (* START FIXME: Simplify should do this *)
      | Binop
          ( op,
            IT (Const (Bits (_, n)), bt, _),
            IT (Binop (Sub, it', IT (Const (Bits (_, m)), _, _)), _, _) ) ->
        let loc = Locations.other __LOC__ in
        (match op with
         | EQ | LT | LE ->
           of_it (IT.arith_binop op (IT.num_lit_ (Z.add n m) bt loc, it') loc)
         | _ -> None)
      | Binop
          ( op,
            IT (Const (Bits (_, n)), bt, _),
            IT (Binop (Add, it', IT (Const (Bits (_, m)), _, _)), _, _) ) ->
        let loc = Locations.other __LOC__ in
        (match op with
         | EQ | LT | LE ->
           of_it (IT.arith_binop op (IT.num_lit_ (Z.sub n m) bt loc, it') loc)
         | _ -> None)
      | Binop
          ( op,
            IT (Binop (Sub, it', IT (Const (Bits (_, m)), _, _)), _, _),
            IT (Const (Bits (_, n)), bt, _) ) ->
        let loc = Locations.other __LOC__ in
        (match op with
         | EQ | LT | LE ->
           of_it (IT.arith_binop op (it', IT.num_lit_ (Z.add n m) bt loc) loc)
         | _ -> None)
      | Binop
          ( op,
            IT (Binop (Add, it', IT (Const (Bits (_, m)), _, _)), _, _),
            IT (Const (Bits (_, n)), bt, _) ) ->
        let loc = Locations.other __LOC__ in
        (match op with
         | EQ | LT | LE ->
           of_it (IT.arith_binop op (it', IT.num_lit_ (Z.sub n m) bt loc) loc)
         | _ -> None)
        (* END Simplify stuff*)
      | Unop
          (Not, IT (Binop (EQ, IT (Sym x, x_bt, _), IT (Const (Bits (_, n)), _, _)), _, _))
      | Unop
          (Not, IT (Binop (EQ, IT (Const (Bits (_, n)), _, _), IT (Sym x, x_bt, _)), _, _))
        ->
        let@ bt_rep = IntRep.of_bt x_bt in
        Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.ne n))))
      | Binop
          ( EQ,
            IT (Binop (Mod, IT (Sym x, x_bt, _), IT (Const (Bits (_, n)), _, _)), _, _),
            IT (Const (Bits (_, m)), _, _) )
      | Binop
          ( EQ,
            IT (Const (Bits (_, m)), _, _),
            IT (Binop (Mod, IT (Sym x, x_bt, _), IT (Const (Bits (_, n)), _, _)), _, _) )
        when Z.equal m Z.zero ->
        let@ bt_rep = IntRep.of_bt x_bt in
        Some (true, (x, Int (IntRep.intersect bt_rep (IntRep.of_mult n))))
      | _ -> None


    let intersect (Int r1) (Int r2) : t = Int (IntRep.intersect r1 r2)

    let is_const (Int r) = IntRep.is_const r

    let to_stmts (x : Sym.t) (bt : BT.t) (Int r : t) : GS.t list =
      let aux (sgn : BT.sign) (sz : int) : GS.t list =
        let loc = Locations.other __LOC__ in
        let min_bt, max_bt = BT.bits_range (sgn, sz) in
        let min, max = (IntRep.minimum r, IntRep.maximum r) in
        let stmt_min =
          if Z.lt min_bt min then
            [ GS.Assert (LC.T (IT.le_ (IT.num_lit_ min bt loc, IT.sym_ (x, bt, loc)) loc))
            ]
          else
            []
        in
        let stmt_max =
          if Z.lt max max_bt then
            [ GS.Assert (LC.T (IT.le_ (IT.sym_ (x, bt, loc), IT.num_lit_ max bt loc) loc))
            ]
          else
            []
        in
        let stmt_mult =
          if Z.equal r.mult Z.one then
            []
          else
            [ GS.Assert
                (LC.T
                   (IT.eq_
                      ( IT.mod_ (IT.sym_ (x, bt, loc), IT.num_lit_ r.mult bt loc) loc,
                        IT.num_lit_ Z.zero bt loc )
                      loc))
            ]
        in
        stmt_min @ stmt_max @ stmt_mult
      in
      match bt with
      | Loc () ->
        let sgn, sz = Option.get (BT.is_bits_bt Memory.uintptr_bt) in
        aux sgn sz
      | Bits (sgn, sz) -> aux sgn sz
      | _ -> failwith (Pp.plain (BT.pp bt) ^ " @ " ^ __LOC__)
  end

  module Constraint = struct
    type t =
      | Eq
      | Ne
      | Lt
      | Le
      | Invalid
    [@@deriving eq, ord]

    let default = Invalid

    let of_it (it : IT.t) : (Sym.t * t * Sym.t) option =
      let (IT (it_, _, _)) = it in
      match it_ with
      | Binop (op, IT (Sym x, _, _), IT (Sym y, _, _)) ->
        (match op with
         | EQ -> Some (x, Eq, y)
         | LT -> Some (x, Lt, y)
         | LE -> Some (x, Le, y)
         | _ -> None)
      | Binop
          ( op,
            IT (Sym x, _, _),
            IT (Binop (Add, IT (Sym y, _, _), IT (Const (Bits (_, n)), _, _)), _, _) )
      | Binop
          ( op,
            IT (Sym x, _, _),
            IT (Binop (Add, IT (Const (Bits (_, n)), _, _), IT (Sym y, _, _)), _, _) ) ->
        (match op with
         | LT -> if Z.equal n Z.one then Some (x, Le, y) else None
         | _ -> None)
      | Binop
          ( op,
            IT (Binop (Sub, IT (Sym x, _, _), IT (Const (Bits (_, n)), _, _)), _, _),
            IT (Sym y, _, _) ) ->
        (match op with
         | LT -> if Z.equal n Z.one then Some (x, Le, y) else None
         | _ -> None)
      | Unop (Not, IT (Binop (EQ, IT (Sym x, _, _), IT (Sym y, _, _)), _, _)) ->
        Some (x, Ne, y)
      | _ -> None


    let intersect (c1 : t) (c2 : t) : t option =
      match (c1, c2) with
      | Eq, Eq | Ne, Ne | Lt, Lt | Le, Le -> Some c1
      | Eq, Le | Le, Eq -> Some Eq
      | Lt, Le | Le, Lt | Lt, Ne | Ne, Lt -> Some Lt
      | Eq, Ne | Ne, Eq | Eq, Lt | Lt, Eq | Le, Ne | Ne, Le | Invalid, _ | _, Invalid ->
        None
  end

  module ConstraintNetwork = struct
    open struct
      module G = Graph.Persistent.Digraph.ConcreteLabeled (Sym) (Constraint)
    end

    type t = Domain.t SymMap.t * G.t

    let empty = (SymMap.empty, G.empty)

    let variables ((ds, _) : t) : Domain.t SymMap.t = ds

    let constraints ((_, g) : t) : (Sym.t * Constraint.t * Sym.t) list =
      G.fold_edges_e (fun edge edges -> edge :: edges) g []


    let add_variable (x : Sym.t) (d : Domain.t) ((ds, g) : t) : t =
      ( SymMap.update
          x
          (fun od ->
            match od with Some d' -> Some (Domain.intersect d d') | None -> Some d)
          ds,
        G.add_vertex g x )


    let add_constraint (c : Constraint.t) (x : Sym.t) (y : Sym.t) ((ds, g) : t) : t =
      let g =
        match G.find_all_edges g x y with
        | [ (x', c', y') ] ->
          G.add_edge_e
            (G.remove_edge_e g (x', c', y'))
            (x, Option.get (Constraint.intersect c c'), y)
        | [] -> G.add_edge_e g (x, c, y)
        | _ -> failwith __LOC__
      in
      (ds, g)


    let domain (x : Sym.t) ((ds, _) : t) : Domain.t = SymMap.find x ds

    let domain_opt (x : Sym.t) ((ds, _) : t) : Domain.t option = SymMap.find_opt x ds

    let related_constraints ((_, g) : t) (x : Sym.t) : (Sym.t * Constraint.t * Sym.t) list
      =
      G.fold_edges_e
        (fun (y, c, z) acc ->
          if Sym.equal x y || Sym.equal x z then (y, c, z) :: acc else acc)
        g
        []
  end

  let construct_network (stmts : GS.t list) : GS.t list * ConstraintNetwork.t =
    let rec aux (stmts : GS.t list) : GS.t list * ConstraintNetwork.t =
      match stmts with
      | (Asgn _ as stmt) :: stmts'
      | (Let _ as stmt) :: stmts'
      | (Assert (Forall _) as stmt) :: stmts' ->
        let stmts', network = aux stmts' in
        (stmt :: stmts', network)
      | (Assert (T it) as stmt) :: stmts' ->
        let stmts', network = aux stmts' in
        (match (Domain.of_it it, Constraint.of_it it) with
         | Some (redundant, (x, d)), None ->
           (* We don't include these constraints, as we will add refined ones later *)
           if redundant then
             (stmts', ConstraintNetwork.add_variable x d network)
           else
             (stmt :: stmts', ConstraintNetwork.add_variable x d network)
         | None, Some (x, c, y) ->
           let xbts = IT.free_vars_bts it in
           let network =
             ConstraintNetwork.add_variable
               x
               (Int (Option.get (IntRep.of_bt (SymMap.find x xbts))))
               network
           in
           let network =
             ConstraintNetwork.add_variable
               y
               (Int (Option.get (IntRep.of_bt (SymMap.find y xbts))))
               network
           in
           (stmt :: stmts', ConstraintNetwork.add_constraint c x y network)
         | None, None -> (stmt :: stmts', network)
         | Some _, Some _ -> failwith __LOC__)
      | [] -> ([], ConstraintNetwork.empty)
    in
    aux stmts


  let revise (c : Constraint.t) (Int r1 : Domain.t) (Int r2 : Domain.t)
    : Domain.t * Domain.t
    =
    match c with
    | Eq ->
      let r : Domain.t = Int (IntRep.intersect r1 r2) in
      (r, r)
    | Ne ->
      let r1' : Domain.t =
        match IntRep.is_const r2 with
        | Some n ->
          Int
            (IntRep.of_
               r1.mult
               (Intervals.intersect
                  r1.intervals
                  (Intervals.complement (Intervals.of_interval (Interval.const n)))))
        | None -> Int r1
      in
      let r2' : Domain.t =
        match IntRep.is_const r1 with
        | Some n ->
          Int
            (IntRep.of_
               r2.mult
               (Intervals.intersect
                  r2.intervals
                  (Intervals.complement (Intervals.of_interval (Interval.const n)))))
        | None -> Int r2
      in
      (r1', r2')
    | Lt ->
      let r1' : Domain.t = Int (IntRep.intersect r1 (IntRep.lt (IntRep.maximum r2))) in
      let r2' : Domain.t = Int (IntRep.intersect r2 (IntRep.geq (IntRep.minimum r1))) in
      (r1', r2')
    | Le ->
      let r1' : Domain.t = Int (IntRep.intersect r1 (IntRep.leq (IntRep.maximum r2))) in
      let r2' : Domain.t = Int (IntRep.intersect r2 (IntRep.gt (IntRep.minimum r1))) in
      (r1', r2')
    | Invalid -> failwith __LOC__


  (** AC-3 from https://doi.org/10.1016/0004-3702(77)90007-8 *)
  let ac3 (network : ConstraintNetwork.t) : ConstraintNetwork.t =
    let rec aux
      (network : ConstraintNetwork.t)
      (worklist : (Sym.t * Constraint.t * Sym.t) list)
      : ConstraintNetwork.t
      =
      match worklist with
      | (x, c, y) :: worklist' ->
        let d1 = ConstraintNetwork.domain x network in
        let d2 = ConstraintNetwork.domain y network in
        let d1', d2' = revise c d1 d2 in
        let queue1 =
          if Domain.equal d1 d1' then
            []
          else
            x
            |> ConstraintNetwork.related_constraints network
            |> List.filter (fun (a, _, b) -> not (Sym.equal a y || Sym.equal b y))
        in
        let queue2 =
          if Domain.equal d2 d2' then
            []
          else
            y
            |> ConstraintNetwork.related_constraints network
            |> List.filter (fun (a, _, b) -> not (Sym.equal a y || Sym.equal b y))
        in
        aux
          (ConstraintNetwork.add_variable
             x
             d1'
             (ConstraintNetwork.add_variable y d2' network))
          (queue1 @ queue2 @ worklist')
      | [] -> network
    in
    aux network (ConstraintNetwork.constraints network)


  (** Adds new asserts encoding the domain information *)
  let add_refined_asserts
    (iargs : BT.t SymMap.t)
    (network : ConstraintNetwork.t)
    (stmts : GS.t list)
    : GS.t list
    =
    let rec aux (ds : Domain.t SymMap.t) (stmts : GS.t list) : GS.t list =
      match stmts with
      | (Let (_, (x, gt)) as stmt) :: stmts' when SymMap.mem x ds ->
        (stmt :: Domain.to_stmts x (GT.bt gt) (SymMap.find x ds)) @ aux ds stmts'
      | (Asgn _ as stmt) :: stmts'
      | (Let _ as stmt) :: stmts'
      | (Assert _ as stmt) :: stmts' ->
        stmt :: aux ds stmts'
      | [] -> []
    in
    let ds = ConstraintNetwork.variables network in
    let ds_iargs, ds_rest = SymMap.partition (fun x _ -> SymMap.mem x iargs) ds in
    let stmts_iargs =
      SymMap.fold
        (fun x d acc -> Domain.to_stmts x (SymMap.find x iargs) d @ acc)
        ds_iargs
        []
    in
    stmts_iargs @ aux ds_rest stmts


  let propagate_constraints (iargs : BT.t SymMap.t) (gt : GT.t) : GT.t =
    let stmts, gt_last = GS.stmts_of_gt gt in
    let stmts, network = construct_network stmts in
    let network = ac3 network in
    let stmts = add_refined_asserts iargs network stmts in
    GS.gt_of_stmts stmts gt_last


  let transform (gd : GD.t) : GD.t =
    let rec aux (iargs : BT.t SymMap.t) (gt : GT.t) : GT.t =
      let rec loop (iargs : BT.t SymMap.t) (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
        | Pick wgts -> GT.pick_ (List.map_snd (aux iargs) wgts) loc
        | Asgn ((it_addr, sct), it_val, gt_rest) ->
          GT.asgn_ ((it_addr, sct), it_val, loop iargs gt_rest) loc
        | Let (backtracks, (x, gt'), gt_rest) ->
          GT.let_
            ( backtracks,
              (x, (aux iargs) gt'),
              loop (SymMap.add x (GT.bt gt') iargs) gt_rest )
            loc
        | Assert (lc, gt_rest) -> GT.assert_ (lc, loop iargs gt_rest) loc
        | ITE (it_if, gt_then, gt_else) ->
          GT.ite_ (it_if, aux iargs gt_then, aux iargs gt_else) loc
        | Map ((i_sym, i_bt, it_perm), gt_inner) ->
          GT.map_ ((i_sym, i_bt, it_perm), aux (SymMap.add i_sym i_bt iargs) gt_inner) loc
      in
      gt |> propagate_constraints iargs |> loop iargs
    in
    let iargs =
      gd.iargs
      |> List.map (fun (x, gbt) -> (x, GenBaseTypes.bt gbt))
      |> List.to_seq
      |> SymMap.of_seq
    in
    { gd with body = Some (aux iargs (Option.get gd.body)) }
end

module Specialization = struct
  module Rep = struct
    type t =
      { mult : IT.t option;
        min : IT.t option;
        max : IT.t option
      }

    let of_mult (it : IT.t) : t = { mult = Some it; min = None; max = None }

    let of_min (it : IT.t) : t = { mult = None; min = Some it; max = None }

    let of_max (it : IT.t) : t = { mult = None; min = None; max = Some it }

    let of_it (x : Sym.t) (it : IT.t) : t option =
      let (IT (it_, _, _)) = it in
      match it_ with
      | Binop (LT, IT (Sym x', _, _), it') when Sym.equal x x' -> Some (of_max it')
      | Binop (LE, IT (Sym x', x_bt, _), it') when Sym.equal x x' ->
        let loc = Locations.other __LOC__ in
        Some (of_max (IT.add_ (it', IT.num_lit_ Z.one x_bt loc) loc))
      | Binop (LT, it', IT (Sym x', x_bt, _)) when Sym.equal x x' ->
        let loc = Locations.other __LOC__ in
        Some (of_min (IT.sub_ (it', IT.num_lit_ Z.one x_bt loc) loc))
      | Binop (LE, it', IT (Sym x', _, _)) when Sym.equal x x' -> Some (of_min it')
      | _ -> None


    let intersect
      ({ mult = mult1; min = min1; max = max1 } : t)
      ({ mult = mult2; min = min2; max = max2 } : t)
      : t
      =
      let mult =
        match (mult1, mult2) with
        | Some n, None | None, Some n -> Some n
        | None, None -> None
        | Some _, Some _ -> failwith __LOC__
      in
      let min =
        match (min1, min2) with
        | Some n1, Some n2 ->
          let loc = Locations.other __LOC__ in
          Some
            (Simplify.IndexTerms.simp
               (Simplify.default Global.empty)
               (IT.max_ (n1, n2) loc))
        | Some n, None | None, Some n -> Some n
        | None, None -> None
      in
      let max =
        match (max1, max2) with
        | Some n1, Some n2 ->
          let loc = Locations.other __LOC__ in
          Some
            (Simplify.IndexTerms.simp
               (Simplify.default Global.empty)
               (IT.min_ (n1, n2) loc))
        | Some n, None | None, Some n -> Some n
        | None, None -> None
      in
      { mult; min; max }
  end

  let collect_constraints (vars : SymSet.t) (x : Sym.t) (bt : BT.t) (stmts : GS.t list)
    : GS.t list * Rep.t
    =
    let rec aux (stmts : GS.t list) : GS.t list * Rep.t =
      match stmts with
      | (Assert (T it) as stmt) :: stmts' when SymSet.subset (IT.free_vars it) vars ->
        let stmts', r = aux stmts' in
        (match Rep.of_it x it with
         | Some r' -> (stmts', Rep.intersect r r')
         | None -> (stmt :: stmts', r))
      | stmt :: stmts' ->
        let stmts', v = aux stmts' in
        (stmt :: stmts', v)
      | [] ->
        (match bt with
         | Bits _ -> ([], { mult = None; min = None; max = None })
         | _ -> failwith __LOC__)
    in
    aux stmts


  let compile_constraints (v : Rep.t) (gt : GT.t) : GT.t =
    match gt with
    | GT (Uniform _, _, _) ->
      let loc = Locations.other __LOC__ in
      (match v with
       | { mult = None; min = None; max = None } -> gt
       | { mult = Some n; min = None; max = None } ->
         GenBuiltins.mult_gen n (GT.bt gt) loc
       | { mult = None; min = Some n; max = None } -> GenBuiltins.ge_gen n (GT.bt gt) loc
       | { mult = None; min = None; max = Some n } -> GenBuiltins.lt_gen n (GT.bt gt) loc
       | { mult = None; min = Some n1; max = Some n2 } ->
         GenBuiltins.range_gen n1 n2 (GT.bt gt) loc
       | { mult = Some n1; min = Some n2; max = None } ->
         GenBuiltins.mult_ge_gen n1 n2 (GT.bt gt) loc
       | { mult = Some n1; min = None; max = Some n2 } ->
         GenBuiltins.mult_lt_gen n1 n2 (GT.bt gt) loc
       | { mult = Some n1; min = Some n2; max = Some n3 } ->
         GenBuiltins.mult_range_gen n1 n2 n3 (GT.bt gt) loc)
    | GT (Alloc sz, _, _) ->
      let loc = Locations.other __LOC__ in
      (match v with
       | { mult = None; min = _; max = _ } -> gt
       | { mult = Some n; min = _; max = _ } -> GenBuiltins.aligned_alloc_gen n sz loc)
    | _ -> gt


  let specialize_stmts (vars : SymSet.t) (stmts : GS.t list) : GS.t list =
    let rec aux (vars : SymSet.t) (stmts : GS.t list) : GS.t list =
      match stmts with
      | Let (backtracks, (x, gt)) :: stmts' ->
        let vars = SymSet.add x vars in
        let stmts', gt =
          if Option.is_some (BT.is_bits_bt (GT.bt gt)) then (
            let stmts', v = collect_constraints vars x (GT.bt gt) stmts' in
            (stmts', compile_constraints v gt))
          else
            (stmts', gt)
        in
        Let (backtracks, (x, gt)) :: aux vars stmts'
      | stmt :: stmts' -> stmt :: aux vars stmts'
      | [] -> []
    in
    aux vars stmts


  let specialize (vars : SymSet.t) (gt : GT.t) : GT.t =
    let stmts, gt_last = GS.stmts_of_gt gt in
    let stmts = specialize_stmts vars stmts in
    GS.gt_of_stmts stmts gt_last


  let transform (gd : GD.t) : GD.t =
    let rec aux (vars : SymSet.t) (gt : GT.t) : GT.t =
      let rec loop (vars : SymSet.t) (gt : GT.t) : GT.t =
        let (GT (gt_, _bt, loc)) = gt in
        match gt_ with
        | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> gt
        | Pick wgts -> GT.pick_ (List.map_snd (aux vars) wgts) loc
        | Asgn ((it_addr, sct), it_val, gt_rest) ->
          GT.asgn_ ((it_addr, sct), it_val, loop vars gt_rest) loc
        | Let (backtracks, (x, gt'), gt_rest) ->
          GT.let_ (backtracks, (x, (aux vars) gt'), loop (SymSet.add x vars) gt_rest) loc
        | Assert (lc, gt_rest) -> GT.assert_ (lc, loop vars gt_rest) loc
        | ITE (it_if, gt_then, gt_else) ->
          GT.ite_ (it_if, aux vars gt_then, aux vars gt_else) loc
        | Map ((i_sym, i_bt, it_perm), gt_inner) ->
          GT.map_ ((i_sym, i_bt, it_perm), aux (SymSet.add i_sym vars) gt_inner) loc
      in
      gt |> specialize vars |> loop vars
    in
    let iargs = gd.iargs |> List.map fst |> SymSet.of_list in
    { gd with body = Some (aux iargs (Option.get gd.body)) }
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
  ({ filename; recursive; name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { filename;
    recursive;
    name;
    iargs;
    oargs;
    body = Option.map (optimize_gen prog5 passes) body
  }
  |> ConstraintPropagation.transform
  |> Specialization.transform
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
