module CF = Cerb_frontend
module BT = BaseTypes
module IT = IndexTerms
module Req = Request
module LC = LogicalConstraints
module RP = ResourcePredicates
module LAT = LogicalArgumentTypes
module GT = GenTerms
module GD = GenDefinitions

let rec is_pure (gt : GT.t) : bool =
  let (GT (gt_, _, _)) = gt in
  match gt_ with
  | Arbitrary | Uniform _ -> true
  | Pick wgts -> wgts |> List.map snd |> List.for_all is_pure
  | Alloc _ -> false
  | Call _ -> false (* Could be less conservative... *)
  | Asgn _ -> false
  | Let (_, (_, gt1), gt2) -> is_pure gt1 && is_pure gt2
  | Return _ -> true
  | Assert _ -> false
  | ITE (_, gt_then, gt_else) -> is_pure gt_then && is_pure gt_else
  | Map _ -> false


let get_single_uses ?(pure : bool = false) (gt : GT.t) : Sym.Set.t =
  let union =
    Sym.Map.union (fun _ oa ob ->
      Some
        (let open Option in
         let@ a = oa in
         let@ b = ob in
         return (a + b)))
  in
  let it_value : int option = if pure then Some 1 else None in
  let aux_it (it : IT.t) : int option Sym.Map.t =
    it
    |> IT.free_vars
    |> Sym.Set.to_seq
    |> Seq.map (fun x -> (x, it_value))
    |> Sym.Map.of_seq
  in
  let aux_lc (lc : LC.t) : int option Sym.Map.t =
    lc
    |> LC.free_vars
    |> Sym.Set.to_seq
    |> Seq.map (fun x -> (x, it_value))
    |> Sym.Map.of_seq
  in
  let rec aux (gt : GT.t) : int option Sym.Map.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ -> Sym.Map.empty
    | Pick wgts ->
      wgts |> List.map snd |> List.map aux |> List.fold_left union Sym.Map.empty
    | Alloc it | Return it -> aux_it it
    | Call (_, iargs) ->
      iargs |> List.map snd |> List.map aux_it |> List.fold_left union Sym.Map.empty
    | Asgn ((it_addr, _), it_val, gt') ->
      aux gt' :: List.map aux_it [ it_addr; it_val ] |> List.fold_left union Sym.Map.empty
    | Let (_, (x, gt1), gt2) -> Sym.Map.remove x (union (aux gt1) (aux gt2))
    | Assert (lc, gt') -> union (aux gt') (aux_lc lc)
    | ITE (it_if, gt_then, gt_else) ->
      aux_it it_if :: List.map aux [ gt_then; gt_else ]
      |> List.fold_left union Sym.Map.empty
    | Map ((i, _, it_perm), gt') ->
      union
        (aux_it it_perm)
        (gt' |> aux |> Sym.Map.remove i |> Sym.Map.map (Option.map (Int.add 1)))
  in
  aux gt
  |> Sym.Map.filter (fun _ -> Option.equal Int.equal (Some 1))
  |> Sym.Map.bindings
  |> List.map fst
  |> Sym.Set.of_list


module Bounds = struct
  let get_lower_bound ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t =
    let min =
      match bt with
      | Bits (sign, sz) -> fst (BT.bits_range (sign, sz))
      | _ -> failwith "unsupported type for `each`"
    in
    let rec aux (it : IT.t) : IT.t option =
      match it with
      | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
      | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
        if Sym.equal x x' then Some tm2 else None
      | IT (Binop (LE, it', IT (Sym x', _, _)), _, _) when Sym.equal x x' -> Some it'
      | IT (Binop (LT, it', IT (Sym x', _, _)), _, _) when Sym.equal x x' ->
        Some
          (IT
             ( Binop (Add, it', IT.num_lit_ Z.one bt Cerb_location.unknown),
               bt,
               Cerb_location.unknown ))
      | IT (Binop (And, tm1, tm2), _, _) ->
        (match (aux tm1, aux tm2) with
         | None, None -> None
         | None, it' | it', None -> it'
         | Some tm1, Some tm2 ->
           Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
      | IT (Binop (Or, tm1, tm2), _, _) ->
        (match (aux tm1, aux tm2) with
         | None, None | None, _ | _, None -> None
         | Some tm1, Some tm2 ->
           Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
      | _ -> None
    in
    aux it |> Option.value ~default:(IT.num_lit_ min bt Cerb_location.unknown)


  let get_upper_bound ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t =
    let max =
      match bt with
      | Bits (sign, sz) -> snd (BT.bits_range (sign, sz))
      | _ -> failwith "unsupported type for `each`"
    in
    let rec aux (it : IT.t) : IT.t option =
      match it with
      | IT (Binop (EQ, IT (Sym x', _, _), tm2), _, _)
      | IT (Binop (EQ, tm2, IT (Sym x', _, _)), _, _) ->
        if Sym.equal x x' then Some tm2 else None
      | IT (Binop (LE, IT (Sym x', _, _), it'), _, _) when Sym.equal x x' -> Some it'
      | IT (Binop (LT, IT (Sym x', _, _), it'), _, _) when Sym.equal x x' ->
        Some
          (IT
             ( Binop (Sub, it', IT.num_lit_ Z.one bt Cerb_location.unknown),
               bt,
               Cerb_location.unknown ))
      | IT (Binop (And, tm1, tm2), _, _) ->
        (match (aux tm1, aux tm2) with
         | None, None -> None
         | None, it' | it', None -> it'
         | Some tm1, Some tm2 ->
           Some (IT (Binop (Min, tm1, tm2), bt, Cerb_location.unknown)))
      | IT (Binop (Or, tm1, tm2), _, _) ->
        (match (aux tm1, aux tm2) with
         | None, None | None, _ | _, None -> None
         | Some tm1, Some tm2 ->
           Some (IT (Binop (Max, tm1, tm2), bt, Cerb_location.unknown)))
      | _ -> None
    in
    aux it |> Option.value ~default:(IT.num_lit_ max bt Cerb_location.unknown)


  let get_bounds ((x, bt) : Sym.sym * BT.t) (it : IT.t) : IT.t * IT.t =
    (get_lower_bound (x, bt) it, get_upper_bound (x, bt) it)
end

let get_bounds = Bounds.get_bounds

let get_recursive_preds (preds : (Sym.t * RP.Definition.t) list) : Sym.Set.t =
  let get_calls (pred : RP.Definition.t) : Sym.Set.t =
    pred.clauses
    |> Option.get
    |> List.map (fun (cl : RP.Clause.t) -> cl.packing_ft)
    |> List.map LAT.r_resource_requests
    |> List.flatten
    |> List.map snd
    |> List.map fst
    |> List.map Req.get_name
    |> List.filter_map (fun (n : Req.name) ->
      match n with PName name -> Some name | Owned _ -> None)
    |> Sym.Set.of_list
  in
  let module G = Graph.Persistent.Digraph.Concrete (Sym) in
  let g =
    List.fold_left
      (fun g (fsym, pred) ->
        Sym.Set.fold (fun gsym g' -> G.add_edge g' fsym gsym) (get_calls pred) g)
      G.empty
      preds
  in
  let module Oper = Graph.Oper.P (G) in
  let closure = Oper.transitive_closure g in
  preds
  |> List.map fst
  |> List.filter (fun fsym -> G.mem_edge closure fsym fsym)
  |> Sym.Set.of_list


module SymGraph = Graph.Persistent.Digraph.Concrete (Sym)

open struct
  let get_calls (gd : GD.t) : Sym.Set.t =
    let rec aux (gt : GT.t) : Sym.Set.t =
      let (GT (gt_, _, _)) = gt in
      match gt_ with
      | Arbitrary | Uniform _ | Alloc _ | Return _ -> Sym.Set.empty
      | Pick wgts ->
        wgts |> List.map snd |> List.map aux |> List.fold_left Sym.Set.union Sym.Set.empty
      | Call (fsym, _) -> Sym.Set.singleton fsym
      | Asgn (_, _, gt') | Assert (_, gt') | Map (_, gt') -> aux gt'
      | Let (_, (_, gt1), gt2) | ITE (_, gt1, gt2) -> Sym.Set.union (aux gt1) (aux gt2)
    in
    aux (Option.get gd.body)


  module SymGraph = Graph.Persistent.Digraph.Concrete (Sym)
  module Oper = Graph.Oper.P (SymGraph)
end

let get_call_graph (ctx : GD.context) : SymGraph.t =
  ctx
  |> List.map_snd (List.map snd)
  |> List.map_snd (fun gds -> match gds with [ gd ] -> gd | _ -> failwith __LOC__)
  |> List.map_snd get_calls
  |> List.fold_left
       (fun cg (fsym, calls) ->
         Sym.Set.fold (fun fsym' cg' -> SymGraph.add_edge cg' fsym fsym') calls cg)
       SymGraph.empty
  |> Oper.transitive_closure
