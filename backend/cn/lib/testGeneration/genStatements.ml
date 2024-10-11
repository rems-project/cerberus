module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms

type t =
  | Asgn of (IT.t * Sctypes.t) * IT.t
  | Let of (int * (Sym.t * GT.t))
  | Assert of LC.t
[@@deriving eq, ord]

let hash = Hashtbl.hash

let stmts_of_gt (gt : GT.t) : t list * GT.t =
  let rec aux (gt : GT.t) : t list * GT.t =
    let (GT (gt_, _, _)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ | Pick _ | Alloc _ | Call _ | Return _ | ITE _ | Map _ ->
      ([], gt)
    | Asgn ((it_addr, sct), it_val, gt_rest) ->
      let stmts, gt_last = aux gt_rest in
      (Asgn ((it_addr, sct), it_val) :: stmts, gt_last)
    | Let (backtracks, (x, gt'), gt_rest) ->
      let stmts, gt_last = aux gt_rest in
      (Let (backtracks, (x, gt')) :: stmts, gt_last)
    | Assert (lc, gt_rest) ->
      let stmts, gt_last = aux gt_rest in
      (Assert lc :: stmts, gt_last)
  in
  aux gt


let gt_of_stmts (stmts : t list) (gt_end : GT.t) : GT.t =
  List.fold_right
    (fun (stmt : t) gt_rest ->
      let loc = Locations.other __LOC__ in
      match stmt with
      | Asgn ((it_addr, sct), it_val) -> GT.asgn_ ((it_addr, sct), it_val, gt_rest) loc
      | Let (backtracks, (x, gt')) -> GT.let_ (backtracks, (x, gt'), gt_rest) loc
      | Assert lc -> GT.assert_ (lc, gt_rest) loc)
    stmts
    gt_end
