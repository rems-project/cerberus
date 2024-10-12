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


let rec replace_struct_memberof_it
  (struct_sym : Sym.t)
  (dict : (Id.t * Sym.t) list)
  (it : IT.t)
  : IT.t
  =
  let repl = replace_struct_memberof_it struct_sym dict in
  let (IT (it_, bt, loc)) = it in
  let it_ =
    match it_ with
    | Const _ | Sym _ | SizeOf _ | OffsetOf _ | Nil _ -> it_
    | Unop (op, it') -> IT.Unop (op, repl it')
    | Binop (op, it1, it2) -> IT.Binop (op, repl it1, repl it2)
    | ITE (it1, it2, it3) -> IT.ITE (repl it1, repl it2, repl it3)
    | EachI ((min, (i_sym, i_bt), max), it') ->
      IT.EachI ((min, (i_sym, i_bt), max), repl it')
    | Tuple its -> IT.Tuple (List.map repl its)
    | NthTuple (n, it') -> IT.NthTuple (n, repl it')
    | Struct (tag, xits) -> IT.Struct (tag, List.map_snd repl xits)
    | StructMember (it', x) ->
      (match IT.is_sym it' with
       | Some (y, _y_bt) when Sym.equal y struct_sym ->
         IT.Sym (List.assoc Id.equal x dict)
       | _ -> IT.StructMember (repl it', x))
    | StructUpdate ((it_struct, x), it_val) ->
      IT.StructUpdate ((repl it_struct, x), repl it_val)
    | Record xits -> IT.Record (List.map_snd repl xits)
    | RecordMember (it', x) -> IT.RecordMember (repl it', x)
    | RecordUpdate ((it_record, x), it_val) ->
      IT.RecordUpdate ((repl it_record, x), repl it_val)
    | Constructor (tag, xits) -> IT.Constructor (tag, List.map_snd repl xits)
    | MemberShift (it', tag, member) -> IT.MemberShift (it', tag, member)
    | ArrayShift { base; ct; index } ->
      IT.ArrayShift { base = repl base; ct; index = repl index }
    | CopyAllocId { addr; loc } -> IT.CopyAllocId { addr = repl addr; loc = repl loc }
    | HasAllocId it' -> IT.HasAllocId (repl it')
    | Cons (it1, it2) -> IT.Cons (repl it1, repl it2)
    | Head it' -> IT.Head (repl it')
    | Tail it' -> IT.Tail (repl it')
    | NthList (it1, it2, it3) -> IT.NthList (repl it1, repl it2, repl it3)
    | ArrayToList (it1, it2, it3) -> IT.ArrayToList (repl it1, repl it2, repl it3)
    | Representable (sct, it') -> IT.Representable (sct, repl it')
    | Good (sct, it') -> IT.Good (sct, repl it')
    | Aligned { t; align } -> IT.Aligned { t = repl t; align = repl align }
    | WrapI (sct, it') -> IT.WrapI (sct, repl it')
    | MapConst (bt, it') -> IT.MapConst (bt, repl it')
    | MapSet (it1, it2, it3) -> IT.MapSet (repl it1, repl it2, repl it3)
    | MapGet (it1, it2) -> IT.MapGet (repl it1, repl it2)
    | MapDef ((x, bt), it') -> IT.MapDef ((x, bt), repl it')
    | Apply (fsym, its) -> IT.Apply (fsym, List.map repl its)
    | Let ((x, it1), it2) -> IT.Let ((x, repl it1), it2)
    | Match (it', pits) -> IT.Match (repl it', List.map_snd repl pits)
    | Cast (bt, it') -> IT.Cast (bt, repl it')
  in
  IT (it_, bt, loc)


let replace_struct_memberof_gt
  (struct_sym : Sym.t)
  (dict : (Id.t * Sym.t) list)
  (gt : GT.t)
  : GT.t
  =
  let repl = replace_struct_memberof_it struct_sym dict in
  let aux (gt : GT.t) : GT.t =
    let (GT (gt_, bt, loc)) = gt in
    let gt_ =
      match gt_ with
      | Alloc it -> GT.Alloc (repl it)
      | Call (fsym, xits) -> GT.Call (fsym, List.map_snd repl xits)
      | Asgn ((it_addr, sct), it_val, gt') ->
        GT.Asgn ((repl it_addr, sct), repl it_val, gt')
      | Return it -> GT.Return (repl it)
      | Assert (T it, gt') -> GT.Assert (LC.T (repl it), gt')
      | Assert (Forall ((i_sym, i_bt), it), gt') ->
        GT.Assert (LC.Forall ((i_sym, i_bt), repl it), gt')
      | ITE (it_if, gt_then, gt_else) -> GT.ITE (repl it_if, gt_then, gt_else)
      | Map ((i_sym, i_bt, it_perm), gt_inner) ->
        GT.Map ((i_sym, i_bt, repl it_perm), gt_inner)
      | _ -> gt_
    in
    GT (gt_, bt, loc)
  in
  GT.map_gen_pre aux gt


(* Should not have any primitve generators of structs *)
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
      (* FIXME: Move this to optimization, since new structs can be introduced *)
      (* Replace references to the members *)
      let gt' =
        replace_struct_memberof_gt
          x
          (List.map (fun (sym, (member, _)) -> (member, sym)) members)
          gt'
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
  ({ filename; name; iargs; oargs; body } : GD.t)
  : GD.t
  =
  { filename; name; iargs; oargs; body = Option.map (normalize_gen prog5) body }


let normalize (prog5 : unit Mucore.file) (ctx : GD.context) : GD.context =
  List.map_snd (List.map_snd (normalize_gen_def prog5)) ctx
