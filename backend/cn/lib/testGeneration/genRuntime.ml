module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GD = GenDefinitions
module GBT = GenBaseTypes
module GA = GenAnalysis
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module SymGraph = Graph.Persistent.Digraph.Concrete (Sym)
module StringMap = Map.Make (String)

let bennet = Sym.fresh_named "bennet"

type term =
  | Uniform of
      { bt : BT.t;
        sz : int
      }
  | Pick of
      { bt : BT.t;
        choice_var : Sym.t;
        choices : (int * term) list;
        last_var : Sym.t
      }
  | Alloc of
      { bytes : IT.t;
        sized : bool
      }
  | Call of
      { fsym : Sym.t;
        iargs : (Sym.t * Sym.t) list;
        oarg_bt : BT.t;
        path_vars : SymSet.t;
        sized : (int * Sym.t) option
      }
  | Asgn of
      { pointer : Sym.t;
        addr : IT.t;
        sct : Sctypes.t;
        value : IT.t;
        last_var : Sym.t;
        rest : term
      }
  | Let of
      { backtracks : int;
        x : Sym.t;
        x_bt : BT.t;
        value : term;
        last_var : Sym.t;
        rest : term
      }
  | Return of { value : IT.t }
  | Assert of
      { prop : LC.t;
        last_var : Sym.t;
        rest : term
      }
  | ITE of
      { bt : BT.t;
        cond : IT.t;
        t : term;
        f : term
      }
  | Map of
      { i : Sym.t;
        bt : BT.t;
        min : IT.t;
        max : IT.t;
        perm : IT.t;
        inner : term;
        last_var : Sym.t
      }
  | SplitSize of
      { marker_var : Sym.t;
        syms : SymSet.t;
        path_vars : SymSet.t;
        last_var : Sym.t;
        rest : term
      }
[@@deriving eq, ord]

let is_return (tm : term) : bool = match tm with Return _ -> true | _ -> false

let rec free_vars_term (tm : term) : SymSet.t =
  match tm with
  | Uniform _ -> SymSet.empty
  | Pick { bt = _; choice_var = _; choices; last_var = _ } ->
    free_vars_term_list (List.map snd choices)
  | Alloc { bytes; sized = _ } -> IT.free_vars bytes
  | Call { fsym = _; iargs; oarg_bt = _; path_vars = _; sized = _ } ->
    SymSet.of_list (List.map snd iargs)
  | Asgn { pointer = _; addr; sct = _; value; last_var = _; rest } ->
    SymSet.union (IT.free_vars_list [ addr; value ]) (free_vars_term rest)
  | Let { backtracks = _; x; x_bt = _; value; last_var = _; rest } ->
    SymSet.union (free_vars_term value) (SymSet.remove x (free_vars_term rest))
  | Return { value } -> IT.free_vars value
  | Assert { prop; last_var = _; rest } ->
    SymSet.union (LC.free_vars prop) (free_vars_term rest)
  | ITE { bt = _; cond; t; f } ->
    SymSet.union (IT.free_vars cond) (free_vars_term_list [ t; f ])
  | Map { i; bt = _; min; max; perm; inner; last_var = _ } ->
    SymSet.remove
      i
      (SymSet.union (IT.free_vars_list [ min; max; perm ]) (free_vars_term inner))
  | SplitSize { marker_var = _; syms = _; path_vars = _; last_var = _; rest } ->
    free_vars_term rest


and free_vars_term_list : term list -> SymSet.t =
  fun xs ->
  List.fold_left (fun ss t -> SymSet.union ss (free_vars_term t)) SymSet.empty xs


let rec pp_term (tm : term) : Pp.document =
  let open Pp in
  match tm with
  | Uniform { bt; sz } -> string "uniform" ^^ angles (BT.pp bt) ^^ parens (int sz)
  | Pick { bt; choice_var; choices; last_var } ->
    string "pick"
    ^^ parens
         (c_comment (string "chosen by " ^^ Sym.pp choice_var)
          ^^ comma
          ^^ break 1
          ^^ twice slash
          ^^ space
          ^^ string "backtracks to"
          ^^ space
          ^^ Sym.pp last_var
          ^^ break 1
          ^^ brackets
               (nest
                  2
                  (break 1
                   ^^ c_comment (BT.pp bt)
                   ^^ break 1
                   ^^ separate_map
                        (semi ^^ break 1)
                        (fun (w, gt) ->
                          parens
                            (int w ^^ comma ^^ braces (nest 2 (break 1 ^^ pp_term gt))))
                        choices)))
  | Alloc { bytes; sized } ->
    (if sized then string "alloc_sized" else string "alloc") ^^ parens (IT.pp bytes)
  | Call { fsym; iargs; oarg_bt; path_vars; sized } ->
    parens
      (Sym.pp fsym
       ^^ optional
            (fun (n, sym) -> brackets (int n ^^ comma ^^ space ^^ Sym.pp sym))
            sized
       ^^ parens
            (nest
               2
               (separate_map
                  (comma ^^ break 1)
                  (fun (x, y) -> Sym.pp x ^^ colon ^^ space ^^ Sym.pp y)
                  iargs))
       ^^ space
       ^^ colon
       ^^ space
       ^^ BT.pp oarg_bt
       ^^ c_comment
            (string "path affected by"
             ^^ space
             ^^ separate_map
                  (comma ^^ space)
                  Sym.pp
                  (path_vars |> SymSet.to_seq |> List.of_seq)))
  | Asgn { pointer; addr; sct; value; last_var; rest } ->
    Sctypes.pp sct
    ^^ space
    ^^ IT.pp addr
    ^^ space
    ^^ string ":="
    ^^ space
    ^^ IT.pp value
    ^^ semi
    ^^ space
    ^^ c_comment
         (string "backtracks to"
          ^^ space
          ^^ Sym.pp last_var
          ^^ string " allocs via "
          ^^ Sym.pp pointer)
    ^^ break 1
    ^^ pp_term rest
  | Let
      { backtracks : int;
        x : Sym.t;
        x_bt : BT.t;
        value : term;
        last_var : Sym.t;
        rest : term
      } ->
    string "let"
    ^^ (if backtracks <> 0 then parens (int backtracks) else empty)
    ^^ (if is_return value then empty else star)
    ^^ space
    ^^ Sym.pp x
    ^^ space
    ^^ colon
    ^^ space
    ^^ BT.pp x_bt
    ^^ space
    ^^ equals
    ^^ nest 2 (break 1 ^^ pp_term value)
    ^^ semi
    ^^ space
    ^^ twice slash
    ^^ space
    ^^ string "backtracks to"
    ^^ space
    ^^ Sym.pp last_var
    ^^ break 1
    ^^ pp_term rest
  | Return { value : IT.t } -> string "return" ^^ space ^^ IT.pp value
  | Assert { prop : LC.t; last_var : Sym.t; rest : term } ->
    string "assert"
    ^^ parens (nest 2 (break 1 ^^ LC.pp prop) ^^ break 1)
    ^^ semi
    ^^ space
    ^^ twice slash
    ^^ space
    ^^ string "backtracks to"
    ^^ space
    ^^ Sym.pp last_var
    ^^ break 1
    ^^ pp_term rest
  | ITE { bt : BT.t; cond : IT.t; t : term; f : term } ->
    string "if"
    ^^ space
    ^^ parens (IT.pp cond)
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ c_comment (BT.pp bt) ^^ break 1 ^^ pp_term t) ^^ break 1)
    ^^ space
    ^^ string "else"
    ^^ space
    ^^ braces (nest 2 (break 1 ^^ pp_term f) ^^ break 1)
  | Map { i; bt; min; max; perm; inner; last_var } ->
    let i_bt, _ = BT.map_bt bt in
    string "map"
    ^^ space
    ^^ parens
         (BT.pp i_bt
          ^^ space
          ^^ Sym.pp i
          ^^ semi
          ^^ space
          ^^ IT.pp perm
          ^^ c_comment
               (IT.pp min ^^ string " <= " ^^ Sym.pp i ^^ string " <= " ^^ IT.pp max)
          ^^ c_comment (string "backtracks to" ^^ space ^^ Sym.pp last_var))
    ^^ braces (c_comment (BT.pp bt) ^^ nest 2 (break 1 ^^ pp_term inner) ^^ break 1)
  | SplitSize { marker_var; syms; path_vars; last_var; rest } ->
    string "split_size"
    ^^ brackets (Sym.pp marker_var)
    ^^ parens
         (separate_map (comma ^^ space) Sym.pp (syms |> SymSet.to_seq |> List.of_seq))
    ^^ space
    ^^ c_comment
         (string "backtracks to"
          ^^ space
          ^^ Sym.pp last_var
          ^^ comma
          ^^ space
          ^^ string "path affected by"
          ^^ space
          ^^ separate_map
               (comma ^^ space)
               Sym.pp
               (path_vars |> SymSet.to_seq |> List.of_seq))
    ^^ semi
    ^^ break 1
    ^^ pp_term rest


let nice_names (inputs : SymSet.t) (gt : GT.t) : GT.t =
  let basename (sym : Sym.t) : string =
    let open Sym in
    match description sym with
    | SD_Id name | SD_CN_Id name | SD_ObjectAddress name | SD_FunArgValue name -> name
    | SD_None -> "fresh"
    | _ ->
      failwith Pp.(plain (Sym.pp_debug sym ^^ space ^^ at ^^ space ^^ string __LOC__))
  in
  let rec aux (vars : int StringMap.t) (gt : GT.t) : int StringMap.t * GT.t =
    let (GT (gt_, _, loc)) = gt in
    match gt_ with
    | Arbitrary | Uniform _ | Alloc _ | Call _ | Return _ -> (vars, gt)
    | Pick wgts ->
      let vars, wgts =
        List.fold_right
          (fun (w, gr') (vars', choices') ->
            let vars'', gr'' = aux vars' gr' in
            (vars'', (w, gr'') :: choices'))
          wgts
          (vars, [])
      in
      (vars, GT.pick_ wgts loc)
    | Asgn ((it_addr, sct), it_val, gt') ->
      let vars', gt' = aux vars gt' in
      (vars', GT.asgn_ ((it_addr, sct), it_val, gt') loc)
    | Let (backtracks, (x, gt_inner), gt') ->
      let vars, gt_inner = aux vars gt_inner in
      let name = basename x in
      let vars, x, gt' =
        match StringMap.find_opt name vars with
        | Some n ->
          let name' = name ^ "_" ^ string_of_int n in
          let y = Sym.fresh_named name' in
          ( StringMap.add name (n + 1) vars,
            y,
            GT.subst
              (IT.make_subst [ (x, IT.sym_ (y, GT.bt gt_inner, GT.loc gt_inner)) ])
              gt' )
        | None -> (StringMap.add name 1 vars, x, gt')
      in
      let vars, gt' = aux vars gt' in
      (vars, GT.let_ (backtracks, (x, gt_inner), gt') loc)
    | Assert (lc, gt') ->
      let vars, gt' = aux vars gt' in
      (vars, GT.assert_ (lc, gt') loc)
    | ITE (it_if, gt_then, gt_else) ->
      let vars, gt_then = aux vars gt_then in
      let vars, gt_else = aux vars gt_else in
      (vars, GT.ite_ (it_if, gt_then, gt_else) loc)
    | Map ((i_sym, i_bt, it_perm), gt_inner) ->
      let vars, gt_inner = aux vars gt_inner in
      let name = basename i_sym in
      let vars, i_sym, it_perm, gt_inner =
        match StringMap.find_opt name vars with
        | Some n ->
          let name' = name ^ "_" ^ string_of_int n in
          let j = Sym.fresh_named name' in
          let su = IT.make_subst [ (i_sym, IT.sym_ (j, i_bt, loc)) ] in
          (StringMap.add name (n + 1) vars, j, IT.subst su it_perm, GT.subst su gt_inner)
        | None -> (StringMap.add name 1 vars, i_sym, it_perm, gt_inner)
      in
      (vars, GT.map_ ((i_sym, i_bt, it_perm), gt_inner) loc)
  in
  snd
    (aux
       (inputs |> SymSet.to_seq |> Seq.map (fun x -> (basename x, 1)) |> StringMap.of_seq)
       gt)


let elaborate_gt (inputs : SymSet.t) (gt : GT.t) : term =
  let rec aux (vars : Sym.t list) (path_vars : SymSet.t) (gt : GT.t) : term =
    let last_var = match vars with v :: _ -> v | [] -> bennet in
    let (GT (gt_, bt, loc)) = gt in
    match gt_ with
    | Arbitrary ->
      failwith
        Pp.(
          plain
            (string "Value from " ^^ Locations.pp loc ^^ string " is still `arbitrary`"))
    | Uniform sz -> Uniform { bt; sz }
    | Pick wgts ->
      let choice_var = Sym.fresh () in
      Pick
        { bt;
          choice_var;
          choices =
            (let wgts =
               let gcd =
                 List.fold_left
                   (fun x y -> Z.gcd x y)
                   (fst (List.hd wgts))
                   (List.map fst (List.tl wgts))
               in
               List.map_fst (fun x -> Z.div x gcd) wgts
             in
             let w_sum = List.fold_left Z.add Z.zero (List.map fst wgts) in
             let max_int = Z.of_int Int.max_int in
             let f =
               if Z.leq w_sum max_int then
                 fun w -> Z.to_int w
               else
                 fun w ->
               Z.to_int
                 (Z.max Z.one (Z.div w (Z.div (Z.add w_sum (Z.pred max_int)) max_int)))
             in
             List.map
               (fun (w, gt) ->
                 (f w, aux (choice_var :: vars) (SymSet.add choice_var path_vars) gt))
               wgts);
          last_var
        }
    | Alloc bytes -> Alloc { bytes; sized = false }
    | Call (fsym, xits) ->
      let (iargs : (Sym.t * Sym.t) list), (gt_lets : Sym.t -> term -> term) =
        List.fold_right
          (fun (y, it) (yzs, f) ->
            let (IT.IT (it_, z_bt, _here)) = it in
            match it_ with
            | Sym z -> ((y, z) :: yzs, f)
            | _ ->
              let z = Sym.fresh () in
              ( (y, z) :: yzs,
                fun w gr ->
                  Let
                    { backtracks = 0;
                      x = z;
                      x_bt = z_bt;
                      value = Return { value = it };
                      last_var = w;
                      rest = f z gr
                    } ))
          xits
          ([], fun _ gr -> gr)
      in
      gt_lets last_var (Call { fsym; iargs; oarg_bt = bt; path_vars; sized = None })
    | Asgn ((addr, sct), value, rest) ->
      let pointer =
        let pointers =
          let free_vars = IT.free_vars_bts addr in
          if SymMap.cardinal free_vars == 1 then
            free_vars
          else
            free_vars |> SymMap.filter (fun _ bt -> BT.equal bt (BT.Loc ()))
        in
        if not (SymMap.cardinal pointers == 1) then
          Cerb_debug.print_debug 2 [] (fun () ->
            Pp.(
              plain
                (braces
                   (separate_map
                      (comma ^^ space)
                      Sym.pp
                      (List.map fst (SymMap.bindings pointers)))
                 ^^ space
                 ^^ string " in "
                 ^^ IT.pp addr)));
        List.find
          (fun x -> SymMap.mem x pointers)
          (vars @ List.of_seq (SymSet.to_seq inputs))
      in
      Asgn { pointer; addr; sct; value; last_var; rest = aux vars path_vars rest }
    | Let (backtracks, (x, gt1), gt2) ->
      Let
        { backtracks;
          x;
          x_bt = GT.bt gt1;
          value = aux vars path_vars gt1;
          last_var;
          rest = aux (x :: vars) path_vars gt2
        }
    | Return value -> Return { value }
    | Assert (prop, rest) -> Assert { prop; last_var; rest = aux vars path_vars rest }
    | ITE (cond, gt_then, gt_else) ->
      let path_vars = SymSet.union path_vars (IT.free_vars cond) in
      ITE { bt; cond; t = aux vars path_vars gt_then; f = aux vars path_vars gt_else }
    | Map ((i, i_bt, perm), inner) ->
      let min, max = GenAnalysis.get_bounds (i, i_bt) perm in
      Map
        { i;
          bt = Map (i_bt, GT.bt inner);
          min;
          max;
          perm;
          inner = aux (i :: vars) path_vars inner;
          last_var
        }
  in
  aux [] SymSet.empty (nice_names inputs gt)


type definition =
  { filename : string;
    sized : bool;
    name : Sym.t;
    iargs : (Sym.t * BT.t) list;
    oargs : (Sym.t * BT.t) list;
    body : term
  }
[@@deriving eq, ord]

let pp_definition (def : definition) : Pp.document =
  let open Pp in
  group
    (string "generator"
     ^^ space
     ^^ braces
          (separate_map
             (comma ^^ space)
             (fun (x, ty) -> BT.pp ty ^^ space ^^ Sym.pp x)
             def.oargs)
     ^^ space
     ^^ Sym.pp def.name
     ^^ parens
          (separate_map
             (comma ^^ space)
             (fun (x, ty) -> BT.pp ty ^^ space ^^ Sym.pp x)
             def.iargs)
     ^^ space
     ^^ lbrace
     ^^ nest 2 (break 1 ^^ pp_term def.body)
     ^^ break 1
     ^^ rbrace)


let elaborate_gd ({ filename; recursive; spec = _; name; iargs; oargs; body } : GD.t)
  : definition
  =
  { filename;
    sized = recursive;
    name;
    iargs = List.map_snd GBT.bt iargs;
    oargs = List.map_snd GBT.bt oargs;
    body =
      Option.get body
      |> GenNormalize.MemberIndirection.transform
      |> elaborate_gt (SymSet.of_list (List.map fst iargs))
  }


type context = (A.ail_identifier * (A.ail_identifier list * definition) list) list

let pp (ctx : context) : Pp.document =
  let defns = ctx |> List.map snd |> List.flatten |> List.map snd in
  let open Pp in
  surround_separate_map
    2
    1
    empty
    lbracket
    (semi ^^ twice hardline)
    rbracket
    pp_definition
    defns


module Sizing = struct
  let count_recursive_calls (syms : SymSet.t) (gr : term) : int =
    let rec aux (gr : term) : int =
      match gr with
      | Uniform _ | Alloc _ | Return _ -> 0
      | Pick { choices; _ } ->
        choices |> List.map snd |> List.map aux |> List.fold_left max 0
      | Call { fsym; _ } -> if SymSet.mem fsym syms then 1 else 0
      | Asgn { rest; _ } -> aux rest
      | Let { value; rest; _ } -> aux value + aux rest
      | Assert { rest; _ } -> aux rest
      | ITE { t; f; _ } -> max (aux t) (aux f)
      | Map { inner; _ } -> aux inner
      | SplitSize _ -> failwith ("unreachable @ " ^ __LOC__)
    in
    aux gr


  let size_recursive_calls (marker_var : Sym.t) (syms : SymSet.t) (size : int) (gr : term)
    : term * SymSet.t
    =
    let rec aux (gr : term) : term * SymSet.t =
      match gr with
      | Call ({ fsym; path_vars; _ } as gr) when SymSet.mem fsym syms ->
        let sym = Sym.fresh () in
        let gr' =
          if size > 1 && TestGenConfig.is_random_size_splits () then
            Call
              { gr with
                sized = Some (size, sym);
                path_vars = SymSet.add marker_var path_vars
              }
          else
            Call { gr with sized = Some (size, sym) }
        in
        (gr', SymSet.singleton sym)
      | Uniform _ | Call _ | Return _ -> (gr, SymSet.empty)
      | Alloc { bytes; sized = _ } -> (Alloc { bytes; sized = true }, SymSet.empty)
      | Pick ({ choices; _ } as gr) ->
        let choices, syms =
          choices
          |> List.map (fun (w, gr) ->
            let gr, syms = aux gr in
            ((w, gr), syms))
          |> List.split
        in
        (Pick { gr with choices }, List.fold_left SymSet.union SymSet.empty syms)
      | Asgn ({ rest; _ } as gr) ->
        let rest, syms = aux rest in
        (Asgn { gr with rest }, syms)
      | Let ({ value; rest; _ } as gr) ->
        let value, syms = aux value in
        let rest, syms' = aux rest in
        (Let { gr with value; rest }, SymSet.union syms syms')
      | Assert ({ rest; _ } as gr) ->
        let rest, syms = aux rest in
        (Assert { gr with rest }, syms)
      | ITE ({ t; f; _ } as gr) ->
        let t, syms = aux t in
        let f, syms' = aux f in
        (ITE { gr with t; f }, SymSet.union syms syms')
      | Map ({ inner; _ } as gr) ->
        let inner, syms = aux inner in
        (Map { gr with inner }, syms)
      | SplitSize _ -> failwith ("unreachable @ " ^ __LOC__)
    in
    aux gr


  let transform_gr (syms : SymSet.t) (gr : term) : term =
    let rec aux (path_vars : SymSet.t) (gr : term) : term =
      match gr with
      | ITE { bt; cond; t; f } ->
        let path_vars = SymSet.union path_vars (IT.free_vars cond) in
        ITE { bt; cond; t = aux path_vars t; f = aux path_vars f }
      | Pick { bt; choice_var; choices; last_var } ->
        Pick
          { bt;
            choice_var;
            choices = List.map_snd (aux (SymSet.add choice_var path_vars)) choices;
            last_var
          }
      | _ ->
        let count = count_recursive_calls syms gr in
        let marker_var = Sym.fresh () in
        let gr, syms = size_recursive_calls marker_var syms count gr in
        if count > 1 then
          SplitSize
            { marker_var;
              syms;
              last_var = Sym.fresh_named "bennet";
              path_vars;
              rest = gr
            }
        else
          gr
    in
    aux SymSet.empty gr


  let transform_def
    (cg : SymGraph.t)
    ({ filename : string;
       sized : bool;
       name : SymSet.elt;
       iargs : (SymSet.elt * BT.t) list;
       oargs : (SymSet.elt * BT.t) list;
       body : term
     } :
      definition)
    : definition
    =
    { filename;
      sized;
      name;
      iargs;
      oargs;
      body = transform_gr (SymGraph.fold_pred SymSet.add cg name SymSet.empty) body
    }


  let transform (cg : SymGraph.t) (ctx : context) : context =
    List.map_snd
      (List.map_snd (fun ({ sized; _ } as def) ->
         if sized then transform_def cg def else def))
      ctx
end

let elaborate (gtx : GD.context) : context =
  let cg = GA.get_call_graph gtx in
  gtx |> List.map_snd (List.map_snd elaborate_gd) |> Sizing.transform cg
