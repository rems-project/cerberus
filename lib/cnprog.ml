module BT = BaseTypes
module IT = IndexTerms
module Loc = Locations
module CF = Cerb_frontend
module Req = Request
module LC = LogicalConstraints

type have_show =
  | Have
  | Show

type extract = Id.t list * (Sym.t, Sctypes.t) CF.Cn.cn_to_extract * IndexTerms.t

type statement =
  | Pack_unpack of CF.Cn.pack_unpack * Request.Predicate.t
  | To_from_bytes of CF.Cn.to_from * Request.Predicate.t
  | Have of LogicalConstraints.t
  | Instantiate of (Sym.t, Sctypes.t) CF.Cn.cn_to_instantiate * IndexTerms.t
  | Split_case of LogicalConstraints.t
  | Extract of extract
  | Unfold of Sym.t * IndexTerms.t list
  | Apply of Sym.t * IndexTerms.t list
  | Assert of LogicalConstraints.t
  | Inline of Sym.t list
  | Print of IndexTerms.t

type load =
  { ct : Sctypes.t;
    pointer : IndexTerms.t
  }

type t =
  | Let of Loc.t * (Sym.t * load) * t
  | Statement of Loc.t * statement

let rec subst substitution = function
  | Let (loc, (name, { ct; pointer }), prog) ->
    let pointer = IT.subst substitution pointer in
    let name, prog = suitably_alpha_rename substitution.relevant name prog in
    Let (loc, (name, { ct; pointer }), subst substitution prog)
  | Statement (loc, stmt) ->
    let stmt =
      match stmt with
      | Pack_unpack (pack_unpack, pt) ->
        Pack_unpack (pack_unpack, Req.Predicate.subst substitution pt)
      | To_from_bytes (to_from, pt) ->
        To_from_bytes (to_from, Req.Predicate.subst substitution pt)
      | Have lc -> Have (LC.subst substitution lc)
      | Instantiate (o_s, it) ->
        (* o_s is not a (option) binder *)
        Instantiate (o_s, IT.subst substitution it)
      | Split_case lc -> Split_case (LC.subst substitution lc)
      | Extract (attrs, to_extract, it) ->
        Extract (attrs, to_extract, IT.subst substitution it)
      | Unfold (fsym, args) ->
        (* fsym is a function symbol *)
        Unfold (fsym, List.map (IT.subst substitution) args)
      | Apply (fsym, args) ->
        (* fsym is a lemma symbol *)
        Apply (fsym, List.map (IT.subst substitution) args)
      | Assert lc -> Assert (LC.subst substitution lc)
      | Inline nms -> Inline nms
      | Print it -> Print (IT.subst substitution it)
    in
    Statement (loc, stmt)


and alpha_rename_ ~from ~to_ prog = (to_, subst (IT.make_rename ~from ~to_) prog)

and alpha_rename from prog =
  let to_ = Sym.fresh_same from in
  alpha_rename_ ~from ~to_ prog


and suitably_alpha_rename syms s prog =
  if Sym.Set.mem s syms then
    alpha_rename s prog
  else
    (s, prog)


let dtree_of_to_instantiate =
  let open Cerb_frontend.Pp_ast in
  function
  | CF.Cn.I_Function f -> Dnode (pp_ctor "[CN]function", [ Dleaf (Sym.pp f) ])
  | I_Good ty -> Dnode (pp_ctor "[CN]good", [ Dleaf (Sctypes.pp ty) ])
  | I_Everything -> Dleaf Pp.(!^"[CN]everything")


let dtree_of_to_extract =
  let open Cerb_frontend.Pp_ast in
  function
  | CF.Cn.E_Everything -> Dleaf Pp.(!^"[CN]everything")
  | E_Pred pred ->
    let pred =
      match pred with
      | CN_owned oct -> CF.Cn.CN_owned (Option.map Sctypes.to_ctype oct)
      | CN_block ct -> CN_block (Option.map Sctypes.to_ctype ct)
      | CN_named p -> CN_named p
    in
    Dnode (pp_ctor "[CN]pred", [ Cerb_frontend.Cn_ocaml.PpAil.dtree_of_cn_pred pred ])


let dtree_of_statement =
  let open Cerb_frontend.Pp_ast in
  function
  | Pack_unpack (Pack, pred) -> Dnode (pp_ctor "Pack", [ Request.Predicate.dtree pred ])
  | Pack_unpack (Unpack, pred) ->
    Dnode (pp_ctor "Unpack", [ Request.Predicate.dtree pred ])
  | To_from_bytes (To, pred) ->
    Dnode (pp_ctor "To_bytes", [ Request.Predicate.dtree pred ])
  | To_from_bytes (From, pred) ->
    Dnode (pp_ctor "From_bytes", [ Request.Predicate.dtree pred ])
  | Have lc -> Dnode (pp_ctor "Have", [ LC.dtree lc ])
  | Instantiate (to_instantiate, it) ->
    Dnode (pp_ctor "Instantiate", [ dtree_of_to_instantiate to_instantiate; IT.dtree it ])
  | Split_case lc -> Dnode (pp_ctor "Split_case", [ LC.dtree lc ])
  | Extract (attrs, to_extract, it) ->
    Dnode
      ( pp_ctor "Extract",
        [ Dnode (pp_ctor "Attrs", List.map (fun s -> Dleaf (Id.pp s)) attrs);
          dtree_of_to_extract to_extract;
          IT.dtree it
        ] )
  | Unfold (s, args) ->
    Dnode (pp_ctor "Unfold", Dleaf (Sym.pp s) :: List.map IT.dtree args)
  | Apply (s, args) -> Dnode (pp_ctor "Apply", Dleaf (Sym.pp s) :: List.map IT.dtree args)
  | Assert lc -> Dnode (pp_ctor "Assert", [ LC.dtree lc ])
  | Inline nms -> Dnode (pp_ctor "Inline", List.map (fun nm -> Dleaf (Sym.pp nm)) nms)
  | Print it -> Dnode (pp_ctor "Print", [ IT.dtree it ])


let rec dtree =
  let open Cerb_frontend.Pp_ast in
  function
  | Let (_loc, (s, load), prog) ->
    Dnode
      ( pp_ctor "LetLoad",
        [ Dleaf (Sym.pp s);
          IT.dtree load.pointer;
          Dleaf (Sctypes.pp load.ct);
          dtree prog
        ] )
  | Statement (_loc, stmt) -> dtree_of_statement stmt
