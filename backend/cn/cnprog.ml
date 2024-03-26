module BT = BaseTypes
module IT = IndexTerms
module Loc = Locations
module CF = Cerb_frontend
module RET = ResourceTypes
module LC = LogicalConstraints

open IT

type have_show =
  | Have
  | Show

type cn_extract = Id.t list * (Sym.t, Sctypes.t) CF.Cn.cn_to_extract * IndexTerms.t

type cn_statement =
  | M_CN_pack_unpack of CF.Cn.pack_unpack * ResourceTypes.predicate_type
  | M_CN_have of LogicalConstraints.t
  | M_CN_instantiate of (Sym.t, Sctypes.t) CF.Cn.cn_to_instantiate * IndexTerms.t
  | M_CN_split_case of LogicalConstraints.t
  | M_CN_extract of cn_extract
  | M_CN_unfold of Sym.t * IndexTerms.t list
  | M_CN_apply of Sym.t * IndexTerms.t list
  | M_CN_assert of LogicalConstraints.t
  | M_CN_inline of Sym.t list
  | M_CN_print of IndexTerms.t




type cn_load = {ct : Sctypes.t; pointer : IndexTerms.t}



type cn_prog =
  | M_CN_let of Loc.t * (Sym.t * cn_load) * cn_prog
  | M_CN_statement of Loc.t * cn_statement


let rec subst substitution = function
  | M_CN_let (loc, (name, {ct; pointer}), prog) ->
     let pointer = IT.subst substitution pointer in
     let name, prog =
       suitably_alpha_rename substitution.relevant
         (name, Memory.bt_of_sct ct) prog
     in
     M_CN_let (loc, (name, {ct; pointer}), subst substitution prog)
  | M_CN_statement (loc, stmt) ->
     let stmt = match stmt with
       | M_CN_pack_unpack (pack_unpack, pt) ->
          M_CN_pack_unpack (pack_unpack, RET.subst_predicate_type substitution pt)
       | M_CN_have lc ->
          M_CN_have (LC.subst substitution lc)
       | M_CN_instantiate (o_s, it) ->
          (* o_s is not a (option) binder *)
          M_CN_instantiate (o_s, IT.subst substitution it)
       | M_CN_split_case lc ->
          M_CN_split_case (LC.subst substitution lc)
       | M_CN_extract (attrs, to_extract, it) ->
           M_CN_extract (attrs, to_extract, IT.subst substitution it)
       | M_CN_unfold (fsym, args) ->
          (* fsym is a function symbol *)
          M_CN_unfold (fsym, List.map (IT.subst substitution) args)
       | M_CN_apply (fsym, args) ->
          (* fsym is a lemma symbol *)
          M_CN_apply (fsym, List.map (IT.subst substitution) args)
       | M_CN_assert lc ->
          M_CN_assert (LC.subst substitution lc)
       | M_CN_inline nms ->
          M_CN_inline nms
       | M_CN_print it ->
          M_CN_print (IT.subst substitution it)
     in
     M_CN_statement (loc, stmt)


and alpha_rename_ s' (s, ls) prog =
  (s', subst (IT.make_subst [(s, IT.sym_ (s', ls))]) prog)

and alpha_rename (s, ls) prog =
  let s' = Sym.fresh_same s in
  alpha_rename_ s' (s, ls) prog

and suitably_alpha_rename syms (s, ls) prog =
  if SymSet.mem s syms
  then alpha_rename (s, ls) prog
  else (s, prog)



open Cerb_frontend.Pp_ast
open Cerb_frontend.Cn
open Pp

let dtree_of_to_instantiate = function
  | I_Function f -> Dnode (pp_ctor "[CN]function", [Dleaf (Sym.pp f)])
  | I_Good ty -> Dnode(pp_ctor "[CN]good", [Dleaf (Sctypes.pp ty)])
  | I_Everything -> Dleaf !^"[CN]everything"

let dtree_of_to_extract = function
  | E_Everything -> Dleaf !^"[CN]everything"
  | E_Pred pred ->
     let pred = match pred with
     | CN_owned oct -> CN_owned (Option.map Sctypes.to_ctype oct)
     | CN_block ct -> CN_block (Sctypes.to_ctype ct)
     | CN_named p -> CN_named p
     in
     Dnode (pp_ctor "[CN]pred", [Cerb_frontend.Cn_ocaml.PpAil.dtree_of_cn_pred pred])

let dtree_of_cn_statement = function
  | M_CN_pack_unpack (Pack, pred) ->
     Dnode (pp_ctor "Pack", [ResourceTypes.dtree_of_predicate_type pred])
  | M_CN_pack_unpack (Unpack, pred) ->
     Dnode (pp_ctor "Unpack", [ResourceTypes.dtree_of_predicate_type pred])
  | M_CN_have lc ->
     Dnode (pp_ctor "Have", [LC.dtree lc])
  | M_CN_instantiate (to_instantiate, it) ->
     Dnode (pp_ctor "Instantiate",
            [dtree_of_to_instantiate to_instantiate; IT.dtree it])
  | M_CN_split_case lc ->
     Dnode (pp_ctor "Split_case", [LC.dtree lc])
  | M_CN_extract (attrs, to_extract, it) ->
     Dnode (pp_ctor "Extract",
            [Dnode (pp_ctor "Attrs", List.map (fun s -> Dleaf (Id.pp s)) attrs);
                dtree_of_to_extract to_extract; IT.dtree it])
  | M_CN_unfold (s, args) ->
     Dnode (pp_ctor "Unfold", Dleaf (Sym.pp s) :: List.map IT.dtree args)
  | M_CN_apply (s, args) ->
     Dnode (pp_ctor "Apply", Dleaf (Sym.pp s) :: List.map IT.dtree args)
  | M_CN_assert lc ->
     Dnode (pp_ctor "Assert", [LC.dtree lc])
  | M_CN_inline nms ->
     Dnode (pp_ctor "Inline", List.map (fun nm -> Dleaf (Sym.pp nm)) nms)
  | M_CN_print it ->
     Dnode (pp_ctor "Print", [IT.dtree it])


let rec dtree = function
  | M_CN_let (_loc, (s, load), prog) ->
     Dnode (pp_ctor "LetLoad", [
           Dleaf (Sym.pp s);
           IT.dtree load.pointer;
           Dleaf (Sctypes.pp load.ct);
           dtree prog])
  | M_CN_statement (_loc, stmt) ->
     dtree_of_cn_statement stmt
