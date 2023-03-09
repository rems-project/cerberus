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



type cn_statement =
  | M_CN_pack_unpack of CF.Cn.pack_unpack * ResourceTypes.predicate_type
  | M_CN_have of LogicalConstraints.t
  | M_CN_instantiate of (Sym.t, Sctypes.t) CF.Cn.cn_to_instantiate * IndexTerms.t
  | M_CN_unfold of Sym.t * IndexTerms.t list

type cn_load = {ct : Sctypes.t; pointer : IndexTerms.t}



type cn_prog = 
  | M_CN_let of Loc.t * (Sym.t * cn_load) * cn_prog
  | M_CN_statement of Loc.t * cn_statement


let rec subst substitution = function
  | M_CN_let (loc, (name, {ct; pointer}), prog) ->
     let pointer = IT.subst substitution pointer in
     let name, prog = 
       suitably_alpha_rename substitution.relevant 
         (name, BT.of_sct ct) prog
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
       | M_CN_unfold (fsym, args) ->
          (* fsym is a function symbol *)
          M_CN_unfold (fsym, List.map (IT.subst substitution) args)
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
