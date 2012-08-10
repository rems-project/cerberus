open Typed_ast
open Util
exception Trans_error of Ast.l * string

let r = Ulib.Text.of_latin1

let l_unk = Ast.Unknown

let name_to_lower n = 
  if Name.starts_with_upper_letter n then
    Some(Name.uncapitalize n)
  else 
    None

let ntl n = 
  let n' =
    match name_to_lower (Name.strip_lskip n) with
      | None -> Name.strip_lskip n
      | Some(n) -> n
  in
    Name.lskip_rename (fun _ -> Name.to_rope n') n

(* coq-backend
- create the constructors for records declarations
- propagate the result type for variant type declarations
- make type variables in variant type declarations uppercase
*)

let capitalise_tvar (s,r,l) = 
(*  (s, Ulib.Text.capitalize r, l) *)
  (s,r,l)

let capitalise_tvar_list tvs = 
  Seplist.map (fun tv -> capitalise_tvar tv) tvs

let rec coq_synt_records = function
  | [] -> []
  | ((def,s),l)::defs ->
      ((begin
        match def with
          | Type_def(s,tdefs) ->
              Type_def(s, 
                       Seplist.map 
                         (fun (s1,tvs,s2,(n,l),texp) ->
                            let coq_tvs = capitalise_tvar_list tvs in
                            let new_texp = 
                              match texp with
                                | Te_opaque -> Te_opaque
                                | Te_abbrev(s,t) -> Te_abbrev(s,t)
                                | Te_record(s3,s1,fields,s2) ->
                                    (* FZ TODO: ugly...  need a concat over names *)
                                    let lskips = Name.get_lskip n in
                                    let r = Name.to_rope (Name.strip_lskip n) in
                                    let nr = Ulib.Text.append (Ulib.Text.of_string "mk") r in
                                    let nn = Name.add_pre_lskip lskips (Name.add_lskip (Name.from_rope nr)) in
                                    Te_record_coq(s3, (nn,l), s1,fields,s2)
                                | Te_record_coq(_,_,_,_,_) ->
                                    failwith ("Cannot happen in coq_synt_records - record")
                                | Te_variant(s,vars) ->
                                    let tvars = Seplist.map (fun (n1,s,sl) -> 
                                      let tsl = Seplist.map (fun t -> 
                                        match t.term with 
                                        | Typ_var (s,tv) ->
                                            let utv = Tyvar.from_rope (Name.to_rope (Name.capitalize (Name.from_rope (Tyvar.to_rope tv)))) in
                                            { t with term = Typ_var (s,utv) }
                                        | _ -> t) sl in
                                      (n1,s,tsl,(n,Ast.Unknown),coq_tvs)) vars in
                                    Te_variant_coq(s,tvars)
                                | Te_variant_coq(_,_) ->
                                    failwith ("Cannot happen in coq_synt_records - variant")
                            in
                              (s1,coq_tvs,s2,(ntl n, l), new_texp))
                         tdefs)
          | x -> x
      end,s),l) :: coq_synt_records defs

type 'a macro = 'a -> 'a option

module Macros(I : Types.Global_defs)(E : sig val env : env end) = struct

module C = Exps_in_context(struct let check = Some(I.d) let avoid = None end)

let d = I.d
let inst = I.i
open E

(* Macros *)

(* Make type-variables uppercase - Coq specific *)
(* let capitalize_typ_vars e = *)
(*   let l_unk = Ast.Trans("capitalize_typ_vars") in *)
(*   match C.exp_to_term e with *)
(*   | Typ_var (s,tv) ->  *)
(*       Some (C.mk_tvar l_unk s (Ulib.Text.capitalize r) (C.exp_to_type e)) *)
(*   | _ -> None *)

(* Turn record construction into a call to the record constructot - Coq specific *)
let build_records e =
  let l_unk = Ast.Trans("build_records") in
  match C.exp_to_term e with
  | Record(s1,recexp,s2) ->
      Some (C.mk_record_coq l_unk s1 recexp s2 (Some (exp_to_typ e)))
  | _ -> None

(* Turn function | pat1 -> exp1 ... | patn -> expn end into
 * fun x -> match x with | pat1 -> exp1 ... | patn -> expn end *)
  let remove_function e = 
    let l_unk = Ast.Trans("remove_function") in
      match C.exp_to_term e with
        | Function(s1,cases,s2) ->
            let free = C.exp_to_free e in
            let v = Name.fresh (r"x") (fun n -> not (Nfmap.in_dom n free)) in
            let (from_t,to_t) =
              match (Types.head_norm d (exp_to_typ e)).Types.t with
                | Types.Tfn(t1,t2) -> (t1,t2)
                | _ -> assert false
            in
            let pat_v = C.mk_pvar l_unk (Name.add_lskip v) from_t in
            let exp_v = C.mk_var l_unk (Name.add_lskip v) from_t in
              Some(C.mk_fun (exp_to_locn e) s1 [pat_v] space
                     (C.mk_case l_unk space exp_v space cases s2 None)
                     None)
        | _ -> None

(* Remove patterns from (fun ps -> ...), except for variable and 
 * (optionally) tuple patterns *)
let remove_fun_pats keep_tup e = 
  let l_unk = Ast.Trans("remove_fun_pats") in
  let rec keep p : bool = match p.term with
    | P_wild _ | P_as _ | P_constr _ | P_record _ | P_list _ | P_cons _ 
    | P_lit _ -> false
    | P_paren(_,p,_) -> keep p
    | P_var _ | P_var_annot _ -> true
    | P_typ(_,p,_,_,_) -> keep p
    | P_tup(_,ps,_) -> keep_tup && Seplist.for_all keep ps
  in
  let rec group acc = function
    | [] -> 
        if acc = [] then
          []
        else
          [(true,List.rev acc)]
    | p::ps -> 
        if keep p then
          group (p::acc) ps
        else if acc = [] then 
          (false,[p])::group [] ps 
        else 
          (true,List.rev acc)::(false,[p])::group [] ps
  in
    match C.exp_to_term e with
      | Fun(s1,ps,s2,e') ->
          let pss = group [] ps in
            begin
              match pss with
                | [(true,_)] -> None
                | _ ->
                    let e =
                      List.fold_right
                        (fun ps res_e ->
                           match ps with
                             | (true,ps) ->
                                 C.mk_fun l_unk space ps space res_e None
                             | (false,[p]) ->
                                 C.mk_function l_unk 
                                   space 
                                   (Seplist.from_list [((p,space,res_e,l_unk),no_lskips)])
                                   no_lskips
                                   None
                             | _ -> assert false)
                        pss
                        e'
                    in
                      match (C.exp_to_term e) with
                        | Fun(_,ps,_,e') ->
                            Some(C.mk_fun (exp_to_locn e) s1 ps s2 e'
                                   (Some(exp_to_typ e)))
                        | Function(_,x,_) ->
                            Some(C.mk_function (exp_to_locn e) 
                                   (Ast.combine_lex_skips s1 s2) x no_lskips
                                   (Some(exp_to_typ e)))
                        | _ -> assert false
            end
      | _ -> None

let app_list e = 
  let rec help e = match (C.exp_to_term e) with
    | App(e1,e2) ->
        let (f,infix,args) = help e1 in
          (f,infix,(e2,exp_to_locn e)::args)
    | Infix(e1,e2,e3) ->
       (e2,true,[(e3,exp_to_locn e);(e1,exp_to_locn e)]) 
    | _ -> (e,false,[])
  in
  let (f,infix,args) = help e in
    (f, infix, List.rev args)

let in_target p t =
  let tn = target_to_mname t in
    Path.check_prefix tn p

let insert2 subst (p1,e1) (p2,e2) =
  Nfmap.insert (Nfmap.insert subst (p1,e1)) (p2,e2)

let rec build_subst (params : (Name.t,unit) annot list) (args : (exp * Ast.l) list) 
      : exp_subst Nfmap.t * (Name.t,unit) annot list * (exp * Ast.l) list =
  match (params, args) with
    | ([],args) -> (Nfmap.empty, [], args)
    | (params, []) -> (Nfmap.empty, params, [])
    | (p::params, (a,_)::args) ->
        let (subst, x, y) = build_subst params args in
          (Nfmap.insert subst (p.term, Sub(a)), x, y)

(* Inline sub [target] bindings *)
let do_substitutions target e =
  let l_unk = Ast.Trans("do_substitutions") in
  let (f,infix,args) = app_list e in
    match C.exp_to_term f with
      | Constant(c) ->
          begin
            match Targetmap.apply c.descr.substitutions target with
              | None -> None
              | Some((params,body)) ->
                  let tsubst = 
                    Types.TVfmap.from_list2 c.descr.const_tparams c.instantiation
                  in
                  let (vsubst, leftover_params, leftover_args) = 
                    build_subst params args
                  in
                  let b = 
                    C.exp_subst (tsubst,vsubst) 
                      (fst (alter_init_lskips (fun _ -> (Ident.get_first_lskip c.id_path, None)) body))
                  in
                    if params = [] && infix then
                      begin
                        match leftover_args with
                          | (a1,l)::(a2,_)::args ->
                              Some(List.fold_left 
                                     (fun e (e',l) -> C.mk_app l e e' None)
                                     (C.mk_infix l a1 b a2 None)
                                     args)
                          | _ -> assert false
                      end
                    else if leftover_params = [] then
                      Some(List.fold_left 
                             (fun e (e',l) -> C.mk_app l e e' None)
                             b
                             leftover_args)
                    else
                      Some(C.mk_fun l_unk
                             None (List.map 
                                     (fun n -> 
                                        C.mk_pvar n.locn (Name.add_lskip n.term) n.typ) 
                                     leftover_params) 
                             None b
                             None)
          end
      | _ -> None

(* Change constructors into tupled constructors *) 
let rec tup_ctor build_result args e = 
  let l_unk = Ast.Trans("tup_ctor") in
  match C.exp_to_term e with
  | Constructor(c) ->
      let l = List.length c.descr.constr_args in
        if Seplist.length args = l then
          Some(C.mk_tup_ctor (exp_to_locn e) c None args None None)
        else
          let names = Name.fresh_list l (r"x") (fun n -> true) in
          let tsubst = Types.TVfmap.from_list2 c.descr.constr_tparams c.instantiation in
          let types = List.map (Types.type_subst tsubst) c.descr.constr_args in
          let pats = 
            List.map2 
              (fun n t -> C.mk_pvar l_unk (Name.add_lskip n) t)
              names
              types
          in
          let refs =
            List.fold_right2 
              (fun n t l -> 
                 Seplist.cons_entry
                   (C.mk_var l_unk (Name.add_lskip n) t)
                   (Seplist.cons_sep_alt None l))
              names
              types
              Seplist.empty
          in
          let body = C.mk_tup_ctor l_unk c None refs None None in
          let f = C.mk_fun l_unk None pats None body None in
            Some(build_result f)
  | App(e1,e2) ->
      tup_ctor 
        (fun e' -> 
           build_result 
             (C.mk_app (exp_to_locn e) e' e2 (Some (exp_to_typ e)))) 
        (Seplist.cons_entry e2 (Seplist.cons_sep_alt None args)) e1
  (* TODO: Is this right *)
  | Infix(e1,e2,e3) ->
      tup_ctor 
        (fun e' ->
           build_result 
             (C.mk_infix (exp_to_locn e) e1 e' e3 (Some (exp_to_typ e))))
        (Seplist.cons_entry e1 
           (Seplist.cons_sep_alt None 
              (Seplist.cons_entry e3 
                 (Seplist.cons_sep_alt None args)))) e2
  | _ -> None

let rec names_get_const env path =
  match path with
    | [] -> assert false
    | [p] ->
        begin
          match Nfmap.apply env.v_env p with
            | Some(Val(x)) -> x
            | _ -> Format.printf "[Trans.names.get_const] %a\n" Name.pp p; assert false
        end
    | n::p ->
        begin
          match Nfmap.apply env.m_env n with
            | Some(x) ->
                names_get_const x p
            | None -> 
                Format.printf "[Trans.names.get_const] %a\n" Name.pp n;
                assert false
        end

let names_mk_ident l i loc =
  Ident.mk_ident (List.map (fun r -> (Name.add_lskip r, None)) l)
    (Name.add_lskip i)
    loc

let rec get_const env path =
  names_get_const env (List.map Name.from_rope path)

let mk_ident l i loc =
  names_mk_ident (List.map Name.from_rope l) (Name.from_rope i) loc

(* TODO: Get the Suc constructor properly when the library is working with
 * datatypes *)
let peanoize_num_pats _ p =
  let l_unk = Ast.Trans("peanoize_num_pats") in
  match p.term with
    | P_lit({ term = L_num(s,i)}) when i > 0 ->
        let suc =
          { id_path = mk_ident [] (r"Suc") l_unk;
            id_locn = l_unk;
            descr = 
              { constr_binding = Path.mk_path [] (Name.from_rope (r"Suc"));
                constr_tparams = [];
                constr_args = [{ Types.t = Types.Tapp([], Path.numpath) }];
                constr_tconstr = Path.numpath;
                constr_names = 
                  NameSet.add (Name.from_rope (r"Zero"))
                    (NameSet.singleton (Name.from_rope (r"Suc"))) };
            instantiation = [] }
        in
        let rec f i =
          if i = 0 then
            C.mk_plit l_unk (C.mk_lnum l_unk None 0 None) None
          else
            C.mk_pconstr l_unk suc [f (i - 1)] None
        in
          Some(pat_append_lskips 
                 (Ast.combine_lex_skips s (Some([Ast.Com(Ast.Comment([Ast.Chars(Ulib.Text.of_latin1 (string_of_int i))]))]))) 
                 (f i))
    | _ -> None


(*
let rec check_cmp_type init t = match Types.head_norm d t.Types.t with
  | Tvar(tv) ->
      false
  | Tfn(tv) ->
      false
  | Ttup(ts) ->
      List.every (check_cmp_type init) ts
  | Tapp(ts, p) ->
      begin
        match Pfmap.apply d p with
          | None -> assert false
          | Some(

  | Tuvar _ -> assert false
*)

let special_type = 
  { Types.t = Types.Tapp([], Path.mk_path [Name.from_rope (r"MachineDefTypes")] (Name.from_rope (r"instruction_instance"))) }

(* Csem hack: Types and comparision functions.. *)

(* Multiset.t *)
let special_type_spec = {
  Types.t = Types.Tapp (
    [],
    Path.mk_path [Name.from_rope (r"Cabs")] (Name.from_rope (r"specifier"))
  )
}

let special_type_mset = {
  Types.t = Types.Tapp (
    [special_type_spec; {Types.t = Types.Tapp ([], Path.numpath)}],
    Path.mk_path
      [Name.from_rope (r"Hol"); Name.from_rope (r"Finite_map")]
      (Name.from_rope (r"fmap"))
  )
}

let compare_mset =
  let l = Ast.Trans("compare_mset") in
  C.mk_const
    l
    { id_path = mk_ident [r"Multiset"] (r"compare_int") l_unk;
      id_locn = l;
      descr = (let x = get_const env [r"Multiset"; r"compare_int"] in Printf.printf ">>>>>> %d\n" (List.length x.const_tparams); x);
      instantiation = [{Types.t = Types.Tapp ([], Path.numpath)}; (* special_type_spec *)]
    }
    None

(* Meaning.Denotation.t *)
let special_type_denot = {
  Types.t  = Types.Tapp (
    [],
    Path.mk_path [Name.from_rope (r"Meaning"); Name.from_rope (r"Denotation")] (Name.from_rope (r"t"))
  )
}

let compare_denot =
  let l = Ast.Trans("compare_denot") in
  C.mk_const
    l
    { id_path = mk_ident [r"Meaning"; r"Denotation"] (r"compare_int") l_unk;
      id_locn = l;
      descr = (get_const env [r"Meaning"; r"Denotation"; r"compare_int"]);
      instantiation = []
    }
    None

(* Action.t *)
let special_type_action = {
  Types.t  = Types.Tapp (
    [],
    Path.mk_path [Name.from_rope (r"Action")] (Name.from_rope (r"t"))
  )
}

let compare_action =
  let l = Ast.Trans("compare_action") in
  C.mk_const
    l
    { id_path = mk_ident [r"Action"] (r"compare_int") l_unk;
      id_locn = l;
      descr = (get_const env [r"Action"; r"compare_int"]);
      instantiation = []
    }
    None

let neq_action =
  let l = Ast.Trans("ne_action") in
  C.mk_const
    l
    { id_path = mk_ident [r"Action"] (r"ne") l_unk;
      id_locn = l;
      descr = (get_const env [r"Action"; r"ne"]);
      instantiation = []
    }
    None

(* Action.t set *)
let special_type_action_set = {
  Types.t  = Types.Tapp ([special_type_action], Path.setpath)
}

(*
let compare_action_set =
  let l = Ast.Trans("compare_action") in
  C.mk_const
    l
    { id_path = mk_ident [r"Pset"] r"compare";
      id_locn = l;
      descr = (get_const env [r"Ocaml"; r"Pset"; r"compare"]);
      instantiation = [special_type_action_set; special_type_action_set]
    }
    None
*)

let eq_action_set =
  let l = Ast.Trans("eq_action_set") in
  C.mk_const
    l
    { id_path = mk_ident [r"Set"] (r"equal") l_unk;
      id_locn = l;
      descr = (get_const env [r"Set"; r"equal"]);
      instantiation = [special_type_action]
    }
    None

(* (Action.t * Action.t) *)
let special_type_action_pair = {
  Types.t  = Types.Ttup [special_type_action; special_type_action]
}

let compare_action_pair =
  let l = Ast.Trans("compare_action_pair") in
  C.mk_const
    l
    { id_path = mk_ident [r"Action"] (r"compare_pair_int") l_unk;
      id_locn = l;
      descr = (get_const env [r"Action"; r"compare_pair_int"]);
      instantiation = []
    }
    None

(* Constraint.constr *)
let special_type_constr = {
  Types.t  = Types.Tapp (
    [],
    Path.mk_path [Name.from_rope (r"Constraint")] (Name.from_rope (r"constr"))
  )
}

let compare_constr =
  let l = Ast.Trans("compare_constr") in
  C.mk_const
    l
    { id_path = mk_ident [r"Constraint"] (r"compare_constr_int") l_unk;
      id_locn = l;
      descr = (get_const env [r"Constraint"; r"compare_constr_int"]);
      instantiation = []
    }
    None

(* End of csem hack. *)

let get_compare t = 
  let l_unk = Ast.Trans("get_compare") in
  let type_eq t' = Types.compare (Types.head_norm d t) t' = 0 in
  (* TODO: Remove this hack *)
    if type_eq  special_type then
    C.mk_const l_unk
      { id_path = mk_ident [r"MachineDefTypes"] (r"compare_instruction_instance") l_unk;
        id_locn = l_unk;
        descr = (get_const env [r"MachineDefTypes"; r"compare_instruction_instance"]);
        instantiation = [] }
      None
  else if type_eq special_type_mset then
    compare_mset
  else if type_eq special_type_denot then
    compare_denot
  else if type_eq special_type_action then
    compare_action
  else if type_eq special_type_action_pair then
    compare_action_pair
  else if type_eq special_type_constr then
    compare_constr
  else
  C.mk_const l_unk
    { id_path = mk_ident [r"Pervasives"] (r"compare") l_unk;
      id_locn = l_unk;
      descr = get_const env [r"Ocaml"; r"compare"];
      instantiation = [t] }
    None

(* Turn comprehensions into nested folds, fails on unrestricted quantifications
* *)
let remove_comprehension for_lst e = 
  let l_unk n = Ast.Trans("remove_comprehension " ^ string_of_int n) in
  match C.exp_to_term e with
  | Comp_binding(is_lst,s1,e1,s2,s3,qbs,s4,e2,s5) when is_lst = for_lst ->
      let avoid = 
        List.fold_right
          (fun qb s ->
             match qb with 
               | Qb_var(n) ->
                   raise (Trans_error(n.locn, "cannot generate code for unrestricted set comprehension"))
               | Qb_restr(_,_,_,_,e,_) ->
                   Nfmap.union (C.exp_to_free e) s)
          qbs
          (Nfmap.union (C.exp_to_free e1) (C.exp_to_free e2))
      in
      let (acc_name,param_name) = 
        match
          List.map (fun n -> Name.add_pre_lskip space (Name.add_lskip n))
            (Name.fresh_list 2 (r"x") (fun n -> not (Nfmap.in_dom n avoid)))
        with
          | [x;y] -> (x,y)
          | _ -> assert false
      in
      let acc_var = C.mk_var (l_unk 1) acc_name (exp_to_typ e) in
      let acc_pat = C.mk_pvar (l_unk 2) acc_name (exp_to_typ e) in
      let result_type = 
        { Types.t = 
            Types.Tapp([(exp_to_typ e1)], 
                       if is_lst then Path.listpath else Path.setpath) }
      in
      let list_fold_const t =
        append_lskips space
          (C.mk_const (l_unk 3)
             { id_path = mk_ident [r"List"] (r"fold_right") (l_unk 28);
               id_locn = (l_unk 4);
               descr = get_const env [r"List"; r"fold_right"];
               instantiation = [t; result_type]; }
             None)
      in
      let set_fold_const t =
        append_lskips space
          (C.mk_const (l_unk 5)
             { id_path = mk_ident [r"Set"] (r"fold") (l_unk 29);
               id_locn = (l_unk 6);
               descr = get_const env [r"Set"; r"fold"];
               instantiation = [t; result_type]; }
             None)
      in
      let f = 
        if is_lst then
          let add_const =
            C.mk_const (l_unk 7)
              { id_path = mk_ident [] (r"::") (l_unk 30);
                id_locn = (l_unk 8);
                descr = get_const env [r"::"];
                instantiation = [exp_to_typ e1] }
              None
          in
            C.mk_infix (l_unk 9) e1 add_const acc_var None
        else
          let add_const =
            C.mk_const (l_unk 10)
              { id_path = mk_ident [r"Set"] (r"add") (l_unk 31);
                id_locn = (l_unk 11);
                descr = get_const env [r"Set"; r"add"];
                instantiation = [exp_to_typ e1] }
              None
          in
          let f_app1 = 
            C.mk_app (l_unk 12) add_const e1 None
          in
            C.mk_app (l_unk 13) f_app1 acc_var None
      in
      let rec helper = function
        | [] -> C.mk_if (l_unk 14) space e2 space f space acc_var None
        | Qb_var(n)::_ -> assert false
        | Qb_restr(is_lst,s1',p,s2',e,s3')::qbs ->
            let param_var = C.mk_var (l_unk 15) param_name p.typ in
            let param_pat = C.mk_pvar (l_unk 16) param_name p.typ in
            let res = helper qbs in
            let s = lskips_only_comments [s1';s2';s3'] in
            let arg1 = 
              if single_pat_exhaustive p then
                C.mk_fun (l_unk 17) s [p; acc_pat] space res None
              else
                C.mk_fun (l_unk 18) s [param_pat; acc_pat] space
                  (C.mk_case (l_unk 19) space param_var space
                     (Seplist.from_list
                        [((p, space, res, l_unk 20), space);
                         ((C.mk_pwild (l_unk 21) space p.typ, space, acc_var, 
                           (l_unk 22)), space)])
                     None
                     None)
                  None
            in
            let app1 = 
              C.mk_app (l_unk 23) 
                (if is_lst then
                   list_fold_const p.typ 
                 else 
                   set_fold_const p.typ) 
                arg1 
                None
            in
            let app2 = C.mk_app (l_unk 24) app1 e None in
              C.mk_app (l_unk 25) app2 acc_var None
      in
      let t = 
        { Types.t = 
            Types.Tapp([exp_to_typ e1], if for_lst then Path.listpath else Path.setpath) }
      in
      let empexp = 
        (if for_lst then C.mk_list else C.mk_set) 
          (l_unk 26) space (Seplist.from_list []) None t in
      let letexp = 
        C.mk_let (exp_to_locn e) 
          s1 
          (C.mk_let_val (l_unk 27) acc_pat None space empexp) 
          (lskips_only_comments [s2;s3;s4;s5])
          (helper qbs)
          None
      in
        Some(letexp)
  | _ -> 
      None

(* Remove set notation *)
let remove_sets e = 
  let l_unk = Ast.Trans("remove_sets") in
  match C.exp_to_term e with
  | Set(s1,es,s2) ->
      begin
        match (Types.head_norm d (exp_to_typ e)).Types.t with
          | Types.Tapp([t],_) ->
              let lst = 
                C.mk_list (exp_to_locn e) 
                  space es s2 { Types.t = Types.Tapp([t],Path.listpath) }
              in
              let from_list =
                C.mk_const l_unk
                  { id_path = Ident.mk_ident [(Name.from_x (Ast.X_l((s1, r"Pset"),l_unk)), None)] 
                                (Name.from_x (Ast.X_l((None, r"from_list"),l_unk)))
                                l_unk;
                    id_locn = l_unk;
                    descr = get_const env [r"Ocaml"; r"Pset"; r"from_list"];
                    instantiation = [t] }
                  None
              in
              let cmp = get_compare t in
              let app1 = C.mk_app l_unk from_list (append_lskips space cmp) None in
              let app = C.mk_app l_unk app1 lst None in
                Some(app)
          | _ -> 
              assert false
      end
  | Setcomp _ ->
      raise (Trans_error(exp_to_locn e, "cannot generate code for unrestricted set comprehension"))
  | _ -> remove_comprehension false e

(* Turn list comprehensions into nested folds *)
let remove_list_comprehension e = remove_comprehension true e

let get_quant_lskips = function
  | Ast.Q_forall(s) -> s
  | Ast.Q_exists(s) -> s

let strip_quant_lskips = function
  | Ast.Q_forall(s) -> Ast.Q_forall(space)
  | Ast.Q_exists(s) -> Ast.Q_exists(space)

let get_quant_impl is_lst t : Ast.q -> exp = 
  let l_unk = Ast.Trans("get_quant_impl") in
  let f path name s =
    let d = get_const env (path @ [name]) in
      append_lskips s
        (C.mk_const l_unk 
           { id_path = mk_ident path name l_unk;
             id_locn = l_unk;
             descr = d;
             instantiation = [t] }
           None)
  in
    function
      | Ast.Q_forall(s) ->
          if is_lst then
            f [r"List"] (r"for_all") s
          else
            f [r"Set"] (r"for_all") s
      | Ast.Q_exists(s) ->
          if is_lst then
            f [r"List"] (r"exists") s
          else
            f [r"Set"] (r"exists") s

(* Turn quantifiers into iteration, fails on unrestricted quantifications *)
let remove_quant e = 
  let l_unk = Ast.Trans("remove_quant") in
  match C.exp_to_term e with
  | Quant(q,[],s,e) ->
      Some(append_lskips s e)
  | Quant(q,qb::qbs,s1,e') ->
      begin
        match qb with
          | Qb_var(n) ->
              raise (Trans_error(n.locn, "cannot generate code for unrestricted quantifier"))
          | Qb_restr(is_lst,s2,p,s3,e_restr,s4) ->
              let q_impl = get_quant_impl is_lst p.typ q in
              let f = 
                C.mk_fun l_unk
                  (lskips_only_comments [s2;s3;s4])
                  [pat_append_lskips space p] 
                  space
                  (C.mk_quant l_unk (strip_quant_lskips q) qbs s1 e' None)
                  None
              in
              let app1 = C.mk_app l_unk q_impl f None in
                Some(C.mk_app (exp_to_locn e) app1 e_restr None)
      end
  | _ -> None

(* Turn forall (x MEM L). P x into forall (x IN Set.from_list L). P x *)
let list_quant_to_set_quant e = 
  let l_unk = Ast.Trans("list_quant_to_set_quant") in
  match C.exp_to_term e with
  | Quant(q,qbs,s1,e') ->
      let qbs =
        Util.map_changed
          (fun e -> match e with
             | Qb_restr(is_lst,s2,p,s3,e,s4) when is_lst->
                 let lst_to_set = 
                   append_lskips space
                     (C.mk_const l_unk
                        { id_path = mk_ident [r"Set"] (r"from_list") l_unk;
                          id_locn = l_unk;
                          descr = 
                            get_const env [r"Set"; r"from_list"];
                          instantiation = [p.typ] }
                        None)
                 in
                 let app = C.mk_app l_unk lst_to_set e None in
                   Some(Qb_restr(false,s2,p,s3,app,s4))
             | _ -> None)
          qbs
      in
        begin
          match qbs with
            | None -> None
            | Some(qbs) -> Some(C.mk_quant (exp_to_locn e) q qbs s1 e' None)
        end
  | _ -> None

let rec pat_to_exp d p = 
  let l_unk = Ast.Trans("pat_to_exp") in
  match p.term with
    | P_wild(lskips) -> 
        raise (Util.TODO "_ pattern in restricted set comprehension")
    | P_as(p,_,(n,_)) ->
        raise (Util.TODO "as pattern in restricted set comprehension")
    | P_typ(lskips1,p,lskips2,t,lskips3) ->
        C.mk_typed p.locn lskips1 (pat_to_exp d p) lskips2 t lskips3 None
    | P_var(n) ->
        C.mk_var p.locn n p.typ
    | P_constr(c,ps) ->
        List.fold_left
          (fun e p -> C.mk_app l_unk e (pat_to_exp d p) None)
          (C.mk_constr p.locn c None)
          ps
    | P_record(_,fieldpats,_) ->
        raise (Util.TODO "record pattern in restricted set comprehension")
    | P_tup(lskips1,ps,lskips2) ->
        C.mk_tup p.locn lskips1 (Seplist.map (pat_to_exp d) ps) lskips2 None
    | P_list(lskips1,ps,lskips2) ->
        C.mk_list p.locn lskips1 (Seplist.map (pat_to_exp d) ps) lskips2 p.typ
    | P_paren(lskips1,p,lskips2) ->
        C.mk_paren p.locn lskips1 (pat_to_exp d p) lskips2 None
    | P_cons(p1,lskips,p2) ->
        let cons =
          C.mk_const l_unk
            { id_path = mk_ident [] (r"::") l_unk;
              id_locn = l_unk;
              descr = get_const env [r"::"];
              instantiation = [p1.typ] }
            None
        in
          C.mk_infix p.locn (pat_to_exp d p1) (append_lskips lskips cons) (pat_to_exp d p2) None
    | P_lit(l) ->
        C.mk_lit p.locn l None
    | P_var_annot(n,t) ->
        C.mk_typed p.locn None (C.mk_var p.locn n p.typ) None t None None


let rec pat_vars_src p = match p.term with
  | P_wild _ -> []
  | P_as(p,_,(n,_)) ->
      { term = n; typ = p.typ; locn = p.locn; rest = (); } :: pat_vars_src p
  | P_typ(_,p,_,_,_) ->
      pat_vars_src p
  | P_var(n) | P_var_annot(n,_) ->
      [{ term = n; typ = p.typ; locn = p.locn; rest = (); }]
  | P_constr(_,ps) ->
      List.concat (List.map pat_vars_src ps)
  | P_record(_,fieldpats,_) ->
      List.concat (Seplist.to_list_map (fun (_,_,p) -> pat_vars_src p) fieldpats)
  | P_tup(_,ps,_) ->
      List.concat (Seplist.to_list_map pat_vars_src ps)
  | P_list(_,ps,_) ->
      List.concat (Seplist.to_list_map pat_vars_src ps)
  | P_paren(_,p,_) ->
      pat_vars_src p
  | P_cons(p1,_,p2) ->
      (pat_vars_src p1) @ (pat_vars_src p2)
  | P_lit _ -> []

(* Turn restricted quantification into unrestricted quantification:
 * { f x | forall (p IN e) | P x } goes to
 * { f x | FV(p) | forall FV(p). p IN e /\ P x } *)
let remove_set_restr_quant e = 
  let l_unk = Ast.Trans("remove_set_restr_quant") in
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      if List.for_all (function | Qb_var _ -> true | Qb_restr _ -> false) qbs then
        None
      else
        let and_const = 
          C.mk_const l_unk
            { id_path = mk_ident [] (r"&&") l_unk;
              id_locn = l_unk;
              descr = get_const env [r"&&"];
              instantiation = [] }
            None
        in
        let in_const t = 
          C.mk_const l_unk
            { id_path = mk_ident [] (r"IN") l_unk;
              id_locn = l_unk;
              descr = get_const env [r"IN"];
              instantiation = [t] }
            None
        in 
        let mem_const t = 
          C.mk_const l_unk
            { id_path = mk_ident [r"List"] (r"mem") l_unk;
              id_locn = l_unk;
              descr = get_const env [r"List"; r"mem"];
              instantiation = [t] }
            None
        in 
        let pred_exp =
          List.fold_right 
            (fun qb res_e ->
               match qb with
                 | Qb_var(n) -> res_e
                 | Qb_restr(is_lst, s1', p, s2', e', s3') ->
                     let e =
                       C.mk_paren l_unk 
                         s1'
                         (C.mk_infix l_unk
                            (pat_to_exp d p)
                            (append_lskips s2' (if is_lst then mem_const p.typ else in_const p.typ))
                            e'
                            None)
                         s3'
                         None
                     in
                       C.mk_infix l_unk
                         e
                         (append_lskips space and_const)
                         res_e
                         None)
            qbs
            e2
        in
        let new_qbs = 
          List.concat
            (List.map 
               (function
                  | Qb_var(n) -> [Qb_var(n)]
                  | Qb_restr(_,_,p,_,_,_) -> List.map (fun v -> Qb_var(v)) (pat_vars_src p))
               qbs)
        in
          Some(C.mk_comp_binding (exp_to_locn e) 
                 false s1 e1 s2 s3 new_qbs s4 pred_exp s5 None)
  | _ -> None

(* Turns (let f p1 p2 = e in e') into (let f = fun p1 p2 -> e in e') *)
let remove_letfun always e = 
  let l_unk = Ast.Trans("remove_letfun") in
  match C.exp_to_term e with
    | Let(s1,(Let_fun(n, ps, topt, s2, e1),l),s3,e2) ->
        if always || topt <> None then
          Some(C.mk_let (exp_to_locn e)
                 s1 
                 (C.mk_let_val l
                    (C.mk_pvar n.locn n.term n.typ) 
                    begin
                      match topt with
                        | None -> None
                        | Some((s,t)) ->
                            Some(s,
                                 List.fold_right
                                   (fun p t ->
                                      C.mk_tfn l_unk (C.t_to_src_t p.typ) None t None)
                                   ps
                                   t)
                    end
                    space
                    (C.mk_fun l_unk space ps s2 e1 None))
                 s3 
                 e2
                 None)
        else
          None
    | _ -> 
        None

let eq_path = Path.mk_path [Name.from_rope (r"Ocaml"); Name.from_rope (r"Pervasives")] (Name.from_rope (r"="))
let neq_path = Path.mk_path [Name.from_rope (r"Ocaml"); Name.from_rope (r"Pervasives")] (Name.from_rope (r"<>"))
let cmp_path = Path.mk_path [Name.from_rope (r"Ocaml"); Name.from_rope (r"Pervasives")] (Name.from_rope (r"compare"))

let hack e = 
  match C.exp_to_term e with
  | Constant(c) ->
      if Path.compare c.descr.const_binding eq_path = 0 then
        let l_unk = Ast.Trans("hack") in
        begin
          match c.instantiation with
            | [t] when Types.compare (Types.head_norm d t) special_type_action = 0 ->
                Some
                  (C.mk_const l_unk
                     { id_path = Ident.mk_ident [] (Name.from_x (Ast.X_l((None, r"eq_instruction_instance"), l_unk))) l_unk;
                       id_locn = l_unk;
                       descr = { const_binding = Path.mk_path [Name.from_rope (r"")] (Name.from_rope (r"eq_instruction_instance"));
                                 const_tparams = [];
                                 const_class = [];
                                 const_type = Types.multi_fun [special_type; special_type] 
                                                { Types.t = Types.Tapp([], Path.mk_path [] (Name.from_rope (r"num"))) };
                                 env_tag = K_target(true,Targetset.empty);
                                 spec_l = l_unk;
                                 substitutions = Targetmap.empty };
                       instantiation = [] }
                     None)
            | [t] ->
		let type_eq t' = Types.compare (Types.head_norm d t) t' = 0 in
		if type_eq special_type_action_set then
                  Some eq_action_set
		else None
            | _ -> None
	end
      else if Path.compare c.descr.const_binding cmp_path = 0 then
	begin
          match c.instantiation with
            | [t] ->
	      let type_eq t' = Types.compare (Types.head_norm d t) t' = 0 in
		if type_eq special_type_mset then
                  Some compare_mset
		else if type_eq special_type_denot then
		  Some compare_denot
		else if type_eq special_type_action then
		  Some compare_action
		else None
            | _ -> None
        end
      else if Path.compare c.descr.const_binding neq_path = 0 then
	begin
          match c.instantiation with
            | [t] ->
		let type_eq t' = Types.compare (Types.head_norm d t) t' = 0 in
		if type_eq special_type_action then
                  Some neq_action
		else None
            | _ -> None
        end
      else
        None
  | _ -> None


(* Isabelle Transformations *)

let remove_set_comp_binding init e = 
  let l_unk = Ast.Trans("remove_set_comp_binding") in
  match C.exp_to_term e with
  | Comp_binding(false,s1,e1,s2,s3,qbs,s4,e2,s5) ->
      if List.for_all (function | Qb_var _ -> true | Qb_restr _ -> false) qbs then
        None
      else
        let and_const = 
          C.mk_const l_unk
            { id_path = Ident.mk_ident [] (Name.from_x (Ast.X_l((None, r"&&"),l_unk))) l_unk;
              id_locn = l_unk;
              descr = get_const env [r"&&"];
              instantiation = [] }
            None
        in
        let in_descr = get_const env [r"IN"] in
        let pred_exp =
          List.fold_right 
            (fun qb res_e ->
               match qb with
                 | Qb_var(n) -> res_e
                                  (* TODO*) 
                 | Qb_restr(is_lst,s1', p, s2', e', s3') ->
                     let in_const =
                       C.mk_const l_unk
                         { id_path =
                             Ident.mk_ident [] 
                               (Name.from_x (Ast.X_l((None, r"IN"), l_unk)))
                               l_unk;
                           id_locn = l_unk;
                           descr = in_descr;
                           instantiation = [p.typ] }
                         None
                     in
                     let e =
                       C.mk_infix l_unk
                         (pat_to_exp d p)
                         in_const
                         e'
                         None
                     in
                       C.mk_infix l_unk e and_const res_e None)
            qbs
            e2
        in
        let new_qbs = 
          List.concat
            (List.map 
               (function
                  | Qb_var(n) -> [Qb_var(n)]
                  | Qb_restr(_,_,p,_,_,_) -> List.map (fun v -> Qb_var(v)) (pat_vars_src p))
               qbs)
        in
          Some(C.mk_comp_binding (exp_to_locn e) false s1 e1 s2 s3 new_qbs s4 pred_exp s5 None)
  | _ -> None


let remove_class_const e =
  let l_unk = Ast.Trans("remove_class_const") in
  match C.exp_to_term e with
  | Constant(c) ->
      if c.descr.env_tag = K_method then
        let (instance_path, instance_constraints) =
          match (c.descr.const_class, c.instantiation) with
            | ([(c_path,tparam)],[targ]) -> 
                begin
                  match Types.get_matching_instance d (c_path, targ) inst with
                    | None ->
                        Format.fprintf Format.std_formatter "%a@\n"
                          Types.pp_type targ;
                        raise (Util.TODO "Instance at a type variable")
                    | Some(x) -> x
                end
            | _ -> assert false
        in
          match instance_constraints with
            | [] ->
                let new_const = 
                  names_get_const env (instance_path @ 
                                       [Path.get_name c.descr.const_binding]) 
                in
                let id = 
                  { id_path = 
                      names_mk_ident instance_path 
                        (Path.get_name c.descr.const_binding)
                        l_unk;
                    id_locn = c.id_locn;
                    descr = new_const;
                    (* TODO : compute the instantiation in the general case.
                    * This is ok for unconstrained instances. *)
                    instantiation = []; }
                in
                  Some(C.mk_const l_unk id None)
            | _ -> 
                raise (Util.TODO "Instance with constraints")
      else
        None
  | _ -> None

(* Add type annotations to pattern variables whose type contains a type variable
 * (only add for arguments to top-level functions) *)
let rec coq_type_annot_pat_vars (level,pos) p = 
  let l_unk = Ast.Trans("coq_type_annot_pat_vars") in
  match p.term with
    | P_var(n) when level = Macro_expander.Top_level && 
                    pos = Macro_expander.Param && 
                    not (Types.TVset.is_empty (Types.free_vars p.typ)) ->
        Some(C.mk_pvar_annot l_unk n (C.t_to_src_t p.typ) (Some(p.typ)))
    | _ -> None




end

