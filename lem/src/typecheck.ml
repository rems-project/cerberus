open Format
open Types
open Typed_ast

let raise_error = Ident.raise_error

let r = Ulib.Text.of_latin1

module Namel = struct
  type t = Name.t * Ast.l
  let compare (n1,_) (n2,_) =
    Name.compare n1 n2
end

module NamelSet = Set.Make(Namel)

module DupNames = Util.Duplicate(NamelSet)
module DupTvs = Util.Duplicate(TVset)

type pat_env = (t * Ast.l) Nfmap.t
let empty_pat_env = Nfmap.empty

(* Non-top level binders map to a type, not a type scheme, method or constructor
 * *) 
type lex_env = (t * Ast.l) Nfmap.t
let empty_lex_env = Nfmap.empty

let annot_name n l env = 
  { term = n;
    locn = l;
    typ = 
      begin
        match Nfmap.apply env (Name.strip_lskip n) with
          | Some((x,l)) -> x 
          | None -> assert false
      end;
    rest = (); }

let xl_to_nl xl = (Name.from_x xl, Ast.xl_to_l xl)

let id_to_identl id =
  (Ident.from_id id, match id with | Ast.Id(mp,xl,l) -> l)

(* Assume that the names in mp must refer to modules.  Corresponds to judgment
 * look_m 'E1(x1..xn) gives E2' *)
let rec path_lookup (e : env) (mp : (Name.lskips_t * Ast.l) list) : env = 
  match mp with
    | [] -> e
    | (n,l)::nls ->
        match Nfmap.apply e.m_env (Name.strip_lskip n) with
          | None -> 
              raise_error l "unknown module"
                Name.pp (Name.strip_lskip n)
          | Some(e) -> path_lookup e nls

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_m_id 'E1(id) gives E2' *)
let lookup_mod (e : env) (Ast.Id(mp,xl,l'')) : env = 
  let e = path_lookup e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply e.m_env (Name.strip_lskip (Name.from_x xl)) with
      | None -> 
          raise_error (Ast.xl_to_l xl) "unknown module"
            Name.pp (Name.strip_lskip (Name.from_x xl))
      | Some(e) -> e

(* Assume that the names in mp must refer to modules. Corresponds to judgment
 * look_tc 'E(id) gives p' *)
let lookup_p msg (e : env) (Ast.Id(mp,xl,l) as i) : Path.t =
  let e = path_lookup e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
    match Nfmap.apply e.p_env (Name.strip_lskip (Name.from_x xl)) with
      | None ->
          raise_error l (Printf.sprintf "unbound type %s" msg)
            Ident.pp (Ident.from_id i)
      | Some(p) -> p

(* Lookup in the lex env.  A formula in the formal type system *)
let lookup_l (l_e : lex_env) mp n : (t * Ast.l * Name.lskips_t) option =
  match mp with
    | [] -> 
        begin
          match Nfmap.apply l_e (Name.strip_lskip n) with
            | None -> None
            | Some((t,l)) -> Some((t,l,n))
        end
    | _ -> None

(* Checks the well-formedness of a type that appears in the source.  Corresponds
 * to judgment convert_typ 'Delta, E |- typ ~> t'.  The wild_f function is used
 * for an underscore/wildcard type (which should be allowed in type annotations,
 * but not in type definitions).  The do_tvar function is called on each type
 * variable in the type, for its side effect (e.g., to record the tvars that
 * occur in the type. *)
let rec typ_to_src_t (wild_f : Ast.l -> lskips -> src_t) 
      (do_tvar : Tyvar.t -> unit) (d : type_defs) (e : env) (Ast.Typ_l(typ,l)) 
      : src_t = 
  match typ with
    | Ast.Typ_wild(sk) -> 
        wild_f l sk
    | Ast.Typ_var(Ast.A_l((sk,tv),l')) -> 
        do_tvar (Tyvar.from_rope tv);
        { term = Typ_var(sk,Tyvar.from_rope tv); 
          locn = l'; 
          typ = { t = Tvar(Tyvar.from_rope tv); }; 
          rest = (); }
    | Ast.Typ_fn(typ1, sk, typ2) ->
        let st1 = typ_to_src_t wild_f do_tvar d e typ1 in
        let st2 = typ_to_src_t wild_f do_tvar d e typ2 in
          { term = Typ_fn(st1, sk, st2);
            locn = l; 
            typ = { t = Tfn(st1.typ,st2.typ) };
            rest = (); }
    | Ast.Typ_tup(typs) ->
        let typs = Seplist.from_list typs in
        let sts = Seplist.map (typ_to_src_t wild_f do_tvar d e) typs in
          { term = Typ_tup(sts); 
            locn = l; 
            typ = { t = Ttup(Seplist.to_list_map annot_to_typ sts) };
            rest = (); }
    | Ast.Typ_app(i,typs) ->
        let p = lookup_p "constructor" e i in
          begin
            match Pfmap.apply d p with
              | None -> assert false
              | Some(Tc_abbrev(tvs,_)) ->
                  if List.length tvs = List.length typs then
                    let sts = 
                      List.map (typ_to_src_t wild_f do_tvar d e) typs 
                    in
                    let id = {id_path = Ident.from_id i; 
                              id_locn = (match i with Ast.Id(_,_,l) -> l);
                              descr = p;
                              instantiation = []; }
                    in

                      { term = Typ_app(id,sts);
                        locn = l;
                        typ = { t = Tapp(List.map annot_to_typ sts,p) };
                        rest = (); }
                  else
                    raise_error l (Printf.sprintf "type constructor expected %d type arguments, given %d" 
                                   (List.length tvs)
                                   (List.length typs))
                      Ident.pp (Ident.from_id i)
              | Some(Tc_class _) ->
                  raise_error l "type class used as type constructor" 
                    Ident.pp (Ident.from_id i)
          end
    | Ast.Typ_paren(sk1,typ,sk2) ->
        let st = typ_to_src_t wild_f do_tvar d e typ in
        { term = Typ_paren(sk1,st,sk2); 
          locn = l; 
          typ = st.typ; 
          rest = (); }

(* Corresponds to judgment check_lit '|- lit : t' *)
let check_lit (Ast.Lit_l(lit,l)) =
  let annot (lit : lit_aux) (t : t) : lit = 
    { term = lit; locn = l; typ = t; rest = (); } 
  in 
  match lit with
    | Ast.L_true(sk) -> annot (L_true(sk)) { t = Tapp([], Path.boolpath) }
    | Ast.L_false(sk) -> annot (L_false(sk)) { t = Tapp([], Path.boolpath) }
    | Ast.L_num(sk,i) -> annot (L_num(sk,i)) { t = Tapp([], Path.numpath) }
    | Ast.L_string(sk,i) ->
        annot (L_string(sk,i)) { t = Tapp([], Path.stringpath) }
    | Ast.L_unit(sk1,sk2) ->
        annot (L_unit(sk1,sk2)) { t = Tapp([], Path.unitpath) }

let check_dup_field_names (fns : (Name.t * Ast.l) list) : unit = 
  match DupNames.duplicates fns with
    | DupNames.Has_dups(fn) ->
        raise_error (snd fn) "duplicate field name" 
          (fun fmt x -> Format.fprintf fmt "%a" Name.pp x)
          (fst fn)
    | _ -> ()

(* We split the environment between top-level and lexically nested binders, and
 * inside of expressions, only the lexical environment can be extended, we
 * parameterize the entire expression-level checking apparatus over the
 * top-level environment.  This contrasts with the formal type system where
 * Delta and E get passed around.  The Make_checker functor also instantiates
 * the state for type inference, so checking of different expressions doesn't
 * interfere with each other.  We also imperatively collect class constraints
 * instead of passing them around as the formal type system does *)

module type Expr_checker = sig
  val check_letbind : 
    (* Should be None, unless checking a method definition in an instance.  Then
     * it should contain the type that the instance is at.  In this case the
     * returned constraints and type variables must be empty. *)
    t option ->
    (* The set of targets that this definition is for *)
    Targetset.t option ->
    Ast.l ->
    Ast.letbind -> 
    letbind * 
    (* The types of the bindings *)
    pat_env * 
    (* The type variabes, and class constraints on them used in typechecking the
     * let binding.  Must be empty when the optional type argument is Some *)
    (TVset.t * (Path.t * Tyvar.t) list)

  (* As in the comments on check letbind above *)
  val check_funs : 
    t option ->
    Targetset.t option ->
    Ast.l ->
    Ast.funcl lskips_seplist -> 
    funcl_aux lskips_seplist * 
    pat_env * 
    (TVset.t * (Path.t * Tyvar.t) list)

  (* As in the comments on check letbind above, but cannot be an instance
   * method definition *)
  val check_indrels : 
    Targetset.t option ->
    Ast.l ->
    (Ast.rule * lskips) list -> 
    (lskips * name_lskips_annot list * lskips * exp * lskips * name_lskips_annot * exp list) lskips_seplist * 
    pat_env *
    (TVset.t * (Path.t * Tyvar.t) list)
end

module Make_checker(T : sig 
                      (* The backend targets that each identifier use must be
                       * defined for *)
                      val targets : Targetset.t
                      (* The current top-level environment *)
                      val e : env 
                      (* The environment so-far of the module we're defining *)
                      val new_module_env : env
                      include Global_defs 
                    end) : Expr_checker = struct

  module C = Constraint(T)
  module A = Exps_in_context(struct let check = None let avoid = None end)
          
  (* An identifier instantiated to fresh type variables *)
  let make_new_id ((id : Ident.t), l) (tvs : Tyvar.t list) (descr : 'a) : 'a id =
    let ts_inst = List.map (fun _ -> C.new_type ()) tvs in
      { id_path = id; 
        id_locn = l;
        descr = descr; 
        instantiation = ts_inst; }

  (* Assumes that mp refers to only modules and xl a field name.  Corresponds to
   * judgment inst_field 'Delta,E |- field id : t_args p -> t gives (x of
   * names)'.  Instantiates the field descriptor with fresh type variables, also
   * calculates the type of the field as a function from the record type to the
   * field's type.
   *)
  let check_field (Ast.Id(mp,xl,l) as i) 
        : (field_descr id * t * Name.t * NameSet.t) * Ast.l =
    let env = path_lookup T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
      match Nfmap.apply env.f_env (Name.strip_lskip (Name.from_x xl)) with
        | None ->
            begin
              match Nfmap.apply env.v_env (Name.strip_lskip (Name.from_x xl)) with
                | None ->
                    raise_error l "unbound field name" 
                      Ident.pp (Ident.from_id i)
                | Some(Constr(c)) ->
                    raise_error l "constructor name used as a field name"
                      Ident.pp (Ident.from_id i)
                | Some(Val(c)) ->
                    if c.env_tag = K_method then
                      raise_error l "method name used as a field name"
                        Ident.pp (Ident.from_id i)
                    else
                      raise_error l "top level variable binding used as a field name"
                        Ident.pp (Ident.from_id i)
            end
        | Some(f) ->
            let id_l = id_to_identl i in
            let new_id = make_new_id id_l f.field_tparams f in
            let trec = { t = Tapp(new_id.instantiation,f.field_tconstr) } in
            let subst = 
              TVfmap.from_list2 f.field_tparams new_id.instantiation 
            in
            let tfield = type_subst subst f.field_arg in
            let t = { t = Tfn(trec,tfield) } in
            let a = C.new_type () in
              C.equate_types new_id.id_locn a t;
              ((new_id, a, Path.get_name f.field_binding, f.field_names), l)

  (* Instantiates a constructor descriptor with fresh type variables, also
   * calculates the type of the constructor as a function.  Corresponds to
   * judgment inst_ctor 'Delta,E |- ctor id : t_multi -> t_args p gives (x of
   * names)', except that that also looks up the descriptor *)
  let inst_constr id_l (c : constr_descr) : constr_descr id * t * int =
    let new_id = make_new_id id_l c.constr_tparams c in
    let subst = TVfmap.from_list2 c.constr_tparams new_id.instantiation in
    let t = multi_fun 
              (List.map (type_subst subst) c.constr_args)
              { t = Tapp(new_id.instantiation,c.constr_tconstr) }
    in
    let a = C.new_type () in
      C.equate_types new_id.id_locn a t;
      (new_id, a, List.length c.constr_args)

  (* Instantiates a top-level constant descriptor with fresh type variables,
   * also calculates its type.  Corresponds to judgment inst_val 'Delta,E |- val
   * id : t gives Sigma', except that that also looks up the descriptor *)
  let inst_const id_l (c : const_descr) : const_descr id * t =
    let new_id = make_new_id id_l c.const_tparams c in
    let subst = TVfmap.from_list2 c.const_tparams new_id.instantiation in
    let t = type_subst subst c.const_type in
    let a = C.new_type () in
      C.equate_types new_id.id_locn a t;
      List.iter 
        (fun (p, tv) -> 
           C.add_constraint p (type_subst subst { t = Tvar(tv) })) 
        c.const_class;
      (new_id, a)

  let add_binding (pat_e : pat_env) ((v : Name.lskips_t), (l : Ast.l)) (t : t) 
        : pat_env =
    if Nfmap.in_dom (Name.strip_lskip v) pat_e then
      raise_error l "duplicate binding" Name.pp (Name.strip_lskip v)
    else
      Nfmap.insert pat_e (Name.strip_lskip v,(t,l))

  let build_wild l sk =
    { term = Typ_wild(sk); locn = l; typ = C.new_type (); rest = (); }

  (* Corresponds to judgment check_pat 'Delta,E,E_l1 |- pat : t gives E_l2' *)
  let rec check_pat (l_e : lex_env) (Ast.Pat_l(p,l)) (acc : pat_env) 
        : pat * pat_env = 
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in
      match p with
        | Ast.P_wild(sk) -> 
            let a = C.new_type () in
              C.equate_types l ret_type a;
              (A.mk_pwild l sk ret_type, acc)
        | Ast.P_as(s1,p, s2, xl,s3) -> 
            let nl = xl_to_nl xl in
            let (pat,pat_e) = check_pat l_e p acc in
            let ax = C.new_type () in
              C.equate_types (snd nl) ax pat.typ;
              C.equate_types l pat.typ ret_type;
              (A.mk_pas l s1 pat s2 nl s3 rt, add_binding pat_e nl ax)
        | Ast.P_typ(sk1,p,sk2,typ,sk3) ->
            let (pat,pat_e) = check_pat l_e p acc in
            let src_t = 
              typ_to_src_t build_wild C.add_tyvar T.d T.e typ
            in
              C.equate_types l src_t.typ pat.typ;
              C.equate_types l src_t.typ ret_type;
              (A.mk_ptyp l sk1 pat sk2 src_t sk3 rt, pat_e)
        | Ast.P_app(Ast.Id(mp,xl,l'') as i, ps) ->
            let l' = Ast.xl_to_l xl in
            let e = path_lookup T.e (List.map (fun (xl,_) -> xl_to_nl xl) mp) in
              begin
                match Nfmap.apply e.v_env (Name.strip_lskip (Name.from_x xl)) with
                  | Some(Constr(c)) when (lookup_l l_e mp (Name.from_x xl) = None) ->
                      (* i is bound to a constructor that is not lexically
                       * shadowed, this corresponds to the
                       * check_pat_aux_ident_constr case *)
                      let (id,t,num_args) = inst_constr (id_to_identl i) c in
                      let (pats,pat_e) = check_pats l_e acc ps in
                        if List.length pats <> num_args then
                          raise_error l' 
                            (Printf.sprintf "constructor pattern expected %d arguments, given %d"
                               num_args
                               (List.length pats))
                            Ident.pp (Ident.from_id i); 
                        C.equate_types l'' t 
                          (multi_fun (List.map annot_to_typ pats) ret_type);
                        (A.mk_pconstr l id pats rt, pat_e)
                  | _ ->
                      (* the check_pat_aux_var case *)
                      match mp with
                        | [] ->
                            if ps <> [] then
                              raise_error l' "non-constructor pattern given arguments" 
                                Ident.pp (Ident.from_id i)
                            else
                              let ax = C.new_type () in
                              let n = Name.from_x xl in
                                C.equate_types l'' ret_type ax;
                                (A.mk_pvar l n ret_type, 
                                 add_binding acc (n,l') ax)
                        | _ ->
                            raise_error l' "non-constructor pattern has a module path" 
                              Ident.pp (Ident.from_id i)
              end
        | Ast.P_record(sk1,ips,sk2,term_semi,sk3) ->
            let fpats = Seplist.from_list_suffix ips sk2 term_semi in
            let a = C.new_type () in
            let (checked_pats, pat_e) = 
              Seplist.map_acc_left (check_fpat a l_e) acc fpats 
            in
              check_dup_field_names 
                (Seplist.to_list_map snd checked_pats);
              C.equate_types l a ret_type;
              (A.mk_precord l sk1 (Seplist.map fst checked_pats) sk3 rt,
               pat_e)
        | Ast.P_tup(sk1,ps,sk2) -> 
            let pats = Seplist.from_list ps in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
              C.equate_types l ret_type 
                { t = Ttup(Seplist.to_list_map annot_to_typ pats) };
              (A.mk_ptup l sk1 pats sk2 rt, pat_e)
        | Ast.P_list(sk1,ps,sk2,semi,sk3) -> 
            let pats = Seplist.from_list_suffix ps sk2 semi in
            let (pats,pat_e) = 
              Seplist.map_acc_left (check_pat l_e) acc pats
            in
            let a = C.new_type () in
              Seplist.iter (fun pat -> C.equate_types l a pat.typ) pats;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              (A.mk_plist l sk1 pats sk3 ret_type, pat_e)
        | Ast.P_paren(sk1,p,sk2) -> 
            let (pat,pat_e) = check_pat l_e p acc in
              C.equate_types l ret_type pat.typ;
              (A.mk_pparen l sk1 pat sk2 rt, pat_e)
        | Ast.P_cons(p1,sk,p2) ->
            let (pat1,pat_e) = check_pat l_e p1 acc in
            let (pat2,pat_e) = check_pat l_e p2 pat_e in
              C.equate_types l ret_type { t = Tapp([pat1.typ], Path.listpath) };
              C.equate_types l ret_type pat2.typ;
              (A.mk_pcons l pat1 sk pat2 rt, pat_e)
        | Ast.P_lit(lit) ->
            let lit = check_lit lit in
              C.equate_types l ret_type lit.typ;
              (A.mk_plit l lit rt, acc)

  and check_fpat a (l_e : lex_env) (Ast.Fpat(id,sk,p,l)) (acc : pat_env)  
                : (((field_descr id * lskips * pat) * (Name.t * Ast.l)) * pat_env)=
    let (p,acc) = check_pat l_e p acc in
    let ((id,t,n,_),l') = check_field id in
      C.equate_types l t { t = Tfn(a,p.typ) };
      (((id,sk,p),(n,l')), acc)

  and check_pats (l_e : lex_env) (acc : pat_env) (ps : Ast.pat list) 
                : pat list * pat_env =
    List.fold_right 
      (fun p (pats,pat_e) -> 
         let (pat,pat_e) = check_pat l_e p pat_e in
           (pat::pats,pat_e))
      ps
      ([],acc) 

  (* Given an identifier, start at the left and follow it as a module path until
   * the first field/value reference (according to for_field) is encountered.
   * Return the prefix including that reference as a separate identifier.  If a
   * lex_env is supplied, check for value reference in it for the first name
   * only.
   *
   * In the formal type system, we don't calculate this split, but instead use
   * the id_field 'E |- id field' and id_value 'E |- id value' judgments to
   * ensure that the id is one that would be returned by this function.  That
   * is, the id follows the module reference whenever there is ambiguity.  *)
  let rec get_id_mod_prefix (for_field : bool) (check_le : lex_env option) 
        (env : env) (Ast.Id(mp,xl,l_add)) 
        (prefix_acc : (Ast.x_l * Ast.lex_skips) list) : Ast.id * (Ast.lex_skips * Ast.id) option =
    match mp with
      | [] -> 
          let n = Name.strip_lskip (Name.from_x xl) in
          let unbound = 
            if for_field then 
              Nfmap.apply env.f_env n = None 
            else 
              (Nfmap.apply env.v_env n = None &&
               (match check_le with 
                  | None -> true 
                  | Some(le) -> Nfmap.apply le n = None))
          in
          let id = Ast.Id(List.rev prefix_acc,xl,l_add) in
            if unbound then
              raise_error (Ast.xl_to_l xl) 
                (if for_field then "unbound field name" else "unbound variable")
                Ident.pp (Ident.from_id id)
            else
              (id, None)
      | (xl',sk)::mp' ->
          let n = Name.strip_lskip (Name.from_x xl') in
          let unbound = 
            if for_field then 
              Nfmap.apply env.f_env n = None 
            else 
              (Nfmap.apply env.v_env n = None &&
               (match check_le with 
                  | None -> true 
                  | Some(le) -> Nfmap.apply le n = None))
          in
          let id = Ast.Id(List.rev prefix_acc,xl',l_add) in
            if unbound then
              begin
                match Nfmap.apply env.m_env n with
                  | None ->
                      raise_error (Ast.xl_to_l xl') 
                        ("unbound module name or " ^
                         if for_field then "field name" else "variable")
                        Ident.pp (Ident.from_id id)
                  | Some(env) ->
                      get_id_mod_prefix for_field None env 
                        (Ast.Id(mp',xl,l_add)) 
                        ((xl',sk)::prefix_acc)
              end
            else
              (id, Some(sk,Ast.Id(mp',xl,l_add)))


  (* Chop up an identifier into a list of record projections.  Each projection
   * can be an identifier with a non-empty module path *)
  let rec disambiguate_projections sk (id : Ast.id) 
        : (Ast.lex_skips * Ast.id) list =
    match get_id_mod_prefix true None T.e id [] with
      | (id,None) -> [(sk,id)]
      | (id1,Some(sk',id2)) -> (sk,id1)::disambiguate_projections sk' id2

  (* Figures out which '.'s in an identifier are actually record projections.
   * This is ambiguous in the source since field names can be '.' separated
   * module paths *)
  let disambiguate_id (le : lex_env) (id : Ast.id) 
        : Ast.id * (Ast.lex_skips * Ast.id) list =
    match get_id_mod_prefix false (Some(le)) T.e id [] with
      | (id,None) -> (id, [])
      | (id1,Some(sk,id2)) ->
          (id1, disambiguate_projections sk id2)

  let rec check_all_fields (exp : Typed_ast.exp) 
        (fids : (Ast.lex_skips * Ast.id) list) =
    match fids with
      | [] ->
          exp
      | (sk,fid)::fids ->
          let ((id,t,fname,all_names),l) = check_field fid in
          let ret_type = C.new_type () in
            C.equate_types l t { t = Tfn(exp_to_typ exp, ret_type) };
            check_all_fields (A.mk_field l exp sk id (Some ret_type)) fids

  (* Corresponds to inst_val 'D,E |- val id : t gives S' and the 
  * var and val cases of check_exp_aux *)
  let check_val (l_e : lex_env) (mp : (Ast.x_l * Ast.lex_skips) list) 
        (n : Name.lskips_t) (l : Ast.l) : exp =
    match lookup_l l_e mp n with
      | Some(t,l,n) ->
          A.mk_var l n t
      | None -> 
          let mp' = List.map (fun (xl,_) -> xl_to_nl xl) mp in
          let mp'' = List.map (fun (xl,skips) -> (Name.from_x xl, skips)) mp in
          let e = path_lookup T.e mp' in
            match Nfmap.apply e.v_env (Name.strip_lskip n) with
              | None ->
                  raise_error l "unbound variable" Name.pp (Name.strip_lskip n)
              | Some(Constr(c)) ->
                  let (id,t,num_args) = 
                    inst_constr (Ident.mk_ident mp'' n l, l) c 
                  in
                    C.equate_types l t (C.new_type());
                    A.mk_constr l id (Some(t))
              | Some(Val(c)) ->
                  begin
                    match c.env_tag with
                      | K_method -> ()
                      | K_val ->
                          if not (Targetset.is_empty T.targets) then
                            raise_error l "unbound variable (has a val specification, but no definition)"
                              Name.pp (Name.strip_lskip n)
                          else
                            ()
                      | K_let -> ()
                      | K_target(letdef,defined_targets) ->
                          let undefined_targets = 
                            Targetset.diff T.targets defined_targets
                          in
                            if not letdef && 
                               not (Targetset.is_empty undefined_targets) then
                              raise_error l 
                                (Pp.pp_to_string
                                   (fun ppf -> 
                                      Format.fprintf ppf
                                        "unbound variable for targets {%a}"
                                        (Pp.lst ";" (fun ppf t -> Pp.pp_str ppf (target_to_string t)))
                                        (Targetset.elements undefined_targets)))
                                Name.pp (Name.strip_lskip n)
                            else
                              ()
                  end;
                  let (id,t) = 
                    inst_const (Ident.mk_ident mp'' n l, l) c 
                  in
                    C.equate_types l t (C.new_type());
                    A.mk_const l id (Some(t))

  let check_id (l_e : lex_env) (Ast.Id(mp,xl,l_add) as id) : exp =
    (* We could type check and disambiguate at the same time, but that would
     * have a more complicated implementation, so we don't *)
    let (Ast.Id(mp,xl,l), fields) = disambiguate_id l_e id in
    let exp = check_val l_e mp (Name.from_x xl) l in
      check_all_fields exp fields

  (* Corresponds to judgment check_exp 'Delta,E,E_ |- exp : t gives Sigma' *)
  let rec check_exp (l_e : lex_env) (Ast.Expr_l(exp,l)) : exp =
    let ret_type = C.new_type () in
    let rt = Some(ret_type) in 
      match exp with
        | Ast.Ident(i) -> 
            let exp = check_id l_e i in
              C.equate_types l ret_type (exp_to_typ exp);
              exp
        | Ast.Fun(sk,pse) -> 
            let (param_pats,sk',body_exp,t) = check_psexp l_e pse in
              C.equate_types l t ret_type;
              A.mk_fun l sk param_pats sk' body_exp rt
        | Ast.Function(sk,bar_sk,bar,pm,end_sk) -> 
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l t ret_type;
                     res)
                pm
            in
              A.mk_function l sk res end_sk rt
        | Ast.App(fn,arg) ->
            let fnexp = check_exp l_e fn in
            let argexp = check_exp l_e arg in
              C.equate_types l { t = Tfn(exp_to_typ argexp,ret_type) } (exp_to_typ fnexp);
              A.mk_app l fnexp argexp rt
        | Ast.Infix(e1, xl, e2) ->
            let n = Name.from_ix xl in
            let id = check_val l_e [] n (Ast.ixl_to_l xl) in
            let arg1 = check_exp l_e e1 in
            let arg2 = check_exp l_e e2 in
              C.equate_types l 
                { t = Tfn(exp_to_typ arg1, { t = Tfn(exp_to_typ arg2,ret_type) }) }
                (exp_to_typ id);
              A.mk_infix l arg1 id arg2 rt
        | Ast.Record(sk1,r,sk2) ->
            let (res,t,given_names,all_names) = check_fexps l_e r in
              if not (NameSet.subset all_names given_names) then
                raise_error l "missing field"
                  Name.pp
                  (NameSet.choose (NameSet.diff all_names given_names));
              C.equate_types l t ret_type;
              A.mk_record l sk1 res sk2 rt
        | Ast.Recup(sk1,e,sk2,r,sk3) ->
            let exp = check_exp l_e e in
            let (res,t,_,_) = check_fexps l_e r in
              C.equate_types l (exp_to_typ exp) t;
              C.equate_types l t ret_type;
              A.mk_recup l sk1 exp sk2 res sk3 rt
        | Ast.Field(e,sk,fid) ->
            let exp = check_exp l_e e in
            let fids = disambiguate_projections sk fid in
            let new_exp = check_all_fields exp fids in
              C.equate_types l ret_type (exp_to_typ new_exp);
              new_exp
        | Ast.Case(sk1,e,sk2,bar_sk,bar,pm,l',sk3) ->
            let pm = Seplist.from_list_prefix bar_sk bar pm in
            let exp = check_exp l_e e in
            let a = C.new_type () in
            let res = 
              Seplist.map
                (fun pe ->
                   let (res,t) = check_pexp l_e pe in
                     C.equate_types l' t a;
                     res)
                pm
            in
              C.equate_types l a { t = Tfn(exp_to_typ exp,ret_type) };
              A.mk_case l sk1 exp sk2 res sk3 rt
        | Ast.Typed(sk1,e,sk2,typ,sk3) ->
            let exp = check_exp l_e e in
            let src_t = typ_to_src_t build_wild C.add_tyvar T.d T.e typ in
              C.equate_types l src_t.typ (exp_to_typ exp);
              C.equate_types l src_t.typ ret_type;
              A.mk_typed l sk1 exp sk2 src_t sk3 rt
        | Ast.Let(sk1,lb,sk2, body) -> 
            let (lb,pat_env) = check_letbind_internal l_e lb in
            let body_exp = check_exp (Nfmap.union l_e pat_env) body in
              C.equate_types l ret_type (exp_to_typ body_exp);
              A.mk_let l sk1 lb sk2 body_exp rt
        | Ast.Tup(sk1,es,sk2) ->
            let es = Seplist.from_list es in
            let exps = Seplist.map (check_exp l_e) es in
              C.equate_types l ret_type 
                { t = Ttup(Seplist.to_list_map exp_to_typ exps) };
              A.mk_tup l sk1 exps sk2 rt
        | Ast.List(sk1,es,sk3,semi,sk2) -> 
            let es = Seplist.from_list_suffix es sk3 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              Seplist.iter (fun exp -> C.equate_types l a (exp_to_typ exp)) exps;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              A.mk_list l sk1 exps sk2 ret_type
        | Ast.Paren(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l ret_type (exp_to_typ exp);
              A.mk_paren l sk1 exp sk2 rt
        | Ast.Begin(sk1,e,sk2) ->
            let exp = check_exp l_e e in
              C.equate_types l ret_type (exp_to_typ exp);
              A.mk_begin l sk1 exp sk2 rt
        | Ast.If(sk1,e1,sk2,e2,sk3,e3) ->
            let exp1 = check_exp l_e e1 in
            let exp2 = check_exp l_e e2 in
            let exp3 = check_exp l_e e3 in
              C.equate_types l ret_type (exp_to_typ exp2);
              C.equate_types l ret_type (exp_to_typ exp3);
              C.equate_types l (exp_to_typ exp1) { t = Tapp([], Path.boolpath) };
              A.mk_if l sk1 exp1 sk2 exp2 sk3 exp3 rt
        | Ast.Cons(e1,sk,e2) ->
            let e = 
              check_exp l_e 
                (Ast.Expr_l(Ast.Infix(e1,Ast.SymX_l((sk,r"::"), l),e2), l))
            in 
              C.equate_types l ret_type (exp_to_typ e);
              e
        | Ast.Lit(lit) ->
            let lit = check_lit lit in
              C.equate_types l ret_type lit.typ;
              A.mk_lit l lit rt
        | Ast.Set(sk1,es,sk2,semi,sk3) -> 
            let es = Seplist.from_list_suffix es sk2 semi in
            let exps = Seplist.map (check_exp l_e) es in
            let a = C.new_type () in
              Seplist.iter (fun exp -> C.equate_types l a (exp_to_typ exp)) exps;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_set l sk1 exps sk3 ret_type
        | Ast.Setcomp(sk1,e1,sk2,e2,sk3) ->
            let not_shadowed n =
              not (Nfmap.in_dom n l_e) &&
              not (Nfmap.in_dom n T.e.v_env)
            in
            let vars = Ast_util.setcomp_bindings not_shadowed e1 in
            let new_vars = 
              NameSet.fold
                (fun v m -> Nfmap.insert m (v, (C.new_type (),l)))
                vars
                Nfmap.empty
            in
            let env = Nfmap.union l_e new_vars in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_setcomp l sk1 exp1 sk2 exp2 sk3 vars rt
        | Ast.Setcomp_binding(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.setpath) };
              A.mk_comp_binding l false sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt
        | Ast.Quant(q,qbs,s,e) ->
            let (quant_env,qbs) = check_qbs false l_e qbs in
            let et = check_exp (Nfmap.union l_e quant_env) e in
              C.equate_types l ret_type { t = Tapp([], Path.boolpath) };
              C.equate_types l ret_type (exp_to_typ et);
              A.mk_quant l q (List.rev qbs) s et rt
        | Ast.Listcomp(sk1,e1,sk2,sk5,qbs,sk3,e2,sk4) ->
            let (quant_env,qbs) = check_qbs true l_e qbs in
            let env = Nfmap.union l_e quant_env in
            let exp1 = check_exp env e1 in
            let exp2 = check_exp env e2 in
            let a = C.new_type () in
              C.equate_types l (exp_to_typ exp2) { t = Tapp([], Path.boolpath) };
              C.equate_types l (exp_to_typ exp1) a;
              C.equate_types l ret_type { t = Tapp([a], Path.listpath) };
              A.mk_comp_binding l true sk1 exp1 sk2 sk5 
                (List.rev qbs) sk3 exp2 sk4 rt

  (* Corresponds to check_quant_binding or check_listquant_binding
   * 'D,E,EL |- qbind .. qbind gives EL2,S' depending on is_list *)
  and check_qbs (is_list : bool) (l_e : lex_env) (qbs : Ast.qbind list)=
    List.fold_left
      (fun (env,lst) -> 
         function
           | Ast.Qb_var(xl) ->
               if is_list then
                 raise_error (Ast.xl_to_l xl) "unrestricted quantifier in list comprehension"
                   Name.pp (Name.strip_lskip (Name.from_x xl));
               let a = C.new_type () in
               let n = Name.from_x xl in
                 (add_binding env (n, Ast.xl_to_l xl) a,
                  Qb_var({ term = n; locn = Ast.xl_to_l xl; typ = a; rest = (); })::lst)
           | Ast.Qb_list_restr(s1,p,s2,e,s3) ->
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn pt.typ a;
                 C.equate_types (exp_to_locn et) (exp_to_typ et)
                   { t = Tapp([a], Path.listpath) };
                 (p_env,
                  Qb_restr(true,s1, pt, s2, et, s3)::lst)
           | Ast.Qb_restr(s1,(Ast.Pat_l(_,l) as p),s2,e,s3) ->
               if is_list then
                 raise_error l "set-restricted quantifier in list comprehension"
                   (* TODO: Add a pretty printer *)
                   (fun _ _ -> ()) p;
               let et = check_exp (Nfmap.union l_e env) e in
               let (pt,p_env) = check_pat (Nfmap.union l_e env) p env in
               let a = C.new_type () in
                 C.equate_types pt.locn pt.typ a;
                 C.equate_types (exp_to_locn et) (exp_to_typ et) 
                   { t = Tapp([a], Path.setpath) };
                 (p_env,
                  Qb_restr(false,s1, pt, s2, et, s3)::lst))
      (empty_lex_env,[])
      qbs

  and check_fexp (l_e : lex_env) (Ast.Fexp(i,sk1,e,l)) 
                 : (field_descr id * lskips * exp * Ast.l) * t *
                                           Name.t * Ast.l * NameSet.t =
    let ((id,t,fname,all_names),l') = check_field i in
    let exp = check_exp l_e e in
    let ret_type = C.new_type () in
      C.equate_types l t { t = Tfn(ret_type, exp_to_typ exp) };
      ((id,sk1,exp,l), ret_type, fname, l', all_names)

  and check_fexps (l_e : lex_env) (Ast.Fexps(fexps,sk,semi,l)) 
        : (field_descr id * lskips * exp * Ast.l) lskips_seplist * t * 
                                             NameSet.t * NameSet.t =
    let fexps = Seplist.from_list_suffix fexps sk semi in
    let stuff = Seplist.map (check_fexp l_e) fexps in
    let ret_type = C.new_type () in
      check_dup_field_names (Seplist.to_list_map (fun (_,_,n,l,_) -> (n,l)) stuff);
      Seplist.iter (fun (_,t,_,_,_) -> C.equate_types l t ret_type) stuff;
      (Seplist.map (fun (x,_,_,_,_) -> x) stuff,
       ret_type,
       List.fold_right 
         NameSet.add
         (Seplist.to_list_map (fun (_,_,n,_,_) -> n) stuff)
         NameSet.empty, 
       (match Seplist.to_list_map (fun (_,_,_,_,x) -> x) stuff with
          | x::_ -> x
          | _ -> assert false))

  and check_psexp_help l_e ps ot sk e l
        : pat list * (lskips * src_t) option * lskips * exp * t = 
    let ret_type = C.new_type () in
    let (param_pats,pat_env) = check_pats l_e empty_pat_env ps in
    let body_exp = check_exp (Nfmap.union l_e pat_env) e in
    let t = multi_fun (List.map annot_to_typ param_pats) (exp_to_typ body_exp) in
    let annot = 
      match ot with
        | Ast.Typ_annot_none -> 
            None
        | Ast.Typ_annot_some(sk',typ) ->
            let src_t' = typ_to_src_t build_wild C.add_tyvar T.d T.e typ in
              C.equate_types l src_t'.typ (exp_to_typ body_exp);
              Some (sk',src_t')
    in
      C.equate_types l ret_type t;
      (param_pats,annot,sk,body_exp,ret_type)

  and check_psexp (l_e : lex_env) (Ast.Patsexp(ps,sk,e,l)) 
        : pat list * lskips * exp * t = 
    let (a,b,c,d,e) = check_psexp_help l_e ps Ast.Typ_annot_none sk e l in
      (a,c,d,e)

  and check_pexp (l_e : lex_env) (Ast.Patexp(p,sk1,e,l)) 
        : (pat * lskips * exp * Ast.l) * t = 
    match check_psexp l_e (Ast.Patsexp([p],sk1,e,l)) with
      | ([pat],_,exp,t) -> ((pat,sk1,exp,l),t)
      | _ -> assert false 

  and check_funcl (l_e : lex_env) (Ast.Funcl(xl,ps,topt,sk,e)) l =
    let (ps,topt,s,e,t) = check_psexp_help l_e ps topt sk e l in
      ({ term = Name.from_x xl;
         locn = Ast.xl_to_l xl;
         typ = t;
         rest = (); },
       (ps,topt,s,e,t))

  and check_letbind_internal (l_e : lex_env) (Ast.Letbind(lb,l)) 
        : letbind * pat_env = 
    match lb with
      | Ast.Let_val(p,topt,sk',e) ->
          let (pat,pat_env) = check_pat l_e p empty_pat_env in
          let exp = check_exp l_e e in
          let annot = 
            match topt with
              | Ast.Typ_annot_none -> 
                  None
              | Ast.Typ_annot_some(sk',typ) ->
                  let src_t' = typ_to_src_t build_wild C.add_tyvar T.d T.e typ in
                    C.equate_types l src_t'.typ pat.typ;
                    Some (sk',src_t')
          in
            C.equate_types l pat.typ (exp_to_typ exp);
            ((Let_val(pat,annot,sk',exp),l), pat_env)
      | Ast.Let_fun(funcl) ->
          let (xl, (a,b,c,d,t)) = check_funcl l_e funcl l in
            ((Let_fun(xl,a,b,c,d),l),
             add_binding empty_pat_env (xl.term, xl.locn) t)

  let check_constraint_subset l cs1 cs2 = 
    unsat_constraint_err l
      (List.filter
         (fun (p,tv) ->
            not (List.exists 
                   (fun (p',tv') -> 
                      Path.compare p p' = 0 && Tyvar.compare tv tv' = 0)
                   cs2))
         cs1)

  (* Check that a value definition has the right type according to previous
   * definitions of that name in the same module.
   * def_targets is None if the definitions is not target specific, otherwise it
   * is the set of targets that the definition is for.  def_env is the name and
   * types of all of the variables defined *)
  let apply_specs_for_def (def_targets : Targetset.t option) l def_env  =
    Nfmap.iter
      (fun n (t,l) ->
         let const_data = Nfmap.apply T.new_module_env.v_env n in
           match const_data with
             | None ->
                 begin
                   match def_targets with
                     | Some _ -> 
                         raise_error l
                           "target-specific definition without preceding 'val' specification"
                           Name.pp n
                     | None -> ()
                 end
             | Some(Val(c)) ->
                 begin
                   match (c.env_tag,def_targets) with
                     | (K_method,_) ->
                         raise_error l "defined variable is already defined as a class method" 
                           Name.pp n
                     | (K_val,_) ->
                         ()
                     | (K_let,None) | (K_target(true,_),None)->
                         raise_error l
                           "defined variable is already defined"
                           Name.pp n
                     | (K_let,Some _) ->
                         raise_error l
                           "target-specific definition without preceding 'val' specification"
                           Name.pp n
                     | (K_target(false,_), None) -> 
                         ()
                     | (K_target(_,prior_targets),Some(def_targets)) ->
                         let duplicate_targets = 
                           Targetset.inter prior_targets def_targets
                         in
                         let relevant_duplicate_targets =
                           Targetset.inter duplicate_targets T.targets
                         in
                           if not (Targetset.is_empty relevant_duplicate_targets) then
                             raise_error l
                               (Printf.sprintf "defined variable already has a %s-specific definition" 
                                  (target_to_string 
                                     (Targetset.choose relevant_duplicate_targets)))
                               Name.pp n 
                 end;
                 let a = C.new_type () in
                   C.equate_types c.spec_l a c.const_type;
                   C.equate_types l a t
             | Some(Constr _) ->
                 raise_error l "defined variable is already defined as a constructor"
                   Name.pp n)
      def_env;
    let (tyvars, constraints) = C.inst_leftover_uvars l in
      Nfmap.iter
        (fun n (_,l') ->
           match Nfmap.apply T.e.v_env n with
             | None -> ()
             | Some(Val(c)) ->
                 check_constraint_subset l constraints c.const_class
             | _ -> assert false)
        def_env;
      (tyvars, constraints)

  let apply_specs_for_method def_targets l def_env inst_type =
    Nfmap.iter
      (fun n (t,l) ->
         if not (def_targets = None) then
           raise_error l "instance method must not be target specific"
             Name.pp n;
         let const_data = Nfmap.apply T.e.v_env n in
           match const_data with
             | Some(Val(c)) when c.env_tag = K_method ->
                 (* assert List.length c.const_tparams = 1 *)
                 let tv = List.hd c.const_tparams in 
                 let subst = TVfmap.from_list [(tv, inst_type)] in
                 let spec_typ = type_subst subst c.const_type in
                 let a = C.new_type () in
                   C.equate_types c.spec_l a spec_typ;
                   C.equate_types l a t
             | _ -> 
                 raise_error l "instance method not bound to class method"
                   Name.pp n)
      def_env;
    let (tyvars, constraints) = C.inst_leftover_uvars l in
      unsat_constraint_err l constraints;
      (tyvars, [])

  let apply_specs for_method (def_targets : Targetset.t option) l env = 
    match for_method with
      | None -> apply_specs_for_def def_targets l env
      | Some(t) -> apply_specs_for_method def_targets l env t

  (* See Expr_checker signature above *)
  let check_letbind for_method (def_targets : Targetset.t option) l lb =
    let (lb,pe) = check_letbind_internal empty_lex_env lb in
      (lb, pe, apply_specs for_method def_targets l pe)

  (* See Expr_checker signature above *)
  let check_funs for_method (def_targets : Targetset.t option) l funcls =
    let env =
      List.fold_left
        (fun l_e (Ast.Rec_l(Ast.Funcl(xl,_,_,_,_),_)) ->
           let n = Name.strip_lskip (Name.from_x xl) in
             if Nfmap.in_dom n l_e then
               l_e
             else
               add_binding l_e (xl_to_nl xl) (C.new_type ()))
        empty_lex_env
        (Seplist.to_list funcls)
      in
      let funcls = 
        Seplist.map
          (fun (Ast.Rec_l(funcl,l')) -> 
             let (n,(a,b,c,d,t)) = check_funcl env funcl l' in
               C.equate_types l' t 
                 (match Nfmap.apply env (Name.strip_lskip n.term) with
                    | Some(t,_) -> t
                    | None -> assert false);
               (n,a,b,c,d))
          funcls
      in
        (funcls, env, apply_specs for_method def_targets l env)

  (* See Expr_checker signature above *)
  let check_indrels (def_targets : Targetset.t option) l clauses =
    let rec_env =
      List.fold_left
        (fun l_e (Ast.Rule_l(Ast.Rule(_,_,_,_,_,xl,_), _), _) ->
           let n = Name.strip_lskip (Name.from_x xl) in
             if Nfmap.in_dom n l_e then
               l_e
             else
               add_binding l_e (xl_to_nl xl) (C.new_type ()))
        empty_lex_env
        clauses
    in
    let clauses = Seplist.from_list clauses in
    let c =
      Seplist.map
        (fun (Ast.Rule_l(Ast.Rule(s1,ns,s2,e,s3,xl,es), l2)) ->
           let quant_env =
             List.fold_left
               (fun l_e xl -> add_binding l_e (xl_to_nl xl) (C.new_type ()))
               empty_lex_env
               ns
           in
           let extended_env = Nfmap.union rec_env quant_env in
           let et = check_exp extended_env e in
           let ets = List.map (check_exp extended_env) es in
           let new_name = annot_name (Name.from_x xl) (Ast.xl_to_l xl) rec_env in
             C.equate_types l2 (exp_to_typ et) { t = Tapp([], Path.boolpath) };
             C.equate_types l2 
               new_name.typ 
               (multi_fun 
                  (List.map exp_to_typ ets) 
                  { t = Tapp([], Path.boolpath) });
             (s1,
              List.map 
                (fun xl -> annot_name (Name.from_x xl) (Ast.xl_to_l xl) quant_env)
                ns,
              s2,
              et,
              s3,
              new_name,
              ets))
        clauses
    in
      (c,rec_env, apply_specs None def_targets l rec_env)

end

let tvs_to_set (tvs : (Tyvar.t * Ast.l) list) : TVset.t =
  match DupTvs.duplicates (List.map fst tvs) with
    | DupTvs.Has_dups(tv) ->
        let (tv',l) = 
          List.find (fun (tv',_) -> Tyvar.compare tv tv' = 0) tvs
        in
          raise_error l "duplicate type variable" Tyvar.pp tv'
    | DupTvs.No_dups(tvs_set) ->
        tvs_set

let anon_error l = 
  raise (Ident.No_type(l, "anonymous types not permitted here: _"))

let rec check_free_tvs (tvs : TVset.t) (Ast.Typ_l(t,l)) : unit =
  match t with
    | Ast.Typ_wild _ ->
        anon_error l
    | Ast.Typ_var(Ast.A_l((t,x),l)) ->
       if TVset.mem (Tyvar.from_rope x) tvs then
        ()
       else
        raise_error l "unbound type variable" 
          Tyvar.pp (Tyvar.from_rope x)
    | Ast.Typ_fn(t1,_,t2) -> 
        check_free_tvs tvs t1; check_free_tvs tvs t2
    | Ast.Typ_tup(ts) -> 
        List.iter (check_free_tvs tvs) (List.map fst ts)
    | Ast.Typ_app(_,ts) -> 
        List.iter (check_free_tvs tvs) ts
    | Ast.Typ_paren(_,t,_) -> 
        check_free_tvs tvs t

(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : type_defs; 
  (* All types defined in this sequence of definitions *)
  new_tdefs : type_defs;

  (* All class instances ever seen *)
  all_instances : instance list Pfmap.t;
  (* All class instances defined in this sequence of definitions *)
  new_instances : instance list Pfmap.t;

  (* The current value/function/module/field/type_name environment *)
  cur_env : env;
  (* The value/function/module/field/type_names defined in this sequence of
   * definitions *)
  new_defs : env }

(* Update the new and cumulative environment with new
 * function/value/module/field/path definitions according to set and select *)
let ctxt_add (select : env -> 'a Nfmap.t) (set : env -> 'a Nfmap.t -> env) 
      (ctxt : defn_ctxt) (m : Name.t * 'a)
      : defn_ctxt =
  { ctxt with 
        cur_env = set ctxt.cur_env (Nfmap.insert (select ctxt.cur_env) m);
        new_defs = set ctxt.new_defs (Nfmap.insert (select ctxt.new_defs) m); } 

(* Update new and cumulative enviroments with a new module definition, after
 * first checking that its name doesn't clash with another module definition in
 * the same definition sequence.  It can have the same name as another module
 * globally. *)
let add_m_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.lskips_t) (v : env)
      : defn_ctxt = 
  let k = Name.strip_lskip k in
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise_error l "duplicate module definition" Name.pp k
    else
      ctxt_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        ctxt 
        (k,v)

(* Add a new type definition to the global and local contexts *)
let add_d_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (d : tc_def) =
  { ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p,d);
              new_tdefs = Pfmap.insert ctxt.new_tdefs (p,d) }

(* Support for maps from paths to lists of things *)
let insert_pfmap_list (m : 'a list Pfmap.t) (k : Path.t) (v : 'a) 
      : 'a list Pfmap.t =
  match Pfmap.apply m k with
    | None -> Pfmap.insert m (k,[v])
    | Some(l) -> Pfmap.insert m (k,v::l)

(* Add a new instance the the new instances and the global instances *)
let add_instance_to_ctxt (ctxt :defn_ctxt) (p : Path.t) (i : instance) 
      : defn_ctxt =
  { ctxt with all_instances = insert_pfmap_list ctxt.all_instances p i;
              new_instances = insert_pfmap_list ctxt.new_instances p i; }

let add_let_defs_to_ctxt 
      (* The path of the enclosing module *)
      (mod_path : Name.t list)
      (ctxt : defn_ctxt)
      (* The type variables that were generalised for this definition *)
      (tyvars : Tyvar.t list) 
      (* The class constraints that the definition's type variables must satisfy
      *) 
      (constraints : (Path.t * Tyvar.t) list) 
      (* The status for just this definition, must be either K_let or
       * K_target(false, ts), and if it is K_target, there must be a preceding
       * K_val *)
      (env_tag : env_tag) 
      (* If this definition should be inlined for a target, give that target,
       * the parameters and the body *)
      (substitution : (Targetset.t * ((Name.t,unit) annot list * exp)) option)
      (l_env : lex_env) 
      : defn_ctxt =
  let add_subst =
    match substitution with
      | None -> (fun c -> c)
      | Some(ts,s) ->
          (fun c -> 
             { c with substitutions = 
                 Targetset.fold
                   (fun t r -> Targetmap.insert r (t,s))
                   ts 
                   c.substitutions 
             })
  in
  let new_env =
    Nfmap.map
      (fun n (t,l) ->
        match Nfmap.apply ctxt.new_defs.v_env n with
          | None ->
              Val(add_subst
                    { const_binding = Path.mk_path mod_path n;
                      const_tparams = tyvars;
                      const_class = constraints;
                      const_type = t;
                      spec_l = l;
                      env_tag = env_tag;
                      substitutions = Targetmap.empty })
          | Some(Val(c)) ->
              (* The definition is already in the context.  Here we just assume
               * it is compatible with the existing definition, having
               * previously checked it. *) 
              let tag =
                match (c.env_tag, env_tag) with
                  | (K_val, K_val) | (K_let,K_let) | (K_method,_) 
                  | (_,K_method) | (K_let, K_val) | (K_target _, K_val) -> 
                      assert false
                  | (K_val, K_let) -> K_target(true, Targetset.empty)
                  | (K_val, K_target(letdef,targets)) -> 
                      K_target(letdef,targets)
                  | (K_let, K_target(_,targets)) -> K_target(true,targets)
                  | (K_target(_,targets),K_let) -> K_target(true,targets)
                  | (K_target(letdef1,targets1), K_target(letdef2,targets2)) ->
                      K_target(letdef1||letdef2, 
                               Targetset.union targets1 targets2)
              in
                Val(add_subst { c with env_tag = tag })
          | _ -> assert false)
      l_env
  in
  { ctxt with 
        cur_env = 
          { ctxt.cur_env with v_env = Nfmap.union ctxt.cur_env.v_env new_env };
        new_defs = 
          { ctxt.new_defs with 
                v_env = Nfmap.union ctxt.new_defs.v_env new_env } }

let a_l_to_tyvar (Ast.A_l((sk,tv),l)) = (sk,tv,l)
let a_l_to_tyvar2 (Ast.A_l((sk,tv),l)) = (Tyvar.from_rope tv,l)

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_def_help (mod_path : Name.t list) (context : defn_ctxt) 
      (tvs : Ast.a_l list) (type_name : Ast.x_l) (type_abbrev : Ast.typ option) 
      : defn_ctxt = 
  let tvs = List.map a_l_to_tyvar2 tvs in
  let tn = Name.strip_lskip (Name.from_x type_name) in
  let l = Ast.xl_to_l type_name in
  let type_path = Path.mk_path mod_path tn in
  let () =
    match Nfmap.apply context.new_defs.p_env tn with
      | None -> ()
      | Some(p) ->
          begin
            match Pfmap.apply context.all_tdefs p with
              | None -> assert false
              | Some(Tc_abbrev _) ->
                  raise_error l "duplicate type constructor definition"
                    Name.pp tn
              | Some(Tc_class _) ->
                  raise_error l "type constructor already defined as a type class" 
                    Name.pp tn
          end
  in
  let new_ctxt = 
    ctxt_add 
      (fun x -> x.p_env) 
      (fun x y -> { x with p_env = y })
      context 
      (tn, type_path)
  in
    begin
      match type_abbrev with
        | Some(typ) ->
            check_free_tvs (tvs_to_set tvs) typ;
            let src_t = 
              typ_to_src_t anon_error ignore context.all_tdefs context.cur_env typ 
            in
              add_d_to_ctxt new_ctxt type_path 
                (Tc_abbrev(List.map fst tvs, Some(src_t.typ)))
        | None ->
            add_d_to_ctxt new_ctxt type_path 
              (Tc_abbrev(List.map fst tvs, None))
    end

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_def (mod_path : Name.t list) (context : defn_ctxt) (td : Ast.td)
      : defn_ctxt = 
  match td with
    | Ast.Td(xl, tvs, _, td) ->
        build_type_def_help mod_path context tvs xl
          (match td with
             | Ast.Te_abbrev(t) -> Some(t)
             | _ -> None)
    | Ast.Td_opaque(xl,tvs) ->
        build_type_def_help mod_path context tvs xl None

(* Check a type definition and add it to the context.  mod_path is the path to
 * the enclosing module.  Ignores any constructors or fields, just handles the
 * type constructors. *)
let build_type_defs (mod_path : Name.t list) (ctxt : defn_ctxt) 
      (tds : Ast.td lskips_seplist) : defn_ctxt =
  List.fold_left (build_type_def mod_path) ctxt (Seplist.to_list tds)
    
let build_record build_descr tvs_set (ctxt : defn_ctxt) 
      (recs : (Ast.x_l * lskips * Ast.typ) lskips_seplist) 
      : (name_l * lskips * src_t) lskips_seplist * defn_ctxt =
  Seplist.map_acc_left
    (fun (field_name,sk1,typ) ctxt ->
       let l' = Ast.xl_to_l field_name in
       let fn = Name.from_x field_name in
       let fn' = Name.strip_lskip fn in
       let src_t = 
         typ_to_src_t anon_error ignore ctxt.all_tdefs ctxt.cur_env typ 
       in
       let field_descr = build_descr fn' src_t.typ in
       let () = 
         match Nfmap.apply ctxt.new_defs.f_env fn' with
           | None -> ()
           | Some _ ->
               raise_error l' "duplicate field name definition"
                 Name.pp fn'
       in
       let ctxt =
         ctxt_add 
           (fun x -> x.f_env) 
           (fun x y -> { x with f_env = y })
           ctxt 
           (fn', field_descr)
       in
         check_free_tvs tvs_set typ;
         (((fn,l'),sk1,src_t), ctxt))
    ctxt
    recs

let rec build_variant build_descr tvs_set (ctxt : defn_ctxt) 
      (vars : Ast.ctor_def lskips_seplist) 
      : (name_l * lskips * src_t lskips_seplist) lskips_seplist * defn_ctxt =
  Seplist.map_acc_left
    (fun (Ast.Cte(ctor_name,sk1,typs)) ctxt ->
       let l' = Ast.xl_to_l ctor_name in 
       let src_ts =
         Seplist.map 
           (fun t ->
              typ_to_src_t anon_error ignore ctxt.all_tdefs ctxt.cur_env t) 
           (Seplist.from_list typs)
        in
        let ctn = Name.from_x ctor_name in
        let ctn' = Name.strip_lskip ctn in
        let constr_descr = build_descr ctn' src_ts in
        let () = 
          match Nfmap.apply ctxt.new_defs.v_env ctn' with
            | None -> ()
            | Some(Constr _) ->
                raise_error l' "duplicate constructor definition"
                  Name.pp ctn'
            | Some(Val(c)) ->
                begin
                  match c.env_tag with
                    | K_method ->
                        raise_error l' "constructor already defined as a class method name"
                          Name.pp ctn'
                    | K_val | K_let | K_target _ ->
                       raise_error l' "constructor already defined as a top-level variable binding" 
                         Name.pp ctn'
                end
        in
        let ctxt =
          ctxt_add 
            (fun x -> x.v_env) 
            (fun x y -> { x with v_env = y })
            ctxt 
            (ctn', constr_descr)
        in
          List.iter (fun (t,_) -> check_free_tvs tvs_set t) typs;
          (((ctn,l'),sk1,src_ts), ctxt))
    ctxt
    vars

let build_ctor_def (mod_path : Name.t list) (context : defn_ctxt)
      type_name tvs td
      : (name_l * tyvar list * texp) * defn_ctxt= 
  let l = Ast.xl_to_l type_name in
  let tvs = List.map a_l_to_tyvar tvs in
  let tvs_set = 
    tvs_to_set 
      (List.map (fun (_,tv,l) -> (Tyvar.from_rope tv, l)) tvs)
  in
  let tn = Name.from_x type_name in
  let type_path = Path.mk_path mod_path (Name.strip_lskip tn) in
    match td with
      | None -> 
          (((tn,l),tvs,Te_opaque), context)
      | Some(sk3, Ast.Te_abbrev(t)) -> 
          (((tn,l), tvs,
            Te_abbrev(sk3,
                      typ_to_src_t anon_error ignore context.all_tdefs context.cur_env t)),
           context)
      | Some(sk3, Ast.Te_record(sk1',ntyps,sk2',semi,sk3')) ->
          let ntyps = Seplist.from_list_suffix ntyps sk2' semi in
          let field_names = 
            List.fold_right 
              (fun (field_name,_,_) s -> 
                 NameSet.add (Name.strip_lskip (Name.from_x field_name)) s) 
              (Seplist.to_list ntyps)
              NameSet.empty 
          in
          let (recs,ctxt) =
            build_record 
              (fun fname t ->
                 { field_binding = Path.mk_path mod_path fname;
                   field_tparams =
                     List.map (fun (_,tv,_) -> Tyvar.from_rope tv) tvs;
                   field_tconstr = type_path;
                   field_arg = t;
                   field_names = field_names; })
              tvs_set
              context
              ntyps
          in
            (((tn,l), tvs, Te_record(sk3,sk1',recs,sk3')), ctxt)
      | Some(sk3, Ast.Te_variant(sk_init_bar,bar,ntyps)) ->
          let ntyps = Seplist.from_list_prefix sk_init_bar bar ntyps in
          let ctor_names = 
            List.fold_right 
              (fun (Ast.Cte(ctor_name,_,_)) s -> 
                 NameSet.add (Name.strip_lskip (Name.from_x ctor_name)) s) 
              (Seplist.to_list ntyps)
              NameSet.empty 
          in
          let (vars,ctxt) =
            build_variant
              (fun cname ts ->
                 Constr({ constr_binding = Path.mk_path mod_path cname;
                          constr_tparams =
                            List.map (fun (_,tv,_) -> Tyvar.from_rope tv) tvs;
                          constr_args = 
                            Seplist.to_list_map (fun t -> annot_to_typ t) ts;
                          constr_tconstr = type_path;
                          constr_names = ctor_names; }))
              tvs_set
              context
              ntyps
          in
            (((tn,l),tvs,Te_variant(sk3,vars)), ctxt)

(* Builds the constructors and fields for a type definition, and the typed AST
 * *) 
let rec build_ctor_defs (mod_path : Name.t list) (ctxt : defn_ctxt) 
      (tds : Ast.td lskips_seplist) 
      : ((name_l * tyvar list * texp) lskips_seplist * defn_ctxt) =
  Seplist.map_acc_left
    (fun td ctxt -> 
       match td with
         | Ast.Td(type_name, tvs, sk3, td) ->
             build_ctor_def mod_path ctxt type_name tvs (Some (sk3,td))
         | Ast.Td_opaque(type_name, tvs) ->
             build_ctor_def mod_path ctxt type_name tvs None)
    ctxt
    tds

(* Finds a type class's path, and its methods, in the current enviroment, given
 * its name. *)
let lookup_class_p (ctxt : defn_ctxt) (id : Ast.id) : Path.t * Name.t list = 
  let p = lookup_p "class" ctxt.cur_env id in
    match Pfmap.apply ctxt.all_tdefs p with
      | None -> assert false
      | Some(Tc_class(methods)) -> (p, methods)
      | Some(Tc_abbrev _) ->
          raise_error (match id with Ast.Id(_,_,l) -> l)
            "type constructor used as type class" Ident.pp (Ident.from_id id)

(* Process the "forall 'a. (C 'a) =>" part of a type,  Returns the bound
 * variables both as a list and as a set *)
let check_constraint_prefix (ctxt : defn_ctxt) 
      : Ast.c_pre -> 
        constraint_prefix option * 
        Tyvar.t list * 
        TVset.t * 
        (Path.t * Tyvar.t) list =
  function
    | Ast.C_pre_empty ->
        (None, [], TVset.empty, [])
    | Ast.C_pre_forall(sk1,tvs,sk2,Ast.Cs_empty) ->
        let tyvars = List.map a_l_to_tyvar2 tvs in
          (Some(Cp_forall(sk1, 
                          List.map a_l_to_tyvar tvs, 
                          sk2, 
                          None)),  
           List.map fst tyvars,
           tvs_to_set tyvars,
           [])
    | Ast.C_pre_forall(sk1,tvs,sk2,Ast.Cs_list(c,sk3)) ->
        let tyvars = List.map a_l_to_tyvar2 tvs in
        let tyvarset = tvs_to_set (List.map a_l_to_tyvar2 tvs) in
        let constraints = 
          let cs =
            List.map
              (fun (Ast.C(id, (Ast.A_l((_,tv),l) as a_l)),sk) ->
                 let (p,_) = lookup_class_p ctxt id in
                   begin
                     if TVset.mem (Tyvar.from_rope tv) tyvarset then
                       ()
                     else
                       raise_error l "unbound type variable" 
                         Tyvar.pp (Tyvar.from_rope tv)
                   end;
                   (((Ident.from_id id, 
                     a_l_to_tyvar a_l),
                    sk),
                   (p, Tyvar.from_rope tv)))
              c
          in
            (Cs_list(Seplist.from_list (List.map fst cs),sk3), List.map snd cs)
        in
          (Some(Cp_forall(sk1, 
                          List.map a_l_to_tyvar tvs, 
                          sk2, 
                          Some(fst constraints))),
           List.map fst tyvars,
           tyvarset,
           snd constraints)

(* Check a "val" declaration. The name must not be already defined in the
 * current sequence of definitions (e.g., module body) *)
let check_val_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (Ast.Val_spec(sk1, xl, sk2, Ast.Ts(cp,typ))) =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let (src_cp, tyvars, tyvarset, sem_cp) = check_constraint_prefix ctxt cp in
  let () = check_free_tvs tyvarset typ in
  let src_t = typ_to_src_t anon_error ignore ctxt.all_tdefs ctxt.cur_env typ in
  let () = 
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(Constr _) ->
          raise_error l' "specified variable already defined as a constructor"
            Name.pp n'
      | Some(Val(c)) ->
          begin 
            match c.env_tag with
              | K_method ->
                  raise_error l' "specified variable already defined as a class method name"
                    Name.pp n'
              | K_val | K_target _ -> 
                  raise_error l' "specified variable already specified"
                    Name.pp n'
              | K_let -> 
                  raise_error l' "specified variable already defined"
                    Name.pp n'
          end
  in
  let v =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = tyvars;
      const_class = sem_cp;
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_val;
      substitutions = Targetmap.empty }
  in
    (ctxt_add 
       (fun x -> x.v_env) 
       (fun x y -> { x with v_env = y })
       ctxt (n',Val(v)),
     (sk1, (n,l'), sk2, (src_cp, src_t)))

(* Check a method definition in a type class.  mod_path is the path to the
 * enclosing module. class_p is the path to the enclosing type class, and tv is
 * its type parameter. *)
let check_class_spec l (mod_path : Name.t list) (ctxt : defn_ctxt)
      (class_p : Path.t) (tv : Tyvar.t) (sk1,xl,sk2,typ) 
      : const_descr * defn_ctxt * _ =
  let l' = Ast.xl_to_l xl in
  let n = Name.from_x xl in
  let n' = Name.strip_lskip n in
  let tyvars = TVset.add tv TVset.empty in
  let () = check_free_tvs tyvars typ in
  let src_t = typ_to_src_t anon_error ignore ctxt.all_tdefs ctxt.cur_env typ in
  let () = 
    match Nfmap.apply ctxt.new_defs.v_env n' with
      | None -> ()
      | Some(Constr _) ->
          raise_error l' "class method already defined as a constructor"
            Name.pp n'
      | Some(Val(c)) ->
          begin
            match c.env_tag with
              | K_method ->
                  raise_error l' "duplicate class method definition"
                    Name.pp n'
              | K_val | K_let | K_target _ ->
                  raise_error l' "class method already defined as a top-level variable"
                    Name.pp n'
          end
  in
  let v =
    { const_binding = Path.mk_path mod_path n';
      const_tparams = [tv];
      const_class = [(class_p, tv)];
      const_type = src_t.typ;
      spec_l = l;
      env_tag = K_method;
      substitutions = Targetmap.empty }
  in
  let ctxt =
    (ctxt_add 
       (fun x -> x.v_env) 
       (fun x y -> { x with v_env = y })
       ctxt (n',Val(v)))
  in
    (v, ctxt, (sk1, (n,l'), sk2, src_t))

let ast_targ_to_targ : Ast.target -> target = function
  | Ast.Target_ocaml _ -> Target_ocaml
  | Ast.Target_hol _ -> Target_hol
  | Ast.Target_isa _ -> Target_isa
  | Ast.Target_coq _ -> Target_coq
  | Ast.Target_tex _ -> Target_tex

let target_opt_to_set : Ast.targets option -> Targetset.t option = function
  | None -> None
  | Some(Ast.Targets_concrete(_,targs,_)) ->
      Some(List.fold_right
             (fun (t,_) ks -> Targetset.add (ast_targ_to_targ t) ks)
             targs
             Targetset.empty)

let target_opt_to_env_tag : Targetset.t option -> env_tag = function
  | None -> K_let
  | Some(ts) -> K_target(false,ts)

let check_target_opt : Ast.targets option -> _ = function
  | None -> None
  | Some(Ast.Targets_concrete(s1,targs,s2)) -> 
      Some(s1,Seplist.from_list targs,s2)

let pat_to_name p = 
  match p.term with
    | P_var n -> { term = n; typ= p.typ; locn = p.locn; rest = (); }
    (* TODO error messages *)
    | _ -> assert false

(* check "let" definitions.  for_method should be None, unless checking a method
 * definition in an instance.  When checking an instance it should contain the
 * type that the instance is at.  In this case the returned env_tag must be
 * K_method, and the returned constraints and type variables must be empty. 
 * ts is the set of targets for which all variables must be defined (i.e., the
 * current backends, not the set of targets that this definition if for) *)
let check_val_def (ts : Targetset.t) (for_method : Types.t option) (l : Ast.l) 
      (ctxt : defn_ctxt) 
      : Ast.val_def -> 
        (* An environment representing the names bound by the definition *)
        pat_env * 
        val_def * 
        (* The type variables the definion is generalised over *)
        TVset.t * 
        (* Class constraints on the type variables *)
        (Path.t * Tyvar.t) list * 
        (* Which targets the binding is for *)
        env_tag =
  let module T = struct 
    let d = ctxt.all_tdefs 
    let i = ctxt.all_instances 
    let e = ctxt.cur_env 
    let new_module_env = ctxt.new_defs
    let targets = ts
  end 
  in
  let module Checker = Make_checker(T) in
    function
      | Ast.Let_def(sk,target_opt,lb) ->
          let target_set = target_opt_to_set target_opt in
          let env_tag = target_opt_to_env_tag target_set in
          let target_opt = check_target_opt target_opt in
          let (lbs,e_v,(tvs, constraints)) = 
            Checker.check_letbind for_method target_set l lb 
          in 
            (e_v, (Let_def(sk,target_opt,lbs)), tvs, constraints, env_tag)
      | Ast.Let_rec(sk1,sk2,target_opt,funcls) ->
          let funcls = Seplist.from_list funcls in
          let target_set = target_opt_to_set target_opt in
          let (lbs,e_v,(tvs, constraints)) = 
            Checker.check_funs for_method target_set l funcls 
          in
          let env_tag = target_opt_to_env_tag target_set in
          let target_opt = check_target_opt target_opt in
            (e_v, (Rec_def(sk1,sk2,target_opt,lbs)), tvs, constraints, env_tag)
      | _ -> assert false

(* Check that a type can be an instance.  That is, it can be a type variable, a
 * function between type variables, a tuple of type variables or the application
 * of a (non-abbreviation) type constructor to variables.  Returns the
 * variables, and which kind of type it was. *)
let rec check_instance_type_shape (ctxt : defn_ctxt) (src_t : src_t)
      : TVset.t * Ulib.Text.t =
  let l = src_t.locn in 
  let err () = 
    raise_error l "class instance type must be a type constructor applied to type variables"
      pp_type src_t.typ
  in
  let to_tyvar src_t = 
    match src_t.term with
      | Typ_var(_,t) -> (t,src_t.locn)
      | _ -> err ()
  in
  match src_t.term with
    | Typ_wild _ -> err ()
    | Typ_var(_,tv) -> (tvs_to_set [(tv,src_t.locn)], r"var")
    | Typ_fn(t1,_,t2) ->
        (tvs_to_set [to_tyvar t1; to_tyvar t2], r"fun")
    | Typ_tup(ts) ->
        (tvs_to_set (Seplist.to_list_map to_tyvar ts), r"tup")
    | Typ_app(p,ts) ->
        begin
          match Pfmap.apply ctxt.all_tdefs p.descr with
            | Some(Tc_abbrev(_,Some _)) ->
                raise_error p.id_locn "type abbreviation in class instance type"
                  Ident.pp p.id_path
            | _ -> 
                (tvs_to_set (List.map to_tyvar ts),
                 Name.to_rope (Path.to_name p.descr))
        end
    | Typ_paren(_,t,_) -> check_instance_type_shape ctxt t

(* If a definition is target specific, we only want to check it with regards to
 * the backends that we are both translating to, and that it is for *)
let change_effective_backends (backend_targets : Targetset.t) (Ast.Def_l(def,l)) = 
  match def with
    | Ast.Val_def(Ast.Let_def(_,target_opt,_) |
                  Ast.Let_inline(_,_,target_opt,_) |
                  Ast.Let_rec(_,_,target_opt,_))
    | Ast.Indreln(_,target_opt,_) ->
        begin
          match target_opt_to_set target_opt with
            | None -> None
            | Some(ts) -> 
                Some(Targetset.inter ts backend_targets)
        end
    | _ -> None 

(* backend_targets is the set of targets for which all variables must be defined
 * (i.e., the current backends, not the set of targets that this definition if
 * for) *)
let rec check_def (backend_targets : Targetset.t) (mod_path : Name.t list) 
      (ctxt : defn_ctxt) (Ast.Def_l(def,l)) semi_sk semi 
      : defn_ctxt * def_aux =
  let module T = 
    struct 
      let d = ctxt.all_tdefs 
      let i = ctxt.all_instances 
      let e = ctxt.cur_env 
      let new_module_env = ctxt.new_defs
    end 
  in
    match def with
      | Ast.Type_def(sk,tdefs) ->
          let tdefs = Seplist.from_list tdefs in
          let new_ctxt = build_type_defs mod_path ctxt tdefs in
          let (res,new_ctxt) = build_ctor_defs mod_path new_ctxt tdefs in
            (new_ctxt,Type_def(sk,res))
      | Ast.Val_def(Ast.Let_inline(sk1,sk2,target_opt,lb)) ->
          let (e_v,vd,tvs,constraints, env_tag) = 
            check_val_def backend_targets None l ctxt 
              (Ast.Let_def(sk1,target_opt,lb))
          in 
          let _ = unsat_constraint_err l constraints in
          let (sk1,sk2,target_opt,n,args,sk3,et) = 
            match vd with
              | Let_def(sk1, target_opt, (Let_val(p,src_t,sk3,e),l)) ->
                  (sk1,sk2,target_opt,pat_to_name p,[],sk3,e)
              | Let_def(sk1, target_opt, (Let_fun(n,ps,src_t,sk3,e),l)) ->
                  (sk1,sk2,target_opt,n, List.map pat_to_name ps,sk3,e)
              | _ ->
                  assert false
          in
          let sub = 
            (List.map 
               (fun x -> {x with term = Name.strip_lskip x.term})
               args, 
             et)
          in
          let ctxt = 
            add_let_defs_to_ctxt mod_path ctxt (TVset.elements tvs)
              constraints env_tag
              (Some(((match env_tag with K_target(_,ts) -> ts | _ -> assert false), sub)))
              e_v
          in
            (ctxt, Val_def(Let_inline(sk1,sk2,target_opt,n,args,sk3,et), tvs))
      | Ast.Val_def(val_def) ->
          let (e_v,vd,tvs,constraints, env_tag) = 
            check_val_def backend_targets None l ctxt val_def 
          in
            (add_let_defs_to_ctxt mod_path ctxt (TVset.elements tvs)
               constraints env_tag None e_v, 
             Val_def(vd,tvs))
      | Ast.Module(sk1,xl, sk2,sk3,Ast.Defs(defs),sk4) ->
          let l' = Ast.xl_to_l xl in
          let n = Name.from_x xl in 
          let ctxt1 = { ctxt with new_defs = empty_env } in
          let (new_ctxt,ds) = 
            check_defs backend_targets (mod_path @ [Name.strip_lskip n]) ctxt1 defs 
          in
          let ctxt2 = 
            { ctxt with all_tdefs = new_ctxt.all_tdefs;
                        new_tdefs = new_ctxt.new_tdefs; 
                        all_instances = new_ctxt.all_instances;
                        new_instances = new_ctxt.new_instances; }
          in
            (add_m_to_ctxt l' ctxt2 n new_ctxt.new_defs,
             Module(sk1,(n,l'), sk2,sk3,ds,sk4))
      | Ast.Rename(sk1,xl',sk2,i) ->
          let l' = Ast.xl_to_l xl' in
          let n = Name.from_x xl' in 
          let env = lookup_mod ctxt.cur_env i in
            (add_m_to_ctxt l' ctxt n env,
             (Rename(sk1,
                     (n,l'), 
                     sk2,
                     { id_path = Ident.from_id i;
                       id_locn = l;
                       descr = { mod_env = env; };
                       instantiation = []; })))
      | Ast.Open(sk,i) -> 
          let env = lookup_mod ctxt.cur_env i in
            ({ ctxt with cur_env = env_union ctxt.cur_env env },
             (Open(sk,
                   { id_path = Ident.from_id i;
                     id_locn = l;
                     descr = { mod_env = env; };
                     instantiation = []; })))
      | Ast.Indreln(sk, target_opt, clauses) ->
          let module T = struct include T let targets = backend_targets end in
          let module Checker = Make_checker(T) in
          let target_opt_checked = check_target_opt target_opt in
          let target_set = target_opt_to_set target_opt in
          let (cls,e_v,(tvs,constraints)) = 
            Checker.check_indrels target_set l clauses 
          in 
            (add_let_defs_to_ctxt mod_path ctxt (TVset.elements tvs) 
               constraints 
               (target_opt_to_env_tag target_set) None e_v,
             (Indreln(sk,target_opt_checked,cls)))
      | Ast.Spec_def(val_spec) ->
          let (ctxt,vs) = check_val_spec l mod_path ctxt val_spec in
            (ctxt, Val_spec(vs))
      | Ast.Class(sk1,sk2,xl,(Ast.A_l((_,tv),_) as a_l),sk4,specs,sk5) ->
          let l' = Ast.xl_to_l xl in
          let cn = Name.from_x xl in
          let cn' = Name.strip_lskip cn in
          let p = Path.mk_path mod_path cn' in
          let () = 
            match Nfmap.apply ctxt.new_defs.p_env cn' with
              | None -> ()
              | Some(p) ->
                  begin
                    match Pfmap.apply ctxt.all_tdefs p with
                      | None -> assert false
                      | Some(Tc_class _) ->
                          raise_error l' "duplicate type class definition" 
                            Name.pp cn'
                      | Some(Tc_abbrev _) ->
                          raise_error l' "type class already defined as a type constructor" 
                            Name.pp cn'
                  end
          in
          let ctxt =
            ctxt_add 
              (fun x -> x.p_env) 
              (fun x y -> { x with p_env = y })
              ctxt 
              (cn', p)
          in
          let (ctxt',vspecs,methods) = 
            List.fold_left
              (fun (ctxt,vs,methods) (a,b,c,d,l) ->
                 let (tc,ctxt,v) = 
                   check_class_spec l mod_path ctxt p (Tyvar.from_rope tv) 
                     (a,b,c,d)
                 in
                   (ctxt,
                    v::vs,
                    Path.get_name tc.const_binding::methods))
              (ctxt,[],[])
              specs
          in
          (add_d_to_ctxt ctxt' p (Tc_class(methods)),
           Class(sk1,sk2,(cn,l'),a_l_to_tyvar a_l,
                 sk4,List.rev vspecs, sk5))
      | Ast.Instance(sk1,Ast.Is(cs,sk2,id,typ,sk3),vals,sk4) ->
          (* TODO: Check for duplicate instances *)
          let (src_cs, tyvars, tyvarset, sem_cs) = 
            check_constraint_prefix ctxt cs 
          in
          let () = check_free_tvs tyvarset typ in
          let src_t = 
            typ_to_src_t anon_error ignore ctxt.all_tdefs ctxt.cur_env typ
          in
          let (used_tvs, type_path) = check_instance_type_shape ctxt src_t in
          let unused_tvs = TVset.diff tyvarset used_tvs in
          let _ = 
            if not (TVset.is_empty unused_tvs) then
              raise_error l "instance type does not use all type variables"
                TVset.pp unused_tvs
          in
          let (p, methods) = lookup_class_p ctxt id in
          let instance_name = 
            Name.from_rope
              (Ulib.Text.concat (r"_")
                 [r"Instance";
                  Name.to_rope (Path.to_name p);
                  type_path])
          in
          let instance_path = mod_path @ [instance_name] in
          let tmp_all_inst = 
            List.fold_left 
              (fun instances (p, tv) -> 
                 insert_pfmap_list instances p ([], [], { t = Tvar(tv)}, instance_path)) 
              ctxt.all_instances
              sem_cs
          in
          let tmp_ctxt = 
            { ctxt with all_instances = tmp_all_inst }
          in
          (* TODO: lexical bindings hide class methods *)
          let (e_v,vdefs) = 
            List.fold_left
              (fun (e_v,vs) (v,l) ->
                 let (e_v',v,tvs,constraints,_) = 
                   check_val_def backend_targets (Some(src_t.typ)) l tmp_ctxt v 
                 in
                 let _ = assert (constraints = []) in
                 let _ = assert (TVset.is_empty tvs) in
                 let new_e_v = 
                    match Nfmap.domains_overlap e_v e_v' with
                      | Some(v) ->
                          let l = 
                            match Nfmap.apply e_v v with
                              | Some(_,l) -> l
                              | _ -> assert false
                          in
                            raise_error l "duplicate definition in an instance" 
                              Name.pp v
                      | None ->
                          Nfmap.union e_v' e_v
                 in
                   (new_e_v, v::vs))
              (Nfmap.empty,[])
              vals
          in
          let _ = 
            List.iter
              (fun n ->
                 match Nfmap.apply e_v n with
                   | None ->
                       raise_error l "missing class method" Name.pp n
                   | Some(t) ->
                       ())
              methods
          in
          let env = 
            Nfmap.map
              (fun n (t,l) -> 
                 Val({ const_binding = Path.mk_path instance_path n;
                       const_tparams = tyvars;
                       const_class = sem_cs;
                       const_type = t;
                       (* TODO: check the following *)
                       env_tag = K_method;
                       spec_l = l;
                       substitutions = Targetmap.empty; }))
              e_v
          in
            (*Format.fprintf Format.std_formatter "%a@\n" pp_env { empty_env with v_env = env};*)
            (add_instance_to_ctxt ctxt p (tyvars, sem_cs, src_t.typ, instance_path),
             Instance(sk1,(src_cs,sk2,Ident.from_id id, src_t, sk3),
                      List.rev vdefs, sk4, env, instance_name))


and check_defs (backend_targets : Targetset.t) (mod_path : Name.t list)
              (ctxt : defn_ctxt) defs
              : defn_ctxt * def list =
  match defs with
    | [] -> (ctxt, [])
    | (Ast.Def_l(_,l) as d,sk,semi)::ds ->
        let s = if semi then Some(sk) else None in
          match change_effective_backends backend_targets d with
            | None ->
                let (ctxt,d) = 
                  check_def backend_targets mod_path ctxt d sk semi
                in
                let (ctxt,ds) = check_defs backend_targets mod_path ctxt ds in
                  (ctxt, ((d,s),l)::ds)
            | Some(new_backend_targets) ->
                if Targetset.is_empty new_backend_targets then
                  check_defs backend_targets mod_path ctxt ds
                else
                  let (ctxt,d) = 
                    check_def new_backend_targets mod_path ctxt d sk semi 
                  in
                  let (ctxt,ds) = 
                    check_defs backend_targets mod_path ctxt ds 
                  in
                    (ctxt, ((d,s),l)::ds)

let check_defs backend_targets mod_path (tdefs, instances) env 
      (Ast.Defs(defs)) =
  let ctxt = { all_tdefs = tdefs;
               new_tdefs = Pfmap.empty;  
               all_instances = instances;
               new_instances = Pfmap.empty;
               cur_env = env;
               new_defs = empty_env }
  in
  let (ctxt,b) = check_defs backend_targets mod_path ctxt defs in
    ((ctxt.all_tdefs, ctxt.all_instances, ctxt.new_instances), ctxt.new_defs, b)
