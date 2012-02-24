(* Support for changing the names of top-level definitions, including removal of
 * nested modules.  We also figure out how much of each path needs to be
 * printed.
 *) 

open Typed_ast
open Util

type name_kind =
  | Nk_typeconstr
  | Nk_const
  | Nk_constr
  | Nk_field
  | Nk_module
  | Nk_class

module NKmap = 
  Finite_map.Fmap_map(struct 
                        type t = name_kind
                        let compare = Pervasives.compare 
                      end)

type top_level_renames = (Name.t list * Name.t) Types.Pfmap.t NKmap.t

let compute_rename (path : Name.t list) 
      (f : name_kind -> Name.t list -> Name.t -> (Name.t list * Name.t) option)
      (renames : top_level_renames) (nk : name_kind) (n : Name.t)
      : top_level_renames =
  match f nk path n with
    | None -> renames
    | Some(new_p) ->
        let r = 
          match NKmap.apply renames nk with
            | None -> Types.Pfmap.empty
            | Some(r) -> r
        in
        let new_r = Types.Pfmap.insert r (Path.mk_path path n, new_p) in
        let new_renames = NKmap.insert renames (nk,new_r) in
          new_renames

let compute_renames_v path f renames e_v =
  Nfmap.fold 
    (fun renames n v -> 
       let nk =
         match v with
           | Constr _ -> Nk_constr
           | Val _ -> Nk_const
       in
         compute_rename path f renames nk n)
    renames
    e_v

let compute_renames_f path f renames e_f =
  Nfmap.fold 
    (fun renames n _ -> compute_rename path f renames Nk_field n)
    renames
    e_f

(* TODO: classes in here too *)
let compute_renames_p path f renames e_p =
  Nfmap.fold 
    (fun renames n _ -> compute_rename path f renames Nk_typeconstr n)
    renames
    e_p

let rec compute_renames_m path f renames e_m =
  Nfmap.fold 
    (fun renames n e -> 
       if path = [] && 
          (Name.compare n (target_to_mname (Target_ocaml)) = 0 ||
           Name.compare n (target_to_mname (Target_hol))  = 0 ||
           Name.compare n (target_to_mname (Target_isa)) = 0)
       then
         renames
       else
         let renames = compute_rename path f renames Nk_module n in
           compute_renames (path @ [n]) f renames e)
    renames
    e_m

and compute_renames path f renames e =
  let renames = compute_renames_v path f renames e.v_env in
  let renames = compute_renames_f path f renames e.f_env in
  let renames = compute_renames_p path f renames e.p_env in
  let renames = compute_renames_m path f renames e.m_env in
    renames

(* The path argument here and below is the path to the binding before renaming
* *)
let apply_def_rename_opt renames k path n =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) -> 
        begin
          match Types.Pfmap.apply m (Path.mk_path path (Name.strip_lskip n)) with
            | None -> None
            | Some((new_p,new_n)) ->
                let new_r = Name.to_rope new_n in
                  Some(Name.lskip_rename (fun _ -> new_r) n)
        end

let apply_def_rename renames k path n =
  match apply_def_rename_opt renames k path n with
    | None -> n
    | Some(n) -> n

let apply_rename_opt path (renames : top_level_renames) k binding set_binding id =
  match NKmap.apply renames k with 
    | None -> None
    | Some(m) ->
        begin
          match Types.Pfmap.apply m binding with
            | None -> None
            | Some((new_p,new_n)) ->
                (* TODO: be smarter about this *)
                let p = Path.mk_path new_p new_n in
                let local_new_p = 
                  match new_p with
                    | [] -> []
                    | x::y ->
                        if Name.compare x (List.hd path) = 0 then
                          y
                        else
                          x::y
                in
                let i = 
                  Ident.mk_ident (List.map Name.add_lskip local_new_p)
                    (Name.add_lskip new_n)
                in
                  Some({ id with id_path = i;
                                 descr = set_binding id.descr p })
        end

let apply_rename path renames k binding set_binding id =
  match apply_rename_opt path renames k binding set_binding id with
    | None -> id
    | Some(n) -> n

let rec rename_type_opt renames src_t =
  let new_term =
    match src_t.term with
      | Typ_wild(sk) -> None
      | Typ_var(sk,tv) -> None
      | Typ_fn(t1,sk,t2) -> 
          changed2
            (fun new_t1 new_t2 -> Typ_fn(new_t1,sk,new_t2))
            (rename_type_opt renames)
            t1
            (rename_type_opt renames)
            t2
      | Typ_tup(ts) ->
          option_map
            (fun new_ts -> Typ_tup(new_ts))
            (Seplist.map_changed (rename_type_opt renames) ts)
      | Typ_app(sk1,ts,sk2,id) ->
          (* TODO: Actually rename the id *)
          changed2
            (fun new_ts new_id -> Typ_app(sk1,new_ts,sk2,new_id))
            (Seplist.map_changed (rename_type_opt renames))
            ts
            (fun _ -> None)
            id
      | Typ_paren(sk1,t,sk2) ->
          option_map
            (fun new_t -> Typ_paren(sk1,new_t,sk2))
            (rename_type_opt renames t)
  in
    option_map
      (fun new_term -> { src_t with term = new_term })
      new_term

let rec rename_type renames src_t =
  match rename_type_opt renames src_t with
    | None -> src_t
    | Some(x) -> x

let name_to_lower n = 
  if Name.starts_with_upper_letter n then
    Some(Name.uncapitalize n)
  else 
    None

let name_to_upper n = 
  if Name.starts_with_lower_letter n then
    Some(Name.capitalize n)
  else 
    None

(* TODO: add checking *)
let compute_ocaml_rename_f nk path n =
  let new_n n = 
    match nk with
      | Nk_typeconstr -> name_to_lower n
      | Nk_const -> name_to_lower n
      | Nk_constr -> name_to_upper n
      | Nk_field -> name_to_lower n
      | Nk_module -> name_to_upper n
      | Nk_class -> None
  in
    changed2
      (fun x y -> (x,y))
      (map_changed name_to_upper)
      path
      new_n
      n

(* TODO: Check that the new names are good *)
let compute_module_rename_f nk path n =
  match path with
    | [] | [_] -> None
    | x::y -> 
        let new_n = 
          Name.from_rope (BatRope.concat r"_" (List.map Name.to_rope (y @ [n])))
        in
          Some([x],new_n)

module Ctxt = struct
  let check = None
  let avoid = None
end

module E = Exps_in_context(Ctxt)
(* TODO: This I is back-end specific *)
module M = Macro_expander.Expander(Ctxt)

let rename_def_pat_macro path (renames : top_level_renames) top_level p = 
  let l = p.locn in
  let t = p.typ in
    match p.term with
      | P_as(p,sk,(n,l')) ->
          option_map 
            (fun n -> E.mk_pas l p sk (n,l') (Some(t)))
            (apply_def_rename_opt renames Nk_const path n)
      | P_var(n) ->
          option_map
            (fun n -> E.mk_pvar l n t)
            (apply_def_rename_opt renames Nk_const path n)
      | _ -> None
             
let set_constr_binding c p = { c with constr_binding = p }
let set_field_binding c p = { c with field_binding = p }
let set_const_binding c p = { c with const_binding = p }


let rename_pat_macro path renames top_level p =
  let t = p.typ in
  let l = p.locn in
    match p.term with
      | P_constr(c,ps) ->
          option_map
            (fun c -> E.mk_pconstr l c ps (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding set_constr_binding c)
      | P_record(sk1,fields,sk2) ->
          option_map
            (fun new_fields -> 
               E.mk_precord l sk1 new_fields sk2 (Some(t)))
            (Seplist.map_changed
               (fun (fid,sk,p) ->
                  option_map
                    (fun new_fid -> (new_fid,sk,p))
                    (apply_rename_opt path renames Nk_field 
                       fid.descr.field_binding set_field_binding fid))
               fields)
      | P_typ(sk1,p,sk2,src_t,sk3) ->
          option_map 
            (fun new_t -> E.mk_ptyp l sk1 p sk2 new_t sk3 (Some(t)))
            (rename_type_opt renames src_t)
      | _ -> None

let rename_def_pat path renames p =
  M.expand_pat true p 
    (Macro_expander.list_to_bool_mac 
       [rename_def_pat_macro path renames;
        rename_pat_macro path renames])

let rename_pat path renames p =
  M.expand_pat true p (rename_pat_macro path renames)

let rename_exp_macro path renames (e : exp) : exp option =
  let do_fields fields =
    Seplist.map_changed
      (fun (fid,sk,e,l) ->
         option_map
           (fun new_fid -> (new_fid,sk,e,l))
           (apply_rename_opt path renames Nk_field fid.descr.field_binding 
              set_field_binding fid))
      fields
  in
  let l = exp_to_locn e in
  let t = exp_to_typ e in
    match E.exp_to_term e with
      | Constant(c) ->
          option_map
            (fun new_c -> E.mk_const l new_c (Some(t)))
            (apply_rename_opt path renames Nk_const c.descr.const_binding set_const_binding c)
      | Constructor(c) ->
          option_map
            (fun c -> E.mk_constr l c (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding 
               set_constr_binding c)
      | Tup_constructor(c,sk1,es,sk2) ->
          option_map
            (fun c -> E.mk_tup_ctor l c sk1 es sk2 (Some(t)))
            (apply_rename_opt path renames Nk_constr c.descr.constr_binding 
               set_constr_binding c)
      | Record(sk1,fields,sk2) ->
          option_map
            (fun new_fields -> 
               E.mk_record l sk1 new_fields sk2 (Some(t)))
            (do_fields fields)
      | Record_coq(_, sk1, fields, sk2) ->
          (* TODO: is this right *)
          option_map
            (fun new_fields -> 
               E.mk_record_coq l sk1 new_fields sk2 (Some(t)))
            (do_fields fields)
      | Recup(sk1,e,sk2,fields,sk3) ->
          option_map
            (fun new_fields -> 
               E.mk_recup l sk1 e sk2 new_fields sk3 (Some(t)))
            (do_fields fields)
      | Field(e,sk,fid) ->
          option_map
            (fun new_fid ->
               E.mk_field l e sk new_fid (Some(t)))
            (apply_rename_opt path renames Nk_field fid.descr.field_binding 
               set_field_binding fid)
      | Typed(sk1,e,sk2,src_t,sk3) ->
          option_map 
            (fun new_t -> E.mk_typed l sk1 e sk2 new_t sk3 (Some(t)))
            (rename_type_opt renames src_t)
      | _ -> None

let rename_exp path renames = 
  M.expand_exp (rename_exp_macro path renames, rename_pat_macro path renames)

let rec rename_def renames path ((d,s),l) =
  (*let l_unk = Ast.Trans("fix_ocaml_names_defs") in*)
  let do_fields fields =
    Seplist.map
      (fun ((n,l),sk,t) ->
         ((apply_def_rename renames Nk_field path n, l),sk,t))
      fields
  in
  let res = 
    match d with
      | Type_def(s,tdefs) ->
          let new_tdefs = 
            Seplist.map
              (fun (s1,tvs,s2,(n,l),texp) ->
                 let new_texp = 
                   match texp with
                     | Te_opaque -> Te_opaque
                     | Te_abbrev(s,t) ->
                         Te_abbrev(s, rename_type renames t)
                     | Te_record(s3,s1,fields,s2) ->
                         Te_record(s3,s1,do_fields fields,s2)
                     | Te_record_coq(s3,(n,l),s1,fields,s2) ->
                         (* TODO: Is this right for n? *)
                         let new_n = 
                           apply_def_rename renames Nk_constr path n
                         in
                           Te_record_coq(s2,(new_n,l),s1, do_fields fields, s2)
                     | Te_variant(s,vars) ->
                         let new_vars = 
                           Seplist.map
                             (fun ((n,l),s1,t) ->
                                let new_n = 
                                  apply_def_rename renames Nk_constr path n
                                in
                                  ((new_n,l),s1,t))
                             vars
                         in
                           Te_variant(s,new_vars)
                     | Te_variant_coq(s,vars) ->
                         (* FZ asks: this should never happen...  not implemented *)
                         failwith "Cannot happen in ocaml_fix_names_defs - variant"
                 in
                   (s1,tvs,s2,
                    (apply_def_rename renames Nk_typeconstr path n,l),
                    new_texp))
              tdefs
          in
            Type_def(s,new_tdefs)
      | Val_def(Let_def(s1,targets,(Let_val(p,topt,sk,e),l)),tvs) ->
          let new_p = rename_def_pat path renames p in
          let new_topt =
            option_map
              (fun (sk,t) -> (sk, rename_type renames t))
              topt
          in
          let new_e = rename_exp path renames e in
            Val_def(Let_def(s1,targets,(Let_val(new_p,new_topt,sk,new_e),l)),tvs)
      | Val_def(Let_def(s1,targets,(Let_fun(n,ps,topt,s2,e),l)),tvs) ->
          let new_n = 
            { n with term = apply_def_rename renames Nk_const path n.term } 
          in
          let new_ps = List.map (rename_pat path renames) ps in
          let new_e = rename_exp path renames e in
          let new_t = 
            option_map
              (fun (sk,t) -> (sk,rename_type renames t))
              topt
          in
            Val_def(Let_def(s1,targets,(Let_fun(new_n,new_ps,new_t,s2,new_e),l)),tvs)
      | Val_def(Rec_def(s1,s2,targets,clauses),tvs) ->
          let new_clauses =
            Seplist.map
              (fun (n,ps,topt,s1,e) -> 
                 let new_n = 
                   { n with term = apply_def_rename renames Nk_const path n.term } 
                 in
                 let new_ps = List.map (rename_pat path renames) ps in
                 let new_t = 
                   option_map
                     (fun (sk,t) -> (sk, rename_type renames t))
                     topt
                 in
                 let new_e = rename_exp path renames e in
                   (new_n,new_ps,new_t,s1,new_e))
              clauses
          in
            Val_def(Rec_def(s1,s2,targets,new_clauses),tvs)
      | Open(s1,m) ->
          (* TODO: open*)
          Open(s1,m)
      | Module(s1,(n,l),s2,s3,ds,s4) ->
          let new_n = apply_def_rename renames Nk_module path n in
          let new_ds = 
            rename_defs renames (path @ [Name.strip_lskip n]) ds 
          in
            Module(s1,(new_n,l),s2,s3,new_ds,s4)
      (* TODO: Other definition forms *)
      | x -> x
  in
    ((res,s),l)

and rename_defs renames path defs =
  match defs with
    | [] -> []
    | d::ds ->
        rename_def renames path d :: rename_defs renames path ds

let rename_ocaml p env defs =
  let renames = compute_renames [] compute_ocaml_rename_f NKmap.empty env in
    (*
    Format.fprintf Format.std_formatter "%a@\n"
      (NKmap.pp_map (fun _ _ -> ()) 
         (Types.Pfmap.pp_map Path.pp 
            (fun ppf (v1,v2) -> Path.pp ppf (Path.mk_path v1 v2)))) renames;
     *)
    rename_defs renames p defs

let rename_nested_module p env defs =
  let renames = compute_renames [] compute_module_rename_f NKmap.empty env in
    (*
    Format.fprintf Format.std_formatter "%a@\n"
      (NKmap.pp_map (fun _ _ -> ()) 
         (Types.Pfmap.pp_map Path.pp 
            (fun ppf (v1,v2) -> Path.pp ppf (Path.mk_path v1 v2)))) renames;
     *)
    rename_defs renames p defs

let flatten_modules_macro path env ((d,s),l) =
  let l_unk = Ast.Trans("flatten_modules") in
    match d with
      | Module(sk1,n,sk2,sk3,ds,sk4) ->
          let mod_shell = ((Module(sk1,n,sk2,sk3,[],sk4),s),l) in
          let com = ((Comment(mod_shell),None),l_unk) in
            Some((env,com::ds))
      | _ -> None

let flatten_modules n e d = 
  snd (Def_trans.process_defs [] flatten_modules_macro n e d)
