open Typed_ast
type def_macro = Name.t list -> env -> def -> (env * def list) option

let rec list_to_mac = function
  | [] -> (fun p e d -> None)
  | m1::ms ->
      let ms_f = list_to_mac ms in
        (fun p e d ->
           match m1 p e d with
             | None -> ms_f p e d
             | Some((e,d)) -> Some((e,d)))

let rec process_defs path trans mod_name env defs = 
  let sub_env = 
    match Nfmap.apply env.m_env mod_name with
      | None -> assert false
      | Some(x) -> x
  in
  let rec p env defs =
    match defs with
      | [] -> (env,[])
      | def::defs ->
          begin
            match trans (mod_name::path) env def with
              | Some((env',def')) ->
                  p env' (def'@defs)
              | None -> 
                  let (env',def') = 
                    match def with
                      | ((Module(sk1,(n,l'),sk2,sk3,ds,sk4),s),l) ->
                          let (env',ds') = 
                            process_defs (mod_name::path) trans (Name.strip_lskip n) env ds 
                          in
                            (env',((Module(sk1,(n,l'),sk2,sk3,ds',sk4),s),l))
                      | _ -> (env,def)
                  in
                  let (env'', defs') = p env' defs in
                    (env'', def'::defs')
          end
  in
  let (sub_env',defs') = p sub_env defs in
    ({ env with m_env = Nfmap.insert env.m_env (mod_name, sub_env') },
     defs')

let simple_def d = [((d,None),Ast.Unknown)]

let remove_vals _ env (((d,s),l) as def) =
  match d with
    | Val_spec _ ->
        Some((env, simple_def (Comment(def))))
    | _ -> None

let remove_indrelns _ env (((d,s),l) as def) =
  match d with
    | Indreln _ ->
        Some((env, simple_def (Comment(def))))
    | _ -> None

let remove_opens _ env (((d,s),l) as def) =
  match d with
    | Open _ ->
        Some((env, simple_def (Comment(def))))
    | _ -> None

let remove_classes _ env (((d,s),l) as def) =
  match d with
    | Class _ ->
        Some((env, simple_def (Comment(def))))
    | _ -> None

(* For Coq, add return types to function definitions that have type variables *)
let type_annotate_definitions _ env ((d,s),l) =
  match d with
    | Val_def(Let_def(sk1,topt,(Let_val(ps,Some _,sk2,e),l')),tvs) ->
        None
    | Val_def(Let_def(sk1,topt,(Let_val(ps,None,sk2,e),l')),tvs) ->
        if Types.TVset.is_empty (Types.free_vars (exp_to_typ e)) then
          None
        else
          let module C = Exps_in_context(struct 
                                           let avoid = None
                                           let check = None
                                         end)
         in
          let t = (None,C.t_to_src_t (exp_to_typ e)) in
            Some
              (env,
               [((Val_def(Let_def(sk1,topt,(Let_val(ps,Some t,sk2,e),l')),tvs),
                  s),l)])
    | Val_def(Let_def(sk1,topt,((Let_fun(n,ps,Some _,sk2,e),l'))),tvs) ->
        None
    | Val_def(Let_def(sk1,topt,((Let_fun(n,ps,None,sk2,e),l'))),tvs) ->
        if Types.TVset.is_empty (Types.free_vars (exp_to_typ e)) then
          None
        else
          let module C = Exps_in_context(struct 
                                           let avoid = None
                                           let check = None
                                         end)
         in
          let t = (None,C.t_to_src_t (exp_to_typ e)) in
            Some
              (env,
               [((Val_def(Let_def(sk1,topt,((Let_fun(n,ps,Some t,sk2,e),l'))),tvs), s), l)])
    (* TODO: Rec_def *)
    | _ -> None


let instance_to_module _ env ((d,s),l) =
  let l_unk = Ast.Trans("instance_to_module") in
    match d with
      | Instance(sk1, (prefix, sk2, id, t, sk3), vdefs, sk4, v_env,inst_name) ->
          let env =
            { env with m_env = 
                Nfmap.insert env.m_env 
                  (inst_name, {empty_env with v_env = v_env }) }
          in
          let m = 
            Module(sk1, (Name.add_lskip inst_name, l_unk), sk2, None, 
                   List.map (fun d -> ((Val_def(d,Types.TVset.empty),None), l_unk)) vdefs,
                   sk4)
          in
            Some((env,[((m,s),l)]))
      | _ ->
          None

let find_target target targets =
  let rec f = function
    | [] -> false
    | t'::l ->
        if ast_target_compare target t' = 0 then
          true
        else
          f l
  in
    f (Seplist.to_list targets)

let get_name def l = match def with

  | Indreln(_,_,clauses) -> (match Seplist.to_list clauses with 
    | [] ->  
        raise (Util.TODO(l, "Error while pruning target definitions: empty Indreln clauses in get_name [debug]"))
        
    | ((_,_,_,_,_,name,_)::cs) -> Name.strip_lskip name.term     
    )
  
  | Val_def(Rec_def(_,_,_,clauses),tvs) -> (match Seplist.to_list clauses with

    (* in a Rec_def, the constant names of all clauses should be the same, so we
     * check only the first TODO: check! *)
    
    | [] ->  
        raise (Util.TODO(l, "Error while pruning target definitions: empty Rec_def clauses in get_name [debug]"))

    | ((name,_,_,_,_)::cs) -> Name.strip_lskip name.term     
    )

  | Val_def(Let_def(_,_,lb),tvs) -> (match lb with 
    
    | (Let_fun(name,_,_,_,_), _) -> 
        Name.strip_lskip name.term
    
    | (Let_val(pat,_,_,_), _) ->  
        (match pat.term with
      
      | P_var name -> 
          Name.strip_lskip name
          
      | _ -> 
        raise (Util.TODO(l, "Error while pruning target definitions: unmatched Let_val case in get_name [debug]"))
      ))
  | Val_def(Let_inline(_,_,_,name,_,_,_), _) -> Name.strip_lskip name.term
  | _ -> 
    raise (Util.TODO(l, "Error while pruning target definitions: unmatched top-level case in get_name [debug]"))


let prune_target_bindings target defs =

  (* given a list constant name and a list of definition, rem_dups removes all
   * duplicate definitions (i.e. with the same name) from the list *)
  let rec rem_dups name = function 
    | [] -> []
    | ((def,s),l)::defs -> 
        (match def with 
      | (Val_def _ | Indreln _) -> 
          if (Name.compare name (get_name def l) = 0) then
            rem_dups name defs
          else 
            ((def,s),l) :: rem_dups name defs
      | d -> ((d,s),l) :: rem_dups name defs
    )
  in

  (* def_walker walks over a list of definitions, checks for each def if it is a 
   * target specific one, in which case it invokes rem_dups with both, the
   * already checked defs and the remaining defs *)
  let rec def_walker target acc =  function
    | [] -> List.rev acc

    | ((def,s),l)::defs -> match def with

      | (Val_def(Let_def(_,Some(_,targs,_),_),_) |
         Val_def(Rec_def(_,_,Some(_,targs,_),_),_) |
         Indreln(_,Some(_,targs,_),_) ) as d -> 
          if find_target target targs then 
              let name = get_name d l in
              let acc' = rem_dups name acc in  
              let defs' = rem_dups name defs in
            def_walker target (((def,s),l) :: acc') defs' 
          else
            def_walker target acc defs
      
      | d -> def_walker target (((d,s),l) :: acc) defs

  in def_walker target [] defs

