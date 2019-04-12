open Cfg
open Core

open Apron

module N = Nat_big_num

let debug msg = Debug_ocaml.print_debug 2 [] (fun _ -> msg)

let empty_env = Environment.make [||] [||]

type absvalue =
  | ATunit
  (*| ATtrue => 1
  | ATfalse => 0 *) 
  | ATctype of Core_ctype.ctype0 (* C type as value *)
  | ATtuple of absvalue list
  | ATexpr of Texpr1.t
  | ATcons of Tcons1.t
  | ATpointer of int (* TODO: naive pointer at the moment *)
  | ATunspec
  | ATtop

type 'a absstate =
  { abs_scalar: 'a Abstract1.t; (* integers and floats *)
    abs_term: absvalue SMap.t;
    mem_counter: int;
  }

module StateMonad = Monad.Make(struct type 'a t = 'a absstate end)
open StateMonad

let get_env () = get >>= fun s ->
  return @@ Abstract1.env s.abs_scalar

(*
let add_env man sym e = update @@ fun s ->
  let var = Var.of_string (Sym.show sym) in
  let env0 = Abstract1.env s.abs_scalar in
  let env =
    if Environment.mem_var env0 var then env0
    else Environment.add env0 [| var |] [||]
  in
  let abs_scalar =
    Abstract1.assign_texpr man
      (Abstract1.change_environment man s.abs_scalar env true)
      var e None
  in { s with abs_scalar }
*)

let add_env man sym e = update @@ fun s ->
  let var = Var.of_string (Sym.show sym) in
  let env0 = Abstract1.env s.abs_scalar in
  let env =
    if Environment.mem_var env0 var then env0
    else Environment.add env0 [| var |] [||]
  in
  (* add as assign *)
  let abs_scalar =
    Abstract1.assign_texpr man
      (Abstract1.change_environment man s.abs_scalar env true)
      var e None
  in
  (* and as constraint *)
  let e = Texpr1.of_expr env @@ Texpr1.to_expr e in
 (* let e = { e with Texpr1.env = env } in *)
  let te = Texpr1.binop Texpr1.Sub (Texpr1.var env var) e 
      Texpr1.Real Texpr1.Rnd in
  let cons = Tcons1.make te Tcons1.EQ in
  let ear = Tcons1.array_make env 1 in
  Tcons1.array_set ear 0 cons;
  let abs_scalar = Abstract1.meet_tcons_array man abs_scalar ear
  in { s with abs_scalar }

let add_env_pointed man n e = update @@ fun s ->
  let var = Var.of_string ("@" ^ string_of_int n) in
  let env0 = Abstract1.env s.abs_scalar in
  let env =
    if Environment.mem_var env0 var then env0
    else Environment.add env0 [| var |] [||]
  in
  let abs_scalar =
    Abstract1.assign_texpr man
      (Abstract1.change_environment man s.abs_scalar env true)
      var e None
  in { s with abs_scalar }

let rec show_absvalue = function
  | ATunit -> "unit"
  (*| ATtrue -> "true"
  | ATfalse -> "false"*)
  | ATctype cty -> String_core_ctype.string_of_ctype cty
  | ATtuple vs -> "[" ^ String.concat ";" (List.map show_absvalue vs) ^ "]"
  | ATexpr te -> "te"
  | ATpointer n -> "@" ^ string_of_int n
  | ATunspec -> "unspec"
  | ATtop -> "top"

let show_abs_scalar man st =
  let box = Abstract1.to_box man st in
  Array.iteri (fun i b ->
    Var.print Format.str_formatter @@ Environment.var_of_dim box.Abstract1.box1_env i;
    Format.pp_print_text Format.str_formatter " = ";
    Interval.print Format.str_formatter b;
    Format.pp_print_text Format.str_formatter "; "
  ) box.Abstract1.interval_array;
  Format.flush_str_formatter ()
    (*
  Abstract1.print Format.str_formatter st;
  Format.flush_str_formatter ()
     *)

let show_abs_term st =
  SMap.fold (fun k v acc ->
      acc ^ Sym.show k ^ " -> " ^ show_absvalue v ^ "; \n"
    ) st.abs_term ""

let show_absstate man = fun s ->
    (* TODO/NOTE: ignoring non scalar terms *)
    show_abs_scalar man s.abs_scalar
    (*
    SMap.fold (fun k v acc -> 
        acc ^ Sym.show k ^ "; \n")
      s.abs_term
      (show_abs_scalar s.abs_scalar)
       *)

(* Lift states to a common environment *)
let lift_common_env man (s1, s2) =
  let env1 = Abstract1.env s1.abs_scalar in
  let env2 = Abstract1.env s2.abs_scalar in
  match Environment.compare env1 env2 with
  | -2 -> (* incomparable environments *)
    assert false
  | -1 ->
    let abs_scalar = Abstract1.change_environment man s1.abs_scalar env2 true
    in ({ s1 with abs_scalar }, s2)
  | 0 -> (* equal *)
    (s1, s2)
  | 1 ->
    let abs_scalar = Abstract1.change_environment man s2.abs_scalar env1 true
    in (s1, { s2 with abs_scalar })
  | 2 ->
    let env = Environment.lce env1 env2 in
    let abs_scalar1 = Abstract1.change_environment man s1.abs_scalar env true in
    let abs_scalar2 = Abstract1.change_environment man s2.abs_scalar env true in
    ( { s1 with abs_scalar = abs_scalar1 } , { s2 with abs_scalar = abs_scalar2 } )
  | n ->
    failwith ("lift_common_env: " ^ string_of_int n)

let is_leq man s1 s2 =
  (* TODO/NOTE: this is wrong, it ignores non scalar terms *)
  let (s1, s2) = lift_common_env man (s1, s2) in
  Abstract1.is_leq man s1.abs_scalar s2.abs_scalar

let join man s1 s2 =
  (* TODO/NOTE: this is wrong, it ignores non scalar terms *)
  let (s1, s2) = lift_common_env man (s1, s2) in
  { abs_scalar = Abstract1.join man s1.abs_scalar s2.abs_scalar;
    abs_term =
      SMap.union (fun k v _ -> Some v) (* TODO *)
        s1.abs_term s2.abs_term;
    mem_counter = max s1.mem_counter s2.mem_counter;
  }

let widening man s1 s2 =
  (* TODO/NOTE: this is wrong, it ignores non scalar terms *)
  let (s1, s2) = lift_common_env man (s1, s2) in
  { abs_scalar = Abstract1.widening man s1.abs_scalar s2.abs_scalar;
    abs_term =
      SMap.union (fun k v _ -> Some v) (* TODO *)
        s1.abs_term s2.abs_term;
    mem_counter = max s1.mem_counter s2.mem_counter;
  }

let bot man =
  { abs_scalar = Abstract1.bottom man empty_env;
    abs_term = SMap.empty;
    mem_counter = 0;
  }

(* TODO: top is incorrect *)
let top man =
  { abs_scalar = Abstract1.top man empty_env;
    abs_term = SMap.empty;
    mem_counter = 0;
  }

let init_absstate = top

let is_bottom man = fun s ->
  Abstract1.is_bottom man s.abs_scalar

let rec absvalue_of_texpr ~with_sym man = function
  | TEsym x ->
    get >>= (fun s ->
          if SMap.is_empty s.abs_term then print_endline "is_empty";
          begin match SMap.find_opt x s.abs_term with
            | Some (ATpointer p) when with_sym ->
              let env0 = Abstract1.env s.abs_scalar in
              let var = Var.of_string ("@" ^ string_of_int p) in
              let env =
                if Environment.mem_var env0 var then env0
                else Environment.add env0 [| var |] [||]
              in
              return @@ ATexpr (Texpr1.var env var)
            | Some v ->
              return v
              (* return @@ ATsym x *)
            | None ->
              let env = Abstract1.env s.abs_scalar in
              let var = Var.of_string (Sym.show x) in
              return @@ ATexpr (Texpr1.var env var)
          end)
  | TEval v ->
    get_env () >>= fun env ->
    begin match v with
      | Vobject (OVinteger i)
      | Vloaded (LVspecified (OVinteger i)) ->
        let n = Ocaml_mem.case_integer_value i
          (fun n -> Coeff.s_of_int (N.to_int n))
          (fun _ -> assert false)
        in
        return @@ ATexpr (Texpr1.cst env n)
      | Vunit ->
        return @@ ATunit
      | Vtrue ->
        return @@ ATexpr (Texpr1.cst env (Coeff.s_of_int 1))
      | Vfalse ->
        return @@ ATexpr (Texpr1.cst env (Coeff.s_of_int 0))
      | v ->
        debug @@ String_core.string_of_value v;
        assert false
    end
  | TEcall (Sym (Symbol.Symbol (_, _, Some "catch_exceptional_condition")), [_; te])
  | TEcall (Sym (Symbol.Symbol (_, _, Some "conv_int")), [_; te])
  | TEcall (Sym (Symbol.Symbol (_, _, Some "conv_loaded_int")), [_; te])
    ->
    absvalue_of_texpr ~with_sym man te
  | TEcall (Sym sym, _) ->
    print_endline @@ Sym.show sym;
    assert false
  | TEcall _ ->
    assert false
  | TEundef _ ->
    assert false
  | TEctor (ctor, tes) ->
    begin match ctor, tes with
      | Ctuple, _ ->
        mapM (absvalue_of_texpr ~with_sym man) tes >>= fun tes' ->
        return @@ ATtuple tes'
      | Cspecified, [te] ->
        absvalue_of_texpr ~with_sym man te
      | _ ->
        assert false
    end
  | TEop (bop, te1, te2) ->
    absvalue_of_texpr ~with_sym man te1 >>= fun t1 ->
    absvalue_of_texpr ~with_sym man te2 >>= fun t2 ->
    begin match t1, t2 with
    | ATexpr e1, ATexpr e2 ->
      let bop = match bop with
        | OpAdd -> Texpr1.Add
        | OpSub -> Texpr1.Sub
        | OpMul -> Texpr1.Mul
        | OpDiv -> Texpr1.Div
        | OpRem_t -> Texpr1.Mod
        | OpRem_f -> Texpr1.Mod (* TODO *)
        | _ -> assert false
      in
      return @@ ATexpr (Texpr1.binop bop e1 e2 Texpr1.Int Texpr1.Rnd)
    end
  | TEaction act ->
    absvalue_of_action ~with_sym man act
  | TEnot _ ->
    assert false
  | _ ->
    assert false

and absvalue_of_action ~with_sym man = function
  | TAcreate ->
    modify (fun s ->
          (ATpointer s.mem_counter,
           { s with mem_counter = s.mem_counter + 1 })
      )
  | TAalloc ->
    assert false
  | TAstore (te_p, te_v) ->
    absvalue_of_texpr ~with_sym man te_p >>= fun av_p ->
    absvalue_of_texpr ~with_sym man te_v >>= fun av_v ->
    begin match av_p with
      (*
      | ATsym sym ->
        let rec aux sym =
          get >>= function
          | None -> assert false
          | Some s ->
            match SMap.find_opt sym s.abs_term with
            | None -> assert false
            | Some (ATpointer p) ->
              begin match av_v with
                | ATexpr e ->
                  add_env_pointed s.man p e >>= fun () ->
                  return @@ ATunit
                | _ ->
                  assert false
              end
            | Some (ATsym sym) ->
              aux sym
            | _ -> assert false
        in aux sym
          *)
      | ATpointer p ->
        get >>= begin fun s ->
              begin match av_v with
                | ATexpr e ->
                  add_env_pointed man p e >>= fun () ->
                  return @@ ATunit
                | _ ->
                  assert false
              end
        end
      | _ ->
        assert false
    end
  | TAload te_p ->
    debug "taload";
    absvalue_of_texpr ~with_sym man te_p >>= fun av_p ->
    get >>= begin fun s ->
        match av_p with
        (*
        | ATsym sym ->
          let rec aux sym =
            match SMap.find_opt sym s.abs_term with
            | None -> assert false
            | Some (ATpointer p) ->
              let env = Abstract1.env s.abs_scalar in
              let var = Var.of_string ("@" ^ string_of_int p) in
              return @@ ATexpr (Texpr1.var env var)
            | Some (ATsym sym) ->
              debug (show_abs_term s);
              flush_all ();
              assert false;
              aux sym
            | _ -> assert false
          in aux sym
           *)
        | ATpointer p ->
          let env = Abstract1.env s.abs_scalar in
          let var = Var.of_string ("@" ^ string_of_int p) in
          return @@ ATexpr (Texpr1.var env var)
        | _ ->
          assert false
    end >>= fun t ->
    debug "taload done";
    return t
  | TAkill p ->
    (* TODO *)
    return ATunit

let rec match_pattern pat te =
  match pat, te with
  | Pattern (_, CaseBase (None, _)), _
  | Pattern (_, CaseBase (Some _, _)), _ ->
    true
  | Pattern (_, CaseCtor (Cspecified, [pat])), te ->
    match_pattern pat te
  | Pattern (_, CaseCtor (Ctuple, pats)), TEctor (Ctuple, tes) ->
    if List.length pats = List.length tes then
      List.for_all (fun (pat, te) -> match_pattern pat te)
        @@ List.combine pats tes
    else
      false
  | _ -> false

let assign man pat te =
  let rec aux v = function
    | Pattern (_, CaseBase (None, _)) ->
      debug "assign aux: 1";
      return ()
    | Pattern (_, CaseBase (Some sym, _)) ->
      debug "assign aux: 2";
      begin match v with
        | ATexpr e ->
          add_env man sym e
        | _ ->
          print_endline @@ "adding term: " ^ Sym.show sym;
          update (fun s ->
              print_endline "ok";
              { s with abs_term = SMap.add sym v s.abs_term }
          )
      end
    | Pattern (_, CaseCtor (Cspecified, [pat])) ->
      debug "assign aux: 3";
      aux v pat
    | Pattern (_, CaseCtor (Ctuple, pats)) ->
      debug "assign aux: 4";
      begin match v with
        | ATtuple es ->
          List.fold_left (fun acc (e, pat) ->
              acc >>= fun () ->
              aux e pat
            ) (return ()) (List.combine es pats) >>= fun _ ->
          return ()
        | _ ->
          assert false
      end
    | _ -> assert false
  in match te with
  | TEundef _ -> update (fun _ -> top man)
  | _ ->
    absvalue_of_texpr ~with_sym:false man te >>= fun v ->
    debug "after absvalue";
    aux v pat

(* TODO: type *)
let cons_aux_foo not_flag bop e1 e2 =
  match bop with
  | OpEq ->
    ((if not_flag then Tcons1.DISEQ else Tcons1.EQ),
     Texpr1.binop Texpr1.Sub e1 e2 Texpr1.Real Texpr1.Rnd)
  | OpGt ->
    if not_flag then
      (Tcons1.SUP,
       Texpr1.binop Texpr1.Sub e1 e2 Texpr1.Real Texpr1.Rnd)
    else
      (Tcons1.SUPEQ,
       Texpr1.binop Texpr1.Sub e2 e1 Texpr1.Real Texpr1.Rnd)
  | OpLt ->
    if not_flag then
      (Tcons1.SUPEQ,
       Texpr1.binop Texpr1.Sub e1 e2 Texpr1.Real Texpr1.Rnd)
    else
      (Tcons1.SUP,
       Texpr1.binop Texpr1.Sub e2 e1 Texpr1.Real Texpr1.Rnd)
  | OpGe ->
    if not_flag then
      (Tcons1.SUP,
       Texpr1.binop Texpr1.Sub e2 e1 Texpr1.Real Texpr1.Rnd)
    else
      (Tcons1.SUPEQ,
       Texpr1.binop Texpr1.Sub e1 e2 Texpr1.Real Texpr1.Rnd)
  | OpLe ->
    if not_flag then
      (Tcons1.SUP,
       Texpr1.binop Texpr1.Sub e1 e2 Texpr1.Real Texpr1.Rnd)
    else
      (Tcons1.SUPEQ,
       Texpr1.binop Texpr1.Sub e2 e1 Texpr1.Real Texpr1.Rnd)
  | OpAnd   | OpOr -> assert false
  | OpAdd   | OpSub   | OpMul | OpDiv
  | OpRem_t | OpRem_f | OpExp -> assert false


let rec guard man g st = function
  | Cmatch (pat, te) ->
    (not (match_pattern pat te), st)
  | Cnot (Cmatch (pat, te)) ->
    (match_pattern pat te, st)
  | Cop (bop, te1, te2) ->
    let open Tcons1 in
    let m =
      absvalue_of_texpr ~with_sym:true man te1 >>= fun v1 ->
      absvalue_of_texpr ~with_sym:true man te2 >>= fun v2 ->
      return (v1, v2)
    in
    begin match run m st with
      | (ATexpr e1, ATexpr e2), st ->
        let (typ, t1) = cons_aux_foo false bop e1 e2 in
        let cons = Tcons1.make t1 typ in
        let env = Abstract1.env st.abs_scalar in
        let ear  = Tcons1.array_make env 1 in
        Tcons1.array_set ear 0 cons;
        let abs_scalar = Abstract1.meet_tcons_array man st.abs_scalar ear in
        (false, { st with abs_scalar })
      | _ ->
        assert false
    end
  | Cnot (Cop (bop, te1, te2)) ->
    let open Tcons1 in
    let m =
      absvalue_of_texpr ~with_sym:true man te1 >>= fun v1 ->
      absvalue_of_texpr ~with_sym:true man te2 >>= fun v2 ->
      return (v1, v2)
    in
    begin match run m st with
      | (ATexpr e1, ATexpr e2), st ->
        let (typ, t1) = cons_aux_foo true bop e1 e2 in
        let cons = Tcons1.make t1 typ in
        let env = Abstract1.env st.abs_scalar in
        let ear  = Tcons1.array_make env 1 in
        Tcons1.array_set ear 0 cons;
        let abs_scalar = Abstract1.meet_tcons_array man st.abs_scalar ear in
        (false, { st with abs_scalar })
      | _ ->
        assert false
    end
  | Cnot (Cnot c) ->
    guard man g st c
  | Csym x ->
    let var = Var.of_string (Sym.show x) in
    let env0 = Abstract1.env st.abs_scalar in
    let env =
      if Environment.mem_var env0 var then env0
      else Environment.add env0 [| var |] [||]
    in
    let abs_scalar =
      Abstract1.change_environment man st.abs_scalar env true
    in
    let te = Texpr1.binop Texpr1.Sub (Texpr1.var env var) (Texpr1.cst env (Coeff.s_of_int 1))
        Texpr1.Real Texpr1.Rnd in
    let cons = Tcons1.make te Tcons1.EQ in
    let ear = Tcons1.array_make env 1 in
    Tcons1.array_set ear 0 cons;
    let abs_scalar = Abstract1.meet_tcons_array man abs_scalar ear in
    (false, { st with abs_scalar })
    (*
    begin match SMap.find_opt x st.abs_term with
      | Some ATtrue ->
        (* TODO: THIS IS WRONG *)
        (* FIXME: I need to create a 4 elements lattice for booleans *)
        (false, st)
      | Some ATfalse ->
        (false, st)
      | _ ->
        assert false
    end
       *)
  | Cnot (Csym x) ->
    let var = Var.of_string (Sym.show x) in
    let env0 = Abstract1.env st.abs_scalar in
    let env =
      if Environment.mem_var env0 var then env0
      else Environment.add env0 [| var |] [||]
    in
    let abs_scalar =
      Abstract1.change_environment man st.abs_scalar env true
    in
    let te = Texpr1.binop Texpr1.Sub (Texpr1.var env var) (Texpr1.cst env (Coeff.s_of_int 0))
        Texpr1.Real Texpr1.Rnd in
    let cons = Tcons1.make te Tcons1.EQ in
    let ear = Tcons1.array_make env 1 in
    Tcons1.array_set ear 0 cons;
    let abs_scalar = Abstract1.meet_tcons_array man abs_scalar ear in
    (false, { st with abs_scalar })
    (*
    begin match SMap.find_opt x st.abs_term with
      | Some ATtrue ->
        debug @@ "SYMBOL: " ^ Sym.show x;
        (* TODO: THIS IS WRONG *)
        (* FIXME: I need to create a 4 elements lattice for booleans *)
        (false, st)
      | Some ATfalse ->
        (false, st)
      | _ ->
        assert false
    end
       *)
  | Cnot c -> (* TODO: this might be wrong *)
    let (is_bot, st) = guard man g st c in
    (not is_bot, st)
  | Cval Vtrue ->
    (true, st)
  | Cval Vfalse ->
    (false, st)
  | Cval v ->
    debug @@ String_core.string_of_value v;
    assert false
  | c ->
    debug @@ show_cond c;
    assert false

let apply man g e st =
  let tr = match Pgraph.edge e g with
    | Some (_, tr, _) -> tr
    | None -> assert false
  in
  print_endline @@ "Edge " ^ string_of_int e;
  print_endline @@ Cfg.show_transfer tr;
  print_endline @@ show_absstate man st;
  (*
  Abstract1.fdump man st.abs_scalar;
  Abstract0.print string_of_int Format.std_formatter @@ Abstract1.abstract0 st.abs_scalar;
     *)
  match tr with
  | Tskip -> st
  | Tcond c ->
    print_endline "GUARD";
    print_endline @@ show_cond c;
    Abstract1.fdump man st.abs_scalar;
    print_endline "GUARD BEFORE";
    Abstract0.print string_of_int Format.std_formatter @@ Abstract1.abstract0 st.abs_scalar;
    print_newline();
    let (is_bot, st) = guard man g st c in
    print_endline "GUARD AFTER";
    Abstract0.print string_of_int Format.std_formatter @@ Abstract1.abstract0 st.abs_scalar;
    print_newline();
    if is_bot then bot man else st
  | Tcall _ ->
    print_endline "TODO: call";
    st
  | Tassign (pat, te) ->
    debug "assign";
    let s = snd @@ run (assign man pat te) st in
    (if SMap.is_empty s.abs_term then print_endline "empty" else
       print_endline "non_empty");
    s

module F = Fixpoint.Make (struct type 'a t = 'a absstate end)
open F

let make_lattice man g =
  { bottom = (fun vtx -> bot man);
    is_bottom = (fun vtx -> is_bottom man);
    is_leq = (fun vtx -> is_leq man);
    join = (fun vst -> join man);
    join_list = (fun vtx abs_s -> List.fold_left (join man) (bot man) abs_s);
    widening = (fun vtx abs1 abs2 -> widening man abs1 abs2);
    init = (fun vtx -> init_absstate man);
    apply = (fun e st -> apply man g e st);
  }

let solve typ core =
  let aux man =
    let (v0, cfg) = Cfg.mk_main ~sequentialise:true core in
    F.run (make_lattice man cfg) cfg v0
    |> Pgraph.print stderr
        (fun v s -> string_of_int v ^ ": " ^ show_absstate man s)
        (fun e _ -> string_of_int e)
  in match typ with
  | `Box -> aux @@ Box.manager_alloc ()
  | `Oct -> aux @@ Oct.manager_alloc ()
  | `PolkaLoose -> aux @@ Polka.manager_alloc_loose ()
  | `PolkaStrict -> aux @@ Polka.manager_alloc_strict ()
  | `PolkaEq -> aux @@ Polka.manager_alloc_equalities ()
  | `Taylor1plus -> aux @@ T1p.manager_alloc ()
