open Typed_ast
open Types
open Process_file

let (^^) = Filename.concat

let tds = 
  [(Path.listpath, Tc_abbrev([Tyvar.from_rope r"a"], None));
   (Path.setpath, Tc_abbrev([Tyvar.from_rope r"a"], None));
   (Path.numpath, Tc_abbrev([], None));
   (Path.stringpath, Tc_abbrev([], None));
   (Path.boolpath, Tc_abbrev([], None));
   (Path.unitpath, Tc_abbrev([],None))]

let initial_d : Types.type_defs = 
  List.fold_right (fun x y -> Types.Pfmap.insert y x) tds Types.Pfmap.empty

let initial_env : Typed_ast.env =
  { m_env = Nfmap.empty;
    v_env = Nfmap.empty;
    f_env = Nfmap.empty;
    p_env = Nfmap.from_list 
              [(Name.from_rope r"bool", Path.boolpath);
               (Name.from_rope r"set", Path.setpath);
               (Name.from_rope r"list", Path.listpath);
               (Name.from_rope r"string", Path.stringpath);
               (Name.from_rope r"unit", Path.unitpath);
               (Name.from_rope r"num", Path.numpath)] }

let space = Str.regexp "[ \t\n]+"

let read_constants file =
  let i = open_in file in
  let rec f () =
    try 
      let s = input_line i in
        List.map BatRope.of_latin1 (Str.split space s) @ f ()
    with
      | End_of_file ->
          close_in i;
          []
  in f()

type t = 
    ((type_defs * instance list Pfmap.t) * Typed_ast.env) *
    (Typed_ast.target option * BatRope.t list) list

let filename_to_mod file =
  BatRope.of_latin1 (String.capitalize (Filename.basename (Filename.chop_extension file))) 

let process_lib target file mod_name init_env =
  let mp = 
    match target with
      | None -> []
      | Some(n) -> [(target_to_mname n)]
  in
  let ast = parse_file file in
  let ((tdefs,instances,_),new_defs,_) =
    Process_file.check_ast_as_module mp init_env mod_name ast
  in
    ((tdefs,instances), new_defs)

let add_lib e1 e2 = env_union e1 e2

let add_open_lib k e1 e2 =
  match Nfmap.apply e2.m_env (Name.from_rope k) with
    | Some e ->
        env_union (env_union e1 e2) e
    | None ->
        assert false

(* Process a library for the given target and open it in the current init_env *)
let proc_open target file (td,env) =
  let mod_name = filename_to_mod file in
  let (td, new_env) = process_lib target file mod_name (td,env) in
    (td, add_open_lib mod_name env new_env)

(* Process a library for the given target *)
let proc target file (td,env) =
  let mod_name = filename_to_mod file in
  let (td, new_env) = process_lib target file mod_name (td,env) in
    (td, add_lib env new_env)

(* TODO: Add to the constants *)
let add_to_init targ file ((td,env), consts) =
  let targ_env = 
    match Nfmap.apply env.m_env (target_to_mname targ) with 
      | Some(e) -> e
      | None -> 
          assert false
  in
  let p = 
    match targ with
      | Target_ocaml -> proc
      | Target_isa -> proc_open
      | Target_coq -> proc
      | Target_hol -> proc_open
      | Target_tex -> assert false
  in
  let starg = Some(targ) in
  let (new_td,new_env) = p starg file (td,targ_env) in
    ((new_td, 
      { env with m_env = Nfmap.insert env.m_env (target_to_mname targ, new_env) }), 
     consts)

module Initial_libs (P : sig val path : string end) = struct
  open P

  let td = (initial_d, Pfmap.empty)

  let full_filename targ f = 
    List.fold_right Filename.concat [path; target_to_string targ] (f ^ ".lem")

  (* HOL Env *)
  let (td,hol_env) = 
    List.fold_left
      (fun init_env t -> proc_open (Some(Target_hol)) (full_filename Target_hol t) init_env)
      (td,initial_env)
      ["min"; "bool"; "pair"; "arithmetic"; "pred_set"; "finite_map"; "list"; "string"; "sorting"; "set_relation"]

  let target = Target_ocaml

  (* TODO: Remove so that the OCaml env can't refer to the HOL env *)
  let env =
    { initial_env with 
          m_env = 
            Nfmap.from_list [(target_to_mname Target_hol, hol_env)] }

  
  (* OCAML Env *)
  let (td,ocaml_perv) = proc_open (Some(target)) (full_filename Target_ocaml "pervasives") (td,env)

  let (td,ocaml_env) = 
    List.fold_left
      (fun init_env t -> proc (Some(Target_ocaml)) (full_filename Target_ocaml t) init_env)
      (td,ocaml_perv)
      ["list"; "pset"; "pmap"]
  
  
  (* Isabelle Env *)
  let (td,isa_env) = 
      List.fold_left
        (fun init_env t -> proc_open (Some(Target_isa)) (full_filename Target_isa t) init_env)
        (td,initial_env)
        ["pervasives";"list";"set";"finite_Set"]   
        (* PS HACK - TEMPORARILY REMOVE IN HOPES OF GETTING HOL BUILD *)

        
  
  (*
  let (td,isa_env) =

    List.fold_left 
      (fun (td,isa_env) t -> proc (Some(Ast.Target_isa(None))) t td isa_env)
      (td,isa_perv)
      ["list"; "pred_set"]   *)  

  let env =
    { initial_env with 
          m_env = 
            Nfmap.from_list [(target_to_mname (Target_ocaml), ocaml_env);
                             (target_to_mname (Target_hol), hol_env);
                             (target_to_mname (Target_isa), isa_env)] }

   
  let (td,perv) = proc_open None (Filename.concat path "pervasives.lem") (td,env)

  let init =
    (List.fold_left (fun (td,env) t -> proc None (Filename.concat path (t ^ ".lem")) (td,env))
       (td, perv)
       ["list"; "set"; "pmap"],
     [(Some(Target_hol),
       read_constants (path ^^ target_to_string Target_hol ^^ "constants"));
      (Some(Target_isa),
       []);
      (Some(Target_ocaml),
       []);
      (Some(Target_coq),
       []);
      (None,
       []);
      (Some(Target_tex),
       [])])
end
