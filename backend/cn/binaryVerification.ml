open BinaryVerificationTypes
open Effectful.Make(Typing)
open Pp
open Resources
open ResourceTypes
open Typing
module BT = BaseTypes
module LCSet = Set.Make(LC)


let pp_term (it : IT.t) =
  Terms.dtree it
    |> CF.Pp_ast.pp_doc_tree
    |> fun s -> debug 1 (lazy s)

let debug_pp_it_tree = function
  | LogicalConstraints.T it -> pp_term it
  | LogicalConstraints.Forall (_,it) -> pp_term it

let mk_separator s = blank 1 ^^ !^ s ^^ hardline
let pp_separating_conjunction_seperator = mk_separator "∗"
let pp_magic_wand_separator = mk_separator "-∗"

let pp_mem_maps_to = !^ "↦ₘ"
let pp_mem_array_maps_to = !^ "↦ₘ∗"
let lift_parens = enclose (!^ "⌜") (!^ "⌝")

let print document = when_args_exist (fun args -> print args.coq document)


let cleanup () = when_args_exist (fun args -> close_out args.coq)

let unsupported msg =
  let fail_generic msg loc = fail (fun _ -> {loc; msg = Generic (string msg)}) in
  fail_generic ("[Unsupported] " ^ msg)

(** Imports all the required Coq modules for an aarch64 proof. *)
let get_header f = when_args_exist @@ fun args -> f @@
  !^ "(*" ^^ !^ "Automatically generated Islaris spec and proof from CN *)" ^^ hardline
  ^^ hardline
  ^^ !^ "Require Import isla.aarch64.aarch64." ^^ hardline
  ^^ !^ "Require Import " ^^ string args.coq_dir ^^ dot ^^ !^ "instrs." ^^ hardline
  ^^ hardline


let start_section = !^ "Section" ^//^ !^ "iris."
let end_section = !^ "End" ^//^ !^ "iris."
let isla_context = !^ "Context `{!islaG Σ} `{!threadG}."


(** Prints all required imports, starts a new section, and sets up a context for Iris. *)
let pp_top_parts () = get_header @@ fun header ->
  print @@ Pp.flow hardline [
    header;
    start_section;
    hardline ^^ isla_context ^^ hardline;
  ]

let pp_bottom_parts () = print @@ end_section

let spec_name fsym = Sym.pp fsym ^^ !^ "_spec"
let spec_name' fname = !^ fname ^^ !^ "_spec"


let define fsym = !^ "Definition" ^//^ spec_name fsym ^//^ !^ ": iProp Σ :="


let resource_name loc (O it)  =
  match IT.term it with
  | Sym s -> return (Sym.pp s)
  | _ -> unsupported "Name other than a symbol for resource" loc



let resource_coq_type loc = function
  | P predicate -> return @@ !^ "bv 64"
  | Q quantified_predicate ->
    match quantified_predicate.name with
    | Owned (Integer (Unsigned Long), _) -> return @@ !^ "list (bv 64)"
    | Owned (ct, _) -> unsupported "Quantified owned predicate with non-long-integer type" loc
    | PName pn -> unsupported "Quantified non-owned predicate" loc


let resource_spec precondition loc (resource, oargs) =
  let@ pp_resource_name = resource_name loc oargs in

  let@ pp_pointer_name = match pointer resource with
  | IT (Sym s, _baseType) -> return @@ Sym.pp s
  | _ -> unsupported "Resource pointers other than symbols" loc
  in

  let pp_pointer_name_unsigned = !^ "bv_unsigned " ^^ pp_pointer_name in

  let pp_bound_pointer_physical_limit pp_offset =
    let plus_offset = if pp_offset == empty then empty else plus ^/^ pp_offset in
    lift_parens @@ group @@ pp_pointer_name_unsigned ^/^ plus_offset ^/^ !^ "< 2 ^ 52"
  in

  match resource with
  | P predicate ->
    let pp_memory_maps_to = !^ "bv_unsigned" ^/^ pp_pointer_name ^/^ pp_mem_maps_to ^/^ pp_resource_name in
    let pp_bound_pointer_physical_limit = pp_bound_pointer_physical_limit empty in

    let pp_additional_predicates =
      if precondition
        then [
          pp_bound_pointer_physical_limit;
        ]
      else []
    in

    return @@ flow_map pp_separating_conjunction_seperator group
      (pp_memory_maps_to :: pp_additional_predicates)

  | Q quantified_predicate ->
     let@ pp_upper_bound_length, pp_upper_bound_bytes =
        match quantified_predicate.permission with
        | IT (Binop (And, _, IT (Binop (LT, _, (IT (Sym a, _) as it)), _)), _) ->
          let var = !^ "bv_unsigned " ^^ IT.pp it in return (var, var)
        | IT (Binop (And, _, IT (Binop (LT, _, IT (Const (Z z), _)), _)), _) ->
          let z = Z.to_int z in return (int @@ z, int @@ z * 8)
        | _ -> unsupported "Quantified predicate with permission other than a specific LT" loc
      in
      return @@ flow_map pp_separating_conjunction_seperator group
        [
          pp_pointer_name_unsigned ^/^ pp_mem_array_maps_to ^/^ pp_resource_name;
          lift_parens @@ pp_upper_bound_length ^/^ !^ "= length" ^/^ pp_resource_name;
          pp_bound_pointer_physical_limit pp_upper_bound_bytes
        ]


let pp_lcs loc global contraints global =
  let lc_to_coq_unsafe lc =
    let open Lemmata in
    let (list_mono, global) = monomorphise_dt_lists global in
    lc_to_coq_check_triv loc global list_mono lc PrevDefs.init_t
    |> Result.get_ok
    |> fst
    |> Option.get in
  let representable = function LC.T (IT (IT.Representable _, _)) -> true | _ -> false in
  let manipulate_good lc =
    (* let struct_decls = global.struct_decls in *)
    match lc with
    | LC.T (IT (IT.Good (ctype, (IT (_, BT.Loc) as t)), _)) -> Some (LC.T (IT.aligned_ (t, ctype)))
    | LC.T (IT (IT.Good _, _)) | LC.Forall _-> None
    | _ -> Some lc
  in
  contraints |>
  LCSet.map (fun lc -> debug 1 (lazy (LC.pp lc)); lc) |>
  LCSet.filter (fun lc -> not (representable lc)) |>
  LCSet.filter_map manipulate_good |>
  LCSet.elements |>
  List.map (fun lc -> lc_to_coq_unsafe lc |> lift_parens)


let pp_c_call loc stack_size (pre_ctxt : Context.t) (post_ctxt : Context.t) =
  let pp_condition ~precondition =
    let ctxt = if precondition then pre_ctxt else post_ctxt in
    let resources = ctxt.resources |> fst |> List.map fst in
    let@ pp_resources_names = ListM.mapM (fun (_,oargs) -> resource_name loc oargs) resources in
    let@ pp_resource_coq_types = ListM.mapM (fun (r,_) -> resource_coq_type loc r) resources in
    let@ pp_resources_specs = ListM.mapM (resource_spec precondition loc) resources in
    let@ global = get_global () in
    let pp_lcs =
      let contraints = if precondition
        then ctxt.constraints
        else
          let not_in_pre_ctxt lc = not (LCSet.mem lc pre_ctxt.constraints) in
          LCSet.filter not_in_pre_ctxt ctxt.constraints in
      pp_lcs loc global contraints in
    let pp_resources_with_types =
      let pp_resource_with_type resource_name resource_coq_type =
        parens (resource_name ^//^ colon ^//^ resource_coq_type) in
      flow (break 1) @@ List.map2 pp_resource_with_type pp_resources_names pp_resource_coq_types in
    let introduce_resources =
      if pp_resources_with_types == empty
      then empty
      else !^ "∃" ^//^ pp_resources_with_types ^^ !^ "," in

    let pp_let_bindings =
      let pp_args_bindings =
        let args = pre_ctxt.computational |> SymMap.bindings |> List.map fst |> List.rev in
        flow hardline @@ List.mapi (fun i s ->
          !^ "let" ^//^ Sym.pp s ^//^ !^ ":=" ^//^
            !^ "args" ^//^ !^ "!!!" ^//^ int i ^^ !^ "%nat in") args in
      let pp_rets_bindings = !^ "let ret := (rets !!! 0%nat) in" in
      if precondition then pp_args_bindings else pp_rets_bindings in

    let pp_separating_conjunction_separated_spec =
      let pp_additional_predicates =
        let pp_true = !^ "True" in
        if precondition then [] else [pp_true] in

      flow pp_separating_conjunction_seperator @@
        pp_resources_specs @
        pp_lcs global @
        pp_additional_predicates in

    return @@ flow hardline @@ List.filter ((!=) empty)
      [
        introduce_resources; (* can be empty *)
        pp_let_bindings; (* can be empty *)
        pp_separating_conjunction_separated_spec;
      ] in



    let@ pp_precondition = pp_condition ~precondition:true in
    let@ pp_postcondition = pp_condition ~precondition:false in

    let pp_spec = parens @@
      !^ "λ args sp RET," ^^
      nest 2 @@ hardline ^^
        pp_precondition ^^
        pp_separating_conjunction_seperator ^^
        !^ "RET " ^^ parens @@ !^ "λ rets," ^^
        nest 2 @@ hardline ^^
          pp_postcondition in

    let functional_app f args = group @@ f ^^ group @@ nest 2 @@ break 1 ^^ flow (break 1) args in
    return @@ functional_app (!^ "c_call") [int stack_size; pp_spec] ^^ !^ "%I."


let auto_unfold_spec fsym = !^ "Arguments" ^//^ spec_name fsym ^//^ !^ "/."

let default_proof = flow hardline [
  !^ "Proof." ^^
  nest 2 (hardline ^^ flow hardline [
    !^ "iStartProof.";
    !^ "liARun.";
    !^ "Unshelve. all: prepare_sidecond.";
    !^ "all: try bv_solve.";
  ]);
  !^ "Qed.";
]


let pp_lemma fsym =
  DwarfData.get_instructions fsym @@ fun instrs ->
  DwarfData.get_callees fsym @@ fun callees ->
    let pp_hexplain i = string @@ Dwarf.pphexplain i in
    let pp_hex i = string @@ Dwarf.pphex i in
    let pp_instr i = !^ "instr" ^//^ pp_hex i ^//^ parens (!^ "Some a" ^^ pp_hexplain i) in
    let pp_instr_body i = !^ "instr_body" ^//^ pp_hex i ^//^ spec_name fsym in
    let pp_instr_pre = !^ "□ instr_pre "  in
    let pp_instrs = List.map pp_instr instrs in
    let fn_start = List.hd instrs in

    let pp_callees = List.map
      (fun (addr,fname) -> pp_instr_pre ^^ pp_hex addr ^^ blank 1 ^^ spec_name' fname)
      callees
    in

    let pp_definition = flow pp_magic_wand_separator @@
      pp_instrs @
      pp_callees @
      pp_instr_body fn_start :: []
    in

    print @@ flow empty [
      !^ "Lemma" ^//^ Sym.pp fsym ^^ colon;
      nest 2 @@ hardline ^^ pp_definition ^^ dot;
      hardline;
      default_proof;
      hardline;
    ]


let pp_procedure fsym loc pre_ctxt post_ctxt =
  let pre_ctxt =
    (* add stack pointer as a logical constraint *)
    let sp_sym = IT.sym_ (Sym.fresh_named "sp", BT.Loc) in
    let sctypes = Sctypes.Pointer (Integer (Unsigned Long)) in
    Context.add_c (LC.t_ @@ IT.good_ (sctypes, sp_sym)) pre_ctxt in
  DwarfData.get_stack_size fsym @@ fun stack_size ->
    let pp_define = define fsym in
    let@ pp_c_call = pp_c_call loc stack_size pre_ctxt post_ctxt in
    print @@ flow hardline [
      pp_define ^^ nest 2 (hardline ^^ pp_c_call);
      empty;
      auto_unfold_spec fsym;
      empty; ];
    return ()