open Defacto_memory_types2
open Mem_common

open State

module Sym = Symbol

open Z3

(* wip *)
module Wip = struct
  let submitted : (((string * Mem.mem_iv_constraint) list) list) ref =
    ref []
  
  let to_strings () =
    let css = List.flatten !submitted in
    List.mapi (fun i (str, cs) ->
      "\n[" ^ (string_of_int i) ^ "] -- '" ^ str ^ "'\n" ^ String_mem.string_of_iv_memory_constraint cs
    ) (List.rev css)
  
  let push () =
    submitted := [] :: !submitted
  
  let pop () =
    match !submitted with
      | [] ->
          failwith "Smt.Wip.pop, empty"
      | cs::css ->
          submitted := css;
          cs
  
  let add cs =
    match !submitted with
      | [] ->
          submitted := [cs]
      | x::xs ->
          submitted := (cs@x)::xs
end



type solver_state = {
(*   allocations: allocation_id list; *)
  ctx: context;
  slv: Solver.solver;
  
  addrSort: Sort.sort;
  integerBaseTypeSort: Sort.sort;
  integerTypeSort: Sort.sort;
  basicTypeSort: Sort.sort;
  ctypeSort: Sort.sort;
  
  ivminDecl: FuncDecl.func_decl;
  ivmaxDecl: FuncDecl.func_decl;
  ivsizeofDecl: FuncDecl.func_decl;
  ivalignofDecl: FuncDecl.func_decl;
  fromptrDecl: FuncDecl.func_decl;
}

(*
type 'a solverM = ('a, solver_state) State.stateM
let (>>=) = State.bind
*)


let mk_forall ctx syms sorts expr =
  Quantifier.mk_forall ctx sorts syms expr None [] [] None None






let init_solver () : solver_state =
  let ctx = mk_context [("timeout", "")(*TODO*)] in
  
  let mk_ctor str =
    Datatype.mk_constructor_s ctx str (Symbol.mk_string ctx ("is_" ^ str)) [] [] [] in
  let integerBaseTypeSort = Datatype.mk_sort_s ctx "IntegerBaseType"
    [ mk_ctor "ichar_ibty"
    ; mk_ctor "short_ibty"
    ; mk_ctor "int_ibty"
    ; mk_ctor "long_ibty"
    ; mk_ctor "long_long_ibty"
    ; Datatype.mk_constructor_s ctx "intN_t_ibty" (Symbol.mk_string ctx "is_intN_t_ibty")
        [Symbol.mk_string ctx "intN_size"] [Some (Arithmetic.Integer.mk_sort ctx)]
        [0(*TODO: no idea with I'm doing*)]
    ; mk_ctor "intmax_t_ibty"
    ; mk_ctor "intptr_t_ibty" ] in
  
  let integerTypeSort =
    Datatype.mk_sort_s ctx "IntegerType"
      [ mk_ctor "char_ity"
      ; mk_ctor "bool_ity"
      ; Datatype.mk_constructor_s ctx "Signed_ity" (Symbol.mk_string ctx "is_Signed_ity")
          [Symbol.mk_string ctx "_Signed_ity"] [Some integerBaseTypeSort]
          [0(*TODO: no idea with I'm doing*)]
      ; Datatype.mk_constructor_s ctx "Unsigned_ity" (Symbol.mk_string ctx "is_Unsigned_ity")
          [Symbol.mk_string ctx "_Unsigned_ity"] [Some integerBaseTypeSort]
          [0(*TODO: no idea with I'm doing*)]
      ; mk_ctor "size_t_ity"
      ; mk_ctor "ptrdiff_t_ity" ] in
  
  let basicTypeSort =
    Datatype.mk_sort_s ctx "BasicType"
      [ Datatype.mk_constructor_s ctx "Integer_bty" (Symbol.mk_string ctx "is_Integer_bty")
          [Symbol.mk_string ctx "_Integer_bty"] [Some integerTypeSort]
          [0(*TODO: no idea with I'm doing*)]
      ; Datatype.mk_constructor_s ctx "Floating"
          (Symbol.mk_string ctx "is_Floating") [] [] []
      ] in
  
  let ctypeSort =
    (* TODO: Function, Struct, Union, Builtin *)
    Datatype.mk_sort_s ctx "Ctype"
      [ mk_ctor "ignore_ty"
      ; Datatype.mk_constructor_s ctx "Basic_ty" (Symbol.mk_string ctx "is_Basic_ty")
          [Symbol.mk_string ctx "_Basic_ty"] [Some basicTypeSort]
          [0(*TODO: no idea with I'm doing*)]
      ; Datatype.mk_constructor_s ctx "Array_ty" (Symbol.mk_string ctx "is_Array_ty")
          [Symbol.mk_string ctx "elem_Array_ty"; Symbol.mk_string ctx "size_Array_ty"]
          [None; Some (Arithmetic.Integer.mk_sort ctx)]
          [0; 0(*TODO: no idea with I'm doing*)]
      ; Datatype.mk_constructor_s ctx "Pointer_ty" (Symbol.mk_string ctx "is_Pointer_ty")
          [Symbol.mk_string ctx "_Pointer_ty"] [None]
          [0(*TODO: no idea with I'm doing*)] ] in
  
  let intSort = Arithmetic.Integer.mk_sort ctx in
  let slvSt = {
(*   allocations= []; *)
   ctx= ctx;
   slv= Solver.mk_solver ctx None;
   addrSort= Arithmetic.Integer.mk_sort ctx;
   integerBaseTypeSort= integerBaseTypeSort;
   integerTypeSort= integerTypeSort;
   basicTypeSort= basicTypeSort;
   ctypeSort= ctypeSort;
   ivminDecl= FuncDecl.mk_func_decl_s ctx "ivmin" [integerTypeSort] intSort;
   ivmaxDecl= FuncDecl.mk_func_decl_s ctx "ivmax" [integerTypeSort] intSort;
   ivsizeofDecl= FuncDecl.mk_func_decl_s ctx "ivsizeof" [ctypeSort] intSort;
   ivalignofDecl= FuncDecl.mk_func_decl_s ctx "ivalignof" [ctypeSort] intSort;
   fromptrDecl= FuncDecl.mk_func_decl_s ctx "fromptr" [ctypeSort; integerTypeSort; intSort] intSort;
  } in
  
  (* axiom1 ==> forall ty: Ctype, ivsizeof(ty) > 0 *)
  let axiom1 =
    let ty_sym = Symbol.mk_string ctx "ty" in
    let var_e = Quantifier.mk_bound ctx 0 ctypeSort in
    Quantifier.expr_of_quantifier (
      mk_forall ctx [ty_sym] [ctypeSort]
        (Arithmetic.mk_gt ctx (Expr.mk_app ctx slvSt.ivsizeofDecl [var_e])
                              (Arithmetic.Integer.mk_numeral_i ctx 0))
   ) in
  
  (* axiom2 ==> forall ty: Ctype, ivmin(ty) < ivmax(ty) *)
  let axiom2 =
    let ity_sym = Symbol.mk_string ctx "ity" in
    let var_e = Quantifier.mk_bound ctx 0 integerTypeSort in
    Quantifier.expr_of_quantifier (
      mk_forall ctx [ity_sym] [integerTypeSort]
        (Arithmetic.mk_lt ctx (Expr.mk_app ctx slvSt.ivminDecl [var_e])
                              (Expr.mk_app ctx slvSt.ivmaxDecl [var_e]))
   ) in
  
  Solver.add slvSt.slv [axiom1; axiom2];
  
  (* assert that all the struct/union paddings are positive *)
  begin
    Pmap.iter (fun (Sym.Symbol (tag_sym_n, _)) tagDef ->
      let xs = match tagDef with
        | Tags.StructDef z
        | Tags.UnionDef z -> z in
      List.iter (fun (Cabs.CabsIdentifier (_, membr_str), _) ->
        let padding_str = "padding__tag_" ^ string_of_int tag_sym_n ^ "__" ^ membr_str in
        Solver.add slvSt.slv [
          Arithmetic.mk_le ctx (Arithmetic.Integer.mk_numeral_i ctx 0)
                               (Expr.mk_const_s slvSt.ctx padding_str slvSt.addrSort)
        ]
      ) xs
  ) (Tags.tagDefs ())
  end;
  
  slvSt










let integerBaseType_to_expr slvSt ibty =
  let fdecls = Datatype.get_constructors slvSt.integerBaseTypeSort in
  AilTypes.(match ibty with
    | Ichar ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 0) []
    | Short ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 1) []
    | Int_ ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 2) []
    | Long ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 3) []
    | LongLong ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 4) []
    | IntN_t n ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 5) [Arithmetic.Integer.mk_numeral_i slvSt.ctx n]
    | Int_leastN_t _ ->
        failwith "TODO Smt.integerBaseType_to_expr, Int_leastN_t"
    | Int_fastN_t _ ->
        failwith "TODO Smt.integerBaseType_to_expr, Int_fastN_t"
    | Intmax_t ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 6) []
    | Intptr_t ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 7) []
  )

let integerType_to_expr slvSt (ity: AilTypes.integerType) =
  let fdecls = Datatype.get_constructors slvSt.integerTypeSort in
  AilTypes.(match ity with
    | Char ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 0) []
    | Bool ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 1) []
    | Signed ibty ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 2) [integerBaseType_to_expr slvSt ibty]
    | Unsigned ibty ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 3) [integerBaseType_to_expr slvSt ibty]
    | IBuiltin str ->
        failwith ("TODO Smt.integerType_to_expr, IBuiltin " ^ str)
    | Enum _ ->
        failwith "TODO Smt.integerType_to_expr, Enum"
    | Size_t ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 4) []
    | Ptrdiff_t ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 5) []
  )

let basicType_to_expr slvSt (bty: AilTypes.basicType) =
  let fdecls = Datatype.get_constructors slvSt.basicTypeSort in
  AilTypes.(match bty with
    | Integer ity ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 0) [integerType_to_expr slvSt ity]
    | Floating _ ->
      (* TODO: this is probably wrong *)
        Expr.mk_app slvSt.ctx (List.nth fdecls 1) []
      (*  failwith "Smt.basicType_to_expr, Floating" *)
  )

let rec ctype_to_expr slvSt ty =
  let fdecls = Datatype.get_constructors slvSt.ctypeSort in
  Core_ctype.(
    match ty with
      | ignore0 ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 0) []
      | Basic0 bty ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 1) [basicType_to_expr slvSt bty]
      | Array0 (_, None) ->
          (* Ail type error *)
          assert false
      | Array0 (elem_ty, Some n) ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 2)
            [ctype_to_expr slvSt elem_ty; Arithmetic.Integer.mk_numeral_i slvSt.ctx (Nat_big_num.to_int n)]
      | Pointer0 (_, ref_ty) ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 3)
            [ctype_to_expr slvSt ref_ty]
      | _ ->
          prerr_endline "TODO: Smt.ctype_to_expr";
          Expr.mk_const_s slvSt.ctx "ignore_ty" slvSt.ctypeSort
  )






let address_expression_of_pointer_base = function
  | PVunspecified ty ->
      failwith "PVunspecified"
  | PVnull ty ->
      failwith "PVnull"
  | PVfunction sym ->
      failwith  "PVfunction"
  | PVbase (alloc_id, pref) ->
      IVaddress alloc_id
  | PVfromint ival_ ->
      ival_


let integer_value_base_to_expr slvSt ival_ =
  let rec aux = function
    | IVunspecified ->
        failwith "IVunspecified"
    | IVconcurRead _ ->
        failwith "Smt.integer_value_base_to_expr: IVconcurRead"
    | IVconcrete n ->
        Arithmetic.Integer.mk_numeral_s slvSt.ctx (Nat_big_num.to_string n)
    | IVaddress alloc_id ->
        Expr.mk_const_s slvSt.ctx ("addr_" ^ string_of_int alloc_id) slvSt.addrSort
    | IVfromptr (ty, ity, ptrval_) ->
        (* the result of a cast from pointer to integer. The first
           parameter is the referenced type of the pointer value, the
           second is the integer type *)
        let ty_e = ctype_to_expr slvSt ty in
        let ity_e = integerType_to_expr slvSt ity in
        let ptrval_e = (* WIP *) aux (address_expression_of_pointer_base ptrval_) in
        Expr.mk_app slvSt.ctx slvSt.fromptrDecl [ty_e; ity_e; ptrval_e]
    | IVop (iop, [ival_1; ival_2]) ->
        let mk_op = function
          | IntAdd ->
              fun e1 e2 -> Arithmetic.mk_add slvSt.ctx [e1; e2]
          | IntSub ->
              fun e1 e2 -> Arithmetic.mk_sub slvSt.ctx [e1; e2]
          | IntMul ->
              fun e1 e2 -> Arithmetic.mk_mul slvSt.ctx [e1; e2]
          | IntDiv ->
              Arithmetic.mk_div slvSt.ctx 
          | IntRem_t ->
              failwith "TODO Smt: IntRem_t"
          | IntRem_f ->
              Arithmetic.Integer.mk_mod slvSt.ctx 
          | IntExp ->
              Arithmetic.mk_power slvSt.ctx  in
        mk_op iop (aux ival_1) (aux ival_2)
    | IVop _ ->
        (* Core type error *)
        assert false
    | IVmin ity ->
        Expr.mk_app slvSt.ctx slvSt.ivminDecl [integerType_to_expr slvSt ity]
    | IVmax ity ->
        Expr.mk_app slvSt.ctx slvSt.ivmaxDecl [integerType_to_expr slvSt ity]
    | IVsizeof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivsizeofDecl [ctype_to_expr slvSt ty]
    | IValignof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivalignofDecl [ctype_to_expr slvSt ty]
    | IVoffsetof (tag_sym, memb_ident) ->
      failwith "TODO Smt: IVoffsetof"
    | IVpadding (Sym.Symbol (tag_sym_n, _), Cabs.CabsIdentifier (_, membr_str)) ->
        Expr.mk_const_s slvSt.ctx ("padding__tag_" ^ string_of_int tag_sym_n ^ "__" ^ membr_str) slvSt.addrSort
    | IVptrdiff (diff_ty, (ptrval_1, sh1), (ptrval_2, sh2)) ->
        let ptrval_e1 = (* WIP *) aux (IVop (IntAdd, [ address_expression_of_pointer_base ptrval_1
                                                     ; Defacto_memory2.integer_value_baseFromShift_path sh1 ])) in
        let ptrval_e2 = (* WIP *) aux (IVop (IntAdd, [ address_expression_of_pointer_base ptrval_2
                                                     ; Defacto_memory2.integer_value_baseFromShift_path sh2 ])) in
        Arithmetic.mk_div slvSt.ctx
          (Arithmetic.mk_sub slvSt.ctx [ptrval_e1; ptrval_e2])
          (aux (Mem_simplify.lifted_simplify_integer_value_base (IVsizeof diff_ty)))
    | IVbyteof (ival_, mval) ->
        failwith "TODO Smt: IVbyteof"
    | IVcomposite ival_s ->
        failwith "TODO Smt: IVcomposite"
    | IVbitwise (ity, bwop) ->
        let is_signed = AilTypesAux.is_signed_ity ity in
        let size_ity = 64 in
        BitVector.mk_bv2int slvSt.ctx begin match bwop with
          | BW_complement ival_ ->
              BitVector.mk_not slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_))
          | BW_AND (ival_1, ival_2) ->
              BitVector.mk_and slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
          | BW_OR (ival_1, ival_2) ->
              BitVector.mk_or slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
          | BW_XOR (ival_1, ival_2) ->
              BitVector.mk_xor slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
        end is_signed
  in
  aux (Either.either_case
    (fun n -> IVconcrete n)
    (fun z -> z)
    (Mem_simplify.simplify_integer_value_base ival_)
  )





let mem_constraint_to_expr st constr =
  let rec aux = function
    | MC_empty ->
        None
    | MC_eq (IV (_, ival_1), IV (_, ival_2)) ->
        Some (Boolean.mk_eq st.ctx (integer_value_base_to_expr st ival_1) (integer_value_base_to_expr st ival_2))
    | MC_lt (IV (_, ival_1), IV (_, ival_2)) ->
        Some (Arithmetic.mk_lt st.ctx (integer_value_base_to_expr st ival_1) (integer_value_base_to_expr st ival_2))
    | MC_le (IV (_, ival_1), IV (_, ival_2)) ->
        Some (Arithmetic.mk_le st.ctx (integer_value_base_to_expr st ival_1) (integer_value_base_to_expr st ival_2))
    | MC_or (cs1, cs2) ->
        begin match (aux cs1, aux cs2) with
          | (Some e1, Some e2) ->
              Some (Boolean.mk_or st.ctx [e1; e2])
          | (Some e1, None) ->
              Some e1
          | (None, Some e2) ->
              Some e2
          | (None, None) ->
              None
        end
    | MC_conj css ->
        Some (Boolean.mk_and st.ctx (
          List.fold_left (fun acc cs ->
            match aux cs with
              | Some e ->
                  e :: acc
              | None ->
                  acc
          ) [] css
       ))
    | MC_not cs ->
        begin match aux cs with
          | Some e ->
              Some (Boolean.mk_not st.ctx e)
          | None ->
              None
        end
  in aux constr



(*
let declare_address alloc_id : unit solverM =
  (* (declare-const addr_n Addr) *)
  (* NOTE: Z3 doesn't need constant to be declared *)
  return ()
*)

let add_constraint slvSt debug_str cs =
(*  prerr_endline ("ADDING CONSTRAINT [" ^ debug_str ^ "] ==> " ^ String_mem.string_of_iv_memory_constraint cs); *)
  match mem_constraint_to_expr slvSt cs with
    | Some e ->
          Wip.add [(debug_str, cs)];
        Solver.add slvSt.slv [e]
    | None ->
        ()




open Nondeterminism2

(* TODO: silly duplication *)
type ('a, 'err, 'cs) nd_tree =
  | Thole
  | Tdeadend
  | Tbtrack_marker of ('a, 'err, 'cs) nd_tree * ('a, 'err, 'cs) nd_tree
  | Tactive of 'a
  | Tkilled of 'err kill_reason
  | Tnd of string * (string * ('a, 'err, 'cs) nd_tree) list
  | Tguard of string * 'cs * ('a, 'err, 'cs) nd_tree
  | Tbranch of string * 'cs * ('a, 'err, 'cs) nd_tree * ('a, 'err, 'cs) nd_tree

let fill_hole_with t fill =
  let rec aux = function
    | Thole ->
        Some fill
    | Tdeadend ->
        None
    | Tbtrack_marker (t1, t2) ->
        failwith ""
    | Tactive _
    | Tkilled _ ->
        None
    | Tnd (debug_str, str_ts) ->
        let (b, xs) = List.fold_right (fun (str, t) _acc ->
          match _acc with
            | (true, xs) ->
                (true, (str, t) :: xs)
            | (false, xs) ->
                begin match aux t with
                  | Some t' ->
                      (true, (str, t') :: xs)
                  | None ->
                      (false, (str, t) :: xs)
                end
        ) str_ts (false, []) in
        if b then
          Some (Tnd (debug_str, xs))
        else
          None
    | Tguard (debug_str, cs, t') ->
        begin match aux t' with
          | Some z ->
              Some (Tguard (debug_str, cs, z))
          | None ->
              None
        end
    | Tbranch (debug_str, cs, t1, t2) ->
        begin match aux t1 with
          | Some t1' ->
              Some (Tbranch (debug_str, cs, t1', t2))
          | None ->
              begin match aux t2 with
                | Some t2' ->
                    Some (Tbranch (debug_str, cs, t1, t2'))
                | None ->
                    None
              end
        end in
  match aux t with
    | Some t' ->
        t'
    | None ->
        t


let dot_from_nd_tree t =
  let saved = !Colour.do_colour in
  Colour.do_colour := false;
  let rec aux n = function
    | Thole ->
        (n+1, [string_of_int n ^ "[label= \"HOLE\"]"], [])
    | Tdeadend ->
        ( n+1, [string_of_int n ^ "[label= \"DEAD END\"]"], [])
    | Tbtrack_marker (_, t') ->
        aux n t'
    | Tactive (_, st) ->
        ( n+1
        , [string_of_int n ^"[label= \"active(" ^ string_of_int n ^ ")\n" ^
           String.escaped (String_core_run.string_of_core_state st.Driver.core_state) ^ "\"]"]
        , [] )
    | Tkilled _ ->
        ( n+1
        , [string_of_int n ^"[label= \"killed(" ^ string_of_int n ^ ")\"]"]
        , [] )
    | Tnd (debug_str, str_acts) ->
        let (n', str_ns, nodes, edges) =
          List.fold_left (fun (n', accNs, accNodes, accEdges) (str, act) ->
            let str = if debug_str = "step_constrained" then "" else str in
            let (n'', nodes, edges) = aux n' act in
            (n'', (str, n') :: accNs, nodes @ accNodes, edges @ accEdges)
          ) (n+1, [], [], []) str_acts in
        ( n'
        , (string_of_int n ^"[label= \"nd(" ^ string_of_int n ^ ")\\n[" ^ debug_str ^ "]\\n" ^
           (*String.escaped (String_core_run.string_of_core_state st.Driver.core_state)*) "ARENA" ^ "\"]") :: nodes
        , (List.map (fun (str, z) -> string_of_int n ^ " -> " ^ string_of_int z ^ "[label= \""^ String.escaped str ^ "\"]") str_ns) @ edges )
    | Tguard (_, _, act) ->
        let (n', nodes, edges) = aux (n+1) act in
        ( n'
        , (string_of_int n ^"[label= \"guard(" ^ string_of_int n ^ ")\"]") :: nodes
        , (string_of_int n ^ " -> " ^ string_of_int (n+1)) :: edges )
    | Tbranch (debug_str, _, act1, act2) ->
        let (n' , nodes1, edges1) = aux (n+1) act1 in
        let (n'', nodes2, edges2) = aux (n'+1) act2 in
        ( n''
        , (string_of_int n ^"[label= \"branch(" ^ string_of_int n ^ ")\\n[" ^ debug_str ^ "]\\n" ^
           (*String.escaped (String_core_run.string_of_core_state st.Driver.core_state)*) "ARENA" ^ "\"]") :: (nodes1 @ nodes2)
        , (string_of_int n ^ " -> " ^ string_of_int (n+1)) ::
          (string_of_int n ^ " -> " ^ string_of_int (n'+1)) :: (edges1 @ edges2) )
  in
  let (_, nodes, edges) = aux 1 t in
  let ret = "digraph G {node[shape=box];" ^ String.concat ";" (nodes @ edges) ^ ";}" in
  Colour.do_colour := saved;
  ret



(*
let json_from_nd_action act =
  let arena_thread0 st =
    match st.Driver.core_state.Core_run.thread_states with
    | [] -> failwith "json_from_nd_action: No thread!"
    | (_, (_, th_st))::_ ->
      String.escaped (String_core.string_of_expr th_st.Core_run.arena)
  in
  let json_new items = "{" ^ String.concat "," items ^ "}" in
  let json_val name value = "\"" ^ name ^ "\":\"" ^ value ^ "\"" in
  let json_obj name value = "\"" ^ name ^ "\":" ^ value in
  let rec aux = function
    | NDactive (_, st) ->
      [ json_val "label" "active";
        json_val "arena" (arena_thread0 st)
      ] |> json_new
    | NDkilled _ ->
      [ json_val "label" "killed";
      ] |> json_new
    | NDnd (debug_str, st, str_acts) ->
      [ json_val "label" "nd";
        json_val "debug" debug_str;
        json_val "arena" (arena_thread0 st);
        json_obj "children" ("[" ^ String.concat "," (List.map (fun (_, a) -> aux a) str_acts) ^ "]")
      ]
      |> json_new
    | NDguard (debug_str, _, act) ->
      [ json_val "label" "guard";
        json_val "debug" debug_str;
        json_obj "child" (aux act)
      ] |> json_new
    | NDbranch (debug_str, st, _, act1, act2) ->
      [ json_val "label" "branch";
        json_val "debug" debug_str;
        json_val "arena" (arena_thread0 st);
        json_obj "child1" (aux act1);
        json_obj "child2" (aux act2)
      ] |> json_new
  in aux act
*)


let create_dot_file act =
  (* TODO: should use the name of the c file here *)
  let oc = open_out "cerb.dot" in
  "dot_from_nd_action act"
  |> Printf.fprintf oc "%s"

let create_json_file act =
  let oc = open_out "cerb.json" in
  "json_from_nd_action act"
  |> Printf.fprintf oc "%s"

exception Backtrack of
  ((string * (bool * Cmm_op.symState * Core.value) * (int * int), Driver.driver_error) nd_status *
     string list *
     Driver.driver_state) list

(* DEBUG *)
let check_counter = ref 0

let check_sat slv es =
(*  prerr_endline (Colour.(ansi_format [Green] (Solver.to_string slv))); *)
  if !Debug_ocaml.debug_level >= 1 then begin
    prerr_string ("CALLING Z3 (" ^ string_of_int !check_counter ^ ") ... ")
  end;
  let ret = Solver.check slv es in
  if !Debug_ocaml.debug_level >= 1 then begin
    prerr_endline "done"
  end;
  check_counter := !check_counter + 1;
  ret



(* val runND: forall 'a 'err 'cs 'st. ndM 'a 'err 'cs 'st -> list (nd_status 'a 'err * 'st) *)
let runND_exhaustive m st0 =
  prerr_endline "HELLO runND_exhaustive";
(*
    let act = m st0 in
    begin
      let oc = open_out "graph.dot" in
      output_string oc (dot_from_nd_action act);
      close_out oc
    end;
*)

  let slvSt = init_solver () in
  (* TODO: yuck, redo it without a reference *)
  let tree_so_far = ref Thole in

  let rec aux acc (ND m_act) st =
    let oc = open_out "graph.dot" in
    output_string oc (dot_from_nd_tree !tree_so_far);
    close_out oc;
    let _ = Unix.system "dot -Tpdf graph.dot > graph.pdf" in
    match m_act st with
      | (NDactive a, st') ->
          tree_so_far := fill_hole_with !tree_so_far (Tactive (a, st'));
          prerr_endline "NDactive";
(*          prerr_endline (Solver.to_string slvSt.slv); *)

(*          Params.update_param_value slvSt.ctx "timeout" ""; *)
          begin match check_sat slvSt.slv [] with
            | Solver.UNKNOWN ->
                prerr_endline "STILL UNKNOWN";
            | Solver.UNSATISFIABLE ->
                prerr_endline "NDactive found to be UNSATISFIABLE";
            | Solver.SATISFIABLE ->
                ()
          end;
(*          (Active (a, Solver.to_string slvSt.slv), st') :: acc *)
          (Active a, Wip.to_strings (), st') :: acc
      
      | (NDkilled r, st') ->
          tree_so_far := fill_hole_with !tree_so_far (Tkilled r);
          prerr_endline "NDkilled BEGIN";
          prerr_endline (Z3.Solver.to_string slvSt.slv);
          prerr_endline "END";
          
          (Killed r, Wip.to_strings (), st') :: acc
      
      | (NDnd (debug_str, str_ms), st') ->
          prerr_endline ("NDnd(" ^ debug_str ^ ")[" ^ string_of_int (List.length str_ms) ^ "]");
          List.fold_left (fun acc (_, m_act) ->
            try
              Wip.push ();
              Solver.push slvSt.slv;
              let ret = aux acc m_act st' in
              ignore (Wip.pop ());
              Solver.pop slvSt.slv 1;
              ret
            with Backtrack new_acc ->
              ignore (Wip.pop ());
              Solver.pop slvSt.slv 1;
              new_acc
          ) acc str_ms
      
      | (NDguard (debug_str, cs, m_act), st') ->
          tree_so_far := fill_hole_with !tree_so_far (Tguard (debug_str, cs, Thole));
          prerr_endline ("NDguard(" ^ debug_str ^ ")");
          add_constraint slvSt debug_str cs;
          begin match check_sat slvSt.slv [] with
            | Solver.UNSATISFIABLE ->
(*
                prerr_endline ("BEGIN SOLVER\n" ^ Solver.to_string slvSt.slv ^ "\nEND");
                prerr_endline ("BEGIN CS\n" ^ String.concat "\n" (Wip.to_strings ()) ^ "\nEND");
*)
                prerr_endline "NDguard BACKTRACKING";
               tree_so_far := fill_hole_with !tree_so_far Tdeadend;
               raise (Backtrack acc)

            | Solver.UNKNOWN ->
                prerr_endline "TIMEOUT in NDguard";
                aux acc m_act st'

            | Solver.SATISFIABLE ->
               aux acc m_act st'
          end
      
      | (NDbranch (debug_str, cs, m_act1, m_act2), st') ->
          tree_so_far := fill_hole_with !tree_so_far (Tbranch (debug_str, cs, Thole, Thole));
          prerr_endline ("NDbranch(" ^ debug_str ^ ")");
          Wip.push ();
          Solver.push slvSt.slv;
          add_constraint slvSt debug_str cs;
          let acc' = begin match check_sat slvSt.slv [] with
            | Solver.UNKNOWN ->
                prerr_endline (Z3.Solver.to_string slvSt.slv);
                failwith ("TIMEOUT in NDbranch 1 (" ^ debug_str ^ ")")

            | Solver.SATISFIABLE (* | Solver.UNKNOWN *) ->
(*               prerr_endline ("SAT ==> " ^ debug_str ^ " :- " ^ String_mem.string_of_iv_memory_constraint cs); *)
               begin try
                 aux acc m_act1 st'
               with
                 | Backtrack new_acc ->
                     new_acc (* acc *)
               end
            | Solver.UNSATISFIABLE ->
                prerr_endline "NDbranch ==> UNSATISFIABLE";
                prerr_endline (Z3.Solver.to_string slvSt.slv);
                prerr_endline "END\n\n";
                acc
          end in
          ignore (Wip.pop ());
          Solver.pop slvSt.slv 1;
          Wip.push ();
          Solver.push slvSt.slv;
          add_constraint slvSt (debug_str ^ " (not)") (MC_not cs);
          let acc'' = begin match check_sat slvSt.slv [] with
            | Solver.UNKNOWN ->
                failwith ("TIMEOUT in NDbranch 2(" ^ debug_str ^ ")")

            | Solver.SATISFIABLE (* | Solver.UNKNOWN *) ->
                begin try
                  aux acc' m_act2 st'
                with
                  | Backtrack new_acc ->
                      new_acc (* acc' *)
                end
            | Solver.UNSATISFIABLE ->
                ignore (Wip.pop ());
                Solver.pop slvSt.slv 1;
               tree_so_far := fill_hole_with !tree_so_far Tdeadend;
                raise (Backtrack acc')
          end in
          ignore (Wip.pop ());
          Solver.pop slvSt.slv 1;
          acc''
  in

  let ret =
    try
(*    let act = m st0 in
    if Global_ocaml.show_action_graph() then (create_dot_file act; create_json_file act);
*)
      aux [] m st0
    with
      | Backtrack acc ->
          acc
  in
  let oc = open_out "graph.dot" in
  output_string oc (dot_from_nd_tree !tree_so_far);
  close_out oc;
  let _ = Unix.system "dot -Tpdf graph.dot > graph.pdf" in
  ret


exception Done of
  (((string * (bool * Cmm_op.symState * Core.value) * (int * int)) * string, Driver.driver_error) nd_status *
     Driver.driver_state)

exception BacktrackRandom of string

let runND_random m st0 =
  let slvSt = init_solver () in
  
  let do_something cs now later =
    Wip.push ();
    Solver.push slvSt.slv;
    add_constraint slvSt "TODO" cs;
    begin match check_sat slvSt.slv [] with
      | Solver.UNKNOWN ->
          failwith "TIMEOUT in NDbranch"
      | Solver.SATISFIABLE ->
          let ret = try
            Some (now ())
          with
          | BacktrackRandom _ ->
              None
          in
          ignore (Wip.pop ());
          Solver.pop slvSt.slv 1;
          begin match ret with
            | Some z ->
                z
            | None ->
                later ()
          end
      | Solver.UNSATISFIABLE ->
          ignore (Wip.pop ());
          Solver.pop slvSt.slv 1;
          later ()
    end in
  
  let rec aux (ND m_act) st =
    match m_act st with
      | (NDactive a, st') ->
          (Active a, Wip.to_strings (), st')
      | (NDkilled (Undef0 _ as reason), st') ->
          (Killed reason, Wip.to_strings (), st')
      | (NDkilled r, st') ->
          raise (BacktrackRandom "NDkilled")
      | (NDnd (debug_str, str_ms), st') ->
          (* TODO: this is not really random (see http://okmij.org/ftp/Haskell/perfect-shuffle.txt) *)
          let suffled_str_ms =
            let with_index = List.map (fun z ->
              (Random.bits (), z)
            ) str_ms in
            List.map snd (List.sort (fun (x, _) (y, _) -> compare x y) with_index) in
          let ret = List.fold_left (fun acc (str, m) ->
            match acc with
              | Some _ ->
                  acc
              | None ->
                  try
                    Wip.push ();
                    Solver.push slvSt.slv;
                    Some (aux m st')
                  with
                    | BacktrackRandom _ -> 
                        ignore (Wip.pop ());
                        Solver.pop slvSt.slv 1;
                        None
          ) None suffled_str_ms in
          begin match ret with
            | Some z ->
                z
            | None ->
                raise (BacktrackRandom "NDnd")
          end
      | (NDguard (debug_str, cs, m_act), st') ->
          add_constraint slvSt debug_str cs;
          begin match check_sat slvSt.slv [] with
            | Solver.UNSATISFIABLE ->
                raise (BacktrackRandom "NDguard")
            | Solver.UNKNOWN ->
                failwith "TIMEOUT in NDguard"
            | Solver.SATISFIABLE ->
                aux m_act st'
          end
      | (NDbranch (debug_str, cs, m_act1, m_act2), st') ->
          let ret = if Random.bool () then
            do_something cs (fun () -> aux m_act1 st')
              (fun () -> do_something (MC_not cs) (fun () -> aux m_act2 st')
                           (fun () -> raise (BacktrackRandom "NDbranch 1")))
          else
            do_something (MC_not cs) (fun () -> aux m_act2 st')
              (fun () -> do_something cs (fun () -> aux m_act1 st')
                  (fun () -> raise (BacktrackRandom ("NDbranch 2 ==> " ^ debug_str)))) in
          ret
  in try
    [aux m st0]
  with
    | BacktrackRandom str ->
        prerr_endline ("runND_random (outer BacktrackRAandom '" ^ str ^ "')");
        []

let rec select options =
     Printf.printf "Choose option between: 1 to %d: " options;
     try
        let p = read_int() in
        if p > 0 && p <= options then p-1
        else (prerr_endline "Wrong option!"; select options)
     with Failure _ -> prerr_endline "Wrong option! Enter a number."; select options

let pp_core_exp e =
  PPrint.ToChannel.pretty 1.0 150 Pervasives.stdout (Pp_core.Basic.pp_expr e)

let print_thread_state tid st =
  prerr_endline "-------";
  (*
  Printf.printf "Thread %s:\n" (string_of_int tid);
  begin match st.Core_run.arena with
    | Core.(Expr (_, Eunseq es)) ->
      prerr_endline "Unsequenced executions. Choose one option to execute first:";
      let i = ref 0 in
      List.map (fun e -> i := !i + 1; Printf.printf "Option %d:\n" !i; pp_core_exp e; prerr_endline "") es |> ignore
    | Core.(Expr(_, End es)) ->
      prerr_endline "Non deterministic executions. Choose one option to execute:";
      let i = ref 0 in
      List.map (fun e -> i := !i + 1; Printf.printf "Option %d:\n" !i; pp_core_exp e; prerr_endline "") es |> ignore
    | Core.(Expr (_, Eaction _)) -> pp_core_exp st.Core_run.arena
    | _ -> failwith "print_thread_state: unexpected Core expression"
  end;
     *)
  prerr_endline "-------"

let print_driver_state st =
  List.map (fun(tid, (_, th_st)) -> print_thread_state tid th_st) (st.Driver.core_state.Core_run.thread_states)
  |> ignore; flush stdout

let runND_interactive (ND m) st0 =
  failwith "runND_interactive"
(*
  let slvSt = init_solver () in
  let rec run_action = function
      | NDactive (a, st') ->
        Params.update_param_value slvSt.ctx "timeout" "";
        begin match check_sat slvSt.slv [] with
          | Solver.UNKNOWN ->
              prerr_endline "STILL UNKNOWN";
          | _ ->
              ()
        end;
        Active a, Wip.to_strings (), st'

      | NDkilled r ->
        Killed r, Wip.to_strings (), st0

      | NDnd (debug_str, st, acts) ->
        let rec choose xs =
          let rec rm_by_index acc xs i =
            match xs with
            | x::xs ->
              if i = 0 then acc @ xs
              else rm_by_index (acc@[x]) xs (i-1)
            | _ -> failwith "runND_interactive: wrong index"
          in
          match List.length xs with
          | 0 -> failwith "runND_interactive: no action"
          | 1 -> run_action (snd (List.hd xs))
          | size ->
            print_driver_state st;
            let n = select size in
            try run_action (snd (List.nth xs n))
            with Backtrack _ ->
              prerr_endline "Failed execution. Selecting alternative option.";
              choose (rm_by_index [] xs n)
        in choose acts

      | NDguard (debug_str, cs, act) ->
        prerr_endline ("Adding constraint: " ^ String_mem.string_of_iv_memory_constraint cs);
        add_constraint slvSt cs;
        begin match check_sat slvSt.slv [] with
          | Solver.UNSATISFIABLE ->
            prerr_endline "WARN: Unsatisfiable execution. Backtracking...";
            raise (Backtrack [])
          | _ ->
             run_action act
        end

      | NDbranch (debug_str, st, cs, act1, act2) ->
        Printf.printf "Branching options: %s\n" debug_str;
        print_driver_state st;
        let first = (select 2 = 0) in
        let (sel, sel_cs, alt, alt_cs) =
          if first then (act1, cs, act2, MC_not cs)
          else (act2, MC_not cs, act1, cs)
        in
        let exec_alt () =
            Solver.pop slvSt.slv 1;
            Solver.push slvSt.slv;
            prerr_endline ("Adding constraint: " ^ String_mem.string_of_iv_memory_constraint alt_cs);
            add_constraint slvSt alt_cs;
            begin match check_sat slvSt.slv [] with
              | Solver.SATISFIABLE | Solver.UNKNOWN ->
                run_action alt
              | Solver.UNSATISFIABLE ->
                failwith "runND_inderactive: no satisiable execution"
            end
        in
        Solver.push slvSt.slv;
        prerr_endline ("Adding constraint: " ^ String_mem.string_of_iv_memory_constraint sel_cs);
        add_constraint slvSt sel_cs;
        begin match check_sat slvSt.slv [] with
          | Solver.SATISFIABLE | Solver.UNKNOWN ->
            begin
              try run_action sel
              with Backtrack _ ->
                prerr_endline "Backtrack(NDbranch)";
                exec_alt ()
            end
          | Solver.UNSATISFIABLE ->
            prerr_endline "WARN: Unsatisfiable execution. Executing alternative option.";
            exec_alt ()
        end

  in [run_action (m st0)]
*)

let runND m st0 =
  flush stdout;
  Global_ocaml.(match current_execution_mode () with
    | Some Random ->
        runND_random m st0
    | Some Exhaustive ->
        runND_exhaustive m st0
    | Some Interactive ->
        runND_interactive m st0
    | None ->
        failwith "Smt.runND, no execution mode"
  )
