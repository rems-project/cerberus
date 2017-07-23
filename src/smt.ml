open Defacto_memory_types2
open Mem_common

open State

module Sym = Symbol

open Z3



(* wip *)
module Wip = struct
  let submitted : ((Mem.mem_iv_constraint list) list) ref =
    ref []
  
  let to_strings () =
    let css = List.flatten !submitted in
    List.mapi (fun i cs ->
      "[" ^ (string_of_int i) ^ "] " ^ String_mem.string_of_iv_memory_constraint cs
    ) (List.rev css (*TODO: why? *))
  
  let push () =
    submitted := [] :: !submitted
  
  let pop () =
    match !submitted with
      | [] ->
          failwith "Wip.pop, empty"
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
  let ctx = mk_context [("timeout", "100")(*TODO*)] in
  
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
          [0(*TODO: no idea with I'm doing*)] ] in
  
  let ctypeSort =
    (* TODO: Function, Struct, Union, Builtin *)
    Datatype.mk_sort_s ctx "Ctype"
      [ mk_ctor "void_ty"
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
        failwith "Smt.integerBaseType_to_expr, Int_leastN_t"
    | Int_fastN_t _ ->
        failwith "Smt.integerBaseType_to_expr, Int_fastN_t"
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
        failwith ("Smt.integerType_to_expr, IBuiltin " ^ str)
    | Enum _ ->
        failwith "Smt.integerType_to_expr, Enum"
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
        failwith "Smt.basicType_to_expr, Floating"
  )

let rec ctype_to_expr slvSt ty =
  let fdecls = Datatype.get_constructors slvSt.ctypeSort in
  Core_ctype.(
    match ty with
      | Void0 ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 0) []
      | Basic0 bty ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 1) [basicType_to_expr slvSt bty]
      | Array0 (_, _, None) ->
          failwith "Smt.ctype_to_expr, Array None"
      | Array0 (_, elem_ty, Some n) ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 2)
            [ctype_to_expr slvSt elem_ty; Arithmetic.Integer.mk_numeral_i slvSt.ctx (Nat_big_num.to_int n)]
      | Pointer0 (_, ref_ty) ->
        Expr.mk_app slvSt.ctx (List.nth fdecls 3)
            [ctype_to_expr slvSt ref_ty]
      | _ ->
          print_endline "TODO: Smt.ctype_to_expr";
          Expr.mk_const_s slvSt.ctx "void_ty" slvSt.ctypeSort
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
              failwith "IntRem_t"
          | IntRem_f ->
              Arithmetic.Integer.mk_mod slvSt.ctx 
          | IntExp ->
              Arithmetic.mk_power slvSt.ctx  in
        mk_op iop (aux ival_1) (aux ival_2)
    | IVop _ ->
        failwith "Smt.integer_value_base_to_expr: IVop, arity error"
    | IVmin ity ->
        Expr.mk_app slvSt.ctx slvSt.ivminDecl [integerType_to_expr slvSt ity]
    | IVmax ity ->
        Expr.mk_app slvSt.ctx slvSt.ivmaxDecl [integerType_to_expr slvSt ity]
    | IVsizeof (Core_ctype.Array0 (_, _, None)) ->
        failwith "Smt, sizeof array None"
    | IVsizeof (Core_ctype.Array0 (_, elem_ty, Some n)) ->
        Arithmetic.mk_mul slvSt.ctx
          [ Arithmetic.Integer.mk_numeral_s slvSt.ctx (Nat_big_num.to_string n)
          ; Expr.mk_app slvSt.ctx slvSt.ivsizeofDecl [ctype_to_expr slvSt elem_ty] ]
    | IVsizeof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivsizeofDecl [ctype_to_expr slvSt ty]
    | IValignof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivalignofDecl [ctype_to_expr slvSt ty]
  | IVoffsetof (tag_sym, memb_ident) ->
      failwith "IVoffsetof"
  | IVptrdiff (ptrval_1, ptrval_2) ->
      failwith "IVptrdiff"
  | IVbyteof (ival_, mval) ->
      failwith "IVbyteof"
  | IVcomposite ival_s ->
      failwith "IVcomposite"
  | IVbitwise (ity, bwop) ->
      failwith "IVbitwise"
  
  in aux ival_



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

let add_constraint slvSt cs =
  match mem_constraint_to_expr slvSt cs with
    | Some e ->
          Wip.add [cs];
        Solver.add slvSt.slv [e]
    | None ->
        ()




open Nondeterminism2

let rec string_of_nd_action = function
  | NDactive ((_, (_, _, pe), (_, _)), _) ->
      "NDactive(" ^ String_core.string_of_pexpr pe ^ ")"
  | NDkilled _ ->
      "NDkilled"
  | NDnd (debug_str, acts) ->
      "NDnd(" ^ debug_str ^ ", " ^
      String.concat ", " (List.map string_of_nd_action acts) ^
      ")"
  | NDguard (debug_str, cs, act) ->
      "NDguard(" ^ debug_str ^ ", " ^
      String_mem.string_of_iv_memory_constraint cs ^
      ", " ^
      string_of_nd_action act ^
      ")"
  | NDbranch (debug_str, cs, act1, act2) ->
      "NDbranch(" ^ debug_str ^ ", " ^
        String_mem.string_of_iv_memory_constraint cs ^
        ", " ^ 
        string_of_nd_action act1 ^
        ", " ^ 
        string_of_nd_action act2 ^
      ")"

exception Backtrack of
  ((string * (bool * Cmm_op.symState * (unit, Sym.sym) Core.generic_pexpr) * (int * int), Driver.driver_error) nd_status *
     string list *
     Driver.driver_state) list


let check_sat slv es =
(*  print_string "CALLING Z3 ... ";
  flush stdout; *)
  let ret = Solver.check slv es in
(*  print_endline "done"; *)
  ret



(* val runND: forall 'a 'err 'cs 'st. ndM 'a 'err 'cs 'st -> list (nd_status 'a 'err * 'st) *)
let runND_exhaustive (ND m) st0 =
  let slvSt = init_solver () in
  let rec aux acc = function
      | NDactive (a, st') ->
(*          print_endline "NDactive"; *)
(*          print_endline (Solver.to_string slvSt.slv); *)
          Params.update_param_value slvSt.ctx "timeout" "";
          begin match check_sat slvSt.slv [] with
            | Solver.UNKNOWN ->
                print_endline "STILL UNKNOWN";
            | _ ->
                ()
          end;
(*          (Active (a, Solver.to_string slvSt.slv), st') :: acc *)
          (Active a, Wip.to_strings (), st') :: acc
      
      | NDkilled r ->
(*          print_endline "NDkilled"; *)
          (Killed r, Wip.to_strings (), st0) :: acc
      
      | NDnd (debug_str, acts) ->
(*          print_endline ("NDnd(" ^ debug_str ^ ")"); *)
          List.fold_left aux acc acts
      
      | NDguard (debug_str, cs, act) ->
(*          print_endline ("NDguard(" ^ debug_str ^ ")"); *)
          add_constraint slvSt cs;
          begin match check_sat slvSt.slv [] with
            | Solver.UNSATISFIABLE ->
(*
                print_endline (Solver.to_string slvSt.slv);
                print_endline "NDguard BACKTRACKING";
*)
               raise (Backtrack acc)
            | _ ->
               aux acc act
          end
      
      | NDbranch (debug_str, cs, act1, act2) ->
(*          print_endline ("NDbranch(" ^ debug_str ^ ")"); *)
          Solver.push slvSt.slv;
          add_constraint slvSt cs;
          let acc' = begin match check_sat slvSt.slv [] with
            | Solver.SATISFIABLE | Solver.UNKNOWN ->
(*               print_endline ("SAT ==> " ^ debug_str ^ " :- " ^ String_mem.string_of_iv_memory_constraint cs); *)
               begin try
                 aux acc act1
               with
                 | Backtrack new_acc ->
                     new_acc (* acc *)
               end
            | Solver.UNSATISFIABLE ->
                acc
          end in
          Solver.pop slvSt.slv 1;
          Solver.push slvSt.slv;
          add_constraint slvSt (MC_not cs);
          let acc'' = begin match check_sat slvSt.slv [] with
            | Solver.SATISFIABLE | Solver.UNKNOWN ->
                begin try
                  aux acc' act2
                with
                  | Backtrack new_acc ->
                      new_acc (* acc' *)
                end
            | Solver.UNSATISFIABLE ->
                Solver.pop slvSt.slv 1;
                raise (Backtrack acc')
          end in
          Solver.pop slvSt.slv 1;
          acc''
  in
  try
    aux [] (m st0)
  with
    | Backtrack acc ->
        acc


exception Done of
  (((string * (bool * Cmm_op.symState * (unit, Sym.sym) Core.generic_pexpr) * (int * int)) * string, Driver.driver_error) nd_status *
     Driver.driver_state)

let runND_random (ND m) st0 =
  failwith "runND_random"
(*
  let slvSt = init_solver () in
  let rec aux acc = function
      | NDactive (a, st') ->
          Params.update_param_value slvSt.ctx "timeout" "";
          begin match Solver.check slvSt.slv [] with
            | Solver.UNKNOWN ->
                print_endline "STILL UNKNOWN";
            | _ ->
                ()
          end;
          raise (Done (Active (a, Solver.to_string slvSt.slv), st'))
      
      | NDkilled r ->
          (Killed r, st0) :: acc
      
      | NDnd (_, acts) ->
          failwith "List.fold_left aux acc acts"
      
      | NDguard (cs, act) ->
          add_constraint slvSt cs;
          begin match Solver.check slvSt.slv [] with
            | Solver.UNSATISFIABLE ->
               raise (Backtrack acc)
            | _ ->
               aux acc act
          end
      
      | NDbranch (cs, act1, act2) ->
          let acc' = begin match Solver.check slvSt.slv [] with
            | Solver.SATISFIABLE | Solver.UNKNOWN ->
               begin try
                 aux acc act1
               with
                 | Backtrack new_acc ->
                     new_acc (* acc *)
               end
            | Solver.UNSATISFIABLE ->
                acc
          end in
          Solver.pop slvSt.slv 1;
          Solver.push slvSt.slv;
          add_constraint slvSt (MC_not cs);
          let acc'' = begin match Solver.check slvSt.slv [] with
            | Solver.SATISFIABLE | Solver.UNKNOWN ->
                begin try
                  aux acc' act2
                with
                  | Backtrack new_acc ->
                      new_acc (* acc' *)
                end
            | Solver.UNSATISFIABLE ->
                Solver.pop slvSt.slv 1;
                raise (Backtrack acc')
          end in
          Solver.pop slvSt.slv 1;
          acc''
  in
  try
    aux [] (m st0)
  with
    | Done z ->
        [z]
    | Backtrack acc ->
        acc
*)


let runND m st0 =
(*  print_endline "STARTING Smt.runND"; *)
  flush stdout;
  Global_ocaml.(match current_execution_mode () with
    | Some Random (* ->
        runND_random m st0 *)
    | Some Exhaustive ->
        runND_exhaustive m st0
    | Some Interactive ->
        failwith "TODO: Smt.runND Interactive"
    | None ->
        failwith "Smt.runND, no execution mode"
  )
