open Memory_model
(* we need to do this because of Lem's renaming not understanding modules... *)

let name = "I am the defacto memory model" (* TODO: debug *)
type pointer_value = Defacto_memory_types.impl_pointer_value
type integer_value = Defacto_memory_types.impl_integer_value
type floating_value = Defacto_memory_types.impl_floating_value
type mem_value = Defacto_memory_types.impl_mem_value
type mem_iv_constraint = integer_value Mem_common.mem_constraint



module Constraints = struct
  type t = mem_iv_constraint
  let negate x = Mem_common.MC_not x
  
  module Sym = Symbol
  open Z3
  
  let mk_forall ctx syms sorts expr =
    Quantifier.mk_forall ctx sorts syms expr None [] [] None None
  
  type solver_state = {
      submitted: (string * t) list;
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
      
      in_device_memDecl: FuncDecl.func_decl;
    }
  
  let init_solver () : solver_state =
    let ctx = mk_context [(*("timeout", "")*)] in
    
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
    let boolSort = Boolean.mk_sort ctx in
    let slvSt = {
  (*   allocations= []; *)
     submitted= [];
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
     in_device_memDecl= FuncDecl.mk_func_decl_s ctx "in_device_mem" [intSort] boolSort;
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
    
    (* axiom3 ==> forall ity: Ctype, ivmin(ity) <= fromptr(_, ity, _) <= ivmax(ity) *)
    let axiom3 =
      let ty_sym = Symbol.mk_string ctx "ty" in
      let ity_sym = Symbol.mk_string ctx "ity" in
      let ptr_i_sym = Symbol.mk_string ctx "ptr_i" in
      let ty_e = Quantifier.mk_bound ctx 2 ctypeSort in
      let ity_e = Quantifier.mk_bound ctx 1 integerTypeSort in
      let ptr_i_e = Quantifier.mk_bound ctx 0 intSort in
      Quantifier.expr_of_quantifier (
        mk_forall ctx [ty_sym; ity_sym; ptr_i_sym] [ctypeSort; integerTypeSort; intSort]
          (Boolean.mk_and ctx 
            [ Arithmetic.mk_le ctx (Expr.mk_app ctx slvSt.ivminDecl [ity_e])
                                   (Expr.mk_app slvSt.ctx slvSt.fromptrDecl [ty_e; ity_e; ptr_i_e])
            ; Arithmetic.mk_le ctx (Expr.mk_app slvSt.ctx slvSt.fromptrDecl [ty_e; ity_e; ptr_i_e])
                                   (Expr.mk_app ctx slvSt.ivmaxDecl [ity_e]) ])
       ) in
    
    Solver.add slvSt.slv [axiom1; axiom2; axiom3];
  
    (* If the size of pointer is given specified, we can assert fromptr()
       say within this size *)
    (* NOTE: we assume 2's complement encoding with no padding bits *)
  (*
    begin match Ocaml_implementation.Impl.sizeof_pointer with
      | None ->
          ()
      | Some ptr_size ->
          let ptr_min
  
  
          let axiom3 =
            let ival_sym = Symbol.mk_string ctx "ival" in
            Quantifier.expr_of_quantifier (
              mk_forall ctx [ival_sym] [intSort]
              (Arithmetic.mk_lt ctx
              ) in
    end;
  *)
    
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
  
  type 'a eff =
    | Eff of (solver_state -> 'a)
  
  let return a =
    Eff (fun _ -> a)
  
  let bind (Eff ma) f =
    Eff (fun st ->
      let a = ma st in
      let Eff mb = f a in
      mb st
    )
  
  let rec foldlM f a = function
    | [] -> return a
    | b::bs -> bind (f a b) (fun a' -> foldlM f a' bs)
  
  let runEff (Eff mk) =
    mk (init_solver ())


  let string_of_solver =
    Eff (fun st ->
      List.mapi (fun i (str, cs) ->
        "\n[" ^ (string_of_int i) ^ "] -- '" ^ str ^ "'\n" ^ String_defacto_memory.string_of_iv_memory_constraint cs
      ) (List.rev st.submitted)

(*
      [Solver.to_string st.slv]
*)
    )

  let check_sat =
    Eff (fun st ->
      match Solver.check st.slv [] with
        | UNSATISFIABLE -> `UNSAT
        | _ -> `SAT
    )

  
(*
  val with_constraints: string -> t -> 'a eff -> 'a eff
*)
open Mem_common





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
      | Void0 ->
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
      | Function0 _ ->
          failwith "TODO: Smt.ctype_to_expr, Function"
      | Atomic0 _ ->
          failwith "TODO: Smt.ctype_to_expr, Atomic"
      | Struct0 tag_sym ->
          failwith "TODO: Smt.ctype_to_expr, Struct"
      | Union0 _ ->
          failwith "TODO: Smt.ctype_to_expr, Union"
      | Builtin0 _ ->
          failwith "TODO: Smt.ctype_to_expr, Builtin"
      
(*
      | _ ->
          failwith "TODO: Smt.ctype_to_expr"
          (* Expr.mk_const_s slvSt.ctx "void_ty" slvSt.ctypeSort *)
*)
  )

let address_expression_of_pointer_base = function
  | Defacto_memory_types.PVunspecified ty ->
      failwith "PVunspecified"
  | Defacto_memory_types.PVnull ty ->
      failwith "PVnull"
  | Defacto_memory_types.PVfunction sym ->
      failwith  "PVfunction"
  | Defacto_memory_types.PVbase (alloc_id, pref) ->
      Defacto_memory_types.IVaddress (alloc_id, pref)
  | Defacto_memory_types.PVfromint ival_ ->
      ival_

let integer_value_base_to_expr slvSt ival_ =
  let rec aux = function
    | Defacto_memory_types.IVunspecified ->
        failwith "IVunspecified"
    | Defacto_memory_types.IVconcurRead _ ->
        failwith "Smt.integer_value_base_to_expr: IVconcurRead"
    | Defacto_memory_types.IVconcrete n ->
        Arithmetic.Integer.mk_numeral_s slvSt.ctx (Nat_big_num.to_string n)
    | Defacto_memory_types.IVaddress (alloc_id, _) ->
        Expr.mk_const_s slvSt.ctx ("addr_" ^ string_of_int alloc_id) slvSt.addrSort
    | Defacto_memory_types.IVfromptr (ty, ity, ptrval_, sh) ->
        (* the result of a cast from pointer to integer. The first
           parameter is the referenced type of the pointer value, the
           second is the integer type *)
        let ty_e = ctype_to_expr slvSt ty in
        let ity_e = integerType_to_expr slvSt ity in
        let ptrval_e = (* WIP *) aux (Mem_simplify.lifted_simplify_integer_value_base (address_expression_of_pointer_base ptrval_)) in
        let sh_ival_e = (* WIP *) aux (Mem_simplify.lifted_simplify_integer_value_base (Defacto_memory.integer_value_baseFromShift_path sh)) in
        if Mem_simplify.simple_fromptr then begin
          Arithmetic.mk_add slvSt.ctx [ptrval_e; sh_ival_e]
        end else begin
          Expr.mk_app slvSt.ctx slvSt.fromptrDecl [ty_e; ity_e; Arithmetic.mk_add slvSt.ctx [ptrval_e; sh_ival_e]]
        end
    | Defacto_memory_types.IVop (iop, [ival_1; ival_2]) ->
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
    | Defacto_memory_types.IVop _ ->
        (* Core type error *)
        assert false
    | Defacto_memory_types.IVmin ity ->
        Expr.mk_app slvSt.ctx slvSt.ivminDecl [integerType_to_expr slvSt ity]
    | Defacto_memory_types.IVmax ity ->
        Expr.mk_app slvSt.ctx slvSt.ivmaxDecl [integerType_to_expr slvSt ity]
    | Defacto_memory_types.IVsizeof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivsizeofDecl [ctype_to_expr slvSt ty]
    | Defacto_memory_types.IValignof (Core_ctype.Struct0 tag_sym) ->
        prerr_endline "BOGUS!!!!";
        Arithmetic.Integer.mk_numeral_s slvSt.ctx "8"
    | Defacto_memory_types.IValignof ty ->
        Expr.mk_app slvSt.ctx slvSt.ivalignofDecl [ctype_to_expr slvSt ty]
    | Defacto_memory_types.IVoffsetof (tag_sym, memb_ident) ->
      failwith "TODO Smt: IVoffsetof"
    | Defacto_memory_types.IVpadding (Sym.Symbol (tag_sym_n, _), Cabs.CabsIdentifier (_, membr_str)) ->
        Expr.mk_const_s slvSt.ctx ("padding__tag_" ^ string_of_int tag_sym_n ^ "__" ^ membr_str) slvSt.addrSort
    | Defacto_memory_types.IVptrdiff (diff_ty, (ptrval_1, sh1), (ptrval_2, sh2)) ->
        let ptrval_e1 = (* WIP *) aux (Defacto_memory_types.IVop (IntAdd, [ address_expression_of_pointer_base ptrval_1
                                                                          ; Defacto_memory.integer_value_baseFromShift_path sh1 ])) in
        let ptrval_e2 = (* WIP *) aux (Defacto_memory_types.IVop (IntAdd, [ address_expression_of_pointer_base ptrval_2
                                                                          ; Defacto_memory.integer_value_baseFromShift_path sh2 ])) in
        (* TODO: maybe have that conversion be done when the IVptrdiff is created? *)
        (* TODO: check that this is correct for arrays of arrays ... *)
        let diff_ty' = begin match diff_ty with
          | Core_ctype.Array0 (elem_ty, _) ->
              elem_ty
          | _ ->
              diff_ty
        end in
        Arithmetic.mk_div slvSt.ctx
          (Arithmetic.mk_sub slvSt.ctx [ptrval_e1; ptrval_e2])
          (aux (Mem_simplify.lifted_simplify_integer_value_base (Defacto_memory_types.IVsizeof diff_ty')))
    | Defacto_memory_types.IVbyteof (ival_, mval) ->
        failwith "TODO Smt: IVbyteof"
    | Defacto_memory_types.IVcomposite ival_s ->
        failwith "TODO Smt: IVcomposite"
    | Defacto_memory_types.IVbitwise (ity, bwop) ->
        let is_signed = AilTypesAux.is_signed_ity ity in
        let size_ity = 8 (* TODO: should be 64 *) in
        BitVector.mk_bv2int slvSt.ctx begin match bwop with
          | Defacto_memory_types.BW_complement ival_ ->
              BitVector.mk_not slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_))
          | Defacto_memory_types.BW_AND (ival_1, ival_2) ->
              BitVector.mk_and slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
          | Defacto_memory_types.BW_OR (ival_1, ival_2) ->
              BitVector.mk_or slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
          | Defacto_memory_types.BW_XOR (ival_1, ival_2) ->
              BitVector.mk_xor slvSt.ctx
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_1))
                (Arithmetic.Integer.mk_int2bv slvSt.ctx size_ity (aux ival_2))
        end is_signed
  in
  aux (Either.either_case
    (fun n -> Defacto_memory_types.IVconcrete n)
    (fun z -> z)
    (Mem_simplify.simplify_integer_value_base ival_)
  )


let mem_constraint_to_expr st (constr: mem_iv_constraint) =
  let rec aux = function
    | MC_empty ->
        None
    | MC_eq (Defacto_memory_types.IV (_, ival_1), Defacto_memory_types.IV (_, ival_2)) ->
        Some (Boolean.mk_eq st.ctx (integer_value_base_to_expr st ival_1) (integer_value_base_to_expr st ival_2))
    | MC_lt (Defacto_memory_types.IV (_, ival_1), Defacto_memory_types.IV (_, ival_2)) ->
        Some (Arithmetic.mk_lt st.ctx (integer_value_base_to_expr st ival_1) (integer_value_base_to_expr st ival_2))
    | MC_le (Defacto_memory_types.IV (_, ival_1), Defacto_memory_types.IV (_, ival_2)) ->
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
    | MC_in_device (Defacto_memory_types.IV (_, ival_)) ->
        Some (Expr.mk_app st.ctx st.in_device_memDecl [integer_value_base_to_expr st ival_])
  in aux constr


  let with_constraints debug_str cs (Eff m) =
    Eff (fun st ->
      Solver.push st.slv;
(*
      if !Debug_ocaml.debug_level >= 1 then begin
        prerr_endline ("ADDING CONSTRAINT [" ^ debug_str ^ "] ==> " ^ String_mem.string_of_iv_memory_constraint cs)
      end;
*)
      begin match mem_constraint_to_expr st cs with
        | Some e ->
(*            Wip.add [(debug_str, cs)]; *)
            Solver.add st.slv [e]
        | None ->
            ()
      end;
      let st' = { st with submitted= (debug_str, cs) :: st.submitted } in
      let ret = m st' in
      Solver.pop st.slv 1;
      ret
    )

end

















(*
let cs_module = (module struct
  type t = mem_iv_constraint
  let negate x = Mem_common.MC_not x
  
  type 'a eff = 'a
  let return a = a
  let bind ma f = f ma
  let foldlM f a bs = List.fold_left f a bs
  
  let runEff a = a
  
(*    let init_solver = return () *)
  let string_of_solver = return []
  let check_sat = return `SAT
  
  let with_constraints _ _ a = a
end : Constraints with type t = mem_iv_constraint)
*)
let cs_module = (module Constraints : Constraints with type t = mem_iv_constraint)

type footprint = Defacto_memory_types.impl_footprint
let do_overlap _ _ = false (* TODO *)
type mem_state = Defacto_memory.impl_mem_state
let initial_mem_state = Defacto_memory.impl_initial_mem_state
type 'a memM =
  ('a, Mem_common.mem_error, integer_value Mem_common.mem_constraint, mem_state) Nondeterminism.ndM
let return = Defacto_memory.impl_return
let bind = Nondeterminism.nd_bind
let allocate_static = Defacto_memory.impl_allocate_static

let allocate_dynamic = Defacto_memory.impl_allocate_dynamic
let kill = Defacto_memory.impl_kill
let load = Defacto_memory.impl_load
let store = Defacto_memory.impl_store
let null_ptrval = Defacto_memory.impl_null_ptrval
let fun_ptrval = Defacto_memory.impl_fun_ptrval
let eq_ptrval = Defacto_memory.impl_eq_ptrval
let ne_ptrval = Defacto_memory.impl_ne_ptrval
let lt_ptrval = Defacto_memory.impl_lt_ptrval
let gt_ptrval = Defacto_memory.impl_gt_ptrval
let le_ptrval = Defacto_memory.impl_le_ptrval
let ge_ptrval = Defacto_memory.impl_ge_ptrval
let diff_ptrval = Defacto_memory.impl_diff_ptrval
let validForDeref_ptrval = Defacto_memory.impl_validForDeref_ptrval
let isWellAligned_ptrval = Defacto_memory.impl_isWellAligned_ptrval
let ptrcast_ival = Defacto_memory.impl_ptrcast_ival
let intcast_ptrval = Defacto_memory.impl_intcast_ptrval
let array_shift_ptrval = Defacto_memory.impl_array_shift_ptrval
let member_shift_ptrval = Defacto_memory.impl_member_shift_ptrval
let memcmp = Defacto_memory.impl_memcmp
let concurRead_ival = Defacto_memory.impl_concurRead_ival
let integer_ival = Defacto_memory.impl_integer_ival
let max_ival = Defacto_memory.impl_max_ival
let min_ival = Defacto_memory.impl_min_ival
let op_ival = Defacto_memory.impl_op_ival
let offsetof_ival = Defacto_memory.impl_offsetof_ival
let sizeof_ival = Defacto_memory.impl_sizeof_ival
let alignof_ival = Defacto_memory.impl_alignof_ival
let bitwise_complement_ival = Defacto_memory.impl_bitwise_complement_ival
let bitwise_and_ival = Defacto_memory.impl_bitwise_and_ival
let bitwise_or_ival = Defacto_memory.impl_bitwise_or_ival
let bitwise_xor_ival = Defacto_memory.impl_bitwise_xor_ival
let case_integer_value = Defacto_memory.impl_case_integer_value
let is_specified_ival = Defacto_memory.impl_is_specified_ival
let eq_ival = Defacto_memory.impl_eq_ival
let lt_ival = Defacto_memory.impl_lt_ival
let le_ival = Defacto_memory.impl_le_ival
let eval_integer_value = Defacto_memory.impl_eval_integer_value
let zero_fval = Defacto_memory.impl_zero_fval
let str_fval = Defacto_memory.impl_str_fval
let case_fval = Defacto_memory.impl_case_fval
let op_fval = Defacto_memory.impl_op_fval
let eq_fval = Defacto_memory.impl_eq_fval
let lt_fval = Defacto_memory.impl_lt_fval
let le_fval = Defacto_memory.impl_le_fval
let fvfromint = Defacto_memory.impl_fvfromint
let ivfromfloat = Defacto_memory.impl_ivfromfloat
let unspecified_mval = Defacto_memory.impl_unspecified_mval
let integer_value_mval = Defacto_memory.impl_integer_value_mval
let floating_value_mval = Defacto_memory.impl_floating_value_mval
let pointer_mval = Defacto_memory.impl_pointer_mval
let array_mval = Defacto_memory.impl_array_mval
let struct_mval = Defacto_memory.impl_struct_mval
let union_mval = Defacto_memory.impl_union_mval
let case_mem_value = Defacto_memory.impl_case_mem_value
let sequencePoint = Defacto_memory.impl_sequencePoint

include Pp_defacto_memory

(* JSON serialisation *)
let serialise_pointer_value _ = failwith "serialise pointer_value"
let parse_pointer_value _ = failwith "parse pointer_value"
let serialise_integer_value _ = failwith "serialise integer_value"
let parse_integer_value _ = failwith "parse integer_value"
let serialise_floating_value _ = failwith "serialise floating_value"
let parse_floating_value _ = failwith "parse floating_value"
let serialise_mem_value _ = failwith "serialise mem_value"
let parse_mem_value _ = failwith "parse mem_value"
let serialise_mem_state _ = failwith "serialise mem_state"
