open Bmc_conc
open Bmc_globals
open Bmc_sorts
open Bmc_substitute
open Bmc_types
open Bmc_utils
open Z3
open Z3.Arithmetic

open AilTypes
open Core
open Core_aux
open Ocaml_mem
open Printf
open Util

(* TODO:
 *  - Maintain memory table properly
 *      - Also creates within branches not preserved.
 *  - Kill ignored; Ebound ignored
 *  - More complex create types
 *  - Alias analysis
 *  - Alignment
 *  - PtrValidForDeref
 *  - See if guarding assumptions will reduce solver time
 *  - Try replacing let_bindings with actual expression
 *  - Atomic and pointer ctype not translated properly in Z3
 *  - C functions are currently just identifiers.
 *  - Structs; Core Arrays (brace initialized arrays)
 *  - int x[2][2]; x[0][3] not detected as undefined
 *  - Check arbitrary functions with arguments
 *
 *  - Concurrency
 *     - Convert lists -> sets/hashtables where appropriate
 *     - Should asw be included in po?
 *)

(* =========== TYPES =========== *)
type ctype = Core_ctype.ctype0

(* TODO: use Set.Make *)
module AddrSet = struct
    type t = addr_ty Pset.set

    let cmp = Pervasives.compare
    let empty = Pset.empty cmp
    let of_list = Pset.from_list cmp
    let union s1 s2 = Pset.union s1 s2
    let fold = Pset.fold

    let pp s = Pset.fold (fun (x,y) acc ->
      sprintf "(%d,%d) %s" x y acc) s ""
end

type bmc_ret = {
  expr      : Expr.expr;
  assume    : Expr.expr list;
  vcs       : Expr.expr list;
  drop_cont : Expr.expr; (* drop continuation; e.g. after Erun *)
  mod_addr  : AddrSet.t; (* addresses modified in memory; sequential mode *)
  ret_cond  : Expr.expr; (* constraints on the returned value *)
  preexec   : preexec;   (* concurrent mode *)
}

type bmc_pret = {
  expr      : Expr.expr;
  assume    : Expr.expr list;
  vcs       : Expr.expr list;
}

type bmc_gret = {
  assume    : Expr.expr list;
  vcs       : Expr.expr list;
  preexec   : preexec;
}

let pget_expr   (pret: bmc_pret) = pret.expr
let pget_assume (pret: bmc_pret) = pret.assume
let pget_vcs    (pret: bmc_pret) = pret.vcs

let eget_expr    (eret: bmc_ret) = eret.expr
let eget_assume  (eret: bmc_ret) = eret.assume
let eget_vcs     (eret: bmc_ret) = eret.vcs
let eget_cont    (eret: bmc_ret) = eret.drop_cont
let eget_ret     (eret: bmc_ret) = eret.ret_cond
let eget_preexec (eret: bmc_ret) = eret.preexec

let bmc_pret_to_ret (pret: bmc_pret) : bmc_ret =
  { expr      = pret.expr
  ; assume    = pret.assume
  ; vcs       = pret.vcs
  ; drop_cont = mk_false
  ; mod_addr  = AddrSet.empty
  ; ret_cond  = mk_true
  ; preexec   = mk_initial_preexec
  }

let initial_gret = {assume = []; vcs = []; preexec = mk_initial_preexec}
let merge_grets grets = List.fold_left (
    fun acc gret ->
      { assume  = gret.assume @ acc.assume
      ; vcs     = gret.vcs    @ acc.vcs
      ; preexec = combine_preexecs [gret.preexec; acc.preexec]
      }) initial_gret grets

(* =========== BmcZ3Sort: Z3 representation of Ctypes =========== *)
type bmcz3sort =
  | CaseSortBase of ctype * Sort.sort
  | CaseSortList of bmcz3sort list

let rec bmcz3sort_size (sort: bmcz3sort) =
  match sort with
  | CaseSortBase _        -> 1
  | CaseSortList sortlist ->
      List.fold_left (fun x y -> x + (bmcz3sort_size y)) 0 sortlist

let rec flatten_bmcz3sort (l: bmcz3sort): (ctype * Sort.sort) list =
  match l with
  | CaseSortBase (expr, sort) -> [(expr, sort)]
  | CaseSortList ss -> List.concat (List.map flatten_bmcz3sort ss)


(* =========== CUSTOM Z3 FUNCTIONS =========== *)
(* Used for declaring Ivmin/Ivmax/is_unsigned/sizeof/etc *)
module ImplFunctions = struct
  open Z3.FuncDecl
  (* ---- Implementation ---- *)
  let sizeof_ity = Ocaml_implementation.Impl.sizeof_ity

  (* TODO: precision of Bool is currently 8... *)
  let impl : Implementation.implementation = {
    binary_mode = Two'sComplement;
    signed      = (function
                   | Char       -> Ocaml_implementation.Impl.char_is_signed
                   | Bool       -> false
                   | Signed _   -> true
                   | Unsigned _ -> false
                   | _          -> assert false);
    precision   = (fun i -> match sizeof_ity i with
                   | Some x -> x * 8
                   | None   -> assert false );
    size_t     = Unsigned Long;
    ptrdiff_t0  = Signed Long
  }

  (* ---- Helper functions ---- *)
  let integer_range (impl: Implementation.implementation)
                    (ity : AilTypes.integerType) =
    let prec = impl.precision ity in
    if impl.signed ity then
      let prec_minus_one = prec - 1 in
      (match impl.binary_mode with
       | Two'sComplement ->
          (Nat_big_num.sub (Nat_big_num.of_int 0)
                           (Nat_big_num.pow_int (Nat_big_num.of_int 2)
                                                prec_minus_one)),
          (Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2)
                                                prec_minus_one)
                           (Nat_big_num.of_int 1))
       | _ -> assert false)
    else
     Nat_big_num.of_int 0,
     Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2) prec)
                     (Nat_big_num.of_int 1)
  let ibt_list = [Ichar; Short; Int_; Long; LongLong]
  let signed_ibt_list = List.map (fun ty -> Signed ty) ibt_list
  let unsigned_ibt_list = List.map (fun ty -> Unsigned ty) ibt_list

  let ity_list = signed_ibt_list
               @ unsigned_ibt_list
               @ [Char; Bool]

  let ity_to_ctype (ity: AilTypes.integerType) : ctype =
    Core_ctype.Basic0 (Integer ity)


  (* ---- HELPER MAP MAKING FUNCTION ---- *)
  let mk_ctype_map (name : string)
                   (types: ctype list)
                   (sort : Sort.sort)
                   : (ctype, Expr.expr) Pmap.map =
    List.fold_left (fun acc ctype ->
      let ctype_expr = CtypeSort.mk_expr ctype in
      let expr = mk_fresh_const
                    (sprintf "%s(%S)" name (Expr.to_string ctype_expr))
                    sort in
      Pmap.add ctype expr acc) (Pmap.empty Pervasives.compare) types
  (* ---- Constants ---- *)


  (* TODO: massive code duplication *)
  let ivmin_map : (ctype, Expr.expr) Pmap.map =
    mk_ctype_map "ivmin" (List.map ity_to_ctype ity_list) integer_sort

  let ivmax_map : (ctype, Expr.expr) Pmap.map =
    mk_ctype_map "ivmax" (List.map ity_to_ctype ity_list) integer_sort


  let sizeof_map : (ctype, Expr.expr) Pmap.map =
    mk_ctype_map "sizeof" (List.map ity_to_ctype ity_list) integer_sort

  let is_unsigned_map : (ctype, Expr.expr) Pmap.map =
    mk_ctype_map "is_unsigned" (List.map ity_to_ctype ity_list)
                               boolean_sort
  (* ---- Assertions ---- *)
  let ivmin_asserts =
    let ivmin_assert (ctype: ctype) : Expr.expr =
      let const = Pmap.find ctype ivmin_map in
      match ctype with
      | Basic0 (Integer ity) ->
          let (min, _) = integer_range impl ity in
          mk_eq const (big_num_to_z3 min)
      | _ -> assert false
    in
    List.map (fun ity -> ivmin_assert (ity_to_ctype ity))
             ity_list

  let ivmax_asserts =
    let ivmax_assert (ctype: ctype) : Expr.expr =
      let const = Pmap.find ctype ivmax_map in
      match ctype with
      | Basic0 (Integer ity) ->
          let (_, max) = integer_range impl ity in
          mk_eq const (big_num_to_z3 max)
      | _ -> assert false
    in
    List.map (fun ity -> ivmax_assert (ity_to_ctype ity))
             ity_list

  let sizeof_asserts =
    let sizeof_assert (ctype: ctype) : Expr.expr =
      let const = Pmap.find ctype sizeof_map in
      match ctype with
      | Basic0 (Integer ity) ->
          mk_eq const (int_to_z3 (Option.get (sizeof_ity ity)))
      | _ -> assert false
    in
    List.map (fun ity -> sizeof_assert (ity_to_ctype ity))
             ity_list

  (* TODO: char; other types *)
  let is_unsigned_asserts =
    let signed_tys =
      List.map (fun ty -> Pmap.find (ity_to_ctype ty) is_unsigned_map)
               signed_ibt_list in
    let unsigned_tys =
      List.map (fun ty -> Pmap.find (ity_to_ctype ty) is_unsigned_map)
               unsigned_ibt_list in
    List.map (fun signed_const ->
                mk_eq signed_const (mk_false)) signed_tys
    @ List.map (fun unsigned_const ->
                  mk_eq unsigned_const (mk_true)) unsigned_tys

  (* ---- All assertions ---- *)
  let all_asserts =   ivmin_asserts
                    @ ivmax_asserts
                    @ sizeof_asserts
                    @ is_unsigned_asserts
end

(* =========== MISCELLANEOUS HELPER FUNCTIONS =========== *)
let mk_unspecified_expr (sort: Sort.sort) (ctype: Expr.expr)
                        : Expr.expr =
  if (Sort.equal (LoadedInteger.mk_sort) sort) then
    LoadedInteger.mk_unspecified ctype
  else if (Sort.equal (LoadedPointer.mk_sort) sort) then
    LoadedPointer.mk_unspecified ctype
  else
    assert false

let mk_initial_value (ctype: ctype) (name: string) =
  match ctype with
  | Void0 ->
      (UnitSort.mk_unit, [])
  | Basic0 (Integer ity) ->
      let const = mk_fresh_const name integer_sort in
      let ge_ivmin =
          binop_to_z3 OpGe const (Pmap.find ctype ImplFunctions.ivmin_map) in
      let le_ivmax =
          binop_to_z3 OpLe const (Pmap.find ctype ImplFunctions.ivmax_map) in
      (const, [ge_ivmin;le_ivmax])
  | _ -> assert false

let mk_initial_loaded_value (sort: Sort.sort) (name: string)
                            (ctype: ctype) (specified: bool)
                            : Expr.expr * (Expr.expr list) =
  if specified then begin
    let (initial_value, assertions) = mk_initial_value ctype name in
    assert (Sort.equal (LoadedInteger.mk_sort) sort);
    (LoadedInteger.mk_specified initial_value, assertions)
  end else
    (mk_unspecified_expr sort (CtypeSort.mk_nonatomic_expr ctype), [])

(* =========== PPRINTERS =========== *)
let pp_bmc_ret (bmc_ret: bmc_ret) =
  sprintf ">>Expr: %s\n>>Assume:%s\n>>VCs:%s\n"
          (Expr.to_string bmc_ret.expr)
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.assume
          )
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.vcs
          )

let rec pp_bmcz3sort (sort: bmcz3sort) =
  match sort with
  | CaseSortBase (ctype, sort) ->
      sprintf "(%s,%s)" (Expr.to_string (CtypeSort.mk_expr ctype))
                        (Sort.to_string sort)
  | CaseSortList sortlist ->
      "[" ^ (String.concat "," (List.map pp_bmcz3sort sortlist)) ^ "]"

let pp_addr (addr: int * int) =
  sprintf "(%d,%d)" (fst addr) (snd addr)

(* =========== CORE TYPES -> Z3 SORTS =========== *)
let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer     -> integer_sort
  | OTy_pointer     -> PointerSort.mk_sort
  | OTy_floating
  | OTy_array _
  | OTy_struct _ ->
      assert false
  | OTy_cfunction _ -> CFunctionSort.mk_sort (* TODO *)
  | OTy_union _ ->
      assert false

let cbt_to_z3 (cbt: core_base_type) : Sort.sort =
  match cbt with
  | BTy_unit                -> UnitSort.mk_sort
  | BTy_boolean             -> boolean_sort
  | BTy_ctype               -> CtypeSort.mk_sort
  | BTy_list _              -> assert false
  | BTy_tuple cbt_list      -> assert false
  | BTy_object obj_type     -> cot_to_z3 obj_type
  | BTy_loaded OTy_integer  -> LoadedInteger.mk_sort
  | BTy_loaded OTy_pointer  -> LoadedPointer.mk_sort
  | BTy_loaded _            -> assert false

let sorts_to_tuple (sorts: Sort.sort list) : Sort.sort =
  let tuple_name =
    "(" ^ (String.concat "," (List.map Sort.to_string sorts)) ^ ")" in
  let arg_list = List.mapi
    (fun i _ -> mk_sym ("#" ^ (string_of_int i))) sorts in
  Tuple.mk_sort g_ctx (mk_sym tuple_name) arg_list sorts

let ctor_to_z3 (ctor  : typed_ctor)
               (exprs : Expr.expr list)
               (bTy   : core_base_type option) =
  match ctor with
  | Ctuple ->
      let sort = sorts_to_tuple (List.map Expr.get_sort exprs) in
      let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl exprs
  | Civmax ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civmin ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civsizeof ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Cspecified ->
      assert (List.length exprs = 1);
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_specified (List.hd exprs)
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_specified (List.hd exprs)
      else
        assert false
  | Cunspecified ->
      assert (List.length exprs = 1);
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_unspecified (List.hd exprs)
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_unspecified (List.hd exprs)
      else
        assert false
  | _ ->
      assert false

let integer_value_to_z3 (ival: Ocaml_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match eval_integer_value ival with
  | None -> assert false
  | Some i -> big_num_to_z3 i

let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _ ->
      assert false
  | OVpointer pv ->
      assert (is_null pv);
      PointerSort.mk_null
  | OVcfunction (Sym sym) ->
      CFunctionSort.mk_cfun (int_to_z3 (symbol_to_int sym))
  | OVcfunction _ ->
      assert false
  | OVarray _
  | OVstruct _
  | OVunion _
  | OVcomposite _ ->
      assert false

let value_to_z3 (value: value)
                : Expr.expr =
  match value with
  | Vunit        -> UnitSort.mk_unit
  | Vtrue        -> mk_true
  | Vfalse       -> mk_false
  | Vlist _      -> assert false
  | Vtuple _     -> assert false
  | Vctype cty   -> CtypeSort.mk_expr cty
  | Vobject oval -> object_value_to_z3 oval
  | Vloaded (LVspecified oval) ->
      begin match oval with
       | OVinteger ival ->
           LoadedInteger.mk_specified (integer_value_to_z3 ival)
       | _ -> assert false
      end
  | Vloaded (LVunspecified ctype) ->
      begin
      match ctype with
      | Basic0 (Integer _) ->
          LoadedInteger.mk_unspecified (CtypeSort.mk_expr ctype)
      | _ -> assert false
      end

let rec ailctype_to_ctype (ty: AilTypes.ctype)
                          : Core_ctype.ctype0 =
  match ty with
  | Void -> Void0
  | Basic bty -> Basic0 bty
  | Array (cty, n) -> Array0 (ailctype_to_ctype cty, n)
  | Function (_, (q,ty1), args, variadic) ->
      Function0 ((q, ailctype_to_ctype ty1),
                 List.map (fun (q,ty1,_) -> (q, ailctype_to_ctype ty1)) args,
                 variadic)
  | Pointer (v1,v2) -> Pointer0 (v1,ailctype_to_ctype v2)
  | Atomic cty -> Atomic0 (ailctype_to_ctype cty)
  | Struct v -> Struct0 v
  | Union v ->  Union0 v
  | Builtin v -> Builtin0 v

let rec ctype_to_bmcz3sort (ty  : ctype)
                           (file: unit typed_file)
                           : bmcz3sort =
  match ty with
  | Void0     -> assert false
  | Basic0(Integer i) ->
      CaseSortBase (ty, LoadedInteger.mk_sort)
  | Basic0 _ -> assert false
  | Array0(ty2, Some n) ->
      let sort = ctype_to_bmcz3sort ty2 file in
      CaseSortList (repeat_n (Nat_big_num.to_int n) sort)
  | Array0(_, None) ->
      assert false
  | Function0 _ -> assert false
  | Pointer0 _ ->
      CaseSortBase (ty, LoadedPointer.mk_sort)
  | Atomic0 (Basic0 ty2) ->
      begin
      match ctype_to_bmcz3sort (Basic0 ty2) file with
      | CaseSortBase(_, sort) -> CaseSortBase (Atomic0 (Basic0 ty2), sort)
      | _ -> assert false
      end
  | Atomic0 _ ->
      assert false
  | Struct0 sym ->
      begin match Pmap.lookup sym file.tagDefs with
      | Some (StructDef memlist) ->
          CaseSortList (List.map (fun (_, ty) -> ctype_to_bmcz3sort ty file)
                                 memlist)
      | _ -> assert false
      end
  | Union0 _
  | Builtin0 _ -> assert false

(* =========== SOME MONAD FUN =========== *)

module BmcM = struct
  type sym_table = (sym_ty, Expr.expr) Pmap.map
  type run_depth_table = (name, int) Pmap.map
  type alloc = int
  type memory_table = (addr_ty, Expr.expr) Pmap.map

  type action_id = int

  type bmc_state = {
    file              : unit typed_file;
    ail_opt           : GenTypes.genTypeCategory AilSyntax.ail_program option;

    sym_supply        : sym_supply_ty;
    sym_table         : sym_table;

    (* Map from Erun/Eccall symbol to number of times encountered.
     * Used to control depth of potentially recursive Erun/Eccall *)
    run_depth_table   : run_depth_table;

    (* Allocation id supply *)
    alloc_supply      : alloc;
    (* Map from address to current Z3 expression in ``memory'' *)
    memory            : memory_table;   (* sequential mode *)

    (* Procedure-local state *)
    proc_expr         : (unit typed_expr) option; (* Procedure being checked *)
    ret_const         : Expr.expr option;         (* Expression returned *)

    (* Concurrency stuff *)
    tid        : tid;

    tid_supply : tid;
    aid_supply : action_id;

    addr_ty_table : (addr_ty, ctype) Pmap.map;
    parent_tids   : (tid, tid) Pmap.map;
  }

  (* =========== MONADIC FUNCTIONS =========== *)
  type 'a eff =
    Eff of (bmc_state -> 'a * bmc_state)

  let return (a: 't) : 't eff = Eff (fun st -> (a, st))

  let bind ((Eff ma): 'a eff) (f: 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st ->
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st'
    end

  let (>>=) = bind

  let (>>) m m' = bind m (fun _ -> bind m' (fun x' -> return x'))

  let run : bmc_state -> 'a eff -> 'a * bmc_state =
    fun st (Eff ma) -> ma st

  let sequence ms =
    List.fold_right (
      fun m m' ->
      m  >>= fun x  ->
      m' >>= fun xs ->
      return (x :: xs)
    ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM  f ms = sequence (List.map f ms)
  let mapMi f ms = sequence (List.mapi f ms)
  let mapM2 f ms1 ms2  = sequence (List.map2 f ms1 ms2)
  let mapM_ f ms = sequence_ (List.map f ms)
  let mapM2_ f ms1 ms2 = sequence_ (List.map2 f ms1 ms2)

  let get : bmc_state eff =
    Eff (fun st -> (st, st))

  let put (st' : bmc_state) : unit eff =
    Eff (fun _ -> ((), st'))

  (* =========== STATE ACCESSORS =========== *)
  (* file *)
  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  (* ail option *)
  let get_ail_opt : 'a eff =
    get >>= fun st ->
    return st.ail_opt

  (* sym table *)
  let get_sym_table : sym_table eff =
    get >>= fun st ->
    return st.sym_table

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get_sym_table >>= fun sym_table ->
    return (Pmap.find sym sym_table)

  let update_sym_table (new_table: sym_table)
                       : unit eff =
    get >>= fun st ->
    put {st with sym_table = new_table}

  let add_sym_to_sym_table (sym: sym_ty) (expr: Expr.expr)
                           : unit eff =
    get_sym_table >>= fun sym_table ->
    update_sym_table (Pmap.add sym expr sym_table)

  (* run depth table *)
  let get_run_depth_table : run_depth_table eff =
    get >>= fun st ->
    return st.run_depth_table

  let lookup_run_depth (label: name) : int eff =
    get_run_depth_table >>= fun table ->
    match Pmap.lookup label table with
    | None  -> return 0
    | Some i -> return i

  let update_run_depth_table (new_table: run_depth_table)
                             : unit eff =
    get >>= fun st ->
    put {st with run_depth_table = new_table}

  let increment_run_depth (label: name) : unit eff =
    lookup_run_depth label  >>= fun depth ->
    get_run_depth_table    >>= fun table ->
    update_run_depth_table (Pmap.add label (depth+1) table)

  let decrement_run_depth (label: name) : unit eff =
    lookup_run_depth label >>= fun depth ->
    get_run_depth_table    >>= fun table ->
    update_run_depth_table (Pmap.add label (depth-1) table)

  (* allocation *)
  let get_new_alloc_and_update_supply : alloc eff =
    get                    >>= fun st ->
    return st.alloc_supply >>= fun alloc ->
    put {st with alloc_supply = alloc + 1} >>= fun () ->
    return alloc

  (* memory *)
  let get_memory : memory_table eff =
    get >>= fun st ->
    return st.memory

  let update_memory (addr: addr_ty) (expr: Expr.expr) : unit eff =
    if !!bmc_conf.concurrent_mode then assert false
    else get >>= fun st ->
         put {st with memory = Pmap.add addr expr st.memory}

  let update_memory_table (memory: memory_table) : unit eff =
    get >>= fun st ->
    put {st with memory = memory}

  let get_all_addresses : (addr_ty list) eff =
    get >>= fun st ->
    return (List.map fst (Pmap.bindings_list st.memory))

  (* proc expr *)
  let get_proc_expr : (unit typed_expr) eff =
    get >>= fun st ->
    return (Option.get st.proc_expr)

  let update_proc_expr (proc_expr: unit typed_expr) : unit eff =
    get >>= fun st ->
    put {st with proc_expr = Some proc_expr}

  (* ret_const*)
  let get_ret_const : Expr.expr eff =
    get >>= fun st ->
    return (Option.get st.ret_const)

  let update_ret_const (expr: Expr.expr) =
    get >>= fun st ->
    put {st with ret_const = Some expr}

  (* =========== CONCURRENCY =========== *)
  let get_tid        : tid eff =
    get >>= fun st ->
    return st.tid

  let put_tid (tid: tid) : unit eff =
    get >>= fun st ->
    put {st with tid = tid}

  let get_fresh_tid  : tid eff =
    get                                >>= fun st ->
    return st.tid_supply               >>= fun ret ->
    put {st with tid_supply = ret + 1} >>= fun () ->
    return ret

  let get_fresh_aid  : action_id eff =
    get                                >>= fun st ->
    return st.aid_supply               >>= fun ret ->
    put {st with aid_supply = ret + 1} >>= fun () ->
    return ret

  let add_addr_type (addr: addr_ty) (ty: ctype) : unit eff =
    get >>= fun st ->
    put {st with addr_ty_table = Pmap.add addr ty st.addr_ty_table}

  let get_parent_tids : ((tid, tid) Pmap.map) eff =
    get >>= fun st ->
    return st.parent_tids

  let add_parent_tid (child_tid: tid) (parent_tid: tid) : unit eff =
    get >>= fun st ->
    put {st with parent_tids = Pmap.add child_tid parent_tid st.parent_tids}

  (* =========== STATE INIT =========== *)
  let mk_initial_state (file       : unit typed_file)
                       (sym_supply : sym_supply_ty)
                       (ail_opt)
                       : bmc_state =
    { file             = file
    ; ail_opt          = ail_opt

    ; sym_supply       = sym_supply
    ; sym_table        = Pmap.empty sym_cmp

    ; run_depth_table  = Pmap.empty name_cmp

    ; alloc_supply     = 0
    ; memory           = Pmap.empty Pervasives.compare

    ; proc_expr        = None
    ; ret_const        = None

    ; tid              = 0
    ; tid_supply       = 1
    ; aid_supply       = 0
    ; addr_ty_table    = Pmap.empty Pervasives.compare
    ; parent_tids      = Pmap.empty Pervasives.compare
    }

  (* =========== Manipulating functions ========== *)

  (* For each modified address, update base memory using tables
   * guarded by guards. *)
  let merge_memory (base     : memory_table)
                   (mod_addr : AddrSet.t)
                   (tables   : memory_table list)
                   (guards   : Expr.expr list) =
    let guarded_tables : (memory_table * Expr.expr) list =
      List.combine tables guards in
    AddrSet.fold (fun addr acc ->
      match Pmap.lookup addr acc with
      | None -> acc
      | Some expr_base ->
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
            match Pmap.lookup addr table with
            | None      -> acc_expr
            | Some expr -> mk_ite guard expr acc_expr
         ) guarded_tables expr_base in
        (* TODO: create new seq variable? *)
        Pmap.add addr new_expr acc
    ) mod_addr base

  (* =========== Pprinters =========== *)
  let pp_sym_table (table: sym_table) =
    Pmap.fold (fun sym expr acc ->
      sprintf "%s\n%s -> %s" acc (symbol_to_string sym) (Expr.to_string expr))
      table ""

  let pp_addr ((x,y): addr_ty) =
    sprintf "(%d,%d)" x y

  let pp_memory (memory: memory_table) =
    Pmap.fold (fun addr expr acc ->
      sprintf "%s\n%s -> %s" acc (pp_addr addr) (Expr.to_string expr))
    memory ""
end

let (>>=)  = BmcM.bind
let return = BmcM.return

(* =========== SYMBOL TABLE MAINTENANCE FUNCTIONS =========== *)
let symbol_to_fresh_z3_const (sym: sym_ty) (sort: Sort.sort) : Expr.expr =
  mk_fresh_const (symbol_to_string sym) sort

let add_sym_to_sym_table (sym: sym_ty) (ty: core_base_type)
                         : unit BmcM.eff =
  let z3_sort = cbt_to_z3 ty in
  let z3_sym  = symbol_to_fresh_z3_const sym z3_sort in
  BmcM.add_sym_to_sym_table sym z3_sym

let initialise_simple_param ((sym, ty) : sym_ty * core_base_type)
                            : unit BmcM.eff =
  assert (not (is_core_ptr_bty ty));
  dprintf "Initialising param: %s %s\n"
          (symbol_to_string sym)
          (pp_to_string (Pp_core.Basic.pp_core_base_type ty));
  (* TODO: do not handle pointers for now.
   *       Pointers: need to do a create maybe. *)
  add_sym_to_sym_table sym ty

let rec add_pattern_to_sym_table (pattern: typed_pattern)
                                 : unit BmcM.eff =
  match pattern with
  | CaseBase(None, _) ->
      return () (* Do nothing; wildcard => no symbol *)
  | CaseBase(Some sym, ty) ->
      add_sym_to_sym_table sym ty
  | CaseCtor (ctor, patlist) ->
      BmcM.mapM_ add_pattern_to_sym_table patlist

(* =========== Z3 LET BINDINGS =========== *)
let mk_let_binding (maybe_sym: sym_ty option)
                   (expr: Expr.expr)
                   : Expr.expr BmcM.eff =
  match maybe_sym with
  | None -> return mk_true
  | Some sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      (* TODO: hack for C functions... *)
      if (Sort.equal CFunctionSort.mk_sort (Expr.get_sort expr)) then
        BmcM.add_sym_to_sym_table sym expr >>= fun () ->
        return (mk_eq sym_expr expr)
      else
        return (mk_eq sym_expr expr)

let rec mk_let_bindings (pat: typed_pattern) (expr: Expr.expr)
                        : Expr.expr BmcM.eff =
  match pat with
  | CaseBase(maybe_sym, _) ->
      mk_let_binding maybe_sym expr
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      BmcM.mapM (fun (pat, e) -> mk_let_bindings pat e)
                (List.combine patlist (Expr.get_args expr)) >>= fun bindings ->
      return (mk_and bindings)
  | CaseCtor(Cspecified, [CaseBase(sym, BTy_object OTy_integer)]) ->
      let is_specified = LoadedInteger.is_specified expr in
      let specified_value = LoadedInteger.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, [CaseBase(sym, BTy_object OTy_pointer)]) ->
      let is_specified = LoadedPointer.is_specified expr in
      let specified_value = LoadedPointer.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(sym, BTy_ctype)]) ->
      let (is_unspecified, unspecified_value) =
        if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
          let is_unspecified = LoadedInteger.is_unspecified expr in
          let unspecified_value = LoadedInteger.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
          let is_unspecified = LoadedPointer.is_unspecified expr in
          let unspecified_value = LoadedPointer.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else
          assert false
      in
      mk_let_binding sym unspecified_value >>= fun is_eq_value ->
      return (mk_and [is_unspecified; is_eq_value])
  | CaseCtor(Cunspecified, _) ->
      assert false
  | CaseCtor(_, _) ->
      assert false

(* =========== PATTERN MATCHING =========== *)
let rec pattern_match (pattern: typed_pattern)
                      (expr: Expr.expr)
                      : Expr.expr =
  match pattern with
  | CaseBase(_,_) ->
      mk_true
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let expr_list = Expr.get_args expr in
      let match_conditions =
        List.map2 (fun pat e -> pattern_match pat e) patlist expr_list in
      mk_and match_conditions
  | CaseCtor(Cspecified, [CaseBase(_, BTy_object OTy_integer)]) ->
      LoadedInteger.is_specified expr
  | CaseCtor(Cspecified, [CaseBase(_, BTy_object OTy_pointer)]) ->
      LoadedPointer.is_specified expr
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(_, BTy_ctype)]) ->
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
        LoadedInteger.is_unspecified expr
      else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
        LoadedPointer.is_unspecified expr
      else
        assert false
  | _ -> assert false

(* Compute conditions for matching cases.
 * Returns (vc, case_guard list) where vc asserts that some pattern is matched.
 *)
let compute_case_guards (patterns: typed_pattern list)
                        (to_match: Expr.expr)
                        : Expr.expr * Expr.expr list =
  let pattern_guards =
    List.map (fun pat -> pattern_match pat to_match) patterns in
  let case_guards = List.mapi (
      fun i expr ->
        mk_and [ mk_not (mk_or (list_take i pattern_guards))
               ; expr]) pattern_guards in
  let vc = mk_or pattern_guards in
  (vc, case_guards)

let mk_guarded_ite (exprs : Expr.expr list)
                   (guards: Expr.expr list) =
  assert (List.length exprs = List.length guards);
  match List.length exprs with
  | 0 -> assert false
  | 1 -> List.hd exprs
  | _ -> let rev_exprs = List.rev exprs in
         let rev_guards = List.rev guards in
         let last_case_expr = List.hd rev_exprs in
         List.fold_left2 (fun acc guard expr -> mk_ite guard expr acc)
                         last_case_expr
                         (List.tl rev_guards)
                         (List.tl rev_exprs)

(* =========== MODEL CHECKING FUNCTIONS =========== *)
let rec bmc_pexpr (Pexpr(_, bTy, pe): typed_pexpr) :
                  bmc_pret BmcM.eff =
  match pe with
  | PEsym sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      return { expr   = sym_expr
             ; assume = []
             ; vcs    = []
             }
  | PEimpl const ->
      BmcM.get_file >>= fun file ->
      begin match Pmap.lookup const file.impl with
      | Some (Def (_, pe)) ->
          bmc_pexpr pe
      | _ -> assert false
      end
  | PEval cval ->
      return { expr   = value_to_z3 cval
             ; assume = []
             ; vcs    = []
             }
  | PEconstrained _
  | PEundef _ ->
      let sort = cbt_to_z3 bTy in
      return { expr   = mk_fresh_const "undef" sort
             ; assume = []
             ; vcs    = [ mk_false ]
             }
  | PEerror _ ->
      let sort = cbt_to_z3 bTy in
      return { expr   = mk_fresh_const "error" sort
             ; assume = []
             ; vcs    = [ mk_false ]
             }
  | PEctor(Civmin, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.ivmin_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor(Civmax, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.ivmax_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor(Civsizeof, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.sizeof_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor (ctor, pelist) ->
      BmcM.mapM bmc_pexpr pelist >>= fun res_pelist ->
      return { expr   = ctor_to_z3 ctor (List.map pget_expr res_pelist)
                                        (Some bTy)
             ; assume = List.concat (List.map pget_assume res_pelist)
             ; vcs    = List.concat (List.map pget_vcs res_pelist)
             }
  | PEcase (pe, caselist) ->
      assert (List.length caselist > 0);
      bmc_pexpr pe >>= fun res_pe ->
      (* match_vc = assert some case is matched *)
      let (match_vc, case_guards) =
        compute_case_guards (List.map fst caselist) res_pe.expr in

      BmcM.get_sym_table >>= fun old_sym_table ->

      BmcM.mapM (fun (pat, case_pexpr) ->
                  add_pattern_to_sym_table pat    >>= fun () ->
                  mk_let_bindings pat res_pe.expr >>= fun let_binding ->
                  bmc_pexpr case_pexpr            >>= fun res_case_pexpr ->
                  BmcM.update_sym_table old_sym_table >>= fun () ->
                  return (let_binding, res_case_pexpr)
                ) caselist >>= fun res_caselist ->
      let reslist : bmc_pret list = List.map snd res_caselist in
      let guarded_bindings = List.map2 (
        fun guard (let_binding, _) -> mk_implies guard let_binding)
        case_guards res_caselist in
      let case_assumes = List.concat (List.map pget_assume reslist) in
      let guarded_vcs = List.map2 (
        fun guard res -> mk_implies guard (mk_and (pget_vcs res)))
        case_guards reslist in
      let ite_expr = mk_guarded_ite (List.map pget_expr reslist) case_guards in
      return { expr   = ite_expr
             ; assume =   res_pe.assume
                          @ guarded_bindings
                          @ case_assumes
             ; vcs    = match_vc :: (res_pe.vcs @ guarded_vcs)
             }
  | PEarray_shift (ptr, ty, index) ->
      bmc_pexpr ptr   >>= fun res_ptr ->
      bmc_pexpr index >>= fun res_index ->
      BmcM.get_file   >>= fun file ->
      let ty_size = bmcz3sort_size (ctype_to_bmcz3sort ty file) in
      let shift_size = binop_to_z3 OpMul res_index.expr (int_to_z3 ty_size) in
      let addr     = PointerSort.get_addr res_ptr.expr in
      let new_addr = AddressSort.shift_index_by_n addr shift_size in
      return { expr   = PointerSort.mk_ptr new_addr
             ; assume = res_ptr.assume @ res_index.assume
             ; vcs    = (mk_not (PointerSort.is_null res_ptr.expr))
                        ::res_ptr.vcs @ res_index.vcs
             }
  | PEmember_shift(ptr, sym, member) ->
      bmc_pexpr ptr >>= fun res_ptr ->
      BmcM.get_file >>= fun file ->
      begin match Pmap.lookup sym file.tagDefs with
      | Some (StructDef memlist) ->
          let memsizes = List.map (fun (cid, cbt) ->
              (cid, bmcz3sort_size (ctype_to_bmcz3sort cbt file))
            ) memlist in
          let (shift_size, _) = List.fold_left (
              fun (acc, skip) (cid, n) ->
                if cabsid_cmp cid member = 0 || skip then (acc, true)
                else (acc + n, false)
          ) (0, false) memsizes in
          let addr = PointerSort.get_addr res_ptr.expr in
          let new_addr =
            AddressSort.shift_index_by_n addr (int_to_z3 shift_size) in
          return { expr   = PointerSort.mk_ptr new_addr
                 ; assume = res_ptr.assume
                 ; vcs    = (mk_not (PointerSort.is_null res_ptr.expr))
                            ::res_ptr.vcs
                 }
      | _ -> assert false
      end
  | PEmemberof _  ->
      assert false
  | PEnot pe ->
      bmc_pexpr pe >>= fun res ->
      return {res with expr = mk_not res.expr}
  | PEop (binop, pe1, pe2) ->
      (* TODO: symbols added in pe1 visible in pe2 *)
      bmc_pexpr pe1 >>= fun res1 ->
      bmc_pexpr pe2 >>= fun res2 ->
      return { expr   = binop_to_z3 binop res1.expr res2.expr
             ; assume = res1.assume @ res2.assume
             ; vcs    = res1.vcs @ res2.vcs
             }
  | PEstruct _
  | PEunion _ ->
      assert false
  | PEcall (name, pelist) ->
      BmcM.get_file >>= fun file ->
      BmcM.lookup_run_depth name >>= fun depth ->
      (* Get the function called; either from stdlib or impl constants *)
      let (ty, args, fun_expr) =
        match name with
        | Sym sym ->
            begin match Pmap.lookup sym file.stdlib with
            | Some (Fun(ty, args, fun_expr)) ->
                (ty, args, fun_expr)
            | _ -> assert false
            end
        | Impl impl ->
            begin match Pmap.lookup impl file.impl with
            | Some (IFun (ty, args, fun_expr)) ->
                (ty, args, fun_expr)
            | _ -> assert false
            end
      in
      if depth >= !!bmc_conf.max_run_depth then
        return { expr   = mk_fresh_const "call_depth_exceeded" (cbt_to_z3 ty)
               ; assume = []
               ; vcs    = [ mk_false ]
               }
      else begin
      (* Bmc each argument *)
      BmcM.mapM (fun pe -> bmc_pexpr pe) pelist >>= fun arg_retlist ->
      (* Substitute arguments in function call *)
      let sub_map = List.fold_right2
          (fun (sym, _) pe table -> Pmap.add sym pe table)
          args pelist (Pmap.empty sym_cmp) in
      (* Bmc the function body *)
      let expr_to_check = substitute_pexpr sub_map fun_expr in
      BmcM.increment_run_depth name       >>= fun () ->
      BmcM.get_sym_table                  >>= fun old_sym_table ->
      bmc_pexpr expr_to_check             >>= fun ret_call ->
      BmcM.decrement_run_depth name       >>= fun () ->
      BmcM.update_sym_table old_sym_table >>= fun () ->

      return { expr   = ret_call.expr
             ; assume =   ret_call.assume
                        @ (List.concat (List.map pget_assume arg_retlist))
             ; vcs    = ret_call.vcs
                        @ (List.concat (List.map pget_vcs arg_retlist))
             }
      end
  | PElet (pat, pe1, pe2) ->
      bmc_pexpr pe1                 >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_pexpr pe2                 >>= fun res2 ->
      return { expr    = res2.expr
             ; assume  = let_binding::(res1.assume @ res2.assume)
             ; vcs     = res1.vcs @ res2.vcs
             }
  | PEif (pe_cond, pe1, pe2) ->
      (* TODO: symbols added in pe1 visible in pe2 *)
      bmc_pexpr pe_cond                   >>= fun res_cond ->
      BmcM.get_sym_table                  >>= fun old_sym_table ->
      bmc_pexpr pe1                       >>= fun res1 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->
      bmc_pexpr pe2                       >>= fun res2 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->
      let new_vcs =
          res_cond.vcs
        @ (List.map (fun vc -> mk_implies res_cond.expr vc) res1.vcs)
        @ (List.map (fun vc -> mk_implies (mk_not res_cond.expr) vc)
                    res2.vcs)
      in
      return { expr   = mk_ite res_cond.expr res1.expr res2.expr
             ; assume = res_cond.assume @ res1.assume @ res2.assume
             ; vcs    = new_vcs
             }
  | PEis_scalar _
  | PEis_integer _ ->
      assert false
  | PEis_signed _ ->
      assert false
  | PEis_unsigned (Pexpr(_, BTy_ctype, PEval (Vctype ctype))) ->
      return { expr   = Pmap.find ctype ImplFunctions.is_unsigned_map
             ; assume = []
             ; vcs = []
             }
  | PEis_unsigned _ ->
      assert false

module Bmc_paction = struct
  type ret = {
    assume   : Expr.expr list;
    vcs      : Expr.expr list;
    mod_addr : AddrSet.t;
    preexec  : preexec;
  }

  let mk_store (ptr: Expr.expr) (value: Expr.expr) (tid: tid)
               (memorder: memory_order) (guard: Expr.expr) (pol: polarity)
               : (Expr.expr * bmc_action) BmcM.eff =
    BmcM.get_fresh_aid >>= fun aid ->
    let const =
      mk_fresh_const ("store_" ^ (Expr.to_string ptr)) (Expr.get_sort value) in
    let binding = mk_eq const value in
    return (binding,
            (BmcAction(pol, guard, Store(aid, tid, memorder, ptr, const))))

  let do_concurrent_create (alloc_id: BmcM.alloc)
                           (sortlist: (ctype * Sort.sort) list)
                           (pol: polarity)
                           (specified: bool)
                           : ret BmcM.eff  =
    let is_atomic = (function ctype -> match ctype with
                     | Core_ctype.Atomic0 _ -> mk_true
                     | _ -> mk_false) in
    BmcM.mapMi (fun i (ctype, sort) ->
      let addr = (alloc_id, i) in
      let addr_expr = AddressSort.mk_from_addr addr in
      let ptr = PointerSort.mk_ptr addr_expr in
      let is_atomic =
        AddressSort.assert_is_atomic addr_expr (is_atomic ctype) in
      let (initial_value, assumptions) =
        mk_initial_loaded_value sort (sprintf "init_%d,%d" alloc_id i)
                                ctype specified in
      mk_store ptr initial_value initial_tid Cmm_csem.NA mk_true pol
        >>= fun (binding, action) ->
      return (binding::(is_atomic::assumptions), action)
    ) sortlist >>= fun retlist ->
    return { assume   = List.concat (List.map fst retlist)
           ; vcs      = []
           ; mod_addr = AddrSet.empty (* sequential only *)
           ; preexec  = List.fold_left (fun acc ret ->
                          add_initial_action (snd ret) acc)
                          mk_initial_preexec retlist
           }

  let do_sequential_create (alloc_id: BmcM.alloc)
                           (sortlist: (ctype * Sort.sort) list)
                           (specified: bool)
                           : ret BmcM.eff =
    BmcM.mapMi (fun i (ctype, sort) ->
      let addr = (alloc_id, i) in
      let seq_var = mk_fresh_const (sprintf "store_(%d %d)" alloc_id i) sort in
      BmcM.update_memory addr seq_var >>= fun () ->
      let (initial_value, assumptions) =
        mk_initial_loaded_value sort (sprintf "init_%d,%d" alloc_id i)
                                ctype specified in
      let binding = mk_eq seq_var initial_value in
      return (addr, binding::assumptions)
    ) sortlist >>= fun retlist ->
    return { assume    = List.concat (List.map snd retlist)
           ; vcs       = []
           ; mod_addr  = AddrSet.of_list (List.map fst retlist)
           ; preexec   = mk_initial_preexec (* concurrent only *)
           }

  let do_concurrent_store (ptr     : Expr.expr)
                          (value   : Expr.expr)
                          (memorder: memory_order)
                          (pol     : polarity)
                          : ret BmcM.eff =
    BmcM.get_tid >>= fun tid ->
    mk_store ptr value tid memorder (mk_not (PointerSort.is_null ptr)) pol
      >>= fun (binding, bmcaction) ->
    return { assume    = [ binding ]
           ; vcs       = []
           ; mod_addr  = AddrSet.empty (* sequential only *)
           ; preexec   = add_action bmcaction mk_initial_preexec
           }

  let do_sequential_store (ptr: Expr.expr) (value: Expr.expr) : ret BmcM.eff =
    (* TODO: alias analysis *)
    let sort = Expr.get_sort value in
    BmcM.get_memory >>= fun possible_addresses ->
    BmcM.mapM (fun (addr, expr_in_memory) ->
      let addr_sort = Expr.get_sort expr_in_memory in
      if (Sort.equal sort addr_sort) then
        let addr_expr = AddressSort.mk_from_addr addr  in
        let new_seq_var = mk_fresh_const (Expr.to_string addr_expr) sort in
        (* new_seq_var is equal to to_store if addr_eq, else old value *)
        let addr_eq =
          mk_and [ mk_not (PointerSort.is_null ptr)
                 ; mk_eq (PointerSort.get_addr ptr) addr_expr] in
        let new_val = mk_eq new_seq_var value in
        let old_val = mk_eq new_seq_var expr_in_memory in
        BmcM.update_memory addr new_seq_var >>= fun () ->
        return (Some (addr, mk_ite addr_eq new_val old_val))
      else
        return None
      ) (Pmap.bindings_list possible_addresses) >>= fun update_list ->
    let filtered = List.map Option.get (List.filter is_some update_list) in
    assert (List.length filtered > 0);
    return { assume    = List.map snd filtered
           ; vcs       = []
           ; mod_addr  = AddrSet.of_list (List.map fst filtered)
           ; preexec   = mk_initial_preexec (* concurent only *)
           }

  let do_concurrent_load (ptr      : Expr.expr)
                         (new_const: Expr.expr)
                         (memorder : memory_order)
                         (pol      : polarity)
                         : ret BmcM.eff =
    BmcM.get_fresh_aid >>= fun aid ->
    BmcM.get_tid >>= fun tid ->
    let action = BmcAction(pol, mk_not (PointerSort.is_null ptr),
                           Load(aid, tid, memorder, ptr, new_const)) in
    return { assume   = []
           ; vcs      = [mk_not (PointerSort.is_null ptr)]
           ; mod_addr = AddrSet.empty (* sequential only *)
           ; preexec  = add_action action mk_initial_preexec
           }

  let do_sequential_load (ptr      : Expr.expr)
                         (new_const: Expr.expr)
                         : ret BmcM.eff =
    (* TODO: alias analysis *)
    BmcM.get_memory >>= fun possible_addresses ->
    let sort = Expr.get_sort new_const in
    (* sym_addr = addr => ret_expr = mem[addr] *)
    BmcM.mapM (fun (addr, expr_in_memory) ->
      let addr_sort = Expr.get_sort expr_in_memory in
      if (Sort.equal sort addr_sort) then
        let addr_expr = AddressSort.mk_from_addr addr in
        let addr_eq =
          mk_and [ mk_not (PointerSort.is_null ptr)
                 ; mk_eq addr_expr (PointerSort.get_addr ptr)] in
        let impl_expr = mk_implies addr_eq (mk_eq new_const expr_in_memory) in
        return (Some (impl_expr, addr_eq))
      else
        return None
    ) (Pmap.bindings_list possible_addresses) >>= fun retlist ->
    let filtered = List.map Option.get (List.filter is_some retlist) in
    return { assume   = List.map fst filtered
           ; vcs      = [mk_or (List.map snd filtered)]
           ; mod_addr = AddrSet.empty
           ; preexec  = mk_initial_preexec (* concurrent only *)
           }
end

let bmc_paction (Paction(pol, Action(_, _, action_)): unit typed_paction)
                : bmc_ret BmcM.eff =
  match action_ with
  | Create (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
      (* TODO: non-basic types? *)
      BmcM.get_file >>= fun file ->
      let sortlist = ctype_to_bmcz3sort ctype file in
      let flat_sortlist = flatten_bmcz3sort sortlist in
      let allocation_size = bmcz3sort_size sortlist in
      BmcM.get_new_alloc_and_update_supply >>= fun alloc_id ->

      let to_run =
        if !!bmc_conf.concurrent_mode
        then Bmc_paction.do_concurrent_create alloc_id flat_sortlist pol false
        else Bmc_paction.do_sequential_create alloc_id flat_sortlist false in
      to_run >>= fun ret ->
      (* Assert alloc_size(alloc_id) = allocation_size *)
      let alloc_size_expr =
        mk_eq (Expr.mk_app g_ctx AddressSort.alloc_size_decl
                                 [int_to_z3 alloc_id])
              (int_to_z3 allocation_size) in
      return { expr      = PointerSort.mk_ptr
                            (AddressSort.mk_from_addr (alloc_id, 0))
             ; assume    = alloc_size_expr :: ret.assume
             ; vcs       = ret.vcs
             ; drop_cont = mk_false
             ; mod_addr  = ret.mod_addr
             ; ret_cond  = mk_true
             ; preexec   = ret.preexec
             }
  | Create _ -> assert false
  | CreateReadOnly _
  | Alloc0 _ ->
      assert false
  | Kill (_, pe) ->
      bmc_debug_print 7 "TODO: kill ignored";
      bmc_pexpr pe >>= fun res_pe ->
      return { expr      = UnitSort.mk_unit
             ; assume    = res_pe.assume
             ; vcs       = res_pe.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             ; preexec   = mk_initial_preexec
             }
  | Store0 (Pexpr(_, _, PEval (Vctype ty)), Pexpr(_, _, PEsym sym),
            wval, memorder) ->
      (* TODO: do alias analysis *)
      (* TODO: check alignment *)
      BmcM.get_file               >>= fun file ->
      BmcM.lookup_sym sym         >>= fun sym_expr ->
      bmc_pexpr wval              >>= fun res_wval ->
      let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
      assert (List.length flat_sortlist = 1);

      let to_run =
        if !!bmc_conf.concurrent_mode
        then Bmc_paction.do_concurrent_store sym_expr res_wval.expr memorder pol
        else Bmc_paction.do_sequential_store sym_expr res_wval.expr in
      to_run >>= fun ret ->
      return { expr      = UnitSort.mk_unit
             ; assume    = ret.assume @ res_wval.assume
             ; vcs       = ret.vcs @ res_wval.vcs
             ; drop_cont = mk_false
             ; mod_addr  = ret.mod_addr
             ; ret_cond  = mk_true
             ; preexec   = ret.preexec
             }
  | Store0 _ ->
      assert false
  | Load0 (Pexpr(_, _, PEval (Vctype ty)), Pexpr(_,_, PEsym sym), memorder) ->
      BmcM.lookup_sym sym         >>= fun sym_expr ->
      BmcM.get_file               >>= fun file ->
      assert (Sort.equal (Expr.get_sort sym_expr) PointerSort.mk_sort);
      let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
      let (_, sort) = List.hd flat_sortlist in
      assert (List.length flat_sortlist = 1);

      let ret_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
      let to_run =
        if !!bmc_conf.concurrent_mode
        then Bmc_paction.do_concurrent_load sym_expr ret_expr memorder pol
        else Bmc_paction.do_sequential_load sym_expr ret_expr in
      to_run >>= fun ret ->
      return { expr      = ret_expr
             ; assume    = ret.assume
             ; vcs       = ret.vcs
             ; drop_cont = mk_false
             ; mod_addr  = ret.mod_addr
             ; ret_cond  = mk_true
             ; preexec   = ret.preexec
             }
  | Load0 _
  | RMW0 _
  | Fence0 _ ->
      assert false
  | CompareExchangeStrong(Pexpr(_, _, PEval (Vctype ty)),
                          Pexpr(_,_, PEsym obj),
                          Pexpr(_,_, PEsym expected),
                          desired, mo_success, mo_failure) ->
    assert (!!bmc_conf.concurrent_mode);
    (* _bool compare_exchange_strong(object, expected, desire, success, failure):
     * if *object == *expected
     *   *object = desire
     * else
     *   *expected = *object
     *
     * r_expected = load(expected, NA)
     * def rval = fresh z3 constant
     * rval = r_expected => RMW(object, desire, success)
     * rval <> r_expected => rval = load(object, failure); store(expected,rval)
     *
     * For sequential mode: this is just read, object, read expected, do
     * assignments. Not implemented.
     *)
    BmcM.get_file            >>= fun file ->
    BmcM.lookup_sym obj      >>= fun obj_sym ->
    BmcM.lookup_sym expected >>= fun expected_sym ->
    bmc_pexpr desired        >>= fun ret_desired ->
    let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
    assert (List.length flat_sortlist = 1);
    let (_, sort) = List.hd flat_sortlist in

    let rval_expected =
      mk_fresh_const ("load_" ^ (symbol_to_string expected)) sort in
    let rval_object =
      mk_fresh_const ("load_" ^ (symbol_to_string obj)) sort in
    Bmc_paction.do_concurrent_load expected_sym rval_expected NA Pos
                                        >>= fun ret_read_expected ->
    let success_guard = mk_eq rval_expected rval_object in
    (* If fail: do a load of object and then a store *)
    let fail_guard = mk_not success_guard in
    Bmc_paction.do_concurrent_load obj_sym rval_object mo_failure Pos
                                        >>= fun fail_load ->
    Bmc_paction.do_concurrent_store expected_sym rval_object NA Pos
                                        >>= fun fail_store ->
    (* If succeed, do a rmw *)
    BmcM.get_fresh_aid >>= fun rmw_aid ->
    BmcM.get_tid       >>= fun tid ->
    let rmw =
      BmcAction(Pos, success_guard,
                RMW(rmw_aid, tid, mo_success,
                    obj_sym, rval_object, ret_desired.expr)) in

    let preexec =
      begin
      let (p_fail_load, p_fail_store, p_read_expected) =
        (guard_preexec fail_guard fail_load.preexec,
         guard_preexec fail_guard fail_store.preexec,
         ret_read_expected.preexec) in
      (* SB the load and store for failed compare_exchange *)
      let failed_preexec = combine_preexecs_and_sb p_fail_load p_fail_store in
      (* SB the read_expected and (load,store) for failed compare exchange *)
      let combined_fail =
        combine_preexecs_and_sb p_read_expected failed_preexec in

      assert (List.length combined_fail.initial_actions = 0);
      assert (List.length combined_fail.asw = 0);

      { actions         = rmw :: combined_fail.actions
      ; initial_actions = combined_fail.initial_actions (*Should be empty *)
      ; sb              = (compute_sb p_read_expected.actions [rmw])
                          @ combined_fail.sb
      ; asw             = combined_fail.asw (* Should be empty *)
      }
      end in

    return { expr      = mk_ite success_guard
                            (LoadedInteger.mk_specified (int_to_z3 1))
                            (LoadedInteger.mk_specified (int_to_z3 0))
           ; assume    = ret_desired.assume
                         @ ret_read_expected.assume
                         @ fail_load.assume
                         @ fail_store.assume
           ; vcs       = ret_desired.vcs           (* TODO: check not null? *)
                         @ ret_read_expected.vcs
                         @ (List.map (mk_implies fail_guard) fail_load.vcs)
                         @ (List.map (mk_implies fail_guard) fail_store.vcs)
           ; drop_cont = mk_false
           ; mod_addr  = AddrSet.empty (* sequential only *)
           ; ret_cond  = mk_true
           ; preexec    = preexec
           }
  | _ -> assert false


let rec bmc_expr (Expr(_, expr_): unit typed_expr)
                 : bmc_ret BmcM.eff =
  match expr_ with
  | Epure pe ->
      bmc_pexpr pe >>= fun pres ->
      return (bmc_pret_to_ret pres)
  | Ememop (PtrValidForDeref, [ptr])  ->
      bmc_pexpr ptr >>= fun res_ptr ->
      let addr = PointerSort.get_addr res_ptr.expr in
      let range_assert = AddressSort.valid_index_range addr in
      return { expr      = mk_and [mk_not (PointerSort.is_null res_ptr.expr)
                                  ;range_assert]
             ; assume    = res_ptr.assume
             ; vcs       = res_ptr.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             ; preexec   = mk_initial_preexec
             }
  | Ememop (PtrEq, [p1;p2]) ->
      bmc_pexpr p1 >>= fun res_p1 ->
      bmc_pexpr p2 >>= fun res_p2 ->
      return { expr      = mk_eq res_p1.expr res_p2.expr
             ; assume    = res_p1.assume @ res_p2.assume
             ; vcs       = res_p1.vcs @ res_p2.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             ; preexec   = mk_initial_preexec
             }
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction paction
  | Ecase (pe, caselist) ->
      (* TODO: code duplication from PEcase *)
      assert (List.length caselist > 0);
      bmc_pexpr pe >>= fun res_pe ->
      let (match_vc, case_guards) =
        compute_case_guards (List.map fst caselist) res_pe.expr in
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.get_memory    >>= fun old_memory ->

      BmcM.mapM (fun (pat, case_expr) ->
                  add_pattern_to_sym_table pat    >>= fun () ->
                  mk_let_bindings pat res_pe.expr >>= fun let_binding ->
                  bmc_expr case_expr              >>= fun res_case_expr ->
                  BmcM.get_memory                 >>= fun mem ->
                  BmcM.update_sym_table old_sym_table >>= fun () ->
                  BmcM.update_memory_table old_memory >>= fun () ->
                  return (let_binding, mem, res_case_expr)
                ) caselist >>= fun res_caselist ->
      let reslist = List.map (fun (_, _, a) -> a) res_caselist in
      (* Update memory *)
      (if !!bmc_conf.concurrent_mode then
         let preexecs = List.map2 guard_preexec case_guards
                                  (List.map eget_preexec reslist) in
         return (AddrSet.empty, combine_preexecs preexecs)
       else
         let mod_addr = List.fold_right(fun res acc ->
           AddrSet.union acc res.mod_addr) reslist AddrSet.empty in
         let new_memory =
           BmcM.merge_memory old_memory mod_addr
                             (List.map (fun (_,m,_) -> m) res_caselist)
                             case_guards in
         BmcM.update_memory_table new_memory >>= fun () ->
         return (mod_addr, mk_initial_preexec)
      ) >>= fun (mod_addr, preexec) ->

      let guarded_bindings = List.map2 (
        fun guard (binding, _, _) -> mk_implies guard binding)
        case_guards res_caselist in
      let case_assumes = List.concat (List.map eget_assume reslist) in
      let guarded_vcs = List.map2 (
        fun guard res -> mk_implies guard (mk_and (eget_vcs res)))
        case_guards reslist in
      let ite_expr = mk_guarded_ite (List.map eget_expr reslist) case_guards in
      let assume = res_pe.assume @ guarded_bindings @ case_assumes in
      let drop_cont = mk_or
        (List.map2 (fun guard res -> mk_and [guard; res.drop_cont])
                   case_guards reslist) in
      let ret_cond_list =
        List.map2 mk_implies case_guards (List.map eget_ret reslist) in

      return { expr      = ite_expr
             ; assume    = assume
             ; vcs       = match_vc :: (res_pe.vcs @ guarded_vcs)
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and ret_cond_list
             ; preexec   = preexec
             }
  | Eskip ->
      return { expr      = UnitSort.mk_unit
             ; assume    = []
             ; vcs       = []
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             ; preexec   = mk_initial_preexec
             }
  | Eproc _ ->
      assert false
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)),
                        PEval(Vobject (OVcfunction (Sym sym)))), arglist)
    (* fall through *)
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)),
                        PEsym sym), arglist) ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.get_file       >>= fun file ->
      assert (Expr.get_num_args sym_expr = 1);
      let sym_id = z3num_to_int (List.hd (Expr.get_args sym_expr)) in
      let func_sym = Sym.Symbol(sym_id, None) in
      BmcM.lookup_run_depth (Sym func_sym) >>= fun depth ->
      begin match Pmap.lookup func_sym file.funs with
      | Some (Proc(_, fun_ty, fun_args, fun_expr)) ->
        if depth >= !!bmc_conf.max_run_depth then
          return { expr      = mk_fresh_const "call_depth_exceeded"
                                              (cbt_to_z3 fun_ty)
                 ; assume    = []
                 ; vcs       = [ mk_false ]
                 ; drop_cont = mk_false
                 ; mod_addr  = AddrSet.empty
                 ; ret_cond  = mk_true
                 ; preexec   = mk_initial_preexec
                 }
        else begin
          BmcM.mapM bmc_pexpr arglist >>= fun arg_retlist ->
          let sub_map = List.fold_right2
            ( fun (sym, _) pe table -> Pmap.add sym pe table)
            fun_args arglist (Pmap.empty sym_cmp) in
          let expr_to_check = substitute_expr sub_map fun_expr in
          let new_ret_const =
            mk_fresh_const (sprintf "ret_%d" sym_id) (cbt_to_z3 fun_ty) in
          BmcM.get_proc_expr                      >>= fun old_proc_expr ->
          BmcM.get_ret_const                      >>= fun old_ret_const ->
          BmcM.get_sym_table                      >>= fun old_sym_table ->
          BmcM.update_proc_expr expr_to_check     >>= fun () ->
          BmcM.update_ret_const new_ret_const     >>= fun () ->
          BmcM.increment_run_depth (Sym func_sym) >>= fun () ->
          bmc_expr expr_to_check                  >>= fun ret_call ->
          BmcM.update_ret_const old_ret_const     >>= fun () ->
          BmcM.update_proc_expr old_proc_expr     >>= fun () ->
          BmcM.update_sym_table old_sym_table     >>= fun () ->
          BmcM.decrement_run_depth (Sym func_sym) >>= fun () ->

          let proc_ret_cond =
            mk_and [mk_implies (mk_not ret_call.drop_cont)
                               (mk_eq new_ret_const ret_call.expr)
                   ; ret_call.ret_cond] in

          return { expr      = new_ret_const
                 ; assume    = proc_ret_cond
                               ::ret_call.assume
                               @(List.concat (List.map pget_assume arg_retlist))
                 ; vcs       = ret_call.vcs
                               @(List.concat (List.map pget_vcs arg_retlist))
                 ; drop_cont = mk_false
                 ; mod_addr  = ret_call.mod_addr
                 ; ret_cond  = mk_true
                 ; preexec   = ret_call.preexec
                 }
        end
      | Some (ProcDecl(_, ty, params)) ->
          bmc_debug_print 2
            (sprintf "TODO: ProcDecl %s treated as nondet, 'random' function\n"
                     (symbol_to_string func_sym));
          BmcM.get_ail_opt >>= fun ail_opt ->
          assert (is_some ail_opt);
          let (_, sigma) = Option.get ail_opt in
          let (id, (_,decl)) = List.find (fun (id, decl) ->
            sym_cmp id func_sym = 0) sigma.declarations in
          let ctype = match decl with
            | Decl_function (_,(_,ctype),_,_,_,_) -> ctype
            | _ -> assert false in
          let (nondet_const,assumptions) =
             mk_initial_loaded_value
                (cbt_to_z3 ty)
                (sprintf "procDecl:%s" (symbol_to_string func_sym))
                (ailctype_to_ctype ctype)
                true in
          return { expr      = nondet_const
                 ; assume    = assumptions
                 ; vcs       = []
                 ; drop_cont = mk_false
                 ; mod_addr  = AddrSet.empty
                 ; ret_cond  = mk_true
                 ; preexec   = mk_initial_preexec
                 }
      | _ -> assert false
      end
  | Eccall _ -> assert false
  | Eunseq elist ->
      assert (not !!bmc_conf.sequentialise);
      assert (!!bmc_conf.concurrent_mode);
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.mapM (fun expr ->
        bmc_expr expr                       >>= fun res_expr ->
        BmcM.update_sym_table old_sym_table >>= fun () ->
        return res_expr
      ) elist >>= fun res_elist ->

      return { expr      = ctor_to_z3 Ctuple (List.map eget_expr res_elist) None
             ; assume    = List.concat (List.map eget_assume res_elist)
             ; vcs       = List.concat (List.map eget_vcs res_elist)
             ; drop_cont = mk_or (List.map eget_cont res_elist)
             ; mod_addr  = AddrSet.empty (* Sequential mode only *)
             ; ret_cond  = mk_or (List.map eget_ret res_elist)
             ; preexec   = combine_preexecs (List.map eget_preexec res_elist)
             }
  | Eindet _ -> assert false
  | Ebound (n, e1) ->
      (* TODO: Ebound currently ignored
       * assert n=0 only because have not worked with C where n!=0
       *)
      assert (n = 0);
      bmc_expr e1
  | End elist ->
      assert (List.length elist > 1);
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.get_memory    >>= fun old_memory ->
      BmcM.mapM (fun expr ->
        bmc_expr expr                       >>= fun res_expr ->
        BmcM.get_memory                     >>= fun mem ->
        BmcM.update_sym_table old_sym_table >>= fun () ->
        BmcM.update_memory_table old_memory >>= fun () ->
        return (mem, res_expr)
      ) elist >>= fun res_elist ->

      let bmc_rets = List.map snd res_elist in
      let choice_vars = List.mapi (
        fun i _ -> mk_fresh_const ("seq_" ^ (string_of_int i))
                                  boolean_sort) elist in
      (* memory *)
      (if !!bmc_conf.concurrent_mode then
        let preexecs = List.map2 guard_preexec
                                 choice_vars (List.map eget_preexec bmc_rets) in
        return (AddrSet.empty, combine_preexecs preexecs)
       else
         let mod_addr = List.fold_right (
           fun res acc -> AddrSet.union acc res.mod_addr)
           bmc_rets AddrSet.empty in
         let new_memory = BmcM.merge_memory old_memory mod_addr
                                            (List.map fst res_elist)
                                            choice_vars in
         BmcM.update_memory_table new_memory >>= fun () ->
         return (mod_addr, mk_initial_preexec)
      ) >>= fun (mod_addr, preexec) ->

      (* Assert exactly one choice is taken *)
      let xor_expr = List.fold_left mk_xor mk_false choice_vars in
      let vcs = List.map2
          (fun choice res -> mk_implies choice (mk_and (eget_vcs res)))
          choice_vars bmc_rets in
      let drop_cont = mk_or (List.map2
          (fun choice res -> mk_and [choice; res.drop_cont])
          choice_vars bmc_rets) in
      let ret_expr = List.fold_left2
          (fun acc choice res -> mk_ite choice (eget_expr res) acc)
          (eget_expr (List.hd bmc_rets))
          (List.tl choice_vars)
          (List.tl bmc_rets) in
      return { expr      = ret_expr
             ; assume    = xor_expr
                           :: (List.concat (List.map eget_assume bmc_rets))
             ; vcs       = vcs
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and (List.map eget_ret bmc_rets)
             ; preexec   = preexec
             }
  | Erun (_, label, pelist) ->
      BmcM.lookup_run_depth (Sym label) >>= fun depth ->
      if depth >= !!bmc_conf.max_run_depth then
        (* TODO: flag as special vc? *)
        return { expr      = UnitSort.mk_unit
               ; assume    = []
               ; vcs       = [mk_false]
               ; drop_cont = mk_true
               ; mod_addr  = AddrSet.empty
               ; ret_cond  = mk_true
               ; preexec   = mk_initial_preexec
               }
      else begin
        BmcM.get_proc_expr >>= fun proc_expr ->
        let (cont_syms, cont_expr) = Option.get (find_labeled_continuation
                          Sym.instance_Basic_classes_Eq_Symbol_sym_dict
                          label proc_expr) in
        assert (List.length pelist = List.length cont_syms);
        (* TODO: rename symbols in continuation? *)
        let sub_map = List.fold_right2 (fun sym pe map -> Pmap.add sym pe map)
                                       cont_syms pelist (Pmap.empty sym_cmp) in
        let cont_to_check = substitute_expr sub_map cont_expr in

        BmcM.increment_run_depth (Sym label) >>= fun () ->
        bmc_expr cont_to_check               >>= fun run_res ->
        BmcM.decrement_run_depth (Sym label) >>= fun () ->
        BmcM.get_ret_const                   >>= fun ret_const ->
        return { expr      = UnitSort.mk_unit
               ; assume    = run_res.assume
               ; vcs       = run_res.vcs
               ; drop_cont = mk_true
               ; mod_addr  = run_res.mod_addr
               ; ret_cond  = mk_and [mk_implies (mk_not run_res.drop_cont)
                                                (mk_eq ret_const run_res.expr)
                                    ; run_res.ret_cond]
               ; preexec   = run_res.preexec
               }
      end
  | Epar elist ->
      assert (!!bmc_conf.concurrent_mode);
      assert (not g_single_threaded);
      BmcM.get_tid       >>= fun old_tid ->
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.mapM (fun expr ->
        BmcM.get_fresh_tid                  >>= fun tid ->
        BmcM.put_tid tid                    >>= fun () ->
        bmc_expr expr                       >>= fun res_expr ->
        BmcM.update_sym_table old_sym_table >>= fun () ->
        BmcM.add_parent_tid tid old_tid     >>= fun () ->
        return res_expr
      ) elist >>= fun res_elist ->
      BmcM.put_tid old_tid                  >>= fun () ->

      let expr =
        let exprlist = List.map eget_expr res_elist in
        ctor_to_z3 Ctuple exprlist None in

      return { expr      = expr
             ; assume    = List.concat (List.map eget_assume res_elist)
             ; vcs       = List.concat (List.map eget_vcs res_elist)
             ; drop_cont = mk_false      (* TODO: Erun within Epar? *)
             ; mod_addr  = AddrSet.empty (* sequential mode only *)
                           (* TODO: hack above to check this *)
             ; ret_cond  = mk_or (List.map eget_ret res_elist)
             ; preexec   = combine_preexecs (List.map eget_preexec res_elist)
        }
  | Ewait _ ->
      assert false
  | Eif (pe, e1, e2) ->
      bmc_pexpr pe                        >>= fun res_pe ->
      BmcM.get_sym_table                  >>= fun old_sym_table ->
      BmcM.get_memory                     >>= fun old_memory ->
      bmc_expr e1                         >>= fun res_e1 ->
      BmcM.get_memory                     >>= fun mem_e1 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->
      BmcM.update_memory_table old_memory >>= fun () ->
      bmc_expr e2                         >>= fun res_e2 ->
      BmcM.get_memory                     >>= fun mem_e2 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->

      let (guard1, guard2) = (res_pe.expr, mk_not res_pe.expr) in

      (* memory *)
      (if !!bmc_conf.concurrent_mode then
         let preexecs = combine_preexecs
             [ guard_preexec guard1 res_e1.preexec
             ; guard_preexec guard2 res_e2.preexec ] in
         return (AddrSet.empty, preexecs)
       else
         let mod_addr = AddrSet.union res_e1.mod_addr res_e2.mod_addr in
         let new_memory = BmcM.merge_memory old_memory mod_addr
                                           [mem_e1; mem_e2] [guard1; guard2] in
         BmcM.update_memory_table new_memory >>= fun () ->
         return (mod_addr, mk_initial_preexec)
      ) >>= fun (mod_addr, preexec) ->

      let vcs = res_pe.vcs
              @ (List.map (fun vc -> mk_implies guard1 vc) res_e1.vcs)
              @ (List.map (fun vc -> mk_implies guard2 vc) res_e2.vcs) in
      let drop_cont = mk_or [ mk_and [guard1; res_e1.drop_cont]
                            ; mk_and [guard2; res_e2.drop_cont]
                            ] in
      return { expr      = mk_ite guard1 res_e1.expr res_e2.expr
             ; assume    = res_pe.assume @ res_e1.assume @ res_e2.assume
             ; vcs       = vcs
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and [ mk_implies guard1 res_e1.ret_cond
                                  ; mk_implies guard2 res_e2.ret_cond
                                  ]
             ; preexec   = preexec
             }
  | Elet _
  | Easeq _ ->
      assert false
  | Ewseq (pat, e1, e2) (* TODO: fall through for now *)
  | Esseq (pat, e1, e2) ->
      bmc_expr e1                   >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_expr e2                   >>= fun res2 ->

      let e2_guard = mk_not res1.drop_cont in

      (if !!bmc_conf.concurrent_mode then
         BmcM.get_parent_tids >>= fun parent_tids ->
         let (p1, p2) = (res1.preexec, guard_preexec e2_guard res2.preexec) in
         let preexec = combine_preexecs [p1;p2] in
         let to_sequence =
           match expr_ with
           | Ewseq _ -> List.filter is_pos_action p1.actions
           | Esseq _ -> p1.actions
           | _       -> assert false in
         let sb = (compute_sb to_sequence p2.actions) @ preexec.sb in
         let asw = (compute_asw p1.actions p2.actions p1.sb p2.sb parent_tids)
                  @ preexec.asw in
         return (AddrSet.empty, {preexec with sb = sb; asw = asw})
       else return (AddrSet.union res1.mod_addr res2.mod_addr,
                    mk_initial_preexec)
      ) >>= fun (mod_addr, preexec) ->

      (* TODO: do we care about properly maintaining the memory table ?*)
      return { expr      = res2.expr
             ; assume    = let_binding::(res1.assume @ res2.assume)
             ; vcs       = (mk_or [ res1.drop_cont; mk_and res2.vcs ])
                           :: res1.vcs
             ; drop_cont = mk_or [res1.drop_cont; res2.drop_cont]
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and [ res1.ret_cond
                                  ; mk_implies e2_guard res2.ret_cond
                                  ]
             ; preexec   = preexec
             }
  | Esave (_, varlist, e) ->
        let sub_map = List.fold_right (fun (sym, (cbt, pe)) map ->
          Pmap.add sym pe map) varlist (Pmap.empty sym_cmp) in
        let to_check = substitute_expr sub_map e in
        bmc_expr to_check

(* Assume, Vcs *)
let bmc_globals globals : bmc_gret BmcM.eff =
  BmcM.mapM (
    fun (sym, cbt, expr) ->
      bmc_expr expr                                      >>= fun ret_expr ->
      add_pattern_to_sym_table (CaseBase(Some sym, cbt)) >>= fun () ->
      mk_let_binding (Some sym) ret_expr.expr            >>= fun binding ->
      return { assume  = binding::ret_expr.assume
             ; vcs     = ret_expr.vcs
             ; preexec = ret_expr.preexec
             }
    ) globals >>= fun ret_globals ->
  return (merge_grets ret_globals)

let initialise_solver (solver: Solver.solver) =
  bmc_debug_print 1 "Initialising solver.";
  Solver.add solver ImplFunctions.all_asserts;
  let params = Params.mk_params g_ctx in
  Params.add_bool params (mk_sym "macro_finder") g_macro_finder;
  Solver.set_parameters solver params

let initialise_param ((sym, cbt) as param: (sym_ty * core_base_type))
                     ((_,ctype,_): qualifiers * AilTypes.ctype * bool) =
  if (not (is_core_ptr_bty cbt)) then
    initialise_simple_param param >>= fun () ->
      return {assume = []; vcs = []; preexec = mk_initial_preexec}
  else begin
    (* TODO: duplicates Create *)
    BmcM.get_file >>= fun file ->
    (* Core pointer: look up Ail type, create an initial value.
     * Initialized to not be unspecified *)
    let sortlist = ctype_to_bmcz3sort (ailctype_to_ctype ctype) file in
    let flat_sortlist = flatten_bmcz3sort sortlist in
    let allocation_size = bmcz3sort_size sortlist in
    BmcM.get_new_alloc_and_update_supply >>= fun alloc_id ->
    let to_run =
        if !!bmc_conf.concurrent_mode
        then Bmc_paction.do_concurrent_create alloc_id flat_sortlist Pos true
        else Bmc_paction.do_sequential_create alloc_id flat_sortlist true in
    to_run >>= fun result ->

    let alloc_size_expr =
      mk_eq (Expr.mk_app g_ctx AddressSort.alloc_size_decl
                               [int_to_z3 alloc_id])
             (int_to_z3 allocation_size) in
    add_sym_to_sym_table sym cbt >>= fun () ->
    BmcM.lookup_sym sym >>= fun expr ->
    let eq_expr =
      mk_eq expr (PointerSort.mk_ptr (AddressSort.mk_from_addr (alloc_id, 0))) in

    return { assume  = eq_expr::(alloc_size_expr::result.assume)
           ; vcs     = result.vcs
           ; preexec = result.preexec
           }
  end

let initialise_params
        (params: (sym_ty * core_base_type) list)
        (function_to_check: sym_ty) =
  BmcM.get_ail_opt >>= fun ail_opt ->
  match ail_opt with
  | Some (_, sigma) ->
      let (id, (_,decl)) = List.find (fun (id, decl) ->
        sym_cmp id function_to_check = 0) sigma.declarations in
      begin match decl with
      | Decl_function (_, _, args, _, _, _) ->
          assert (List.length args = List.length params);
          BmcM.mapM2 initialise_param params args >>= fun retlist ->
          return (merge_grets retlist)
      | _ -> assert false
      end
  | None -> (assert (List.length params = 0);
             BmcM.return initial_gret)

let bmc_file (file              : unit typed_file)
             (sym_supply        : sym_supply_ty)
             (function_to_check : sym_ty)
             (ail_opt: GenTypes.genTypeCategory AilSyntax.ail_program option) =
  (* Create an initial model checking state *)
  let initial_state : BmcM.bmc_state =
    BmcM.mk_initial_state file sym_supply ail_opt in
  initialise_solver g_solver;

  let to_run =
    bmc_globals file.globs >>= fun gret ->
    match Pmap.lookup function_to_check file.funs with
    | Some (Proc (_, ty, params, e)) ->
        initialise_params params function_to_check >>= fun pret ->
        let ret_const = mk_fresh_const "ret_fn" (cbt_to_z3 ty) in
        BmcM.update_proc_expr e         >>= fun () ->
        BmcM.update_ret_const ret_const >>= fun () ->
        bmc_expr e                      >>= fun ret ->
        BmcM.get_parent_tids            >>= fun parent_tids ->
        let new_ret_cond =
          mk_implies (mk_not ret.drop_cont) (mk_eq ret_const ret.expr) in
        bmc_debug_print 3
          "TODO: compute SB of globals and proc arguments properly";
        let preexec =
          let combined =
            combine_preexecs [gret.preexec; pret.preexec; ret.preexec] in
          let sb = (compute_sb_nofilter gret.preexec.actions
                                        ret.preexec.actions)
                 @ (compute_sb_nofilter pret.preexec.actions
                                        ret.preexec.actions)
                 @ combined.sb in
          let filtered_asw = filter_asw combined.asw sb in
          {combined with sb = sb; asw = filtered_asw} in
        return {ret with ret_cond = mk_and [new_ret_cond; ret.ret_cond]
                       ; assume   = gret.assume @ pret.assume @ ret.assume
                       ; vcs      = gret.vcs    @ pret.vcs    @ ret.vcs
                       ; preexec  = preexec
               }
    | Some (Fun (ty, params, pe)) ->
        BmcM.mapM_ initialise_simple_param params >>= fun () ->
        bmc_pexpr pe >>= fun pret ->
        let ret = bmc_pret_to_ret pret in
        return {ret with assume  = gret.assume @ ret.assume
                       ; vcs     = gret.vcs    @ ret.vcs
                       ; preexec = gret.preexec (* Pure Fun *)
               }
    | _ -> failwith "Function to check must be a Core Proc or Fun"
  in
  let (result, new_state) = BmcM.run initial_state to_run in

  (*print_endline "==== FINAL BMC_RET";*)
  (*print_string (pp_bmc_ret result);*)

  (* TODO: assert and track based on annotation *)
  (* TODO: multiple expressions or one expression? *)

  bmc_debug_print 1 "==== DONE BMC_EXPR ROUTINE ";
  (* Assumptions *)
  Solver.add g_solver (List.map (fun e -> Expr.simplify e None) result.assume);
  (*
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_and result.assume) None)
    (Expr.mk_fresh_const g_ctx "assume" boolean_sort);
    *)
  (* Return conditions *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify result.ret_cond None)
    (Expr.mk_fresh_const g_ctx "ret_cond" boolean_sort);

  let final_expr = match new_state.ret_const with
                   | Some expr -> expr
                   | None      -> result.expr in

  (if !!bmc_conf.concurrent_mode && (List.length result.preexec.actions > 0)
    then begin
    let model = BmcMem.compute_executions result.preexec in
    bmc_debug_print 2 "==== PREEXECS ";
    bmc_debug_print 2 (pp_preexec result.preexec);
    BmcMem.add_assertions g_solver model;
    (* Do an initial check *)
    bmc_debug_print 1 "START FIRST CHECK";
    begin match Solver.check g_solver [] with
      | SATISFIABLE -> ()
      | UNSATISFIABLE -> print_endline (Solver.to_string g_solver); assert false
      | _ -> assert false
    end;
    if Solver.check g_solver [] <> SATISFIABLE then assert false;
    bmc_debug_print 1 "DONE FIRST CHECK";
    BmcMem.extract_executions g_solver model final_expr
  end else
    match Solver.check g_solver [] with
    | SATISFIABLE ->
        let model = Option.get (Solver.get_model g_solver) in
        let return_value = Option.get (Model.eval model final_expr false) in
        bmc_debug_print 1 (sprintf "==== RETURN VALUE: %s\n"
                                   (Expr.to_string return_value))
    | _ -> assert false)
  ;

  (* VCs *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_not (mk_and result.vcs)) None)
    (Expr.mk_fresh_const g_ctx "negated_vcs" boolean_sort);

  (*
  print_endline "====FINAL SOLVER";
  print_endline (Solver.to_string g_solver);
  *)

  bmc_debug_print 1 "==== CHECKING";
  match Solver.check g_solver [] with
  | UNKNOWN ->
      printf "STATUS: unknown. Reason: %s\n"
             (Solver.get_reason_unknown g_solver)
  | UNSATISFIABLE ->
      print_endline "STATUS: unsatisfiable :)"
  | SATISFIABLE ->
      begin
      print_endline "STATUS: satisfiable";
      let model = Option.get (Solver.get_model g_solver) in
      bmc_debug_print 1 (Model.to_string model)
      end

let find_function (f_name: string)
                  (fun_map: unit typed_fun_map) =
  let is_f_name = (fun (sym, decl) ->
      match sym with
      | Sym.Symbol(i, Some s) -> String.equal s f_name
      | _ -> false
    ) in
  match (List.find_opt is_f_name (Pmap.bindings_list fun_map)) with
  | Some (sym, _) -> sym
  | None -> failwith ("ERROR: file does not have the function " ^ f_name)

(* Main bmc function: typechecks and sequentialises file.
 * The symbol supply is used to ensure fresh symbols when renaming.
 *)
let bmc (core_file  : unit file)
        (sym_supply : sym_supply_ty)
        (ail_opt    : GenTypes.genTypeCategory AilSyntax.ail_program option)=
  match Core_typing.typecheck_program core_file with
    | Result typed_core ->
        begin
          let core_to_check =
            if !!bmc_conf.sequentialise then
              Core_sequentialise.sequentialise_file typed_core
            else
              typed_core in

          pp_file core_to_check;
          bmc_debug_print 1 "START: model checking";

          let fn_sym = find_function !!bmc_conf.fn_to_check
                                     core_to_check.funs in
          bmc_file core_to_check sym_supply fn_sym ail_opt
        end
    | Exception msg ->
        printf "Typechecking error: %s\n" (Pp_errors.to_string msg)
