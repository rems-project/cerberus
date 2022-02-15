module CF = Cerb_frontend
open CF.Mucore
open Retype.New

module SymSet = Set.Make(Sym)



let union_map (f : 'a -> SymSet.t) (xs : 'a list) =
  List.fold_left (fun acc x ->
      SymSet.union (f x) acc
    ) SymSet.empty xs


let big_union sets =
  union_map (fun s -> s)


let rec bound_by_pattern (M_Pattern (_, _, pat_)) = 
  match pat_ with
  | M_CaseBase (None, _) -> SymSet.empty
  | M_CaseBase (Some s, _) -> SymSet.singleton s
  | M_CaseCtor (_, patterns) -> union_map bound_by_pattern patterns



let bound_by_sym_or_pattern = function
  | M_Symbol s -> SymSet.singleton s
  | M_Pat pattern -> bound_by_pattern pattern


let free_in_asym ({sym; _}: 'TY asym) = 
  SymSet.singleton sym

let free_in_generic_name = function
  | CF.Core.Sym s -> SymSet.singleton s
  | CF.Core.Impl _ic -> SymSet.empty

let free_in_pexpr (M_Pexpr (_, _, _, pexpr_)) : SymSet.t = 
  match pexpr_ with
  | M_PEsym s -> SymSet.singleton s
  | M_PEimpl _ -> SymSet.empty
  | M_PEval _ -> SymSet.empty
  | M_PEconstrained constrained_asym_list ->
     union_map (fun (_, asym) -> free_in_asym asym) constrained_asym_list
  | M_PEerror (_err, asym) -> free_in_asym asym
  | M_PEctor (_ctor, asyms) -> union_map free_in_asym asyms
  | M_CivCOMPL (_act, asym) -> free_in_asym asym
  | M_CivAND (_act, asym1, asym2) -> union_map free_in_asym [asym1;asym2]
  | M_CivOR (_act, asym1, asym2) -> union_map free_in_asym [asym1;asym2]
  | M_CivXOR (_act, asym1, asym2) -> union_map free_in_asym [asym1;asym2]
  | M_Cfvfromint asym -> free_in_asym asym
  | M_Civfromfloat (_act, asym) -> free_in_asym asym
  | M_PEarray_shift (asym1, _ct, asym2) -> union_map free_in_asym [asym1; asym2] 
  | M_PEmember_shift (asym, _sym, _id) -> free_in_asym asym
  | M_PEnot asym -> free_in_asym asym
  | M_PEop (_op, asym1, asym2) -> union_map free_in_asym [asym1; asym2]
  | M_PEstruct (_tag, members) -> union_map (fun (_, asym) -> free_in_asym asym) members
  | M_PEunion (_tag, id, asym) -> free_in_asym asym
  | M_PEmemberof (_sym, _kd, asym) -> free_in_asym asym
  | M_PEcall (name, asyms) -> 
     SymSet.union (union_map free_in_asym asyms)
       (free_in_generic_name name)
  | M_PEassert_undef (asym, _loc, _ub) ->
     free_in_asym asym
  | M_PEbool_to_integer asym -> free_in_asym asym
  | M_PEconv_int (_act, asym) -> free_in_asym asym
  | M_PEwrapI (_act, asym) -> free_in_asym asym


let rec free_in_tpexpr (M_TPexpr (_, _, _, mu_tpexpr_)) = 
  match mu_tpexpr_ with
  | M_PEundef (_loc, _ub) -> SymSet.empty
  | M_PEcase (asym, cases) -> 
     SymSet.union 
       (free_in_asym asym)
       (union_map (fun (pattern, mu_tpexpr) ->
            SymSet.diff (free_in_tpexpr mu_tpexpr)
              (bound_by_pattern pattern)
          ) cases)
  | M_PElet (sym_or_pattern, mu_pexpr, mu_tpexpr) ->
     SymSet.union 
       (free_in_pexpr mu_pexpr)
       (SymSet.diff 
          (free_in_tpexpr mu_tpexpr)
          (bound_by_sym_or_pattern sym_or_pattern)
       )
  | M_PEif (asym, mu_tpexpr1, mu_tpexpr2) ->
     SymSet.union (free_in_asym asym)
       (union_map free_in_tpexpr [mu_tpexpr1; mu_tpexpr2])
  | M_PEdone asym -> 
     free_in_asym asym



let free_in_action (M_Action (_, action_)) = 
  match action_ with
   | M_Create (asym, _act, _prefix) -> free_in_asym asym
   | M_CreateReadOnly (asym1, _act, asym2, _prefix) -> union_map free_in_asym [asym1; asym2]
   | M_Alloc (asym1, asym2, _prefix) -> union_map free_in_asym [asym1; asym2]
   | M_Kill (_kill_kind, asym) -> free_in_asym asym
   | M_Store (_b, _act, asym1, asym2, _order) -> union_map free_in_asym [asym1; asym2]
   | M_Load (_act, asym, _order) -> free_in_asym asym
   | M_RMW (_act, asym1, asym2, asym3, _order1, _order2) -> union_map free_in_asym [asym1; asym2; asym3]
   | M_Fence _order -> SymSet.empty
   | M_CompareExchangeStrong (_act, asym1, asym2, asym3, _order1, _order2) -> union_map free_in_asym [asym1; asym2; asym3]
   | M_CompareExchangeWeak (_act, asym1, asym2, asym3, _order1, order2) -> union_map free_in_asym [asym1; asym2; asym3]
   | M_LinuxFence _order -> SymSet.empty
   | M_LinuxLoad (_act, asym, _order) -> free_in_asym asym
   | M_LinuxStore (_act, asym1, asym2, _order) -> union_map free_in_asym [asym1; asym2]
   | M_LinuxRMW  (_act, asym1, asym2, _order) -> union_map free_in_asym [asym1; asym2]

let free_in_paction = function
  | M_Paction (_polarity, action) -> free_in_action action

let free_in_memop memop = 
  union_map free_in_asym
    begin match memop with
    | M_PtrEq (asym1, asym2) -> [asym1; asym2]
    | M_PtrNe (asym1, asym2) -> [asym1; asym2]
    | M_PtrLt (asym1, asym2) -> [asym1; asym2]
    | M_PtrGt (asym1, asym2) -> [asym1; asym2]
    | M_PtrLe (asym1, asym2) -> [asym1; asym2]
    | M_PtrGe (asym1, asym2) -> [asym1; asym2]
    | M_Ptrdiff (_act, asym1, asym2) -> [asym1; asym2]
    | M_IntFromPtr (_act1, _act2, asym) -> [asym]
    | M_PtrFromInt (_act1, _act2, asym) -> [asym]
    | M_PtrValidForDeref (_act, asym) -> [asym]
    | M_PtrWellAligned (_act, asym) -> [asym]
    | M_PtrArrayShift (asym1, _act, asym2) -> [asym1; asym2]
    | M_Memcpy (asym1, asym2, asym3) -> [asym1; asym2; asym3]
    | M_Memcmp (asym1, asym2, asym3) -> [asym1; asym2; asym3]
    | M_Realloc (asym1, asym2, asym3) -> [asym1; asym2; asym3]
    | M_Va_start (asym1, asym2) -> [asym1; asym2]
    | M_Va_copy asym -> [asym]
    | M_Va_arg (asym, _act) -> [asym]
    | M_Va_end asym -> [asym]
    end


let free_in_expr (M_Expr (_, _, expr_)) =
  match expr_ with
  | M_Epure pexpr -> free_in_pexpr pexpr
  | M_Ememop op -> free_in_memop op
  | M_Eaction paction -> free_in_paction paction
  | M_Eskip -> SymSet.empty
  | M_Eccall (_act, fsym, asyms) -> union_map free_in_asym (fsym :: asyms)
  | M_Eproc (name, asyms) -> SymSet.union (free_in_generic_name name) (union_map free_in_asym asyms)
  | M_Erpredicate (_packunpack, _tpu, asyms) -> union_map free_in_asym asyms 
  | M_Elpredicate (_haveshow, _id, asyms) -> union_map free_in_asym asyms


let rec free_in_texpr (M_TExpr (_, _, texpr_)) = 
  match texpr_ with
  | M_Elet (sym_or_pattern, pexpr, texpr) -> 
     SymSet.union (free_in_pexpr pexpr) 
       (SymSet.diff (free_in_texpr texpr) (bound_by_sym_or_pattern sym_or_pattern))
  | M_Ewseq (pattern, expr, texpr) ->
     SymSet.union (free_in_expr expr) 
       (SymSet.diff (free_in_texpr texpr) (bound_by_pattern pattern))
  | M_Esseq (sym_or_pattern, expr, texpr) -> 
     SymSet.union (free_in_expr expr) 
       (SymSet.diff (free_in_texpr texpr) (bound_by_sym_or_pattern sym_or_pattern))
  | M_Ecase (asym, cases) ->
     SymSet.union (free_in_asym asym)
       (union_map (fun (pattern, texpr) ->
            SymSet.diff (free_in_texpr texpr) (bound_by_pattern pattern)
          ) cases)
  | M_Eif (asym, texpr1, texpr2) ->
     SymSet.union (free_in_asym asym)
       (union_map free_in_texpr [texpr1; texpr2])
  | M_Ebound (_n, texpr) -> free_in_texpr texpr
  | M_End texprs -> union_map free_in_texpr texprs
  | M_Edone asym -> free_in_asym asym
  | M_Eundef (_loc, _ub) -> SymSet.empty
  | M_Erun (label_sym, asyms) -> union_map free_in_asym asyms
