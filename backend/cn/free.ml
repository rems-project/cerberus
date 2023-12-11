module CF = Cerb_frontend
open Mucore

module SymSet = Set.Make(Sym)



let union_map (f : 'a -> SymSet.t) (xs : 'a list) =
  List.fold_left (fun acc x ->
      SymSet.union (f x) acc
    ) SymSet.empty xs


let big_union sets =
  union_map (fun s -> s)


let rec bound_by_pattern (M_Pattern (_, _, _, pat_)) =
  match pat_ with
  | M_CaseBase (None, _) -> SymSet.empty
  | M_CaseBase (Some s, _) -> SymSet.singleton s
  | M_CaseCtor (_, patterns) -> union_map bound_by_pattern patterns




let free_in_generic_name = function
  | CF.Core.Sym s -> SymSet.singleton s
  | CF.Core.Impl _ic -> SymSet.empty

let rec free_in_pexpr (M_Pexpr (_, _, _, pexpr_)) : SymSet.t =
  match pexpr_ with
  | M_PEsym s -> SymSet.singleton s
  | M_PEval _ -> SymSet.empty
  | M_PEconstrained constrained_pe_list ->
     union_map (fun (_, pe) -> free_in_pexpr pe) constrained_pe_list
  | M_PEerror (_err, pe) -> free_in_pexpr pe
  | M_PEctor (_ctor, pes) -> union_map free_in_pexpr pes
  | M_PEbitwise_unop (_uop, pe) -> free_in_pexpr pe
  | M_PEbitwise_binop (_bop, pe1, pe2) -> union_map free_in_pexpr [pe1; pe2]
  | M_Cfvfromint pe -> free_in_pexpr pe
  | M_Civfromfloat (_act, pe) -> free_in_pexpr pe
  | M_PEarray_shift (pe1, _ct, pe2) -> union_map free_in_pexpr [pe1; pe2]
  | M_PEmember_shift (pe, _sym, _id) -> free_in_pexpr pe
  | M_PEnot pe -> free_in_pexpr pe
  | M_PEop (_op, pe1, pe2) -> union_map free_in_pexpr [pe1; pe2]
  | M_PEbounded_binop (_bk, _op, pe1, pe2) -> union_map free_in_pexpr [pe1; pe2]
  | M_PEapply_fun (_f, pes) -> union_map free_in_pexpr pes
  | M_PEstruct (_tag, members) -> union_map (fun (_, pe) -> free_in_pexpr pe) members
  | M_PEunion (_tag, id, pe) -> free_in_pexpr pe
  | M_PEmemberof (_sym, _kd, pe) -> free_in_pexpr pe
  | M_PEbool_to_integer pe -> free_in_pexpr pe
  | M_PEconv_int (_act, pe) -> free_in_pexpr pe
  | M_PEconv_loaded_int (_act, pe) -> free_in_pexpr pe
  | M_PEcatch_exceptional_condition (_act, pe) -> free_in_pexpr pe
  | M_PEis_representable_integer (pe, _act) -> free_in_pexpr pe
  | M_PEwrapI (_act, pe) -> free_in_pexpr pe
  | M_PEundef (_loc, _ub) -> SymSet.empty
  | M_PEcfunction pe -> free_in_pexpr pe
  | M_PElet (pattern, pe1, pe2) ->
     SymSet.union
       (free_in_pexpr pe1)
       (SymSet.diff
          (free_in_pexpr pe2)
          (bound_by_pattern pattern)
       )
  | M_PEif (pe, mu_pexpr1, mu_pexpr2) ->
     SymSet.union (free_in_pexpr pe)
       (union_map free_in_pexpr [mu_pexpr1; mu_pexpr2])



let free_in_action (M_Action (_, action_)) =
  match action_ with
   | M_Create (pe, _act, _prefix) -> free_in_pexpr pe
   | M_CreateReadOnly (pe1, _act, pe2, _prefix) -> union_map free_in_pexpr [pe1; pe2]
   | M_Alloc (pe1, pe2, _prefix) -> union_map free_in_pexpr [pe1; pe2]
   | M_Kill (_kill_kind, pe) -> free_in_pexpr pe
   | M_Store (_b, _act, pe1, pe2, _order) -> union_map free_in_pexpr [pe1; pe2]
   | M_Load (_act, pe, _order) -> free_in_pexpr pe
   | M_RMW (_act, pe1, pe2, pe3, _order1, _order2) -> union_map free_in_pexpr [pe1; pe2; pe3]
   | M_Fence _order -> SymSet.empty
   | M_CompareExchangeStrong (_act, pe1, pe2, pe3, _order1, _order2) -> union_map free_in_pexpr [pe1; pe2; pe3]
   | M_CompareExchangeWeak (_act, pe1, pe2, pe3, _order1, order2) -> union_map free_in_pexpr [pe1; pe2; pe3]
   | M_LinuxFence _order -> SymSet.empty
   | M_LinuxLoad (_act, pe, _order) -> free_in_pexpr pe
   | M_LinuxStore (_act, pe1, pe2, _order) -> union_map free_in_pexpr [pe1; pe2]
   | M_LinuxRMW  (_act, pe1, pe2, _order) -> union_map free_in_pexpr [pe1; pe2]

let free_in_paction = function
  | M_Paction (_polarity, action) -> free_in_action action

let free_in_memop memop =
  union_map free_in_pexpr
    begin match memop with
    | M_PtrEq (pe1, pe2) -> [pe1; pe2]
    | M_PtrNe (pe1, pe2) -> [pe1; pe2]
    | M_PtrLt (pe1, pe2) -> [pe1; pe2]
    | M_PtrGt (pe1, pe2) -> [pe1; pe2]
    | M_PtrLe (pe1, pe2) -> [pe1; pe2]
    | M_PtrGe (pe1, pe2) -> [pe1; pe2]
    | M_Ptrdiff (_act, pe1, pe2) -> [pe1; pe2]
    | M_IntFromPtr (_act1, _act2, pe) -> [pe]
    | M_PtrFromInt (_act1, _act2, pe) -> [pe]
    | M_PtrValidForDeref (_act, pe) -> [pe]
    | M_PtrWellAligned (_act, pe) -> [pe]
    | M_PtrArrayShift (pe1, _act, pe2) -> [pe1; pe2]
    | M_PtrMemberShift (id1, id2, pe) -> [pe]
    | M_Memcpy (pe1, pe2, pe3) -> [pe1; pe2; pe3]
    | M_Memcmp (pe1, pe2, pe3) -> [pe1; pe2; pe3]
    | M_Realloc (pe1, pe2, pe3) -> [pe1; pe2; pe3]
    | M_Va_start (pe1, pe2) -> [pe1; pe2]
    | M_Va_copy pe -> [pe]
    | M_Va_arg (pe, _act) -> [pe]
    | M_Va_end pe -> [pe]
    | M_CopyAllocId (pe1, pe2) -> [pe1; pe2]
    end


let rec free_in_expr (M_Expr (_, _, _, expr_)) =
  match expr_ with
  | M_Epure pexpr -> free_in_pexpr pexpr
  | M_Ememop op -> free_in_memop op
  | M_Eaction paction -> free_in_paction paction
  | M_Eskip -> SymSet.empty
  | M_Eccall (_act, fsym, pes) -> union_map free_in_pexpr (fsym :: pes)
  | M_Elet (pattern, pexpr, expr) ->
     SymSet.union (free_in_pexpr pexpr)
       (SymSet.diff (free_in_expr expr) (bound_by_pattern pattern))
  | M_Ewseq (pattern, e1, e2)
  | M_Esseq (pattern, e1, e2) ->
     SymSet.union (free_in_expr e1)
       (SymSet.diff (free_in_expr e2) (bound_by_pattern pattern))
  | M_Eunseq exps -> union_map free_in_expr exps
  | M_CN_progs (_, _) -> SymSet.empty
  | M_Eif (pe, expr1, expr2) ->
     SymSet.union (free_in_pexpr pe)
       (union_map free_in_expr [expr1; expr2])
  | M_Ebound (expr) -> free_in_expr expr
  | M_End exprs -> union_map free_in_expr exprs
  | M_Erun (label_sym, pes) -> union_map free_in_pexpr pes
