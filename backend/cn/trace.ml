module CF = Cerb_frontend

module Mucore = CF.Mucore
module New = NewMu.New
module SymSet = Set.Make(Sym)

type opt_pat = unit New.mu_sym_or_pattern option
type expr = unit New.mu_expr
type pexpr = unit New.mu_pexpr

type mu_trace_step = {
    expr: expr;
    pat: opt_pat;
    ct_before: Context.t;
    ct_after: Context.t;
  }

type mu_trace = mu_trace_step list

type t = {
  mu_trace: mu_trace
}

let empty = {mu_trace = []}

let add_trace_step pat expr (ct1, ct2) (tr : t) =
  let step = {expr; pat; ct_before = ct1; ct_after = ct2} in
  {mu_trace = step :: tr.mu_trace}

let add_pure_trace_step pat expr cts tr =
  add_trace_step pat (New.embed_pexpr_expr expr) cts tr




