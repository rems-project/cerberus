(* This file is for transforming Core programs which use run/save, into Core
   programs which use a jump/where, a more compositional construct with the
   following semantics (plus context reduction, omitted).

     [Where-Pure]
     ------------------------------
     pure(v) where defs --> pure(v)

     [Jump-Sub]
     ( defs(l) = x . E )
     ----------------------------------------------
     jump l(pe) where defs --> {val/x} E where defs

     [Jump-Where]
     (l not in defs)
     ------------------------------------
     jump l(pe) where defs --> jump l(pe)

     [Jump-Let]
     ---------------------------------------
     lets _ = jump l(pe) in E --> jump l(pe)

   Semantics are reminiscent of checked exceptions: jump
   propagates out through let-strong continuations until caught
   by an enclosing where.

   We do this in 2 stages:
   1. Annotate the AST with dominator context for each label.
    - First, a bottom-up pass which annotates each node with a map from labels
      to number of children which refer to that label.
    - Second, a top-down pass uses that information to find the tightest node
      which encloses all uses of a label.
   2. Start from a label, and capture its context outwards.
      Since labels can share contexts, multiple can be capturing
      at the same time, and this is tracked.
      At each dominator context, remove the dominated labels from
      the tracked set.
      When the set of live labels is empty, that is where we place a
      where-expression.

   We simplifiy the problem by observing (in the absence of GCC statement
   expressions) labels only occur inside some combination of Esseq,
   Eif, Ecase, Esave. *)

open Core

type pattern = Symbol.sym generic_pattern

type pexpr = (unit, Symbol.sym) generic_pexpr

type expr = (unit, unit, Symbol.sym) generic_expr

type 'a param = {
  name : Symbol.sym;
  bTy : core_base_type;
  optCTy : (Ctype.ctype * pass_by_value_or_pointer) option;
  pexpr : 'a;
}

type 'info where = {
  info : 'info;
  annot : Annot.annot list;
  node : 'info where_
}

and 'info where_ =
  | Base of expr
  | If of pexpr * 'info where * 'info where
  | Sseq of pattern * 'info where * 'info where
  | Case of pexpr * (pattern * 'info where) list
  | Run of Symbol.sym * pexpr list
  | Jump of Symbol.sym * pexpr list
  | Where of {
      body : 'info where;
      defs : (unit param list * 'info where) list;
     }
  | Save of { 
      label : Symbol.sym;
      ret_bty : core_base_type;
      params : pexpr param list;
      body : 'info where
    }

type count_labels = (Symbol.sym, int) Pmap.map 

let add_counts sym int_opt1 int_opt2 =
  match int_opt1, int_opt2 with
  | None, None -> assert false
  | Some _, None
  | None, Some _ -> Some 1
  | Some _, Some _ -> Some 2

let merge_counts count1 count2 = Pmap.merge add_counts count1 count2

let transform_file core_file = core_file
