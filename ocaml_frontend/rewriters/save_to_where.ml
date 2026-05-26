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

let transform_file core_file = core_file
