module CF = Cerb_frontend
module A = CF.AilSyntax
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GD = GenDefinitions

module SymSet : Set.S with type elt = Sym.t

type term =
  | Uniform of
      { bt : BT.t;
        sz : int
      }
  | Pick of
      { bt : BT.t;
        choice_var : Sym.t;
        choices : (int * term) list;
        last_var : Sym.t
      }
  | Alloc of
      { bytes : IT.t;
        sized : bool
      }
  | Call of
      { fsym : Sym.t;
        iargs : (Sym.t * Sym.t) list;
        oarg_bt : BT.t;
        path_vars : SymSet.t;
        sized : int option
      }
  | Asgn of
      { pointer : Sym.t;
        offset : IT.t;
        sct : Sctypes.t;
        value : IT.t;
        last_var : Sym.t;
        rest : term
      }
  | Let of
      { backtracks : int;
        x : Sym.t;
        x_bt : BT.t;
        value : term;
        last_var : Sym.t;
        rest : term
      }
  | Return of { value : IT.t }
  | Assert of
      { prop : LC.t;
        last_var : Sym.t;
        rest : term
      }
  | ITE of
      { bt : BT.t;
        cond : IT.t;
        t : term;
        f : term
      }
  | Map of
      { i : Sym.t;
        bt : BT.t;
        min : IT.t;
        max : IT.t;
        perm : IT.t;
        inner : term;
        last_var : Sym.t
      }
[@@deriving eq, ord]

val free_vars_term : term -> SymSet.t

val free_vars_term_list : term list -> SymSet.t

val pp_term : term -> Pp.document

type definition =
  { filename : string;
    sized : bool;
    name : Sym.t;
    iargs : (Sym.t * BT.t) list;
    oargs : (Sym.t * BT.t) list;
    body : term
  }
[@@deriving eq, ord]

val pp_definition : definition -> Pp.document

type context = (A.ail_identifier * (A.ail_identifier list * definition) list) list

val pp : context -> Pp.document

val elaborate : GD.context -> context
