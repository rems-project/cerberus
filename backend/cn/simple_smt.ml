open Printf
open Sexplib

module StrSet = Set.Make(String)
module StrMap = Map.Make(String)

(** {1 SMT Basics } *)

type sexp = Sexp.t

let atom f: sexp                = Sexp.Atom f
let list (xs: sexp list): sexp  = Sexp.List xs

let is_atom (f: sexp) =
  match f with
  | Sexp.Atom _ -> true
  | Sexp.List _ -> false

let to_list (f: sexp) =
  match f with
  | Sexp.Atom _ -> None
  | Sexp.List xs -> Some xs


(** Apply a function to some arguments. *)
let app f args =
  if List.is_empty args then f else list (f :: args)

(** Apply a function to some arguments *)
let app_ f (args: sexp list): sexp = app (atom f) args

(** Type annotation *)
let as_type x t = app_ "as" [x;t]

(** Let expression *)
let let_ xs e =
  match xs with
  | [] -> e
  | _  ->
    let mk_def (x,e) = app_ x [e] in
    app_ "let" [ list (List.map mk_def xs); e ]

(** Non-negative numeric constant. *)
let nat_k x = atom (string_of_int x)

(** Non-negative numeric constant. *)
let nat_zk x = atom (Z.to_string x)


(** Indexed family *)
let fam f is = list (atom "_" :: atom f :: is)

(** Int-indexed family *)
let ifam f is = fam f (List.map nat_k is)

(** Attribute *)
let named x e = app_ "!" [e; atom ":named"; atom x ]

(** Symbols are either simple or quoted (c.f. SMTLIB v2.6 S3.1).
This predicate indicates whether a character is allowed in a simple 
symbol.  Note that only ASCII letters are allowed. *)
let allowed_simple_char c =
  let co = Char.code c in
  let in_range a b = Char.code a <= co && co <= Char.code b in
  in_range 'a' 'z' ||
  in_range 'A' 'Z' ||
  in_range '0' '9' ||
  String.contains "~!@$%^&*_-+=<>.?/" c

let is_simple_symbol s =
  not (String.equal "" s) && String.for_all allowed_simple_char s

let quote_symbol s =
  if is_simple_symbol s
    then s
    else "|" ^ s ^ "|"

(** Make an SMT name, quoting if needed. Note that even with quoting
the name should not contain pipe (|) or backslash (\) *)
let symbol x = atom (quote_symbol x)









(** {1 Booleans } *)

(** The type of booleans. *)
let t_bool = atom "Bool"

(** Boolean constant *)
let bool_k b = atom (if b then "true" else "false")

(** If-then-else. This is polymorphic and can be used to construct any term. *)
let ite x y z = app_ "ite" [x;y;z]

(** Arguments are equal. *)
let eq x y = app_ "=" [x;y]

(** All arguments are pairwise different. *)
let distinct xs = if List.is_empty xs then bool_k true else app_ "distinct" xs

(** Logical negation. *)
let bool_not p = app_ "not" [p]

(** Conjunction. *)
let bool_and p q = app_ "and" [p;q]

(** Conjunction. *)
let bool_ands ps = if List.is_empty ps then bool_k true else app_ "and" ps

(** Disjunction. *)
let bool_or p q = app_ "or" [p;q]

(** Disjunction. *)
let bool_ors ps = if List.is_empty ps then bool_k false else app_ "or" ps

(** Exclusive-or. *)
let bool_xor p q = app_ "xor" [p;q]

(** Implication. *)
let bool_implies p q = app_ "=>" [p;q]




(** {1 Integers and Reals} *)

(** The type of integers. *)
let t_int = atom "Int"

(** The type of reals. *)
let t_real = atom "Real"

(** Numeric negation. *)
let num_neg x = app_ "-" [x]

(** Integer constant *)
let int_k x = if x < 0 then num_neg (nat_k (-x)) else nat_k x

(** Integer constant *)
let int_zk x = if Z.lt x Z.zero then num_neg (nat_zk (Z.neg x)) else nat_zk x

(** Division of real numbers. *)
let real_div x y = app_ "/" [x;y]

(** Real constant. *)
let real_k (q: Q.t) = real_div (int_zk q.num) (int_zk q.den)

(** Greater-then for numbers. *)
let num_gt x y = app_ ">" [x;y]

(** Less-then for numbers. *)
let num_lt x y = app_ "<" [x;y]

(** Greater-than-or-equal-to for numbers. *)
let num_geq x y = app_ ">=" [x;y]

(** Less-than-or-equal-to for numbers. *)
let num_leq x y = app_ "<=" [x;y]

(** Numeric addition. *)
let num_add x y = app_ "+" [x;y]

(** Numeric subtraction. *)
let num_sub x y = app_ "-" [x;y]

(** Numeric multiplication. *)
let num_mul x y = app_ "*" [x;y]

(** Numeric absolute value. *)
let num_abs x = app_ "abs" [x]

(** Numeric division. *)
let num_div x y = app_ "div" [x;y]

(** Numeric modulus. *)
let num_mod x y = app_ "mod" [x;y]

(** Numeric reminder. Nonstandard. *)
let num_rem x y = app_ "rem" [x;y]

(** Is the number divisible by the given constant? *)
let num_divisible x n = app (ifam "divisible" [n]) [x]


(** Satisfies [real_to_int x <= x] (i.e., this is like [floor]) *)
let real_to_int e = app_ "to_int" [e]

(** Promote an integer to a real. *)
let int_to_real e = app_ "to_real" [e]


(** {1 Bit-vectors} *)

(** [t_bits w] is the type of bit vectors of width [w]. *)
let t_bits w = ifam "BitVec" [w]

(** A bit-vector represented in binary.
- The number should be non-negative.
- The number should not exceed the number of bits.
*)
let bv_nat_bin w v = atom ("#b" ^ Z.format ("0" ^ string_of_int w ^ "b") v)

(** A bit-vector represented in hex.
- The number should be non-negative.
- The number should not exceed the number of bits.
- The width should be a multiple of 4.
*)
let bv_nat_hex w v = atom ("#x" ^ Z.format ("0" ^ string_of_int (w/4) ^ "x") v)

(** Bit vector arithmetic negation. *)
let bv_neg x = app_ "bvneg" [x]

(** A bit-vector represented in binary.
The number should fit in the given number of bits. *)
let bv_bin w v =
  if Z.geq v Z.zero
    then bv_nat_bin w v
    else bv_neg (bv_nat_bin w (Z.neg v))

(** A bit-vector represented in hex .
- The number should fit in the given number of bits.
- The width should be a multiple of 4. *)
let bv_hex w v =
  if Z.geq v Z.zero
    then bv_nat_hex w v
    else bv_neg (bv_nat_hex w (Z.neg v))

(** Make a bit-vector literal.  Uses hex representation if the size
is a multiple of 4, and binary otherwise. *)
let bv_k w v =
  if w mod 4 = 0
    then bv_hex w v
    else bv_bin w v



(** Unsigned less-than on bit-vectors. *)
let bv_ult x y = app_ "bvult" [x;y]

(** Unsigned less-than-or-equal on bit-vectors. *)
let bv_uleq x y = app_ "bvule" [x;y]

(** Signed less-than on bit-vectors. *)
let bv_slt x y = app_ "bvslt" [x;y]

(** Signed less-than-or-equal on bit-vectors. *)
let bv_sleq x y = app_ "bvsle" [x;y]

(** Bit vector concatenation. *)
let bv_concat x y = app_ "concat" [x;y]

(** Extend to the signed equivalent bitvector by the given number of bits. *)
let bv_sign_extend i x = app (ifam "sign_extend" [i]) [x]

(** Zero extend by the given number of bits. *)
let bv_zero_extend i x = app (ifam "zero_extend" [i]) [x]

(** [bv_extract i j x] is a sub-vector of [x].
    [i] is the larger bit index, [j] is the smaller one, and indexing
    is inclusive. *)
let bv_extract last_ix first_ix x = app (ifam "extract" [last_ix;first_ix]) [ x ]

(** Bitwise negation. *)
let bv_not x = app_ "bvnot" [x]

(** Bitwise conjuction. *)
let bv_and x y = app_ "bvand" [x;y]

(** Bitwise disjunction. *)
let bv_or x y = app_ "bvor" [x;y]

(** Bitwise exclusive or. *)
let bv_xor x y = app_ "bvxor" [x;y]

(** Addition of bit vectors. *)
let bv_add x y = app_ "bvadd" [x;y]

(** Subtraction of bit vectors. *)
let bv_sub x y = app_ "bvsub" [x;y]

(** Multiplication of bit vectors. *)
let bv_mul x y = app_ "bvmul" [x;y]

(** Bit vector unsigned division. *)
let bv_udiv x y = app_ "bvudiv" [x;y]

(** Bit vector unsigned reminder. *)
let bv_urem x y = app_ "bvurem" [x;y]

(** Bit vector signed division. *)
let bv_sdiv x y = app_ "bvsdiv" [x;y]

(** Bit vector signed reminder. *)
let bv_srem x y = app_ "bvsrem" [x;y]

(** Bit vector signed modulus. Nonstandard? *)
let bv_smod x y = app_ "bvsmod" [x;y]

(** Shift left. *)
let bv_shl x y = app_ "bvshl" [x;y]

(** Logical shift right. *)
let bv_lshr x y = app_ "bvlshr" [x;y]

(** Arithemti shift right (copies most significant bit). *)
let bv_ashr x y = app_ "bvashr" [x;y]



(** {1 Arrays} *)

(** [t_tarray kt vt] is the type of arrays with keys [kt] and values [vt] *)
let t_array kt vt = app_ "Array" [kt;vt]

(** [arr_const kt vt v] is an array of type [Array kt vt] where all elements
    are [v].  [v] should be of type [vt]. *)
let arr_const kt vt v = app (as_type (atom "const") (t_array kt vt)) [v]

(** [arr_select arr ix] is the element stored at index [ix] of [arr]. *)
let arr_select arr i = app_ "select" [arr;i]

(** [arr_store arr ix val] is an array that is the same as [arr],
    except at index [ix] it has [val] *)
let arr_store arr i v = app_ "store" [arr;i;v]


(** {1 Sets} *)

(** Some solvers support theories outside of SMTLIB and, unfortunately,
   there is no standard for what things are called. We use this flag
   to decide how to generate terms for those cases. *)
type solver_extensions = Z3 | CVC5 | Other

(** [t_set t] is the type of sets with elements of type [t]. *)
let t_set x = app_ "Set" [x]

(** [set_empty ext t] is the empty set with elements of type [t] *)
let set_empty ext t =
  match ext with
  | CVC5 -> app_ "as" [ atom "set.empty"; t_set t ]
  | _    -> app (app_ "as" [ atom "const"; t_set t ]) [bool_k false]

(** [set_universe ext t] is the universal set with elements of type [t] *)
let set_universe ext t =
  match ext with
  | CVC5 -> app_ "as" [ atom "set.universe"; t_set t ]
  | _    -> app (app_ "as" [ atom "const"; t_set t ]) [bool_k true]

(** [set_insert ext x xs] is a set that has all elements of [xs] and also [x] *)
let set_insert ext x xs =
  match ext with
  | CVC5 -> app_ "set.insert" [x;xs]
  | _    -> arr_store xs x (bool_k true)

(** [set_union ext xs ys] has all elements from [xs] and also from [ys] *)
let set_union ext x y =
  let nm = match ext with
           | CVC5 -> "set.union"
           | _    -> "union"
  in app_ nm [x;y]

(** [set_intersection ext xs ys] has the elements
    that are in both [xs] and [ys] *)
let set_intersection ext x y =
  let nm = match ext with
           | CVC5 -> "set.inter"
           | _    -> "intersection"
  in app_ nm [x;y]

(** [set_difference ext xs ys] has the elements of [xs] that are not in [ys] *)
let set_difference ext x y =
  let nm = match ext with
           | CVC5 -> "set.minus"
           | _    -> "setminus"
  in app_ nm [x;y]

(** [set_complement ext xs] has all elements that are not in [xs] *)
let set_complement ext x =
  let nm = match ext with
           | CVC5 -> "set.complement"
           | _    -> "complement"
  in app_ nm [x]

(** [set_member ext x xs] is true if [x] is a member of [xs] *)
let set_member ext x xs =
  match ext with
  | CVC5 -> app_ "set.member" [x;xs]
  | _    -> arr_select xs x

(** [set_subset ext xs ys] is true if all elements of [xs] are also in [ys] *)
let set_subset ext xs ys =
  let nm = match ext with
           | CVC5 -> "set.subset"
           | _    -> "subset"
  in app_ nm [xs;ys]


(** {1 Commands}
The S-Expressions in this section define commands to the SMT solver.
These can be sent to solver using {!ack_command}.
*)

(** A command made out of just atoms. *)
let simple_command xs   = list (List.map atom xs)

(** [set_option opt val] sets option [opt] to value [val]. *)
let set_option x y      = simple_command [ "set-option"; x; y ]

(** Set the logic to use. *)
let set_logic l         = simple_command [ "set-logic"; l ]

(** Push a new scope. *)
let push n              = simple_command [ "push"; string_of_int n ]

(** Pop a scope. *)
let pop n               = simple_command [ "pop"; string_of_int n ]

(** [declare_sort name arity] declares a type [name], which expect
  [arity] type parameters. *)
let declare_sort f arity =
  app_ "declare-sort" [ atom f; atom (string_of_int arity) ]

(** [declare_fun name param_types result_type] declareas a function
  expecting arguments with types [param_types] and computes a value
  of type [result_type]. *)
let declare_fun f ps r =
  app_ "declare-fun" [ atom f; list ps; r ]

(** [declare name type] declares a constant [name] of type [type]. *)
let declare f t = declare_fun f [] t

(** [define_fun name params result_type definition]
defines a function called [name], with the given parameters
[(name, type)], that computes a value of [result_type], using [definition]. *)
let define_fun f ps r d =
  let mk_param (x,a) = list [atom x; a] in
  app_ "define-fun" [ atom f; list (List.map mk_param ps); r; d ]

(** [define name type definition] defines a constant [name], of type
    [type] defined as [definition]. *)
let define f r d = define_fun f [] r d

(** The fields of an ADT constructor: [(field_name, field_type)] *)
type con_field = string * sexp

(** [declare_datatype name type_params cons] define an ADT
called [name] with type parameters [type_params] and constructors [cons].
Each constructor is of the form [(name, fields)]. *)
let declare_datatype name type_params cons =
  let mk_field ((f,argTy):con_field)  = list [atom f; argTy] in
  let mk_con (c,fs)       = list (atom c :: List.map mk_field fs) in
  let mk_cons             = list (List.map mk_con cons) in
  let def =
    match type_params with
    | [] -> mk_cons
    | _  -> app_ "par" [ List (List.map atom type_params); mk_cons ]
  in
  app_ "declare-datatype" [ atom name; def ]

(** [declare_datatypes tys] defines a group of mutually recursive ADTs.
Each element if `tys` is (name,type params,cons).
*)
let declare_datatypes tys =
  let mk_field ((f,argTy):con_field)  = list [atom f; argTy] in
  let mk_con (c,fs)       = list (atom c :: List.map mk_field fs) in
  let mk_cons cons        = list (List.map mk_con cons) in
  let def (_,type_params,cons) =
    match type_params with
    | [] -> mk_cons cons
    | _  -> app_ "par" [ List (List.map atom type_params); mk_cons cons ]
  in
  let arity (name,ty_params,_) =
        let n = List.length ty_params in
        list [atom name; atom (string_of_int n) ]
  in
  app_ "declare-datatypes" [ list (List.map arity tys)
                           ; list (List.map def tys)
                           ]



type pat = PVar of string | PCon of (string * string list)

let match_datatype e alts =
  let do_pat pat =
      match pat with
      | PCon (c,xs) -> list (atom c :: List.map atom xs)
      | PVar x      -> atom x
  in
  let do_alt (pat,e)  = list [do_pat pat; e] in
  app_ "match" [e; list (List.map do_alt alts)]

(** [is_con c e] is true if [e] is an expression constructed with [c] *)
let is_con c e = app (fam "is" [atom c]) [e]


(** Add an assertion to the current scope. *)
let assume e = app_ "assert" [e]




(** {1 Solver} *)

type solver_log =
  { send:    string -> unit   (** We sent this to the solver. *)
  ; receive: string -> unit   (** We got this from the solver. *)
  ; stop:    unit   -> unit   (** Do this when done, (close files, etc.) *)
  }

type solver_config =
  { exe:  string
  ; opts: string list
  ; exts: solver_extensions
  ; log:  solver_log
  }

(** A connection to a solver *)
type solver =
  { command:    sexp -> sexp
  ; stop:       unit -> unit
  ; force_stop: unit -> unit
  ; config:     solver_config
  }

exception UnexpectedSolverResponse of sexp

let () =
  Printexc.register_printer
    (function
      | UnexpectedSolverResponse s ->
        Some (Printf.sprintf "UnexpectedSolverResponse(%s)" (Sexp.to_string_hum s))
      | _ -> None
    )


(** Issue a command and wait for it to succeed.
    Throws {! UnexpectedSolverResponse} *)
let ack_command (s: solver) cmd =
  match s.command cmd with
  | Sexp.Atom "success" -> ()
  | ans                 -> raise (UnexpectedSolverResponse ans)



type result = Unsat | Unknown | Sat
  [@@deriving show]

(** Check if the current set of assumptions are consistent.
    Throws {!UnexpectedSolverResponse}. *)
let check s =
  match s.command (Sexp.of_string "(check-sat)") with
  | Sexp.Atom "unsat" -> Unsat
  | Sexp.Atom "sat" -> Sat
  | Sexp.Atom "unknown" -> Unknown
  | ans -> raise (UnexpectedSolverResponse ans)

(** {2 Decoding Results} *)

(** Get all definitions currently in scope. Only valid after a [Sat] result.
See also {!model_eval}. *)
let get_model s =
  let ans = s.command (list [ atom "get-model" ]) in
  match s.config.exts with
  | CVC5  -> ans
  | Other -> ans

  | Z3 ->
      (* Workaround z3 bug #7270: remove `as-array` *)
      let rec drop_as_array x =
          match x with
          | Sexp.List [ _; Sexp.Atom "as-array"; f ] -> f
          | Sexp.List xs -> Sexp.List (List.map drop_as_array xs)
          | _ -> x
      in

      (* Workaround for a z3 bug #7268: rearrange defs in dep. order *)
      let add_binder bound x =
            match x with
            | Sexp.List [Sexp.Atom v; _ty_or_term ] -> StrSet.add v bound
            | _ -> raise (UnexpectedSolverResponse x)
      in
      let add_bound = List.fold_left add_binder in

      let rec free bound vars x =
            match x with
            | Sexp.Atom a  -> if StrSet.mem a bound then vars else a :: vars
            | Sexp.List [ Sexp.Atom q; Sexp.List vs; body ]
              when String.equal q "forall"
                || String.equal q "exist"
                || String.equal q "let" -> free (add_bound bound vs) vars body
            | Sexp.List xs -> List.fold_left (free bound) vars xs
      in
      let check_def x =
            match x with
            | Sexp.List
                [ _def_fun; Sexp.Atom name; Sexp.List args; _ret; def ] ->
                let bound = add_bound StrSet.empty args in
                (name, free bound [] def, x)
            | _ -> raise (UnexpectedSolverResponse ans)
      in
      match ans with
      | Sexp.Atom _ -> raise (UnexpectedSolverResponse ans)
      | Sexp.List xs ->
        let defs                = List.map check_def xs in
        let add_dep mp (x,xs,e) = StrMap.add x (xs,e) mp in
        let deps                = List.fold_left add_dep StrMap.empty defs in

        let processing = ref StrSet.empty in
        let processed  = ref StrSet.empty in
        let decls      = ref [] in
        let rec arrange todo =
            match todo with
            | x :: xs ->
              if StrSet.mem x !processed
                then arrange xs
                else begin
                  if StrSet.mem x !processing
                    then raise (UnexpectedSolverResponse ans) (* recursive *)
                    else
                      begin match StrMap.find_opt x deps with
                      | None -> arrange xs
                      | Some (ds,e) ->
                        processing := StrSet.add x !processing;
                        arrange ds;
                        processing := StrSet.remove x !processing;
                        processed  := StrSet.add x !processed;
                        decls      := drop_as_array e :: !decls;
                        arrange xs
                      end
                end
            | [] -> ()
           in
        arrange (List.map (fun (x,_,_) -> x) defs);
        list (List.rev !decls)

(** Get the values of some s-expressions. Only valid after a [Sat] result.
    Throws {!UnexpectedSolverResponse}. *)
let get_exprs s vals: sexp list =
  let res = s.command (list [ atom "get-value"; list vals ]) in
  match res with
  | Sexp.List xs ->
    let get_val pair =
          match pair with
          | Sexp.List [_;x] -> x
          | _ -> raise (UnexpectedSolverResponse res)
    in List.map get_val xs
  | _ -> raise (UnexpectedSolverResponse res)

(** Evalute the given expression in the current context.
    Only valid after a [Sat] result.
    Throws {!UnexpectedSolverResponse}. *)
let get_expr s v: sexp =
  let res = s.command (list [ atom "get-value"; list [v]]) in
  match res with
  | Sexp.List [ Sexp.List [_;x] ] -> x
  | _ -> raise (UnexpectedSolverResponse res)


let is_let (exp: sexp): (sexp StrMap.t * sexp) option =
  match exp with
  | Sexp.List [ Sexp.Atom "let"; Sexp.List binds; body ] ->
    let add_bind mp bind =
        match bind with
        | Sexp.List [ Sexp.Atom x; y ] -> StrMap.add x y mp
        | _ -> raise (UnexpectedSolverResponse bind)
    in
    let su = List.fold_left add_bind StrMap.empty binds in
    Some (su, body)
  | _ -> None

(** Expand let-definitions in this term.
 NOTE: this is intended to be used mostly on models generated by the
 solver (e.g., `get-value` in Z3 sometimes contains `let`).  As such
 we assume that `forall` and `exist` won't occur, and so we don't need
 to check for variable capture. *)
let no_let (exp0: sexp): sexp =
  let rec expand su exp =
          match is_let exp with
          | Some (binds,body) ->
            let binds1   = StrMap.map (expand su) binds in
            let jn _ x _ = Some x in
            let su1      = StrMap.union jn binds1 su in
            expand su1 body
          | None ->
            match exp with
            | Sexp.List xs -> Sexp.List (List.map (expand su) xs)
            | Sexp.Atom x ->
              match StrMap.find_opt x su with
              | Some e1 -> e1
              | None    -> exp
  in
  expand StrMap.empty exp0



(** Try to decode an s-expression as a boolean
    Throws {!UnexpectedSolverResponse}. *)
let to_bool (exp: sexp) =
  match exp with
  | Sexp.Atom "true"  -> true
  | Sexp.Atom "false" -> false
  | _ -> raise (UnexpectedSolverResponse exp)

(** Try to decode an s-expression as a bitvector of the given width.
The 2nd argument indicates if the number is signed.
Throws {!UnexpectedSolverResponse}. *)
let to_bits w signed (exp: sexp) =
  let bad () = raise (UnexpectedSolverResponse exp) in
  let get_num base digs =
    try
      let z = Z.of_string_base base digs in
      if signed then Z.signed_extract z 0 w else z
    with Invalid_argument _ -> bad ()
  in
  match exp with
  | Sexp.Atom s ->
    let tot_len = String.length s in
    if tot_len < 2 || not (Char.equal (String.get s 0) '#') then bad () else ();
    let dig_len = tot_len - 2 in
    let digs = String.sub s 2 dig_len in
    begin match String.get s 1 with
    | 'b' -> if     dig_len = w then get_num  2 digs else bad ()
    | 'x' -> if 4 * dig_len = w then get_num 16 digs else bad ()
    | _   -> bad ()
    end
  | _ -> bad ()

(** Try to decode an s-expression as an integer.
Throws {!UnexpectedSolverResponse}. *)
let to_z (exp: sexp) =
  let parse do_neg s =
        try
          let r = Z.of_string s in
          if do_neg then Z.neg r else r
        with Invalid_argument _ -> raise (UnexpectedSolverResponse exp)
  in
  match exp with
  | Sexp.Atom s -> parse false s
  | Sexp.List [ Sexp.Atom "-"; Sexp.Atom s ] -> parse true s
  | _ -> raise (UnexpectedSolverResponse exp)

(** Try to decode an s-expression as a rational number.
Throws {!UnexpectedSolverResponse}. *)
let to_q (exp: sexp) =
  let bad () = raise (UnexpectedSolverResponse exp) in
  let rec eval e =
    match e with
    | Sexp.Atom s -> Q.of_string s
    | Sexp.List [ Sexp.Atom "-"; e1] -> Q.neg (eval e1)
    | Sexp.List [ Sexp.Atom "/"; e1; e2] -> Q.div (eval e1) (eval e2)
    | _ -> bad ()
  in
  try eval exp with Invalid_argument _ -> bad ()


(** Try to decode an s-expression as constructor with field values.
Throws {!UnexpectedSolverResponse}. *)
let to_con (exp: sexp): string * sexp list =
  let bad () = raise (UnexpectedSolverResponse exp) in
  match exp with
  | Sexp.Atom x -> (x, [])
  | Sexp.List xs ->
    match xs with
    | y :: ys ->
      begin match y with
      | Sexp.Atom x -> (x,ys)
      | Sexp.List [_; Sexp.Atom x; _] -> (x,ys) (*cvc5: (as con ty)*)
      | _ -> bad ()
      end
    | _ -> bad ()


(** Try to decode an s-expression as an array. The result is `(is,v)`
where is are (key,value) pairs, and `v` is the default array value.
Throws {!UnexpectedSolverResponse}. *)
let to_array (exp0: sexp): (sexp * sexp) list * sexp =
  let bad () = raise (UnexpectedSolverResponse exp0) in
  let rec loop is exp =
      match exp with
      | Sexp.List [ Sexp.List [Sexp.Atom "as"; Sexp.Atom "const"; _]; k ] ->
        (List.rev is, k)
      | Sexp.List [Sexp.Atom "store"; a; i; v] ->
        loop ((i,v)::is) a
      | _ -> bad ()
  in loop [] exp0


(** {2 Creating Solvers} *)

let new_solver (cfg: solver_config): solver =
  let args = Array.of_list (cfg.exe :: cfg.opts) in
  let proc = Unix.open_process_args_full cfg.exe args [| |] in
  let pid = Unix.process_full_pid proc in
  let (in_chan, out_chan, in_err_chan) = proc in
  let in_buf = Lexing.from_channel in_chan in

  let send_string s =
        cfg.log.send s;
        fprintf out_chan "%s\n%!" s in

  let send_command c =
        send_string (Sexp.to_string_hum c);
        let ans = match Sexp.scan_sexp_opt in_buf with
                    | Some x -> x
                    | None -> Sexp.Atom (In_channel.input_all in_err_chan)
        in cfg.log.receive (Sexp.to_string_hum ans); ans
  in

  let stop_command () =
        send_string "(exit)";
        let _ = Unix.close_process_full proc in
        cfg.log.stop ()
  in
  let force_stop_command () =
        Unix.kill pid 9;
        let _ = Unix.close_process_full proc in
        cfg.log.stop ()
  in
  let s =
    { command = send_command
    ; stop = stop_command
    ; force_stop = force_stop_command
    ; config = cfg
    }
  in
    ack_command s (set_option ":print-success" "true");
    ack_command s (set_option ":produce-models" "true");
    Gc.finalise (fun me -> me.stop ()) s;
    s

(** A connection to a solver,
    specialized for evaluting in the context of a model *)
type model_evaluator =
  { eval:       (string * (string*sexp) list * sexp * sexp) list -> sexp -> sexp
(** First define some local variables, then evaluate the expression *)
  ; stop:       unit -> unit
  ; force_stop: unit -> unit
  }


(** {2 Model Evaluation} *)

(* Start a new solver process, used to evaluate expressions in a model.
Unlike a normal solver, the [command] field expects an expression to
evaluate, and gives the value of the expression in the context of the model.

XXX: This does not work correctly with data declarations, because
the model does not contain those.  We need to explicitly add them.
*)
let model_eval (cfg: solver_config) (m: sexp) =
  let bad () = raise (UnexpectedSolverResponse m) in
  match m with
  | Sexp.Atom _ -> bad ()
  | Sexp.List defs ->
    let s = new_solver cfg in
    List.iter (ack_command s) defs;
    let have_model = ref false in
    let get_model () =
          if !have_model
            then true
            else match check s with
                 | Sat -> have_model := true; true
                 | _   -> false
    in
    let eval defs e =
      match defs with
      | [] -> if get_model () then get_expr s e else bad ()
      | _  ->
        let cleanup () = ack_command s (pop 1); have_model := false in
        ack_command s (push 1);
        let mk_def (f,ps,r,d) = ack_command s (define_fun f ps r d) in
        List.iter mk_def defs;
        have_model := false;
        if get_model ()
          then begin let res = get_expr s e in cleanup(); res end
          else begin cleanup (); bad () end
    in
      { eval       = eval
      ; stop       = s.stop
      ; force_stop = s.force_stop
      }


(** {2 Solver Configurations} *)

let quiet_log =
  { send    = (fun _ -> ())
  ; receive = (fun _ -> ())
  ; stop    = (fun _ -> ())
  }

let printf_log =
  { send    = (fun s -> printf "[->] %s\n%!" s)
  ; receive = (fun s -> printf "[<-] %s\n%!" s)
  ; stop    = (fun _ -> ())
  }

let cvc5 : solver_config =
  { exe   = "cvc5"
  ; opts  = ["--incremental"; "--sets-ext"]
  ; exts  = CVC5
  ; log   = quiet_log
  }

let z3 : solver_config =
  { exe   = "z3"
  ; opts  = ["-in"; "-smt2" ]
  ; exts  = Z3
  ; log   = quiet_log
  }
