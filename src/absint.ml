open Core
open Ocaml_mem
module N = Nat_big_num

type loc = Location_ocaml.t

let map_pair f =
  List.map (fun (x, y) -> f x y)

let id = fun x -> x

let debug msg = Debug_ocaml.print_debug 0 [] (fun () -> msg)

let string_of_prefix = function
  | Symbol.PrefSource (_, ss) ->
    begin match List.rev ss with
      | Symbol.Symbol (_, _, Some s) :: _ -> s
      | _ -> "<unknown>"
    end
  | _ -> "<unknown>"

module Binop = struct
  type arith =
    | Add | Sub | Mul | Div | Rem_t | Rem_f | Exp
  type rel =
    | Eq | Gt | Lt | Ge | Le
  let to_arith = function
    | OpAdd -> Add | OpSub -> Sub | OpMul -> Mul
    | OpRem_t -> Rem_t | OpRem_f -> Rem_f | OpExp -> Exp
    | _ -> failwith "Binop.to_arith"
  let to_rel = function
    | OpEq -> Eq | OpGt -> Gt | OpLt -> Lt
    | OpGe -> Ge | OpLe -> Le
    | _ -> failwith "Binop.to_rel"
end


type 'a sym_or_value =
  [ `Sym of Symbol.sym | `Val of 'a ]

type 'a rel_conditional =
  [ `Not of 'a rel_conditional
  | `Bop of Binop.rel * 'a sym_or_value * 'a sym_or_value ]

type 'a conditional =
  [ `Sym of Symbol.sym
  | `Val of 'a
  | `Not of 'a conditional
  | `Bop of Binop.rel * 'a sym_or_value * 'a sym_or_value ]


(* MODULE TYPES *)

module type Show = sig
  type t
  val show: t -> string
end

module type Compare = sig
  include Show
  val compare: t -> t -> int
end

module type Semilattice = sig
  include Show
  val top: t
  val join: t -> t -> t
end

(* TODO: missing meet *)
module type Lattice = sig
  include Semilattice
  val bot: t
end

module type CompleteLattice = sig
  include Lattice
  val bigjoin: t list -> t
end

module type AbstractDomain = sig
  include Semilattice
  val widen: t -> t -> t
end

module type ValueAbstractDomain = sig
  include AbstractDomain
  type value
  val abstract: value -> t
  val concrete: t -> value option
end

module type IntegerDomain = sig
  include ValueAbstractDomain with type value = N.num
  val abstract_arith: loc -> Binop.arith -> t -> t -> t
  val abstract_rel: loc -> Binop.rel -> t -> t -> [ `True | `False | `Top ]
  val rel_conditional: loc -> (Symbol.sym -> t option) -> t rel_conditional ->
    (Symbol.sym * t) list option
end

module type FloatingDomain = ValueAbstractDomain with type value = float

module type ValueDomain = sig
  include ValueAbstractDomain with type value = Core.value

  val bot: t
  val bigjoin: t list -> t

  val undef: t
  val unspec: t
  val unit: t
  val tuple: t list -> t
  val check: t -> [ `True | `False | `Top ]

  val match_case: t -> (('a, Symbol.sym) Core.generic_pattern * 'b) list
    -> ((Symbol.sym * t) list * 'b) list
  val match_pattern: t -> ('a, Symbol.sym) Core.generic_pattern
    -> (Symbol.sym * t) list
  val symbol_of_funptr: t -> Symbol.sym

  val create_pointer: N.num option -> N.num -> t
  val read_pointer: t -> (N.num option * N.num) option

  val abstract_not: t -> t
  val abstract_arith: loc -> Binop.arith -> t -> t -> t
  val abstract_rel: loc -> Binop.rel -> t -> t -> t
  val abstract_operation: loc -> Core.binop -> t -> t -> t

  val conditional: loc -> (Symbol.sym -> t option) -> t conditional ->
    (Symbol.sym * t) list option
end

module type StateAbstractDomain = sig
  include CompleteLattice
  module V: ValueDomain
  val add: t -> Symbol.sym -> V.t -> t
  val find: t -> Symbol.sym -> V.t option
  val initial: t
  val conditional: loc -> V.t conditional -> t -> t
end


(* MODULES *)

module Sym = struct
  type t = Symbol.sym
  let compare (Symbol.Symbol (d1, n1, _)) (Symbol.Symbol (d2, n2, _)) =
    if d1 = d2 then compare n1 n2
    else Digest.compare d1 d2
  let show = function
    | Symbol.Symbol (_, _, Some s) -> s
    | Symbol.Symbol (_, n, None) -> "a" ^ string_of_int n
end

module SymMap = Map.Make(Sym)


(* FUNCTORS *)

module MakeComplete(L: Lattice): CompleteLattice with type t = L.t = struct
  include L
  let bigjoin = List.fold_left join bot
end

module MakeKleene(L: CompleteLattice) = struct
  let fix f =
    let rec gen acc x =
      let f_x = f x in
      if x = f_x then acc
      else gen (f_x::acc) f_x
    in L.bigjoin @@ gen [L.bot] L.bot
end

module MakePure(S: StateAbstractDomain) = struct
  include S

  let call core fun_name args =
    let fundef =
      match fun_name with
      | Core.Sym f ->
        begin match Pmap.lookup f core.stdlib with
          | Some fundef -> fundef
          | None ->
            match Pmap.lookup f core.funs with
            | Some fundef -> fundef
            | None ->
              failwith "calling unknown function"
        end
      | Core.Impl f ->
        begin match Pmap.lookup f core.impl with
          | Some (Core.IFun (bty, params, pe)) ->
            Core.Fun (bty, params, pe)
          | _ ->
            failwith "implementation function"
        end
    in match fundef with
    | Core.Fun (_, params, pe) ->
      if List.length params <> List.length args then
        failwith "fun wrong params"
      else (List.map fst params, pe)
    | _ ->
      failwith "not fundef"

  (* NOTE: unfortunately this is effectfull, since conditionals
   * can update the environment *)
  let rec run (loc, core) (Pexpr (_, _, pe)) = fun st ->
    let self = run (loc, core) in
    match pe with
    | PEsym x ->
      debug @@ "getting x: " ^ Sym.show x;
      begin match find st x with
        | Some v -> (v, st)
        | None -> failwith @@ "missing: " ^ Sym.show x
      end
    | PEimpl impl ->
      failwith "impl"
    | PEval v ->
      debug @@ "getting value: " ^ String_core.string_of_value v;
      (V.abstract v, st)
    | PEconstrained _ ->
      failwith "constrained"
    | PEctor (Ctuple, pes) ->
      let (vs, sts) = List.split (List.map (fun pe -> self pe st) pes) in
      (V.tuple vs, S.bigjoin sts)
    | PEundef (loc, ub) ->
      debug "undefined";
      (V.undef, st)
    | PEerror _ ->
      failwith "Cerb Error"
    | PEctor (Cspecified, [pe]) ->
      debug "specified constructor";
      self pe st
    | PEctor (Cunspecified, [_]) ->
      debug "unspecified";
      (V.unspec, st)
    | PEctor (_, _) ->
      (V.top (* TODO *), st)
    | PEcase (pe, pat_es) ->
      debug "pure case";
      let (v, st) = self pe st in
      let (vs, sts) =
        List.split @@ 
        List.map (fun (xs_vs, pe) ->
            let st = List.fold_left (fun st (x, v) -> S.add st x v) st xs_vs in
            self pe st
          ) @@ V.match_case v pat_es
      in
      (V.bigjoin vs, S.bigjoin sts)
    | PEarray_shift _
    | PEmember_shift _ ->
      failwith "shift"
    | PEnot e ->
      debug "not operator";
      let (v, st) = self e st in
      (V.abstract_not v, st)
    | PEop (bop, e1, e2) ->
      debug "binary operator";
      let (v1, st1) = self e1 st in
      let (v2, st2) = self e2 st  in
      (V.abstract_operation loc bop v1 v2, S.join st1 st2)
    | PEstruct _ ->
      (V.top (* TODO *), st)
    | PEunion _ ->
      (V.top (* TODO *), st)
    | PEcfunction pe ->
      debug "cfunction";
      let (p, st) = self pe st in
      begin match Pmap.lookup (V.symbol_of_funptr p) core.Core.funinfo with
        | Some (ret_ty, arg_ty, is_variadic, has_proto) ->
          (* TODO *)
          (V.tuple [V.top; V.top; V.top; V.top], st)
        | None  ->
          assert false
      end
    | PEmemberof _ ->
      (V.top (* TODO *), st)
    | PEcall (Sym (Symbol.Symbol (_, _, Some "conv_int")), [_; pe]) ->
      self pe st
    | PEcall (Sym (Symbol.Symbol (_, _, Some "conv_loaded_int")), [_; pe]) ->
      self pe st
    | PEcall (Sym (Symbol.Symbol (_, _, Some "catch_exceptional_condition")), [_; pe]) ->
      self pe st
    | PEcall (f_name, arg_pes) ->
      debug "pure call";
      let (arg_vs, sts) = List.split @@
        List.map (fun pe -> self pe st) arg_pes in
      let (params, pe) = call core f_name arg_vs in
      let st' = List.fold_left2 S.add st params arg_vs in
      self pe st'
    | PElet (pat1, pe1, pe2) ->
      debug "pure let";
      let (v1, st1) = self pe1 st in
      let xs_vs = V.match_pattern v1 pat1 in
      let st2 = List.fold_left (fun st (x, v) -> S.add st x v) st xs_vs in
      self pe2 (S.join st1 st2)
    | PEif (pe1, pe2, pe3) ->
      debug "pure if";
      let cond = create_conditional (loc, core) pe1 st in
      begin match V.check @@ run_conditional (loc, core) cond st with
        | `True ->
          self pe2 st
        | `False ->
          self pe3 st
        | `Top ->
          debug "taking both branches on pure if";
          let (v2, st2) = self pe2 (S.conditional loc cond st) in
          let (v3 , st3)= self pe3 (S.conditional loc cond st) in
          (V.join v2 v3, S.join st2 st3)
      end
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _
    | PEbmc_assume _ ->
      (V.top, st) (* TODO *)
    | PEare_compatible _ ->
      (V.top, st) (* TODO *)

  and run_sym (loc, core) (Pexpr (_, _, pe_) as pe) = fun st ->
    match pe_ with
    | PEsym x ->
      debug @@ "creating symbol_or_value: " ^ Sym.show x;
      `Sym x
    | PEcall (Sym (Symbol.Symbol (_, _, Some "conv_int")), [_; pe]) ->
      run_sym (loc, core) pe st
    | PEcall (Sym (Symbol.Symbol (_, _, Some "conv_loaded_int")), [_; pe]) ->
      run_sym (loc, core) pe st
    | _ ->
      let (v, _) = run (loc, core) pe st in
      `Val v

  and create_conditional (loc, core) (Pexpr (_, _, pe)) st: S.V.t conditional =
    debug "create_conditional";
    match pe with
    | PEsym sym ->
      `Sym sym
    | PEval v ->
      `Val (V.abstract v)
    | PEnot pe ->
      `Not (create_conditional (loc, core) pe st)
    | PEop (op, pe1, pe2) ->
      let x_or_v1 = run_sym (loc, core) pe1 st in
      let x_or_v2 = run_sym (loc, core) pe2 st in
      let rel_bop = Binop.to_rel op in
      `Bop (rel_bop, x_or_v1, x_or_v2)
    | _ ->
      assert false

  and run_sym_or_val (loc, core) sym_or_val = fun st ->
    match sym_or_val with
    | `Sym sym ->
      debug @@ "getting sym: " ^ Sym.show sym;
      begin match find st sym with
        | Some v -> v
        | None -> failwith @@ "pe sym: " ^ Sym.show sym
      end
    | `Val v ->
      v

  and run_conditional (loc, core) (cond: S.V.t conditional) = fun st ->
    match cond with
    | `Sym sym ->
      debug @@ "getting sym: " ^ Sym.show sym;
      begin match find st sym with
        | Some v -> v
        | None -> failwith @@ "pe sym: " ^ Sym.show sym
      end
    | `Val v ->
      v
    | `Not cond ->
      V.abstract_not @@ run_conditional (loc, core) cond st
    | `Bop (rel_bop, x_or_v1, x_or_v2) ->
      let v1 = run_sym_or_val (loc, core) x_or_v1 st in
      let v2 = run_sym_or_val (loc, core) x_or_v2 st in
      V.abstract_rel loc rel_bop v1 v2

end

module MakeMem(S:StateAbstractDomain) = struct
  module V = S.V

  module NMap = Map.Make (struct
      type t = N.num
      let compare = N.compare
    end)

  type t =
    { env: S.t;
      mem: (Symbol.prefix * V.t option) NMap.t;
      next_alloc: N.num;
    }

  let init =
    { env = S.bot;
      mem = NMap.empty;
      next_alloc = N.zero;
    }

  let create pre st =
    let p = V.create_pointer (Some st.next_alloc) N.zero in
    (p, { st with next_alloc = N.succ st.next_alloc;
                  mem = NMap.add st.next_alloc (pre, None) st.mem })

  let kill p st =
    match V.read_pointer p with
    | Some (Some prov, _) ->
      begin match NMap.find_opt prov st.mem with
        | Some (pre, _) ->
          debug @@ "killing: " ^ string_of_prefix pre;
          (V.unit, { st with mem = NMap.remove prov st.mem })
        | None ->
          assert false
      end
    | _ ->
      assert false

  let store p v st =
    match V.read_pointer p with
    | Some (Some prov, _) ->
      begin match NMap.find_opt prov st.mem with
        | Some (pre, _) ->
          debug @@ "storing: " ^ string_of_prefix pre;
          (V.unit, { st with mem = NMap.add prov (pre, Some v) st.mem })
        | None ->
          assert false
      end
    | _ ->
      assert false

  let load p st =
    match V.read_pointer p with
    | Some (Some prov, _) ->
      begin match NMap.find_opt prov st.mem with
        | Some (pre, Some v) ->
          debug @@ "loading: " ^ string_of_prefix pre;
          (v, st)
        | _ -> assert false
      end
    | _ ->
      assert false

  let add st x v =
    { st with env = S.add st.env x v }

  let join st1 st2 =
    { env = S.join st1.env st2.env;
      mem = NMap.union (fun _ (p1, v1) (p2, v2) ->
          Some (match v1, v2 with
              | Some v1, Some v2 -> (p1, Some (V.join v1 v2))
              | Some v1, None -> (p1, Some v1)
              | None, Some v2 -> (p2, Some v2)
              | None, None -> (p1, None)
            )
        ) st1.mem st2.mem;
      next_alloc = max (st1.next_alloc) (st2.next_alloc);
    }

  let bigjoin = List.fold_left join init

end

module MakeExpr(S: StateAbstractDomain) = struct
  module Pure = MakePure(S)
  module Mem = MakeMem(S)

  let run_action (loc, core) (Action (_, _, act)) st =
    match act with
    | Create (_, _, pre) ->
      debug @@ "creating: " ^ string_of_prefix pre;
      Mem.create pre st
    | Kill (_, pe) ->
      debug "killing ...";
      let (v, _) = Pure.run (loc, core) pe st.Mem.env in
      Mem.kill v st
    | Store0 (_, _, pe_p, pe_v, _) ->
      debug "storing ...";
      let (p, _) = Pure.run (loc, core) pe_p st.Mem.env in
      let (v, _) = Pure.run (loc, core) pe_v st.Mem.env in
      Mem.store p v st
    | Load0 (_, pe_p, _) ->
      debug "loading ...";
      let (p, _) = Pure.run (loc, core) pe_p st.Mem.env in
      Mem.load p st
    | _ ->
      assert false


  let rec run_label (fenv, loc, core) k lab vs st =
    debug @@ "running label: " ^ Sym.show lab;
    match Pmap.lookup lab fenv with
    | Some (xs, e, None) ->
      debug @@ "args: " ^ String.concat ", " @@ List.map (fun (x, v) -> Sym.show x ^ ":" ^ S.V.show v) @@ List.combine xs vs;
      debug @@ "first time running this label: " ^ Sym.show lab;
      let init_st = List.fold_left2 Mem.add st xs vs in
      let fenv' = Pmap.add lab (xs, e, Some (vs, init_st)) fenv in
      run_aux (fenv', loc, core) (fun _ x -> x) e init_st
    | Some (xs, e, Some (prev_vs, prev_st)) ->
      debug @@ "args: " ^ String.concat ", " @@ List.map (fun (x, v) -> Sym.show x ^ ":" ^ S.V.show v) @@ List.combine xs vs;
      debug @@ "running this label again: " ^ Sym.show lab;
      let new_init_st = List.fold_left2 Mem.add st xs vs in
      let joined_st = Mem.join new_init_st prev_st in
      let joined_vs = List.map (fun (v1, v2) -> S.V.join v1 v2)
        @@ List.combine vs prev_vs in
      let fenv' = Pmap.add lab (xs, e, Some (vs, joined_st)) fenv in
      if joined_vs = prev_vs && joined_st = prev_st then
        let _ = debug "values and states are the same" in
        k fenv' (S.V.unit, joined_st)
      else
        let _ = debug "values or states differ" in
        run_aux (fenv', loc, core) (fun _ x -> x) e joined_st
    | None -> assert false

  (* NOTE: k is a continuation *)
  and run_aux (fenv, loc, core) k (Expr (annot, e_) as e) = fun st ->
    match e_ with
    | Eskip ->
      debug "running skip";
      k fenv (S.V.unit, st)
    | Epure pe ->
      debug "pure";
      let (v, _) =  Pure.run (loc, core) pe st.Mem.env in
      k fenv (v, st)
    | Eaction (Paction (_, act)) ->
      debug "action";
      k fenv @@ run_action (loc, core) act st
    | Eindet (_, e)
    | Ebound (_, e) ->
      run_aux (fenv, loc, core) k e st
    | Esave ((lab, _), param_defpes, e) ->
      debug "running save";
      let pes = List.map (fun (_, (_, arg)) -> arg) param_defpes in
      let vs = List.map (fun pe -> fst @@ Pure.run (loc, core) pe st.Mem.env) pes in
      run_label (fenv, loc, core) k lab vs st
    | Erun (_, lab, pes) ->
      debug "running run";
      let vs = List.map (fun pe -> fst @@ Pure.run (loc, core) pe st.Mem.env) pes in
      debug @@ "save values: " ^ String.concat ", " @@ List.map S.V.show vs;
      run_label (fenv, loc, core) k lab vs st
    | Eunseq es ->
      debug "unseq";
      let vs_sts = List.map (fun e -> run_aux (fenv, loc, core) (fun _ x -> x) e st) es in
      debug @@ "unseq size: " ^ string_of_int @@ List.length vs_sts;
      let (vs, sts) = List.split vs_sts in
      k fenv (S.V.tuple vs, Mem.bigjoin sts)
    | Esseq (pat1, e1, e2)
    | Ewseq (pat1, e1, e2) ->
      let k' fenv (v1, st1) =
        let xs_vs = S.V.match_pattern v1 pat1 in
        let st2 = List.fold_left (fun st (x, v) -> Mem.add st x v) st1 xs_vs in
        run_aux (fenv, loc, core) k e2 st2
      in
      run_aux (fenv, loc, core) k' e1 st
    | Ecase (pe, pat_es) ->
      debug "case";
      let (v, _) = Pure.run (loc, core) pe st.Mem.env in
      let xs_vs_es = S.V.match_case v pat_es in
      let vs_sts = List.map (fun (xs_vs, e) ->
          let st = List.fold_left (fun st (x, v) -> Mem.add st x v) st xs_vs in
          run_aux (fenv, loc, core) (fun _ x -> x) e st
        ) xs_vs_es
      in
      k fenv @@ (fun (vs, sts) -> (S.V.bigjoin vs, Mem.bigjoin sts))
      @@ List.split vs_sts
    | Eif (pe1, e2, e3) ->
      debug "if";
      let cond = Pure.create_conditional (loc, core) pe1 st.Mem.env in
      begin match S.V.check @@ Pure.run_conditional (loc, core) cond st.Mem.env
        with
        | `True ->
          run_aux (fenv, loc, core) k e2 st
        | `False ->
          run_aux (fenv, loc, core) k e3 st
        | `Top ->
          debug "taking both branches on if";
          let (v2, st2) = run_aux (fenv, loc, core) k e2 st in
          let (v3, st3) = run_aux (fenv, loc, core) k e3 st in
          (S.V.join v2 v3, Mem.join st2 st3)
      end
    | _ ->
      print_endline @@ String_core.string_of_expr e;
      assert false

  let run (loc, core) e =
    let labels = Pmap.map (fun (xs, e) -> (xs, e, None)) @@ Core_aux.collect_saves e in
    run_aux (labels, loc, core) (fun _ x -> x) e

end

module MakeValueDomain(I: IntegerDomain)(F: FloatingDomain): ValueDomain = struct

  let symbol_of_funptr _ = assert false
  let concrete _ = assert false

  type value = Core.value

  (* Address semilattice *)
  module A = struct
    type t = N.num option

    let join p q =
      match p, q with
      | Some p, Some q ->
        if p = q then Some p else None
      | _, _ -> None

    let abstract n = Some n

    let show = function
      | Some p -> N.to_string p
      | None -> "top"
  end

  (* Pointer semilattice *)
  module P = struct
    type t =
      | Top
      | Null
      | Concrete of N.num option * A.t
      | Function of Symbol.sym

    let join p q =
      match p, q with
      | Top, _
      | _, Top -> Top
      | Null, Null -> Null
      | Concrete (prov1, a1), Concrete (prov2, a2) ->
        if prov1 = prov2 then Concrete (prov1, A.join a1 a2)
        else Top
      | _, _ -> Top

    let widen = join

    let abstract prov_opt addr =
      Concrete (prov_opt, A.abstract addr)

    let show = function
      | Top -> "top"
      | Null -> "null"
      | Concrete (None, i) -> "(@empty, " ^ A.show i ^ ")"
      | Concrete (Some p, i) -> "(@" ^ N.to_string p ^ ", " ^ A.show i ^ ")"
      | Function (Symbol.Symbol (_, _, Some f)) -> f
      | Function _ -> assert false

  end

  module O = struct
    type t =
      | Top             (* either specified or not *)
      | Unspec          (* unspecified values *)
      | Spec            (* top of specified values *)
      | Integer of I.t
      | Floating of F.t
      | Pointer of P.t
      | Array of t list
      | Struct of unit (* TODO *)
      | Union of unit (* TODO *)
      | Composite of unit (* TODO *)

    let show = function
      | Top -> "(unspec|spec)"
      | Unspec -> "unspec"
      | Spec -> "spec"
      | Integer i -> I.show i
      | Floating x -> F.show x
      | Pointer p -> P.show p
      | Array _ -> "array"
      | Struct _ -> "struct"
      | Union _ -> "union"
      | Composite _ -> "composite"

    let top = Top

    let integer i = Integer i

    let rec join o1 o2 =
      match o1, o2 with
      | Top, _
      | _, Top -> Top
      | Unspec, Unspec -> Unspec
      | Unspec, _ -> Top
      | _, Unspec -> Top
      | Spec, Spec -> Spec
      | Integer x, Integer y -> Integer (I.join x y)
      | Floating x, Floating y -> Floating (F.join x y)
      | Pointer p, Pointer q -> Pointer (P.join p q)
      | Array xs, Array ys -> Array (map_pair join @@ List.combine xs ys)
      | Struct (), Struct () -> Struct () (* TODO *)
      | Union (), Union () -> Union () (* TODO *)
      | Composite (), Composite () -> Composite () (* TODO *)
      | _, _ -> Spec

    let rec widen o1 o2 =
      match o1, o2 with
      | Top, _
      | _, Top -> Top
      | Unspec, Unspec -> Unspec
      | Unspec, _ -> Top
      | _, Unspec -> Top
      | Spec, Spec -> Spec
      | Integer x, Integer y -> Integer (I.widen x y)
      | Floating x, Floating y -> Floating (F.widen x y)
      | Pointer p, Pointer q -> Pointer (P.widen p q)
      | Array xs, Array ys -> Array (map_pair widen @@ List.combine xs ys)
      | Struct (), Struct () -> Struct () (* TODO *)
      | Union (), Union () -> Union () (* TODO *)
      | Composite (), Composite () -> Composite () (* TODO *)
      | _, _ -> Spec


    let rec abstract = function
      | OVinteger x ->
        Ocaml_mem.case_integer_value x
          (fun n -> Integer (I.abstract n))
          (fun _ -> Unspec)
      | OVfloating x ->
        Ocaml_mem.case_fval x
          (fun _ -> Unspec)
          (fun x -> Floating (F.abstract x))
      | OVpointer p ->
        Ocaml_mem.case_ptrval p
          (fun _ -> Pointer P.Null)
          (fun f -> Pointer (P.Function f))
          (fun prov_opt addr -> Pointer (P.abstract prov_opt addr))
          (fun () -> Unspec)
      | OVarray xs ->
        let abstract_elem = function
          | LVspecified o -> abstract o
          | LVunspecified _ -> Unspec
        in Array (List.map abstract_elem xs)
      | OVstruct _ -> Struct () (* TODO *)
      | OVunion _ -> Union () (* TODO *)
      | OVcomposite _ -> Composite () (* TODO *)

    let abstract_arith loc bop o1 o2 =
      match o1, o2 with
      | Integer i1, Integer i2 ->
        Integer (I.abstract_arith loc bop i1 i2)
      | _, _ -> assert false

    let abstract_rel loc bop o1 o2 =
      match o1, o2 with
      | Integer i1, Integer i2 ->
        I.abstract_rel loc bop i1 i2
      | _, _ -> assert false

    let rel_conditional loc env (cond: t rel_conditional) =
      let env_integer s =
        match env s with
        | Some (Integer i) -> Some i
        | _ -> assert false
      in
      let lift_integers = function
        | Some xs_is -> Some (List.map (fun (x, i) -> (x, Integer i)) xs_is)
        | None -> None
      in
      match cond with
      | `Bop (bop, `Val _, `Val _) ->
        assert false
      | `Bop (bop, `Sym x, `Val (Integer i)) ->
        lift_integers @@
        I.rel_conditional loc env_integer @@ `Bop (bop, `Sym x, `Val i)
      | `Bop (bop, `Val (Integer i), `Sym x) ->
        lift_integers @@
        I.rel_conditional loc env_integer @@ `Bop (bop, `Val i, `Sym x)
      | `Bop (bop, `Sym x, `Sym y) ->
        lift_integers @@
        I.rel_conditional loc env_integer @@ `Bop (bop, `Sym x, `Sym y)
      | _ ->
        assert false

  end

  type t =
    | Top
    | Error
    | UB
    | Object of O.t
    | Unit
    | True
    | False
    | Ctype
    | Tuple of t list
    | Bot

  let undef = UB
  let unspec = Object O.Unspec
  let unit = Unit
  let tuple vs = Tuple vs
  let bot = Bot

  let rec show = function
    | Top -> "top"
    | UB -> "UB"
    | Error -> "error"
    | Object o -> O.show o
    | Unit -> "unit"
    | True -> "true"
    | False -> "false"
    | Ctype -> "ctype"
    | Tuple vs -> "[" ^ String.concat ", " (List.map show vs) ^ "]"
    | Bot -> "bot"

  let not = function
    | True -> False
    | False -> True
    | _ -> Top

  let rec join v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top -> Top
    | UB, UB -> UB
    | Error, Error -> Error
    | Object o1, Object o2 -> Object (O.join o1 o2)
    | Unit, Unit -> Unit
    | True, True -> True
    | False, False -> False
    | Ctype, Ctype -> Ctype
    | Tuple xs, Tuple ys -> Tuple (map_pair join @@ List.combine xs ys)
    | _, _ -> Top

  let rec widen v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top -> Top
    | UB, UB -> UB
    | Error, Error -> Error
    | Object o1, Object o2 -> Object (O.widen o1 o2)
    | Unit, Unit -> Unit
    | True, True -> True
    | False, False -> False
    | Ctype, Ctype -> Ctype
    | Tuple xs, Tuple ys -> Tuple (map_pair join @@ List.combine xs ys)
    | _, _ -> Top

  let rec abstract = function
    | Vobject o
    | Vloaded (LVspecified o) -> Object (O.abstract o)
    | Vloaded (LVunspecified _) -> Object O.Unspec
    | Vunit -> Unit
    | Vtrue -> True
    | Vfalse -> False
    | Vctype _ -> Ctype
    | Vlist (_, vs)
    | Vtuple vs -> Tuple (List.map abstract vs)

  let rec match_pattern_aux acc v (Pattern (_, pat)) =
    match pat with
    | CaseBase (None, _) ->
      `Match acc
    | CaseBase (Some sym, _) ->
      `Match ((sym, v)::acc)
    | CaseCtor (Cspecified, [pat]) ->
      begin match v with
        | Top ->
          begin match match_pattern_aux acc Top pat with
            | `Match acc
            | `Continue acc -> `Continue acc
            | `NoMatch -> assert false (* Top should always match something *)
          end
        | Object O.Spec ->
          begin match match_pattern_aux acc Top pat with
            | `Match acc
            | `Continue acc -> `Match acc
            | `NoMatch -> assert false (* Top should always match something *)
          end
        | Object O.Unspec ->
          `NoMatch
        | _ ->
          match_pattern_aux acc v pat
      end
    | CaseCtor (Cunspecified, [pat]) ->
      begin match v with
        | Top ->
          begin match match_pattern_aux acc Top pat with
            | `Match env
            | `Continue env -> `Continue env
            | `NoMatch -> assert false (* Top should always match something *)
          end
        | Object O.Unspec ->
          match_pattern_aux acc v pat
        | _ ->
          `NoMatch
      end
    | CaseCtor (Ctuple, pats) ->
      begin match v with
        | Tuple vs ->
          List.fold_left (fun env_acc (v, pat) ->
              match env_acc with
              | `Match env
              | `Continue env -> match_pattern_aux env v pat
              | `NoMatch -> `NoMatch
            ) (`Match []) @@ List.combine vs pats
        | v ->
          debug @@ show v;
          assert false
      end
    | _ ->
      assert false

  let match_pattern v pat =
    match match_pattern_aux [] v pat with
    | `Match xs_vs
    | `Continue xs_vs -> xs_vs
    | `NoMatch -> []

  let rec match_case v pats =
    let rec aux acc = function
      | [] ->
        acc
      | (pat, e) :: pat_es ->
        match match_pattern_aux [] v pat with
        | `Match env' -> (env', e) :: acc
        | `Continue env' -> aux ((env', e)::acc) pat_es
        | `NoMatch -> aux acc pat_es
    in aux [] pats

  let binop_is_rel = function
    | OpEq | OpGt | OpLt | OpGe | OpLe -> true
    | _ -> false

  let abstract_rel loc bop v1 v2 =
    let lift = function
      | `True -> True
      | `False -> False
      | `Top -> Top
    in
    match v1, v2 with
    | Top, _
    | _, Top ->
      Top
    | Object o1, Object o2 ->
      lift (O.abstract_rel loc bop o1 o2)
    | _, _ ->
      assert false

  let abstract_arith loc bop v1 v2 =
    match v1, v2 with
    | Top, _
    | _, Top ->
      Top
    | Object o1, Object o2 ->
      Object (O.abstract_arith loc bop o1 o2)
    | _, _ ->
      assert false

  let abstract_operation loc bop v1 v2 =
    match bop with
    | OpAdd | OpSub | OpMul | OpDiv | OpRem_t | OpRem_f | OpExp ->
      abstract_arith loc (Binop.to_arith bop) v1 v2
    | OpEq | OpGt | OpLt | OpGe | OpLe ->
      abstract_rel loc (Binop.to_rel bop) v1 v2
    | OpAnd ->
      begin match v1, v2 with
        | Top, Top
        | Top, True
        | True, Top -> Top
        | True, True -> True
        | _, _ -> False
      end
    | OpOr ->
      begin match v1, v2 with
        | Top, Top
        | Top, False
        | False, Top -> Top
        | False, False -> False
        | _, _ -> True
      end

  let abstract_not = function
    | Top -> Top
    | True -> False
    | False -> True
    | _ -> assert false

  let check = function
    | True -> `True
    | False -> `False
    | Top -> `Top
    | _ -> assert false

  let rec bigjoin = function
    | [] -> assert false
    | [v] -> v
    | v::vs -> join v (bigjoin vs)


  let leq x y =
    x = join x y

  let top = Top

  let bot = Bot

  let create_pointer prov_opt addr =
    Object (O.Pointer (P.abstract prov_opt addr))

  let read_pointer = function
    | Object (O.Pointer (P.Concrete (prov_opt, _))) -> Some (prov_opt, N.zero)
    | _ -> None

  let conditional loc env (cond: t conditional) =
    let check_true = function
      | Some True | Some Top -> Some []
      | _ -> None
    in
    let env_object s =
      match env s with
      | Some (Object o) -> Some o
      | _ -> assert false
    in
    let lift_objects = function
      | Some xs_os -> Some (List.map (fun (x, o) -> (x, Object o)) xs_os)
      | None -> None
    in
    match cond with
    | `Sym x ->
      check_true (env x)
    | `Val v ->
      check_true (Some v)
    | `Bop (bop, `Val v1, `Val v2) ->
      check_true @@ Some (abstract_rel loc bop v1 v2)
    | `Bop (bop, `Sym x, `Val (Object o)) ->
      lift_objects @@
      O.rel_conditional loc env_object @@ `Bop (bop, `Sym x, `Val o)
    | `Bop (bop, `Val (Object o), `Sym x) ->
      lift_objects @@
      O.rel_conditional loc env_object @@ `Bop (bop, `Val o, `Sym x)
    | `Bop (bop, `Sym x, `Sym y) ->
      lift_objects @@
      O.rel_conditional loc env_object @@ `Bop (bop, `Sym x, `Sym y)
    | _ ->
        (* TODO: HACK *)
      Some []

end


module MakeStateDomain(V: ValueDomain): StateAbstractDomain = struct
  module V = V

  type t =
    | Top
    | Bot
    | State of V.t SymMap.t

  let add st sym v =
    match st with
    | Top -> Top
    | Bot -> State (SymMap.add sym v SymMap.empty)
    | State s -> State (SymMap.add sym v s)

  let find st sym =
    match st with
    | Top -> Some V.top
    | Bot -> None
    | State s -> SymMap.find_opt sym s

  let show = function
    | Top -> "top"
    | Bot -> "bot"
    | State s ->
      SymMap.fold (fun sym v ss ->
          ss ^ ", " ^ Sym.show sym ^ ": " ^ V.show v
        ) s "{" ^ "}"

  let top = Top

  let bot = Bot

  let initial = Bot

  let pointwise f f_bot1 f_bot2 s1 s2 =
    let domain s = List.map fst @@ SymMap.bindings s in
    let dom = List.sort_uniq Sym.compare @@ domain s1 @ domain s2 in
    List.fold_left (fun acc sym ->
        let v =
          match SymMap.find_opt sym s1, SymMap.find_opt sym s2 with
          | Some v1, Some v2 -> f v1 v2
          | Some v1, None -> f_bot1 v1
          | None, Some v2 -> f_bot2 v2
          | None, None -> assert false
        in SymMap.add sym v acc
      ) SymMap.empty dom

  let join x y =
    match x, y with
    | Top, _
    | _, Top -> Top
    | x, Bot
    | Bot, x -> x
    | State s1, State s2 ->
      State (pointwise V.join id id s1 s2)

  let widen x y =
    match x, y with
    | Top, _
    | _, Top -> Top
    | x, Bot
    | Bot, x -> x
    | State s1, State s2 ->
      State (pointwise V.widen id id s1 s2)

  let meet x y = failwith "state meet"

  let leq x y =
    x = join x y

  let bigjoin xs =
    List.fold_left join Bot xs

  let conditional loc cond st =
    match cond with
    | `Sym x ->
      begin match find st x with
        | Some v ->
          begin match V.check v with
            | `True | `Top -> st
            | `False -> Bot
          end
        | None ->
          assert false
      end
    | `Val v ->
      begin match V.check v with
        | `True | `Top -> st
        | `False -> Bot
      end
    | _ ->
      begin match V.conditional loc (find st) cond with
        | Some xs_vs ->
          List.fold_left (fun st (x, v) -> add st x v) st xs_vs
        | None -> Bot
      end

end



module Make(I: IntegerDomain)(F: FloatingDomain) = struct
  module V = MakeValueDomain(I)(F)
  module S = MakeStateDomain(V)
  module E = MakeExpr(S)

  let run core =
    match core.main with
    | None -> failwith "no main"
    | Some main ->
      match Pmap.lookup main core.funs with
      | Some (Proc (_, _, _, e)) ->
        let (v, _) = E.run (Location_ocaml.unknown, core) e E.Mem.init in
        (*
        let (st, errors) = ErrorMonad.run m []  in
        List.iter (fun (loc, e) -> print_error loc e) errors;
           *)
        print_endline @@ "Returned value: " ^ E.Pure.V.show v;
        print_endline "End of analyse."
      | None
      | Some _ ->
        failwith "main not found"
end


(* SIGN EXAMPLE *)

module Sign: IntegerDomain = struct
  type value = N.num
  type t =
    | Top
    | Pos
    | Neg
    | Zero
    | One

  let show = function
    | Top -> "top"
    | Pos -> "pos"
    | Neg -> "neg"
    | Zero -> "zero"
    | One -> "one"

  let top = Top
  let zero = Zero
  let one = One

  let rec join x y =
    match x, y with
    | Top, _
    | _, Top -> Top
    | Pos, Pos -> Pos
    | Neg, Neg -> Neg
    | Zero, Zero -> Zero
    | One, One -> One
    | One, Pos
    | Pos, One -> Pos
    | _, _ -> Top

  let widen = join

  let leq x y =
    x = join x y

  let abstract n =
    if n = N.zero then Zero
    else if n = N.succ N.zero then One
    else if N.less n N.zero then Neg
    else Pos

  let concrete = function
    | Top | Pos | Neg -> None
    | Zero -> Some N.zero
    | One -> Some (N.succ N.zero)

  let is_zero = function
    | Zero -> Some true
    | One | Pos | Neg -> Some false
    | Top -> None

  let abstract_not = function
    | Top -> Top
    | Pos -> Neg
    | Neg -> Pos
    | Zero -> Zero
    | One -> Neg

  let rec abstract_arith loc bop v1 v2 =
    let open Binop in
    match bop with
    | Add ->
      begin match v1, v2 with
        | Top, _    -> Top
        | _, Top    -> Top
        | Pos, Pos  -> Pos
        | Pos, Neg  -> Top
        | Pos, Zero -> Pos
        | Pos, One  -> Pos
        | Neg, Pos  -> Top
        | Neg, Zero -> Neg
        | Neg, One  -> Top
        | Neg, Neg  -> Neg
        | Zero, Pos -> Pos
        | Zero, Neg -> Neg
        | Zero, Zero -> Zero
        | Zero, One -> One
        | One, Pos  -> Pos
        | One, Neg  -> Top
        | One, Zero -> One
        | One, One  -> Pos
      end
    | Sub ->
      begin match v1, v2 with
        | Top, _    -> Top
        | _, Top    -> Top
        | Pos, Pos  -> Top
        | Pos, Neg  -> Pos
        | Pos, Zero -> Pos
        | Pos, One  -> Top
        | Neg, Pos  -> Neg
        | Neg, Zero -> Neg
        | Neg, One  -> Neg
        | Neg, Neg  -> Top
        | Zero, Pos -> Neg
        | Zero, Neg -> Pos
        | Zero, Zero -> Zero
        | Zero, One -> Neg
        | One, Pos  -> Top
        | One, Neg  -> Pos
        | One, Zero -> One
        | One, One  -> Zero
      end
    | Mul ->
      begin match v1, v2 with
        | Top, _    -> Top
        | _, Top    -> Top
        | Pos, Pos  -> Pos
        | Pos, Neg  -> Neg
        | Pos, Zero -> Zero
        | Pos, One  -> Pos
        | Neg, Pos  -> Neg
        | Neg, Zero -> Zero
        | Neg, One  -> Neg
        | Neg, Neg  -> Pos
        | Zero, Pos -> Zero
        | Zero, Neg -> Zero
        | Zero, Zero -> Zero
        | Zero, One -> Zero
        | One, Pos  -> Pos
        | One, Neg  -> Neg
        | One, Zero -> Zero
        | One, One  -> One
      end
    | Div ->
      begin match v1, v2 with
        | Top, _    -> Top
        | _, Top    -> Top
        | Pos, Pos  -> Pos
        | Pos, Neg  -> Neg
        | Pos, Zero -> Top
        | Pos, One  -> Pos
        | Neg, Pos  -> Neg
        | Neg, Zero -> Top
        | Neg, One  -> Neg
        | Neg, Neg  -> Pos
        | Zero, Pos -> Zero
        | Zero, Neg -> Zero
        | Zero, Zero -> Top
        | Zero, One -> Zero
        | One, Pos  -> Pos
        | One, Neg  -> Neg
        | One, Zero -> Top
        | One, One  -> One
      end
    | Rem_t ->
      failwith "TODO: rem_t"
    | Rem_f ->
      failwith "TODO: rem_f"
    | Exp ->
      failwith "TODO: exp"


  let rec abstract_rel loc bop v1 v2 =
    let open Binop in
    match bop with
    | Eq ->
      begin match v1, v2 with
        | Pos, Neg
        | Neg, Pos -> `False
        | Zero, Zero
        | One, One -> `True
        | _, _ -> `Top
      end
    | Lt ->
      begin match v1, v2 with
        | Top, _    -> `Top
        | _, Top    -> `Top
        | Pos, Pos  -> `Top
        | Pos, Neg  -> `False
        | Pos, Zero -> `False
        | Pos, One  -> `False
        | Neg, Pos  -> `True
        | Neg, Zero -> `True
        | Neg, One  -> `True
        | Neg, Neg  -> `Top
        | Zero, Pos -> `True
        | Zero, Neg -> `False
        | Zero, Zero -> `False
        | Zero, One -> `True
        | One, Pos  -> `Top
        | One, Neg  -> `False
        | One, Zero -> `False
        | One, One  -> `False
      end
    | Le ->
      begin match v1, v2 with
        | Top, _    -> `Top
        | _, Top    -> `Top
        | Pos, Pos  -> `Top
        | Pos, Neg  -> `False
        | Pos, Zero -> `False
        | Pos, One  -> `False
        | Neg, Pos  -> `True
        | Neg, Zero -> `True
        | Neg, One  -> `True
        | Neg, Neg  -> `Top
        | Zero, Pos -> `True
        | Zero, Neg -> `False
        | Zero, Zero -> `True
        | Zero, One -> `True
        | One, Pos  -> `True
        | One, Neg  -> `False
        | One, Zero -> `False
        | One, One  -> `True
      end
    | Gt ->
      abstract_rel loc Le v2 v1
    | Ge ->
      abstract_rel loc Lt v2 v1

  let rel_conditional loc env (cond: t rel_conditional) =
    match cond with
    | `Bop (Binop.Le, `Sym x, `Val Zero) ->
      begin match env x with
        | Some Zero | Some Pos ->
          Some [(x, Zero)]
        | Some Top | Some Neg ->
          Some [(x, Neg)]
        | _ ->
          Some []
      end
    | _ ->
      Some []

end





(* INTERVAL EXAMPLE *)

module Interval: IntegerDomain = struct
  type value = N.num

  type inf_num =
    | MinusInf
    | Num of N.num
    | PlusInf

  let inf_not = function
    | MinusInf -> PlusInf
    | PlusInf -> MinusInf
    | Num n -> Num (N.negate n)

  let inf_min a b =
    match a, b with
    | MinusInf, MinusInf
    | PlusInf, PlusInf -> assert false
    | MinusInf, _
    | _, PlusInf -> a
    | PlusInf, _
    | _, MinusInf -> b
    | Num a, Num b -> Num (min a b)

  let inf_max a b =
    match a, b with
    | MinusInf, MinusInf
    | PlusInf, PlusInf -> assert false
    | MinusInf, _
    | _, PlusInf -> b
    | PlusInf, _
    | _, MinusInf -> a
    | Num a, Num b -> Num (max a b)

  let inf_add a b =
    match a, b with
    | MinusInf, PlusInf
    | PlusInf, MinusInf -> assert false
    | MinusInf, _
    | _, MinusInf -> MinusInf
    | PlusInf, _
    | _, PlusInf -> PlusInf
    | Num a, Num b -> Num (N.add a b)

  let inf_sub a b =
    match a, b with
    | MinusInf, PlusInf
    | PlusInf, MinusInf -> assert false
    | MinusInf, _
    | _, PlusInf -> MinusInf
    | PlusInf, _
    | _, MinusInf -> PlusInf
    | Num a, Num b -> Num (N.sub a b)

  let inf_mul a b =
    match a, b with
    | MinusInf, PlusInf
    | PlusInf, MinusInf -> MinusInf
    | PlusInf, PlusInf
    | MinusInf, MinusInf -> PlusInf
    | PlusInf, Num n
    | Num n, PlusInf ->
      if n = N.zero then Num N.zero
      else if N.greater n N.zero then PlusInf
      else MinusInf
    | MinusInf, Num n
    | Num n, MinusInf ->
      if n = N.zero then Num N.zero
      else if N.greater n N.zero then MinusInf
      else PlusInf
    | Num a, Num b -> Num (N.mul a b)

  let inf_div a b =
    match a, b with
    | MinusInf, PlusInf
    | PlusInf, MinusInf
    | PlusInf, PlusInf
    | MinusInf, MinusInf -> Num N.zero (* NOT SURE *)
    | PlusInf, Num n
    | Num n, PlusInf ->
      if n = N.zero then Num N.zero (* Core's semantics is total *)
      else if N.greater n N.zero then PlusInf
      else MinusInf
    | MinusInf, Num n
    | Num n, MinusInf ->
      if n = N.zero then Num N.zero (* Core's semantics is total *)
      else if N.greater n N.zero then MinusInf
      else PlusInf
    | Num a, Num b -> Num (N.div a b)

  let inf_eq a b =
    match a, b with
    | MinusInf, MinusInf
    | PlusInf, PlusInf -> true
    | Num a, Num b -> N.equal a b
    | _, _ -> false

  let inf_lt a b =
    match a, b with
    | MinusInf, MinusInf
    | PlusInf, PlusInf -> false
    | MinusInf, PlusInf -> true
    | PlusInf, MinusInf -> false
    | Num _, PlusInf
    | MinusInf, Num _ -> true
    | PlusInf, Num _
    | Num _, MinusInf -> false
    | Num a, Num b -> N.less a b

  let inf_le a b =
    inf_lt a b || inf_eq a b

  let inf_to_string = function
    | MinusInf -> "-inf"
    | Num n -> N.to_string n
    | PlusInf -> "+inf"

  type t = inf_num * inf_num

  let show (s, e) =
    "[" ^ inf_to_string s ^ ", " ^ inf_to_string e ^ "]"

  let top = (MinusInf, PlusInf)

  let rec join (s1, e1) (s2, e2) =
    if inf_lt (Num (N.of_int 10)) e1 || inf_lt (Num (N.of_int 10)) e2 then
      (inf_min s1 s2, PlusInf) (* FIXME: TEMPORARY HACK *)
    else
    (inf_min s1 s2, inf_max e1 e2)

  let widen = join

  let abstract n =
    (Num n, Num n)

  let leq x y =
    x = join x y

  let concrete (x, y) =
    match x, y with
    | Num a, Num b when a = b -> Some a
    | _, _ -> None

  let inf_zero = Num N.zero
  let inf_one = Num (N.succ N.zero)
  let inf_minus_one = Num (N.negate (N.succ N.zero))

  let zero = (inf_zero, inf_zero)
  let one  = (inf_one, inf_one)
  let both = (inf_zero, inf_one)

  let rec abstract_arith loc bop (a, b) (c, d) =
    let open Binop in
    match bop with
    | Add ->
      debug @@ "adding : " ^ show (a, b) ^ " + " ^ show (c, d);
      let v = (inf_add a c, inf_add b d) in
      debug @@ "answer: " ^ show v;
      v
    | Sub ->
      (inf_sub a d, inf_sub b c)
    | Mul ->
      (inf_min (inf_min (inf_mul a c) (inf_mul a d))
               (inf_min (inf_mul b c) (inf_mul b d)),
       inf_max (inf_max (inf_mul a c) (inf_mul a d))
               (inf_max (inf_mul b c) (inf_mul b d)))
    | Div ->
      if inf_le inf_one c then
        ((inf_min (inf_div a c) (inf_div a d)),
         (inf_max (inf_div b c) (inf_div b d)))
      else if inf_le d inf_minus_one then
        ((inf_min (inf_div b c) (inf_div b d)),
         (inf_max (inf_div a c) (inf_div a d)))
      else
        failwith "todo: div"
    | Rem_t ->
      failwith "TODO: rem_t"
    | Rem_f ->
      failwith "TODO: rem_f"
    | Exp ->
      failwith "TODO: exp"

  let rec abstract_rel loc bop (a, b) (c, d) =
    let open Binop in
    match bop with
    | Eq ->
      if inf_eq a b && inf_eq b c && inf_eq c d then `True
      else if inf_lt b c || inf_lt d a then `False
      else `Top
    | Lt ->
      if inf_lt b c then `True
      else if inf_lt d a then `False
      else `Top
    | Le ->
      if inf_le b c then `True
      else if inf_le d a then `False
      else `Top
    | Gt ->
      abstract_rel loc Le (c, d) (a, b)
    | Ge ->
      abstract_rel loc Lt (c, d) (a, b)

  let rel_conditional loc env (cond: t rel_conditional) =
    match cond with
    | `Bop (Binop.Le, `Sym x, `Val (v1, v2)) when v1 = v2 ->
      begin match env x with
        | Some (a, b) ->
          if inf_le a v1 then
            Some [(x, (a, inf_min b v1))]
          else
            None
        | _ ->
          Some []
      end
    | `Bop (Binop.Le, `Sym x, `Sym y) ->
      begin match env x, env y with
        | Some (a, b), Some (c, d) ->
          if inf_le a d then
            let _ = debug @@ "previous value of " ^ Sym.show x ^ ": " ^
                             show (a, b) ^ " new value: " ^
                             show (a, inf_min b d) in
            let _ = debug @@ "previous value of " ^ Sym.show y ^ ": " ^
                             show (c, d) ^ " new value: " ^
                             show (inf_max a c, d) in
            Some [(x, (a, inf_min b d));
                  (y, (inf_max a c, d))]
          else
            None
        | _ ->
          Some []
      end
    | `Bop (Binop.Eq, `Sym x, `Sym y) ->
      begin match env x, env y with
        | Some (a, b), Some (c, d) ->
          if inf_le a d then
            let v = (inf_max a c, inf_min b d) in
            let _ = debug @@ "previous value of " ^ Sym.show x ^ ": " ^
                             show (a, b) ^ " new value: " ^ show v in
            let _ = debug @@ "previous value of " ^ Sym.show y ^ ": " ^
                             show (c, d) ^ " new value: " ^ show v in
            Some [(x, v);
                  (y, v)]
          else
            None
        | _ ->
          Some []
      end
    | _ ->
      Some []

end



module Dummy: FloatingDomain = struct
  type value = float
  type t = unit
  let show _ = "unit"
  let top = ()
  let join _ _ = ()
  let widen _ _ = ()
  let leq _ _ = true
  let abstract _ = ()
  let concrete _ = None
end


module IntervalInterpret = Make(Interval)(Dummy)
module SignInterpret = Make(Sign)(Dummy)

(* let run = SignInterpret.run *)
let run = IntervalInterpret.run

