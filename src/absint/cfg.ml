open Core
open Core_ctype

module Int = struct
  type t = int
  let compare = compare
end

module Sym = struct
  type t = Symbol.sym
  let compare (Symbol.Symbol (d1, n1, _)) (Symbol.Symbol (d2, n2, _)) =
    if d1 = d2 then compare n1 n2
    else Digest.compare d1 d2
  let show = function
    | Symbol.Symbol (_, _, Some s) -> s
    | Symbol.Symbol (_, n, None) -> "a" ^ string_of_int n
end

module IMap = Map.Make(Int)

module SMap = Map.Make(Sym)

module GraphM: sig
  type ('a, 'b) t

  val return: 'a -> ('a, 'b) t
  val bind: ('a, 'c) t -> ('a -> ('b, 'c) t) -> ('b, 'c) t
  val (>>=): ('a, 'c) t -> ('a -> ('b, 'c) t) -> ('b, 'c) t
  val mapM: ('a -> ('b, 'c) t) -> 'a list -> ('b list, 'c) t

  val new_vertex: (Pgraph.vertex_id, 'a) t

  val remove_isolated_vertices: (unit, 'a) t

  val add_edge: Pgraph.vertex_id * Pgraph.vertex_id -> 'a -> (unit, 'a) t

  val add_label: Symbol.sym -> Symbol.sym list * Pgraph.vertex_id -> (unit, 'a) t
  val get_label: Symbol.sym -> ((Symbol.sym list * Pgraph.vertex_id) option, 'a) t

  val set_init_vertex: Pgraph.vertex_id -> (unit, 'b) t

  val run: ('a, 'b) t -> Pgraph.vertex_id * (unit, 'b) Pgraph.graph

end = struct

  type 'b state =
    { graph: (unit, 'b) Pgraph.graph;
      labels: (Symbol.sym list * int) SMap.t;
      vinit: Pgraph.vertex_id;
    }

  type ('a, 'b) t = 'b state -> 'a * 'b state

  let return x = fun g -> (x, g)
  let bind m f = fun g ->
    let (x, g') = m g in
    f x g'
  let (>>=) = bind

  let sequence ms =
    let m =
      List.fold_left (fun acc m ->
          m   >>= fun x ->
          acc >>= fun xs ->
          return (x::xs)
        ) (return []) ms
    in fun s ->
      let (xs, s') = m s in
      (List.rev xs, s')
  let mapM f xs = sequence (List.map f xs)

  let new_vertex = fun st ->
    let (v, graph) = Pgraph.add_vertex () st.graph in
    (v, { st with graph })

  let remove_isolated_vertices = fun st ->
    ((), { st with graph = Pgraph.remove_isolated_vertices st.graph })

  let add_edge (v1, v2) l = fun st ->
    ((), { st with graph = snd @@ Pgraph.add_edge v1 v2 l st.graph })

  let add_label lab (xs, v) = fun st ->
    ((), { st with labels = SMap.add lab (xs, v) st.labels })

  let get_label lab = fun st ->
    (SMap.find_opt lab st.labels, st)

  let set_init_vertex vinit = fun st ->
    ((), { st with vinit })

  let run (m: ('a, 'b) t) =
    let (_, st) = m { graph = Pgraph.empty; labels = SMap.empty; vinit = 0 } in
    (st.vinit, st.graph)

end


(* Takes a list and returns all possible sequentialised combination *)
let rec all_sequences = function
  | [] -> []
  | [x] -> [[x]]
  | xs ->
    let rec pivots = function
      | [] -> []
      | x::xs ->
        (x, xs) :: (List.map (fun (y, ys) -> (y, x::ys)) @@ pivots xs)
    in
    let rec aux = function
      | [] -> []
      | (x, xs) :: l ->
        List.rev_append (List.map (fun xs -> x::xs) @@ all_sequences xs) @@ aux l
    in aux (pivots xs)

(* Transfer expression *)
type ('a, 'bty) texpr =
  | TEsym of Symbol.sym
  | TEval of Symbol.sym generic_value
  | TEaction of ('a, 'bty) taction
  | TEmemop of Mem_common.memop * ('a, 'bty) texpr list
  | TEimpl of Implementation_.implementation_constant
  | TEconstrained of (Mem.mem_iv_constraint * ('a, 'bty) texpr) list
  | TEundef of Location_ocaml.t * Undefined.undefined_behaviour
  | TEerror of string * ('a, 'bty) texpr
  | TEctor of 'bty generic_ctor * ('a, 'bty) texpr list
  | TEarray_shift of ('a, 'bty) texpr * ctype0 * ('a, 'bty) texpr
  | TEmember_shift of ('a, 'bty) texpr * Symbol.sym * Cabs.cabs_identifier
  | TEnot of ('a, 'bty) texpr
  | TEop of binop * ('a, 'bty) texpr * ('a, 'bty) texpr
  | TEstruct of Symbol.sym * (Cabs.cabs_identifier * ('a, 'bty) texpr) list
  | TEunion of Symbol.sym * Cabs.cabs_identifier * ('a, 'bty) texpr
  | TEcfunction of ('a, 'bty) texpr
  | TEmemberof of Symbol.sym * Cabs.cabs_identifier * ('a, 'bty) texpr
  | TEcall of Symbol.sym generic_name * ('a, 'bty) texpr list
  | TEis_scalar of ('a, 'bty) texpr
  | TEis_integer of ('a, 'bty) texpr
  | TEis_signed of ('a, 'bty) texpr
  | TEis_unsigned of ('a, 'bty) texpr
  | TEare_compatible of ('a, 'bty) texpr * ('a, 'bty) texpr

and ('a, 'bty) taction =
  | TAcreate
  | TAalloc
  | TAkill of ('a, 'bty) texpr
  | TAstore of ('a, 'bty) texpr * ('a, 'bty) texpr
  | TAload of ('a, 'bty) texpr

(* Conditionals guards *)
type ('a, 'bty) cond =
  | Csym of Symbol.sym
  | Cval of Symbol.sym generic_value
  | Cop of binop * ('a, 'bty) texpr * ('a, 'bty) texpr
  | Cnot of ('a, 'bty) cond
  | Cmatch of ('a, Symbol.sym) generic_pattern * ('a, 'bty) texpr
  | Cis_scalar of ('a, 'bty) texpr
  | Cis_integer of ('a, 'bty) texpr
  | Cis_signed of ('a, 'bty) texpr
  | Cis_unsigned of ('a, 'bty) texpr
  | Care_compatible of ('a, 'bty) texpr * ('a, 'bty) texpr

(* Transfer functions *)
type ('a, 'bty) transfer =
  | Tskip
  | Tcond of ('a, 'bty) cond
  | Tassign of ('a, Symbol.sym) generic_pattern * ('a, 'bty) texpr
  | Tcall of ('a, Symbol.sym) generic_pattern
             * ('a, 'bty) texpr * ('a, 'bty) texpr list

let show_ctor = function
  | Cnil _ -> "Nil"
  | Ccons -> "Cons"
  | Ctuple -> "Tuple"
  | Carray -> "Array"
  | Civmax -> "Ivmax"
  | Civmin -> "Ivmin"
  | Civsizeof -> "Ivsizeof"
  | Civalignof -> "Ivalignof"
  | CivCOMPL -> "IvCOMPL"
  | CivAND -> "IvAND"
  | CivOR -> "IvOR"
  | CivXOR -> "IvXOR"
  | Cspecified -> "Specified"
  | Cunspecified -> "Unspecified"
  | Cfvfromint -> "Cfvfromint"
  | Civfromfloat -> "Civfromfloat"

let show_memop =
  let open Mem_common in
  function
  | PtrEq -> "PtrEq"
  | PtrNe -> "PtrNe"
  | PtrLt -> "PtrLt"
  | PtrGt -> "PtrGt"
  | PtrLe -> "PtrLe"
  | PtrGe -> "PtrGe"
  | Ptrdiff -> "Ptrdiff"
  | IntFromPtr -> "IntFromPtr"
  | PtrFromInt -> "PtrFromInt"
  | PtrValidForDeref -> "PtrValidForDeref"
  | PtrWellAligned -> "PtrWellAligned"
  | Memcmp -> "Memcmp"
  | Memcpy -> "Memcpy"
  | Realloc -> "Realloc"
  | Va_start -> "Va_start"
  | Va_copy -> "Va_copy"
  | Va_arg -> "Va_arg"
  | Va_end -> "Va_end"
  | PtrArrayShift -> "PtrArrayShift"

let show_binop = function
  | OpAdd -> " + "
  | OpSub -> " - "
  | OpMul -> " * "
  | OpDiv -> " / "
  | OpRem_t -> " rem_t "
  | OpRem_f -> " rem_f "
  | OpExp -> " ^ "
  | OpEq  -> " = "
  | OpLt  -> " < "
  | OpLe  -> " <= "
  | OpGt  -> " > "
  | OpGe  -> " >= "
  | OpAnd -> "/\\"
  | OpOr  -> "\\/"

let parens s = "(" ^ s ^ ")"

let brackets s = "[" ^ s ^ "]"

let comma_list f xs = String.concat ", " (List.map f xs)

let rec show_pattern (Pattern (_, pat)) =
  match pat with
  | CaseBase (None, _) -> "_"
  | CaseBase (Some sym, _) -> Sym.show sym
  | CaseCtor (Ctuple, pats) ->
    parens (comma_list show_pattern pats)
  | CaseCtor (ctor, pats) ->
    show_ctor ctor ^ parens (comma_list show_pattern pats)

let polarity = function
  | Pos -> fun z -> z
  | Neg -> fun z -> "neg" ^ parens z

let show_name = function
  | Sym a  -> Sym.show a
  | Impl i -> Implementation_.string_of_implementation_constant i

let rec show_texpr te =
  let self e = show_texpr e in
  match te with
  | TEsym x ->
    Sym.show x
  | TEval v ->
    String_core.string_of_value v
  | TEaction act ->
    show_taction act
  | TEmemop (memop, tes) ->
    "memop" ^ parens (show_memop memop ^ ", " ^ comma_list self tes)
  | TEimpl i ->
    Implementation_.string_of_implementation_constant i
  | TEconstrained (ivs_tes) -> "constrained"
  | TEundef (_, ub) ->
    Undefined.stringFromUndefined_behaviour ub
  | TEerror (str, te) ->
    "error " ^ parens (str ^ ", " ^ self te)
  | TEctor (Cnil _, _) -> "[]"
  | TEctor (Ccons, tes) ->
      let to_list_value =
        let rec aux acc = function
          | TEctor (Cnil _, []) ->
              Some (List.rev acc)
          | TEctor (Ccons, [te1; te2]) ->
                aux (te1 :: acc) te2
          | _ ->
              None
        in
        aux [] te in
      begin match to_list_value with
        | Some pes' -> brackets (comma_list self pes')
        | None -> String.concat " :: " @@ List.map self tes
      end
  | TEctor (Ctuple, tes) ->
      parens (comma_list self tes)
  | TEctor (ctor, tes) ->
      show_ctor ctor ^ parens (comma_list self tes)
  | TEarray_shift (te1, cty, te2) ->
    "array_shift" ^ parens (self te1 ^ ", "
                            ^ String_core_ctype.string_of_ctype cty
                            ^ self te2)
  | TEmember_shift (te, x, Cabs.CabsIdentifier (_, memb)) ->
    "member_shift" ^ parens (self te ^ ", " ^ Sym.show x ^ ", " ^ memb)
  | TEnot te ->
    "not " ^ parens (self te)
  | TEop (bop, te1, te2) ->
    self te1 ^ show_binop bop ^ self te2
  | TEstruct (x, _) ->
    "struct " ^ Sym.show x
  | TEunion (x, _, _) ->
    "union " ^ Sym.show x
  | TEcfunction te ->
    "cfunction" ^ parens (self te)
  | TEmemberof (x, Cabs.CabsIdentifier (_, memb), te) ->
    "memberof" ^ parens (Sym.show x ^ ", " ^ memb ^ ", " ^ self te)
  | TEcall (nm, tes) ->
    show_name nm ^ parens (comma_list self tes)
  | TEis_scalar te ->
    "is_scalar" ^ parens (self te)
  | TEis_integer te ->
    "is_integer" ^ parens (self te)
  | TEis_signed te ->
    "is_signed" ^ parens (self te)
  | TEis_unsigned te ->
    "is_unsigned" ^ parens (self te)
  | TEare_compatible (te1, te2) ->
    "are_compatible" ^ parens (self te1 ^ ", " ^ self te2)

and show_taction = function
  | TAcreate -> "create"
  | TAalloc -> "alloc"
  | TAstore (p, v) -> "store" ^ parens (show_texpr p ^ ", " ^ show_texpr v)
  | TAload p -> "load" ^ parens (show_texpr p)
  | TAkill p -> "kill" ^ parens (show_texpr p)

let rec show_cond = function
  | Csym x -> Sym.show x
  | Cval v -> String_core.string_of_value v
  | Cop (bop, te1, te2) -> show_texpr te1 ^ show_binop bop ^ show_texpr te2
  | Cnot c -> "not " ^ parens (show_cond c)
  | Cmatch (pat, te) -> "match " ^ show_texpr te ^ " with " ^ show_pattern pat
  | Cis_scalar te -> "is_scalar " ^ parens (show_texpr te)
  | Cis_integer te -> "is_integer " ^ parens (show_texpr te)
  | Cis_signed te -> "is_signed " ^ parens (show_texpr te)
  | Cis_unsigned te -> "is_unsigned " ^ parens (show_texpr te)
  | Care_compatible (te1, te2) ->
    "are_compatible " ^ parens (show_texpr te1 ^ ", " ^ show_texpr te2)

let show_transfer =
  let cut s =
    if String.length s > 25 then
      String.sub s 0 25 ^ "..."
    else
      s
  in
  function
  | Tskip ->
    ""
  | Tcond c ->
    cut @@ show_cond c
  | Tassign (pat, te) ->
    cut @@ show_pattern pat ^ " = " ^ show_texpr te
  | Tcall (pat, te_f, tes) ->
    cut @@ show_pattern pat ^ " = CALL " ^
           show_texpr te_f  ^ parens (comma_list show_texpr tes)

(* Try to convert a Core pure expression in transfer node expressions
 * It fails if it contains a control flow branch *)
let rec texpr_of_pexpr (Pexpr (_, _, pe_)) =
  let open Monad.Option in
  let self = texpr_of_pexpr in
  let selfs pes =
    List.fold_left (fun acc pe ->
        acc >>= fun tes ->
        self pe >>= fun te ->
        return @@ te::tes
      ) (Some []) pes
    >>= fun rev_nes ->
    return @@ List.rev rev_nes
  in
  match pe_ with
  | PEsym x ->
    return @@ TEsym x
  | PEimpl c ->
    return @@ TEimpl c
  | PEval v ->
    return @@ TEval v
  | PEconstrained cs ->
    let (ivs, pes) = List.split cs in
    selfs pes >>= fun tes ->
    return @@ TEconstrained (List.combine ivs tes)
  | PEundef (loc, ub) ->
    return @@ TEundef (loc, ub)
  | PEerror (str, pe) ->
    self pe >>= fun te ->
    return @@ TEerror (str, te)
  | PEctor (ctor, pes) ->
    selfs pes >>= fun tes ->
    return @@ TEctor (ctor, tes)
  | PEcase _ ->
    None
  | PEarray_shift (pe1, cty, pe2) ->
    self pe1 >>= fun te1 ->
    self pe2 >>= fun te2 ->
    return @@ TEarray_shift (te1, cty, te2)
  | PEmember_shift (pe, ty, memb) ->
    self pe >>= fun te ->
    return @@ TEmember_shift (te, ty, memb)
  | PEnot pe ->
    self pe >>= fun te ->
    return @@ TEnot te
  | PEop (bop, pe1, pe2) ->
    self pe1 >>= fun te1 ->
    self pe2 >>= fun te2 ->
    return @@ TEop (bop, te1, te2)
  | PEstruct (ty, membs) ->
    let (cids, pes) = List.split membs in
    selfs pes >>= fun tes ->
    return @@ TEstruct (ty, List.combine cids tes)
  | PEunion (ty, memb, pe) ->
    self pe >>= fun te ->
    return @@ TEunion (ty, memb, te)
  | PEcfunction pe ->
    self pe >>= fun te ->
    return @@ TEcfunction te
  | PEmemberof (ty, memb, pe) ->
    self pe >>= fun te ->
    return @@ TEmemberof (ty, memb, te)
  | PEcall (name, pes) ->
    selfs pes >>= fun tes ->
    return @@ TEcall (name, tes)
  | PElet (_, _, _)
  | PEif _ ->
    None
  | PEis_scalar pe ->
    self pe >>= fun te ->
    return @@ TEis_scalar te
  | PEis_integer pe ->
    self pe >>= fun te ->
    return @@ TEis_integer te
  | PEis_signed pe ->
    self pe >>= fun te ->
    return @@ TEis_signed te
  | PEis_unsigned pe ->
    self pe >>= fun te ->
    return @@ TEis_unsigned te
  | PEbmc_assume _ ->
    (* NOTE: ignoring bmc_assumes *)
    return @@ TEval Vunit
  | PEare_compatible (pe1, pe2) ->
    self pe1 >>= fun te1 ->
    self pe2 >>= fun te2 ->
    return @@ TEare_compatible (te1, te2)

(* Try to convert a Core pure expression in a conditional *)
let rec cond_of_pexpr (Pexpr (_, _, pe_)) =
  let open Monad.Option in
  match pe_ with
  | PEsym x ->
    return @@ Csym x
  | PEimpl c ->
    assert false (* NOTE: not sure about this *)
  | PEval v ->
    return @@ Cval v
  | PEconstrained _ | PEundef _ | PEerror _ | PEctor _ ->
    assert false
  | PEcase _ ->
    None
  | PEarray_shift _ | PEmember_shift _ ->
    assert false
  | PEnot pe ->
    cond_of_pexpr pe >>= fun c ->
    return @@ Cnot c
  | PEop (bop, pe1, pe2) ->
    texpr_of_pexpr pe1 >>= fun te1 ->
    texpr_of_pexpr pe2 >>= fun te2 ->
    return @@ Cop (bop, te1, te2)
  | PEstruct _  | PEunion _ | PEcfunction _ | PEmemberof _ ->
    assert false
  | PEcall _ | PElet (_, _, _) | PEif _ ->
    None
  | PEis_scalar pe ->
    texpr_of_pexpr pe >>= fun te ->
    return @@ Cis_scalar te
  | PEis_integer pe ->
    texpr_of_pexpr pe >>= fun te ->
    return @@ Cis_integer te
  | PEis_signed pe ->
    texpr_of_pexpr pe >>= fun te ->
    return @@ Cis_signed te
  | PEis_unsigned pe ->
    texpr_of_pexpr pe >>= fun te ->
    return @@ Cis_unsigned te
  | PEbmc_assume _ ->
    (* NOTE: ignoring bmc_assumes *)
    return @@ Cval Vtrue
  | PEare_compatible (pe1, pe2) ->
    texpr_of_pexpr pe1 >>= fun te1 ->
    texpr_of_pexpr pe2 >>= fun te2 ->
    return @@ Care_compatible (te1, te2)

let new_symbol () =
  let sym = Symbol.fresh () in
  (sym, Pattern ([], CaseBase (Some sym, BTy_unit (* NOTE: type ignored *))))

(* It adds a pure expression to the control flow graph
 * NOTE: multiples nodes could be added if the pure expression contains
 * control flow branches
 * in_v = the input vertex
 * out_v = the output vertex
 * in_pat = the pattern that the pure expression should match to *)
let rec add_pe (in_v, out_v) in_pat (Pexpr (_, _, pe_) as pe) =
  let open GraphM in
  let self = add_pe in
  let add (v1, v2) t = add_edge (v1, v2) t >>= fun () -> return `OK in
  match texpr_of_pexpr pe with
  | Some te ->
    add (in_v, out_v) (Tassign (in_pat, te))
  | None ->
    match pe_ with
    | PEsym _ | PEimpl _ | PEval _ ->
      assert false
    | PEconstrained cs ->
      let (ivs, pes) = List.split cs in
      List.fold_left (fun acc pe ->
          let (sym, pat) = new_symbol () in
          acc >>= fun (syms, in_v) ->
          new_vertex >>= fun out_v ->
          self (in_v, out_v) pat pe >>= fun _ ->
          return (sym::syms, out_v)
        ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
      let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
      add (in_v, out_v) (Tassign (in_pat, TEconstrained (List.combine ivs tes)))
    | PEundef _ ->
      assert false
    | PEerror (str, pe) ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      add (mid_v, out_v) (Tassign (in_pat, TEerror (str, TEsym sym)))
    | PEctor (ctor, pes) ->
      List.fold_left (fun acc pe ->
          let (sym, pat) = new_symbol () in
          acc >>= fun (syms, in_v) ->
          new_vertex >>= fun out_v ->
          self (in_v, out_v) pat pe >>= fun _ ->
          return (sym::syms, out_v)
        ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
      let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
      add (in_v, out_v) (Tassign (in_pat, TEctor (ctor, tes)))
    | PEcase (pe, pat_pes) ->
      let te = match texpr_of_pexpr pe with
        | Some te -> te
        | None -> assert false
      in
      List.fold_left (fun acc (pat, pe_body) ->
          let cond = Cmatch (pat, te) in
          acc >>= fun in_v ->
          new_vertex >>= fun yes_v ->
          add (in_v, yes_v) (Tcond cond) >>= fun _ ->
          new_vertex >>= fun mid_v ->
          self (yes_v, mid_v) pat pe >>= fun _ ->
          self (mid_v, out_v) in_pat pe_body >>= fun _ ->
          new_vertex >>= fun no_v ->
          add (in_v, no_v) (Tcond (Cnot cond)) >>= fun _ ->
          return no_v
        ) (return in_v) pat_pes >>= fun _ ->
      return `OK
      (*
      mapM (fun (pat, pe_body) ->
          new_vertex >>= fun mid_v ->
          self (in_v, mid_v) pat pe >>= fun _ ->
          self (mid_v, out_v) in_pat pe_body
        ) pat_pes >>= fun _ ->
      return `OK
      *)
    | PEarray_shift (pe1, cty, pe2) ->
      let (sym1, pat1) = new_symbol () in
      let (sym2, pat2) = new_symbol () in
      new_vertex >>= fun v1 ->
      new_vertex >>= fun v2 ->
      self (in_v, v1) pat1 pe1 >>= fun _ ->
      self (v1, v2) pat2 pe2 >>= fun _ ->
      let te = TEarray_shift (TEsym sym1, cty, TEsym sym2) in
      add (v2, out_v) (Tassign (in_pat, te))
    | PEmember_shift (pe, x, cid) ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEmember_shift (TEsym sym, x, cid) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEnot pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEnot (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEop (bop, pe1, pe2) ->
      let (sym1, pat1) = new_symbol () in
      let (sym2, pat2) = new_symbol () in
      new_vertex >>= fun v1 ->
      new_vertex >>= fun v2 ->
      self (in_v, v1) pat1 pe1 >>= fun _ ->
      self (v1, v2) pat2 pe2 >>= fun _ ->
      let te = TEop (bop, TEsym sym1, TEsym sym2) in
      add (v2, out_v) (Tassign (in_pat, te))
    | PEstruct (x, cid_pes) ->
      let (cids, pes) = List.split cid_pes in
      List.fold_left (fun acc pe ->
          let (sym, pat) = new_symbol () in
          acc >>= fun (syms, in_v) ->
          new_vertex >>= fun out_v ->
          self (in_v, out_v) pat pe >>= fun _ ->
          return (sym:: syms, out_v)
        ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
      let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
      let te  = TEstruct (x, List.combine cids tes) in
      add (in_v, out_v) (Tassign (in_pat, te))
    | PEunion (x, cid, pe) ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEunion (x, cid, TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEcfunction pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEcfunction (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEmemberof (x, cid, pe) ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEmemberof (x, cid, TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEcall (name, pes) ->
      List.fold_left (fun acc pe ->
          let (sym, pat) = new_symbol () in
          acc >>= fun (syms, in_v) ->
          new_vertex >>= fun out_v ->
          self (in_v, out_v) pat pe >>= fun _ ->
          return (sym:: syms, out_v)
        ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
      let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
      let te  = TEcall (name, tes) in
      add (in_v, out_v) (Tassign (in_pat, te))
    | PElet (pat1, pe1, pe2) ->
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat1 pe1 >>= fun _ ->
      self (mid_v, out_v) in_pat pe2
    | PEif (pe1, pe2, pe3) ->
      begin match cond_of_pexpr pe1 with
        | Some cond ->
          return (in_v, cond)
        | None ->
          let (sym, pat) = new_symbol () in
          new_vertex >>= fun pe_v ->
          add_pe (in_v, pe_v) pat pe1 >>= fun _ ->
          return (pe_v, Csym sym)
      end >>= fun (in_v, cond) ->
      new_vertex >>= fun true_v ->
      add (in_v, true_v) (Tcond cond) >>= fun _ ->
      self (true_v, out_v) in_pat pe2 >>= fun _ ->
      new_vertex >>= fun false_v ->
      add (in_v, false_v) (Tcond (Cnot cond)) >>= fun _ ->
      self (false_v, out_v) in_pat pe3
    | PEis_scalar pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEis_scalar (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEis_integer pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEis_integer (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEis_signed pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEis_signed (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEis_unsigned pe ->
      let (sym, pat) = new_symbol () in
      new_vertex >>= fun mid_v ->
      self (in_v, mid_v) pat pe >>= fun _ ->
      let te = TEis_unsigned (TEsym sym) in
      add (mid_v, out_v) (Tassign (in_pat, te))
    | PEbmc_assume _ ->
      assert false
    | PEare_compatible (pe1, pe2) ->
      let (sym1, pat1) = new_symbol () in
      let (sym2, pat2) = new_symbol () in
      new_vertex >>= fun v1 ->
      new_vertex >>= fun v2 ->
      self (in_v, v1) pat1 pe1 >>= fun _ ->
      self (v1, v2) pat2 pe2 >>= fun _ ->
      let te = TEare_compatible (TEsym sym1, TEsym sym2) in
      add (v2, out_v) (Tassign (in_pat, te))

let add_action (in_v, out_v) in_pat (Action (_, _, act_)) =
  let open GraphM in
  let add (v1, v2) t = add_edge (v1, v2) t >>= fun () -> return `OK in
  match act_ with
  | Create _ ->
    add (in_v, out_v) (Tassign (in_pat, TEaction TAcreate))
  | CreateReadOnly _ ->
    add (in_v, out_v) (Tassign (in_pat, TEaction TAcreate))
  | Alloc0 _ ->
    add (in_v, out_v) (Tassign (in_pat, TEaction TAalloc))
  | Kill (_, pe) ->
    let te = match texpr_of_pexpr pe with
      | Some te -> te
      | None -> assert false
    in
    add (in_v, out_v) (Tassign (in_pat, TEaction (TAkill te)))
  | Store0 (_, _, pe_p, pe_v, _) ->
    let te_p, te_v = match texpr_of_pexpr pe_p, texpr_of_pexpr pe_v with
      | Some te_p, Some te_v -> te_p, te_v
      | _ -> assert false
    in
    add (in_v, out_v) (Tassign (in_pat, TEaction (TAstore (te_p, te_v))))
  | Load0 (_, pe, _) ->
    let te = match texpr_of_pexpr pe with
      | Some te -> te
      | None -> assert false
    in
    add (in_v, out_v) (Tassign (in_pat, TEaction (TAload te)))
  | _ -> assert false (* unsupported *)


(* It adds an expression to the control flow graph
 * in_v = the input vertex
 * out_v = the output vertex
 * in_pat = the pattern that the expression should match to
 * returns `OK if the control flow leaves at out_v
 * otherwise returns `NoOut *)
let rec add_e ~sequentialise (in_v, out_v) in_pat (Expr (_, e_)) =
  let open GraphM in
  let self = add_e ~sequentialise in
  let add (v1, v2) t = add_edge (v1, v2) t >>= fun () -> return `OK in
  match e_ with
  | Epure pe ->
    add_pe (in_v, out_v) in_pat pe
  | Ememop (memop, pes) ->
    List.fold_left (fun acc pe ->
        let (sym, pat) = new_symbol () in
        acc >>= fun (syms, in_v) ->
        new_vertex >>= fun out_v ->
        add_pe (in_v, out_v) pat pe >>= fun _ ->
        return (sym:: syms, out_v)
      ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
    let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
    let te  = TEmemop (memop, tes) in
    add (in_v, out_v) (Tassign (in_pat, te))
  | Eaction (Paction (_, act)) ->
    add_action (in_v, out_v) in_pat act
  | Ecase (pe, pat_es) ->
    let te = match texpr_of_pexpr pe with
      | Some te -> te
      | None -> assert false
    in
    List.fold_left (fun acc (pat, e_body) ->
        let cond = Cmatch (pat, te) in
        acc >>= fun in_v ->
        new_vertex >>= fun yes_v ->
        add (in_v, yes_v) (Tcond cond) >>= fun _ ->
        new_vertex >>= fun mid_v ->
        add_pe (yes_v, mid_v) pat pe >>= fun _ ->
        self (mid_v, out_v) in_pat e_body >>= fun _ ->
        new_vertex >>= fun no_v ->
        add (in_v, no_v) (Tcond (Cnot cond)) >>= fun _ ->
        return no_v
      ) (return in_v) pat_es >>= fun _ ->
    return `OK
        (*
    mapM (fun (pat, e) ->
        new_vertex >>= fun mid_v ->
        add_pe (in_v, mid_v) pat pe >>= fun _ ->
        self (mid_v, out_v) in_pat e
      ) pat_es >>= fun _ ->
    return `OK
           *)
  | Elet (pat1, pe1, e2) ->
    new_vertex >>= fun mid_v ->
    add_pe (in_v, mid_v) pat1 pe1 >>= fun _ ->
    self (mid_v, out_v) in_pat e2
  | Eif (pe1, e2, e3) ->
    begin match cond_of_pexpr pe1 with
      | Some cond ->
        return (in_v, cond)
      | None ->
        let (sym, pat) = new_symbol () in
        new_vertex >>= fun pe_v ->
        add_pe (in_v, pe_v) pat pe1 >>= fun _ ->
        return (pe_v, Csym sym)
    end >>= fun (in_v, cond) ->
    new_vertex >>= fun true_v ->
    add (in_v, true_v) (Tcond cond) >>= fun _ ->
    self (true_v, out_v) in_pat e2 >>= fun _ ->
    new_vertex >>= fun false_v ->
    add (in_v, false_v) (Tcond (Cnot cond)) >>= fun _ ->
    self (false_v, out_v) in_pat e3
  | Eskip ->
    add (in_v, out_v) Tskip
  | Eccall (_, _, pe_f, pes) ->
    let te_f =
      match texpr_of_pexpr pe_f with
      | Some te -> te
      | None -> assert false
    in
    List.fold_left (fun acc pe ->
        let (sym, pat) = new_symbol () in
        acc >>= fun (syms, in_v) ->
        new_vertex >>= fun out_v ->
        add_pe (in_v, out_v) pat pe >>= fun _ ->
        return (sym:: syms, out_v)
      ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
    let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
    add (in_v, out_v) (Tcall (in_pat, te_f, tes))
  | Eproc (_, name, pes) ->
    List.fold_left (fun acc pe ->
        let (sym, pat) = new_symbol () in
        acc >>= fun (syms, in_v) ->
        new_vertex >>= fun out_v ->
        add_pe (in_v, out_v) pat pe >>= fun _ ->
        return (sym::syms, out_v)
      ) (return ([], in_v)) pes >>= fun (rev_syms, in_v) ->
    let tes = List.map (fun sym -> TEsym sym) @@ List.rev rev_syms in
    let te  = TEcall (name, tes) in
    add (in_v, out_v) (Tassign (in_pat, te))
  | Eunseq es ->
    let pats =
      match in_pat with
      | Pattern (_, CaseCtor (Ctuple, pats)) -> pats
      | _ -> assert false
    in
    let pat_es = List.combine pats es in
    mapM (fun pat_es ->
        List.fold_left (fun acc (pat, e) ->
            acc >>= fun in_v ->
            new_vertex >>= fun out_v ->
            self (in_v, out_v) pat e >>= fun _ ->
            return out_v
          ) (return in_v) pat_es >>= fun mid_v ->
        add (mid_v, out_v) Tskip
      ) @@ (if sequentialise then [pat_es] else all_sequences pat_es) >>= fun _ ->
    return `OK
  | Ewseq (pat1, e1, e2)
  | Esseq (pat1, e1, e2) ->
    new_vertex >>= fun mid_v ->
    self (in_v, mid_v) pat1 e1 >>= begin function
      | `OK -> self (mid_v, out_v) in_pat e2
      | `NoOut -> return `NoOut
    end
  | Easeq _ ->
    (* TODO *)
    assert false
  | Eindet (_, e)
  | Ebound (_, e) ->
    (* NOTE: not sure about this *)
    self (in_v, out_v) in_pat e
  | Esave ((lab, _), params, e) ->
    get_label lab >>= begin function
      | Some (_, lab_v) -> return lab_v
      | None -> assert false (* previous pass should guarantee this *)
    end >>= fun lab_v ->
    List.fold_left (fun acc (sym, (_, pe)) ->
        (* NOTE: type in pattern is ignored *)
        let pat = Pattern ([], CaseBase (Some sym, BTy_unit)) in
        acc >>= fun (syms, in_v) ->
        new_vertex >>= fun out_v ->
        add_pe (in_v, out_v) pat pe >>= fun _ ->
        return (sym::syms, out_v)
      ) (return ([], in_v)) params >>= fun (rev_syms, mid_v) ->
    add (mid_v, lab_v) Tskip >>= fun _ ->
    self (lab_v, out_v) in_pat e
  | Erun (_, lab, pes) ->
    get_label lab >>= begin function
      | Some (syms, lab_v) -> return (syms, lab_v)
      | None -> assert false (* previous pass should guarantee this *)
    end >>= fun (syms, lab_v) ->
    List.fold_left (fun acc (sym,  pe) ->
        (* NOTE: type in pattern is ignored *)
        let pat = Pattern ([], CaseBase (Some sym, BTy_unit)) in
        acc >>= fun in_v ->
        new_vertex >>= fun out_v ->
        add_pe (in_v, out_v) pat pe >>= fun _ ->
        return out_v
      ) (return in_v) @@ List.combine syms pes >>= fun mid_v ->
    add (mid_v, lab_v) Tskip >>= fun _ ->
    return `NoOut
  | End es
  | Epar es ->
    mapM (self (in_v, out_v) in_pat) es >>= fun _ ->
    return `OK
  | Ewait _ ->
    (* NOTE: not sure about this *)
    add (in_v, out_v) Tskip

let rec collect_saves (Expr (_, e_)) =
  let open GraphM in
  let self = collect_saves in
  match e_ with
  | Epure _ | Ememop _ | Eaction _ ->
    return ()
  | Ecase (_, pat_es) ->
    mapM self (List.map snd pat_es) >>= fun _ ->
    return ()
  | Elet (_, _, e) ->
    self e
  | Eif (_, e2, e3) ->
    self e2 >>= fun _ -> self e3
  | Eskip | Eccall _ | Eproc (_, _, _) ->
    return ()
  | Eunseq es ->
    mapM self es >>= fun _ ->
    return ()
  | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
    self e1 >>= fun _ -> self e2
  | Easeq _ ->
    return ()
  | Eindet (_, e) | Ebound (_, e) ->
    self e
  | Esave ((lab, _), params, e) ->
    self e >>= fun _ ->
    new_vertex >>= fun lab_v ->
    add_label lab (List.map fst params, lab_v)
  | Erun _ ->
    return ()
  | End es | Epar es ->
    mapM self es >>= fun _ ->
    return ()
  | Ewait _ ->
    return ()

let mk_cfg_e ~sequentialise e =
  let open GraphM in
  let empty_pat = Pattern ([], CaseBase (None, BTy_unit)) in
  run (collect_saves e >>= fun _ ->
       new_vertex >>= fun in_v ->
       new_vertex >>= fun out_v ->
       set_init_vertex in_v >>= fun _ ->
       add_e ~sequentialise (in_v, out_v) empty_pat e >>= fun _ ->
       remove_isolated_vertices)

let dot_of_proc nm g =
  let pre = Sym.show nm in
  Pgraph.iter_vertex (fun v _ ->
        print_endline @@ pre ^ string_of_int v ^ "[label=\"" ^ string_of_int v ^ "\"]"
    ) g;
  Pgraph.iter_edge (fun _ (v1, tf, v2) ->
      print_endline @@
      pre ^ string_of_int v1 ^ " -> " ^ pre ^ string_of_int v2
      ^ "[label=\"" ^ show_transfer tf ^ "\"]"
    ) g

(* TODO: this is to test main for the moment *)
let mk_main ?(sequentialise=false) core =
  let main =
    match core.main with
    | Some main -> main
    | None -> assert false
  in
  match Pmap.lookup main core.funs with
  | Some (Proc (_, _, _, e)) ->
    mk_cfg_e ~sequentialise e
  | _ ->
    assert false

let mk_dot ?(sequentialise=false) core =
  print_endline "digraph G {";
  Pmap.iter (fun nm f ->
      match f with
      | Proc (_, _, _, e) ->
        dot_of_proc nm @@ snd @@ mk_cfg_e ~sequentialise e
      | _ -> ()
    ) core.funs;
  print_endline "}"

