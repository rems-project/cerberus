open Core


module Sym = Symbol
open Z3

(* ========== Type aliases ========== *)
type ksym = Sym.sym
type ksym_supply = ksym UniqueId.supply



(* ========== Debug ========== *)
let debug_print level str = 
  Debug_ocaml.print_debug level [] (fun () -> str)


(* ========== Pprinting ========== *)

let pp_to_stdout (doc: PPrint.document) =
  PPrint.ToChannel.pretty 1.0 150 (Pervasives.stdout) doc

let pp_to_string (doc: PPrint.document) : string =
  Pp_utils.to_plain_string doc

let pp_file (core_file: ('a, 'b) generic_file) =
  let doc = Pp_core.Basic.pp_file core_file in
  pp_to_stdout doc

(* ========== State monads ========== *)
module type Monad = sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val foldlM: ('a -> 'b -> 'b t) -> 'a list -> 'b -> 'b t
end

module State(St : sig type t end) = struct
  type 'a t =
    | State of (St.t -> 'a * St.t)

  let return x =
    State (fun st -> (x, st))
  let bind (State m) f =
    State (fun st ->
      let (a, st') = m st in
      let State mb = f a in
      mb st'
    )
  let (>>=) = bind
  
  let sequence ms =
    List.fold_right
      (fun m m' ->
        m  >>= fun x  ->
        m' >>= fun xs ->
        return (x::xs)
      ) ms (return [])
  
  let listM t xs = sequence (t xs)
  
  let mapM f xs =
     listM (List.map f) xs
  
  let rec foldlM f xs a =
    match xs with
      | [] ->
          return a
      | (x::xs') ->
          f x a >>= foldlM f xs'
 
  let runState (State m) st0 : ('a * 'st) =
    m st0
end


(* ========== Z3 aliases ========== *)
let mk_sym (ctx:context) = Symbol.mk_string ctx


(* ========== Core Symbols ========== *)
let symbol_to_int (Symbol(i, _): Sym.sym) : int = i

let sym_cmp = (Sym.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method)



let symbol_to_string (sym: ksym) =
  match sym with
  | Symbol (num, Some str) -> 
      ((string_of_int num) ^ "_" ^ str)
  | Symbol (num, None) ->
      ((string_of_int num) ^ "_" ^ "?")

let symbol_to_z3 (ctx: context) (sym: ksym) =
  mk_sym ctx (symbol_to_string sym)


let rec list_take k l = 
  if k > 0 then 
    match l with
    | [] -> assert false
    | x :: xs -> x :: (list_take (k-1) xs)
  else []
