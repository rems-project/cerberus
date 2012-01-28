open BinInt
open BinPos
open Coqlib
open Datatypes
open List0
open Zdiv
open Zpower

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge

(** val comparison_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rect f f0 f1 f2 f3 f4 = function
  | Ceq -> f
  | Cne -> f0
  | Clt -> f1
  | Cle -> f2
  | Cgt -> f3
  | Cge -> f4

(** val comparison_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1 **)

let comparison_rec f f0 f1 f2 f3 f4 = function
  | Ceq -> f
  | Cne -> f0
  | Clt -> f1
  | Cle -> f2
  | Cgt -> f3
  | Cge -> f4

(** val negate_comparison : comparison -> comparison **)

let negate_comparison = function
  | Ceq -> Cne
  | Cne -> Ceq
  | Clt -> Cge
  | Cle -> Cgt
  | Cgt -> Cle
  | Cge -> Clt

(** val swap_comparison : comparison -> comparison **)

let swap_comparison = function
  | Clt -> Cgt
  | Cle -> Cge
  | Cgt -> Clt
  | Cge -> Cle
  | x -> x

module Int = 
 struct 
  (** val wordsize : nat -> nat **)
  
  let wordsize wordsize_one =
    S wordsize_one
  
  (** val modulus : nat -> coq_Z **)
  
  let modulus wordsize_one =
    two_power_nat (wordsize wordsize_one)
  
  (** val half_modulus : nat -> coq_Z **)
  
  let half_modulus wordsize_one =
    coq_Zdiv (modulus wordsize_one) (Zpos (Coq_xO Coq_xH))
  
  (** val max_unsigned : nat -> coq_Z **)
  
  let max_unsigned wordsize_one =
    coq_Zminus (modulus wordsize_one) (Zpos Coq_xH)
  
  (** val max_signed : nat -> coq_Z **)
  
  let max_signed wordsize_one =
    coq_Zminus (half_modulus wordsize_one) (Zpos Coq_xH)
  
  (** val min_signed : nat -> coq_Z **)
  
  let min_signed wordsize_one =
    coq_Zopp (half_modulus wordsize_one)
  
  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)
  
  (** val int_rect : nat -> (coq_Z -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rect wordsize_one f i =
    f i __
  
  (** val int_rec : nat -> (coq_Z -> __ -> 'a1) -> int -> 'a1 **)
  
  let int_rec wordsize_one f i =
    f i __
  
  (** val intval : nat -> int -> coq_Z **)
  
  let intval wordsize_one i =
    i
  
  (** val unsigned : nat -> int -> coq_Z **)
  
  let unsigned wordsize_one n =
    intval wordsize_one n
  
  (** val signed : nat -> int -> coq_Z **)
  
  let signed wordsize_one n =
    if zlt (unsigned wordsize_one n) (half_modulus wordsize_one)
    then unsigned wordsize_one n
    else coq_Zminus (unsigned wordsize_one n) (modulus wordsize_one)
  
  (** val repr : nat -> coq_Z -> int **)
  
  let repr wordsize_one x =
    coq_Zmod x (modulus wordsize_one)
  
  (** val zero : nat -> int **)
  
  let zero wordsize_one =
    repr wordsize_one Z0
  
  (** val one : nat -> int **)
  
  let one wordsize_one =
    repr wordsize_one (Zpos Coq_xH)
  
  (** val mone : nat -> int **)
  
  let mone wordsize_one =
    repr wordsize_one (Zneg Coq_xH)
  
  (** val iwordsize : nat -> int **)
  
  let iwordsize wordsize_one =
    repr wordsize_one (coq_Z_of_nat (wordsize wordsize_one))
  
  (** val eq_dec : nat -> int -> int -> bool **)
  
  let eq_dec wordsize_one x y =
    zeq x y
  
  (** val eq : nat -> int -> int -> bool **)
  
  let eq wordsize_one x y =
    if zeq (unsigned wordsize_one x) (unsigned wordsize_one y)
    then true
    else false
  
  (** val lt : nat -> int -> int -> bool **)
  
  let lt wordsize_one x y =
    if zlt (signed wordsize_one x) (signed wordsize_one y)
    then true
    else false
  
  (** val ltu : nat -> int -> int -> bool **)
  
  let ltu wordsize_one x y =
    if zlt (unsigned wordsize_one x) (unsigned wordsize_one y)
    then true
    else false
  
  (** val neg : nat -> int -> int **)
  
  let neg wordsize_one x =
    repr wordsize_one (coq_Zopp (unsigned wordsize_one x))
  
  (** val add : nat -> int -> int -> int **)
  
  let add wordsize_one x y =
    repr wordsize_one
      (coq_Zplus (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val sub : nat -> int -> int -> int **)
  
  let sub wordsize_one x y =
    repr wordsize_one
      (coq_Zminus (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val mul : nat -> int -> int -> int **)
  
  let mul wordsize_one x y =
    repr wordsize_one
      (coq_Zmult (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val coq_Zdiv_round : coq_Z -> coq_Z -> coq_Z **)
  
  let coq_Zdiv_round x y =
    if zlt x Z0
    then if zlt y Z0
         then coq_Zdiv (coq_Zopp x) (coq_Zopp y)
         else coq_Zopp (coq_Zdiv (coq_Zopp x) y)
    else if zlt y Z0
         then coq_Zopp (coq_Zdiv x (coq_Zopp y))
         else coq_Zdiv x y
  
  (** val coq_Zmod_round : coq_Z -> coq_Z -> coq_Z **)
  
  let coq_Zmod_round x y =
    coq_Zminus x (coq_Zmult (coq_Zdiv_round x y) y)
  
  (** val divs : nat -> int -> int -> int **)
  
  let divs wordsize_one x y =
    repr wordsize_one
      (coq_Zdiv_round (signed wordsize_one x) (signed wordsize_one y))
  
  (** val mods : nat -> int -> int -> int **)
  
  let mods wordsize_one x y =
    repr wordsize_one
      (coq_Zmod_round (signed wordsize_one x) (signed wordsize_one y))
  
  (** val divu : nat -> int -> int -> int **)
  
  let divu wordsize_one x y =
    repr wordsize_one
      (coq_Zdiv (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val modu : nat -> int -> int -> int **)
  
  let modu wordsize_one x y =
    repr wordsize_one
      (coq_Zmod (unsigned wordsize_one x) (unsigned wordsize_one y))
  
  (** val coq_Z_shift_add : bool -> coq_Z -> coq_Z **)
  
  let coq_Z_shift_add b x =
    if b
    then coq_Zplus (coq_Zmult (Zpos (Coq_xO Coq_xH)) x) (Zpos Coq_xH)
    else coq_Zmult (Zpos (Coq_xO Coq_xH)) x
  
  (** val coq_Z_bin_decomp : coq_Z -> bool*coq_Z **)
  
  let coq_Z_bin_decomp = function
    | Z0 -> false,Z0
    | Zpos p ->
        (match p with
           | Coq_xI q -> true,(Zpos q)
           | Coq_xO q -> false,(Zpos q)
           | Coq_xH -> true,Z0)
    | Zneg p ->
        (match p with
           | Coq_xI q -> true,(coq_Zminus (Zneg q) (Zpos Coq_xH))
           | Coq_xO q -> false,(Zneg q)
           | Coq_xH -> true,(Zneg Coq_xH))
  
  (** val bits_of_Z : nat -> coq_Z -> coq_Z -> bool **)
  
  let rec bits_of_Z n x =
    match n with
      | O -> (fun i -> false)
      | S m ->
          let b,y = coq_Z_bin_decomp x in
          let f = bits_of_Z m y in
          (fun i -> if zeq i Z0 then b else f (coq_Zminus i (Zpos Coq_xH)))
  
  (** val coq_Z_of_bits : nat -> (coq_Z -> bool) -> coq_Z -> coq_Z **)
  
  let rec coq_Z_of_bits n f i =
    match n with
      | O -> Z0
      | S m -> coq_Z_shift_add (f i) (coq_Z_of_bits m f (coq_Zsucc i))
  
  (** val bitwise_binop :
      nat -> (bool -> bool -> bool) -> int -> int -> int **)
  
  let bitwise_binop wordsize_one f x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let fy = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one y) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i -> f (fx i) (fy i)) Z0)
  
  (** val coq_and : nat -> int -> int -> int **)
  
  let coq_and wordsize_one x y =
    bitwise_binop wordsize_one (fun b1 b2 -> if b1 then b2 else false) x y
  
  (** val coq_or : nat -> int -> int -> int **)
  
  let coq_or wordsize_one x y =
    bitwise_binop wordsize_one (fun b1 b2 -> if b1 then true else b2) x y
  
  (** val xor : nat -> int -> int -> int **)
  
  let xor wordsize_one x y =
    bitwise_binop wordsize_one xorb x y
  
  (** val not : nat -> int -> int **)
  
  let not wordsize_one x =
    xor wordsize_one x (mone wordsize_one)
  
  (** val shl : nat -> int -> int -> int **)
  
  let shl wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) fx
        (coq_Zopp (unsigned wordsize_one y)))
  
  (** val shru : nat -> int -> int -> int **)
  
  let shru wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) fx (unsigned wordsize_one y))
  
  (** val shr : nat -> int -> int -> int **)
  
  let shr wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let sx = fun i ->
      fx
        (if zlt i (coq_Z_of_nat (wordsize wordsize_one))
         then i
         else coq_Zminus (coq_Z_of_nat (wordsize wordsize_one)) (Zpos Coq_xH))
    in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) sx (unsigned wordsize_one y))
  
  (** val shrx : nat -> int -> int -> int **)
  
  let shrx wordsize_one x y =
    divs wordsize_one x (shl wordsize_one (one wordsize_one) y)
  
  (** val shr_carry : nat -> int -> int -> int **)
  
  let shr_carry wordsize_one x y =
    sub wordsize_one (shrx wordsize_one x y) (shr wordsize_one x y)
  
  (** val rol : nat -> int -> int -> int **)
  
  let rol wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let rx = fun i -> fx (coq_Zmod i (coq_Z_of_nat (wordsize wordsize_one)))
    in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) rx
        (coq_Zopp (unsigned wordsize_one y)))
  
  (** val ror : nat -> int -> int -> int **)
  
  let ror wordsize_one x y =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    let rx = fun i -> fx (coq_Zmod i (coq_Z_of_nat (wordsize wordsize_one)))
    in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) rx (unsigned wordsize_one y))
  
  (** val rolm : nat -> int -> int -> int -> int **)
  
  let rolm wordsize_one x a m =
    coq_and wordsize_one (rol wordsize_one x a) m
  
  (** val zero_ext : nat -> coq_Z -> int -> int **)
  
  let zero_ext wordsize_one n x =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i ->
        if zlt i n then fx i else false) Z0)
  
  (** val sign_ext : nat -> coq_Z -> int -> int **)
  
  let sign_ext wordsize_one n x =
    let fx = bits_of_Z (wordsize wordsize_one) (unsigned wordsize_one x) in
    repr wordsize_one
      (coq_Z_of_bits (wordsize wordsize_one) (fun i ->
        if zlt i n then fx i else fx (coq_Zminus n (Zpos Coq_xH))) Z0)
  
  (** val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list **)
  
  let rec coq_Z_one_bits n x i =
    match n with
      | O -> []
      | S m ->
          let b,y = coq_Z_bin_decomp x in
          if b
          then i::(coq_Z_one_bits m y (coq_Zplus i (Zpos Coq_xH)))
          else coq_Z_one_bits m y (coq_Zplus i (Zpos Coq_xH))
  
  (** val one_bits : nat -> int -> int list **)
  
  let one_bits wordsize_one x =
    map (repr wordsize_one)
      (coq_Z_one_bits (wordsize wordsize_one) (unsigned wordsize_one x) Z0)
  
  (** val is_power2 : nat -> int -> int option **)
  
  let is_power2 wordsize_one x =
    match coq_Z_one_bits (wordsize wordsize_one) (unsigned wordsize_one x) Z0 with
      | [] -> None
      | i::l ->
          (match l with
             | [] -> Some (repr wordsize_one i)
             | z::l0 -> None)
  
  (** val cmp : nat -> comparison -> int -> int -> bool **)
  
  let cmp wordsize_one c x y =
    match c with
      | Ceq -> eq wordsize_one x y
      | Cne -> negb (eq wordsize_one x y)
      | Clt -> lt wordsize_one x y
      | Cle -> negb (lt wordsize_one y x)
      | Cgt -> lt wordsize_one y x
      | Cge -> negb (lt wordsize_one x y)
  
  (** val cmpu : nat -> comparison -> int -> int -> bool **)
  
  let cmpu wordsize_one c x y =
    match c with
      | Ceq -> eq wordsize_one x y
      | Cne -> negb (eq wordsize_one x y)
      | Clt -> ltu wordsize_one x y
      | Cle -> negb (ltu wordsize_one y x)
      | Cgt -> ltu wordsize_one y x
      | Cge -> negb (ltu wordsize_one x y)
  
  (** val notbool : nat -> int -> int **)
  
  let notbool wordsize_one x =
    if eq wordsize_one x (zero wordsize_one)
    then one wordsize_one
    else zero wordsize_one
  
  (** val powerserie : coq_Z list -> coq_Z **)
  
  let rec powerserie = function
    | [] -> Z0
    | x::xs -> coq_Zplus (two_p x) (powerserie xs)
  
  (** val int_of_one_bits : nat -> int list -> int **)
  
  let rec int_of_one_bits wordsize_one = function
    | [] -> zero wordsize_one
    | a::b ->
        add wordsize_one (shl wordsize_one (one wordsize_one) a)
          (int_of_one_bits wordsize_one b)
 end

