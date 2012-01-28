open Compare_dec
open Datatypes
open Peano

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val mbind : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let mbind f = function
  | Some x -> f x
  | None -> None

(** val mif : bool -> 'a1 option -> 'a1 option -> 'a1 option **)

let mif c tclause fclause =
  if c then tclause else fclause

(** val mswitch : (bool*'a1 option) list -> 'a1 option -> 'a1 option **)

let rec mswitch cases default_case =
  match cases with
    | [] -> default_case
    | p::cases' ->
        let b,action = p in if b then action else mswitch cases' default_case

(** val mfor : 'a1 list -> ('a1 -> __ option) -> __ option **)

let rec mfor li f =
  match li with
    | [] -> Some __
    | i::li' -> (match f i with
                   | Some _ -> mfor li' f
                   | None -> None)

type coq_Range = { coq_Range_b : nat; coq_Range_e : nat; coq_Range_d : nat }

(** val coq_Range_rect :
    (nat -> nat -> nat -> __ -> 'a1) -> coq_Range -> 'a1 **)

let coq_Range_rect f r =
  let { coq_Range_b = x; coq_Range_e = x0; coq_Range_d = x1 } = r in
  f x x0 x1 __

(** val coq_Range_rec :
    (nat -> nat -> nat -> __ -> 'a1) -> coq_Range -> 'a1 **)

let coq_Range_rec f r =
  let { coq_Range_b = x; coq_Range_e = x0; coq_Range_d = x1 } = r in
  f x x0 x1 __

(** val coq_Range_b : coq_Range -> nat **)

let coq_Range_b x = x.coq_Range_b

(** val coq_Range_e : coq_Range -> nat **)

let coq_Range_e x = x.coq_Range_e

(** val coq_Range_d : coq_Range -> nat **)

let coq_Range_d x = x.coq_Range_d

(** val _range2list_F : (coq_Range -> nat list) -> coq_Range -> nat list **)

let _range2list_F _range2list0 i =
  let { coq_Range_b = b; coq_Range_e = e; coq_Range_d = d } = i in
  if le_lt_dec e b
  then []
  else b::(_range2list0 { coq_Range_b = (plus b (S O)); coq_Range_e = e;
            coq_Range_d = d })

(** val _range2list_terminate : coq_Range -> nat list **)

let rec _range2list_terminate i =
  let { coq_Range_b = b; coq_Range_e = e; coq_Range_d = d } = i in
  if le_lt_dec e b
  then []
  else b::(Obj.magic
            (_range2list_terminate { coq_Range_b = 
              (plus b (S O)); coq_Range_e = e; coq_Range_d = d }))

(** val _range2list : coq_Range -> nat list **)

let _range2list x =
  _range2list_terminate x

type coq_R__range2list =
  | R__range2list_0 of coq_Range * nat * nat * nat
  | R__range2list_1 of coq_Range * nat * nat * nat * 
     nat list * coq_R__range2list

(** val coq_R__range2list_rect :
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> nat list ->
    coq_R__range2list -> 'a1 -> 'a1) -> coq_Range -> nat list ->
    coq_R__range2list -> 'a1 **)

let rec coq_R__range2list_rect f f0 i l = function
  | R__range2list_0 (i0, b, e, d) -> f i0 b e d __ __ __ __
  | R__range2list_1 (i0, b, e, d, res, r0) ->
      f0 i0 b e d __ __ __ __ res r0
        (coq_R__range2list_rect f f0 { coq_Range_b = 
          (plus b (S O)); coq_Range_e = e; coq_Range_d = d } res r0)

(** val coq_R__range2list_rec :
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> nat list ->
    coq_R__range2list -> 'a1 -> 'a1) -> coq_Range -> nat list ->
    coq_R__range2list -> 'a1 **)

let rec coq_R__range2list_rec f f0 i l = function
  | R__range2list_0 (i0, b, e, d) -> f i0 b e d __ __ __ __
  | R__range2list_1 (i0, b, e, d, res, r0) ->
      f0 i0 b e d __ __ __ __ res r0
        (coq_R__range2list_rec f f0 { coq_Range_b = 
          (plus b (S O)); coq_Range_e = e; coq_Range_d = d } res r0)

(** val _range2list_rect :
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) ->
    coq_Range -> 'a1 **)

let rec _range2list_rect f f0 i =
  let f1 = f0 i in
  let f2 = f i in
  let { coq_Range_b = range_b0; coq_Range_e = range_e0; coq_Range_d =
    range_d0 } = i
  in
  let f3 = f2 range_b0 range_e0 range_d0 __ __ in
  let f4 = f1 range_b0 range_e0 range_d0 __ __ in
  if le_lt_dec range_e0 range_b0
  then f3 __ __
  else let f5 = f4 __ __ in
       let hrec =
         _range2list_rect f f0 { coq_Range_b = (plus range_b0 (S O));
           coq_Range_e = range_e0; coq_Range_d = range_d0 }
       in
       f5 hrec

(** val _range2list_rec :
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1) ->
    (coq_Range -> nat -> nat -> nat -> __ -> __ -> __ -> __ -> 'a1 -> 'a1) ->
    coq_Range -> 'a1 **)

let _range2list_rec =
  _range2list_rect

(** val coq_R__range2list_correct :
    coq_Range -> nat list -> coq_R__range2list **)

let coq_R__range2list_correct x res =
  _range2list_rect (fun y y0 y1 y2 _ _ _ _ z _ -> R__range2list_0 (y, y0, y1,
    y2)) (fun y y0 y1 y2 _ _ _ _ y7 z _ -> R__range2list_1 (y, y0, y1, y2,
    (_range2list { coq_Range_b = (plus y0 (S O)); coq_Range_e = y1;
      coq_Range_d = y2 }),
    (y7
      (_range2list { coq_Range_b = (plus y0 (S O)); coq_Range_e = y1;
        coq_Range_d = y2 }) __))) x res __

(** val range2list_1 : nat -> nat -> nat list **)

let range2list_1 b e =
  _range2list { coq_Range_b = b; coq_Range_e = e; coq_Range_d = (S O) }

(** val mifk :
    bool -> 'a1 option -> 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let mifk c tclause fclause con =
  if c then mbind con tclause else mbind con fclause

(** val mswitchk :
    (bool*'a1 option) list -> 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let rec mswitchk cases default_case con =
  match cases with
    | [] -> mbind con default_case
    | p::cases' ->
        let b,action = p in
        if b then mbind con action else mswitchk cases' default_case con

(** val mmap : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let mmap f x =
  mbind (fun x0 -> Some (f x0)) x

(** val mjoin : 'a1 option option -> 'a1 option **)

let mjoin x =
  mbind (fun x0 -> x0) x

(** val mlift : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let mlift f =
  mbind (fun u -> Some (f u))

(** val mlift2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option **)

let mlift2 f a b =
  mbind (fun x -> mbind (fun y -> Some (f x y)) b) a

(** val mlift3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 option -> 'a2 option -> 'a3 option ->
    'a4 option **)

let mlift3 f a b c =
  mbind (fun x -> mbind (fun y -> mbind (fun z -> Some (f x y z)) c) b) a

