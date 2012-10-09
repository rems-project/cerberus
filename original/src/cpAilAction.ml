module A = CpAil
module AC = CpAilConstraint

type action =
  | Load  of A.ctype * AC.constant * AC.constant
  | Store of A.ctype * AC.constant * AC.constant
  | FnStore of A.ctype * AC.constant * AC.constant
  | Modify of A.ctype * AC.constant * AC.constant * AC.constant
  | Create of A.ctype * AC.constant
  | Kill of AC.constant
  | Same of AC.constant * AC.constant
  | Id of AC.constant
  | Call

type t = CpSymbol.t * action

let symbol_set = CpSymbol.make ()
let fresh () = CpSymbol.fresh symbol_set

let load  t addr v = fresh (), Load  (t, addr, v)
let store t addr v = fresh (), Store (t, addr, v)
let fn_store t addr v = fresh (), Store (t, addr, v)
let modify t addr l v = fresh (), Modify (t, addr, l, v)
let create t addr = fresh (), Create (t, addr)
let kill addr = fresh (), Kill addr
let same addr1 addr2 = fresh (), Same (addr1, addr2)
let id addr = fresh (), Id (addr)
let call () = fresh (), Call

let uid (a, _) = a

let is_call = function
  | _, Call -> true
  | _ -> false

let is_access = function
  | _, (Store _ | FnStore _ | Load _ | Modify _) -> true
  | _ -> false

let is_fn_store = function
  | _, FnStore _ -> true
  | _ -> false

module Print = struct
  module P = Pprint

  open P.Operators

  let pp_c = AC.Print.pp_constant
  let pp_t = CpAilPrint.pp_type
  let pp_s s = !^ (CpSymbol.to_string s)

  let pp_uid (uid, _) = pp_s uid

  let pp (uid, action) =
    let eq = (^^^) (pp_s uid ^^^ P.colon) in
    let (^%^) d1 d2 = d1 ^^ P.comma ^^^ d2 in
    match action with
    | Load (t, a, v) ->
        eq !^ "load"  ^^^ P.parens (pp_t t ^%^ pp_c a ^%^ pp_c v)
    | Store (t, a, v) ->
        eq !^ "store" ^^^ P.parens (pp_t t ^%^ pp_c a ^%^ pp_c v)
    | FnStore (t, a, v) ->
        eq !^ "store" ^^^ P.parens (pp_t t ^%^ pp_c a ^%^ pp_c v)
    | Modify (t, a, l, v) ->
        eq !^ "modify" ^^^ P.parens (pp_t t ^%^ pp_c a ^%^ pp_c l ^%^ pp_c v)
    | Create (t, a) ->
        eq !^ "create" ^^^ P.parens (pp_t t ^%^ pp_c a)
    | Kill a ->
        eq !^ "kill" ^^^ P.parens (pp_c a)
    | Same (a1, a2) ->
        eq !^ "same" ^^^ P.parens (pp_c a1 ^%^ pp_c a2)
    | Id a ->
        eq !^ "id" ^^^ P.parens (pp_c a)
    | Call -> eq !^ "call"

  let pp_latex a =
    let pp_c = AC.Print.pp_constant_latex in
    let pp_id (s, _) = !^ (CpSymbol.to_string_id s) in
    let pp_name (_, a) =
      match a with
      | Load _ -> !^ "Load"
      | Store _ -> !^ "Store"
      | FnStore _ -> !^ "Store"
      | Modify _ -> !^ "Modify"
      | Create _ -> !^ "Create"
      | Kill _ -> !^ "Kill"
      | Same _ -> !^ "Same"
      | Id _ -> !^ "Id"
      | Call -> !^ "Call" in
    let pp_args (_, a) =
      let tt d = !^ "\\\\cc" ^^ P.braces d in
      match a with
      | Load (t, a, v) -> [tt (pp_t t); pp_c a; pp_c v]
      | Store (t, a, v) -> [tt (pp_t t); pp_c a; pp_c v]
      | FnStore (t, a, v) -> [tt (pp_t t); pp_c a; pp_c v]
      | Modify (t, a, l, v) -> [tt (pp_t t); pp_c a; pp_c l; pp_c v]
      | Create (t, a) -> [tt (pp_t t); pp_c a]
      | Kill a -> [pp_c a]
      | Same (a1, a2) -> [pp_c a1; pp_c a2]
      | Id a -> [pp_c a]
      | Call -> [] in
    let pp_opts args =
      match args with
      | [] -> P.empty
      | _ -> P.parens (P.sepmap (P.comma ^^ P.space) (fun i -> i) args) in
    let context name id args =
      !^ "\\\\sem" ^^ P.braces name ^^ P.underscore ^^ P.braces id
      ^^^  pp_opts args in
    context (pp_name a) (pp_id a) (pp_args a)

  let pp_dot sb =
    let module S = BatSet in
    let sem_list = P.sep0map (P.semi ^^ P.break1) (fun i -> i) in
    let pre = !^
      "\\newcommand{\\sem}[1]{\\small{\\textsf{#1}}}\
       \\newcommand{\\cc}[1]{\\text{\\footnotesize\\ttfamily{#1}}}" in
    let style = !^ "node [shape=none]" in
    let context d =
      !^ "digraph G" ^^^ P.braces (
        sem_list ((!^ "d2tdocpreamble" ^^ P.equals ^^ P.dquotes pre)::style::d)
      ) in
    let arrow a1 a2 = pp_uid a1 ^^^ P.minus ^^ P.rangle ^^^ pp_uid a2 in
    let rd = CpTransitiveReduction.reduce sb in
    let s, d =
      S.fold
        (fun (a1, a2) (s, d) -> S.add a2 (S.add a1 s), (arrow a1 a2)::d)
        rd (S.empty, []) in
    let def a = pp_uid a ^^^ P.brackets (
      !^ "label" ^^ P.equals ^^ P.dquotes (pp_latex a)
    ) in
    let d = S.fold (fun a d -> def a::d) s d in
    context d    
end

let conflicts sb ts =
  let module S = BatSet in
  let address = function
    | _, Store (_, a, _)
    | _, FnStore (_, a, _)
    | _, Modify (_, a, _, _)
    | _, Load (_, a, _)
    | _, Id a -> a 
    | _ -> assert (false) in
  let filter_store a =
    match a with
    | _, FnStore _ | _, Store _ | _, Modify _ -> Some a
    | _ -> None in
  let filter_other a =
    match a with 
    | _, Load _ | _, Id _ -> Some a
    | _ -> None in
  let stores = S.filter_map filter_store ts in
  let other  = S.filter_map filter_other ts in
  let rec conflict rest c =
    if S.is_empty rest then
      c
    else
      let a, rest = S.pop rest in
      let unseq a' =
        not (S.mem (a, a') sb) && not (S.mem (a', a) sb) in
      let alias c a' =
        if unseq a' then
          AC.add c (AC.implies (AC.eq (address a) (address a')) AC.undef)
        else
          c in
      let c = S.fold (fun a' c -> alias c a') rest c in
      conflict rest (S.fold (fun a' c -> alias c a') other c) in
  conflict stores AC.empty

let unfold (_, a) = a

module Memory = struct
  module AT = CpAilTypes
  module P = AC.Process
  module M = BatMap
  module Array = CpArray.Growable

  type value =
    | Indeterminate
    | Value of AC.constant

  type obj =
    | Scalar of A.ctype * value
    | Array of A.ctype * value Array.t

  type mem = (CpSymbol.t, obj) M.t

  type t = {p : P.p; mem : mem}

  exception Undefined of t

  let address t const =
    let p, addr = P.address t.p const in
    {t with p = p}, addr

  let compare_size ct s =
    let module ATC = CpAilTypeConstraint in
    AC.compare_const s (ATC.size ct) = 0

  let is_valid t addr =
    match addr with
    | P.Base l -> M.mem l t.mem
    | P.Displaced (l, i, s) ->
        begin
          try
            let ct, length =
              match M.find l t.mem with
              | Scalar (ct, _) -> ct, 1 
              | Array(ct, vs) -> ct, (Array.size vs) in
            i >= 0 && i <= length && compare_size ct s
          with Not_found -> false
        end
    | P.NullAddress -> false

  let base_of = function
    | P.Base l -> l
    | P.Displaced (l, _, _) -> l

  let same_base t addr1 addr2 =
    base_of addr1 = base_of addr2 && is_valid t addr1 && is_valid t addr2

  let retrieve t addr =
    match addr with
    | P.Base l ->
        begin
          try
            M.find l t.mem
          with Not_found ->
            raise (Undefined t)
        end
    | P.Displaced (l, i, s) ->
        begin
          try
            M.find l t.mem
          with Not_found ->
            raise (Undefined t)
        end
    | P.NullAddress -> raise (Undefined t)

  let load_scalar t ct' v' ct v =
    let module ATC = CpAilTypeConstraint in
    if AT.compatible ct ct' then
      {t with p = P.conj t.p (AC.eq v v')}
    else if AT.is_unsigned_of ct' ct then
      let a, conv = ATC.conv_int ct v' in
      {t with p = P.conj (P.conj t.p conv) (AC.eq v a)}
    else if AT.is_signed_of ct' ct then
      let overflow = AC.implies (AC.neg (ATC.in_range ct v')) AC.undef in
      {t with p = P.conj (P.conj t.p (AC.eq v v')) overflow}
    else raise (Undefined t)

  let load_event t ct a v =
    let module ATC = CpAilTypeConstraint in
    let t, addr = address t a in
    try
      match (retrieve t addr) with
      | Scalar (_, Indeterminate) ->
          raise (print_endline "Indet."; Undefined t)
      | Scalar (ct', Value v') ->
          load_scalar t ct' v' ct v
      | Array (ct', vs') when AT.compatible ct' ct ->
          match addr with
          | P.Base _ ->
              begin
                match Array.get vs' 0 with
                | Value v' -> load_scalar t ct' v' ct v
                | Indeterminate -> raise (Undefined t)
              end
          | P.Displaced (_, i, s) ->
              let module ATC = CpAilTypeConstraint in
              if i >= 0 && i < Array.size vs' && compare_size ct' s then
                match Array.get vs' i with
                | Value v' -> load_scalar t ct' v' ct v
                | Indeterminate -> raise (Undefined t)
              else
                raise (Undefined t)
          | _ -> raise (Undefined t)
    with Not_found -> raise (Undefined t)

  let write_scalar t ct' ct v =
    let module ATC = CpAilTypeConstraint in
    if AT.compatible ct ct' then
      t, Value v
    else if AT.is_signed_of ct' ct then
      let a, conv = ATC.conv_int ct' v in
      {t with p = P.conj t.p conv}, Value a
    else if AT.is_unsigned_of ct' ct then
      let overflow = AC.implies (AC.neg (ATC.in_range ct' v)) AC.undef in
      {t with p = P.conj t.p overflow}, Value v
    else raise (Undefined t)

  let write_event t ct a v =
    let t, addr = address t a in
    try
      match (retrieve t addr) with
      | Scalar (ct', _) ->
          let t, v = write_scalar t ct' ct v in
          {t with mem = M.add (base_of addr) (Scalar (ct', v)) t.mem}
      | Array (ct', vs') when AT.compatible ct' ct ->
          match addr with
          | P.Base _ ->
              let t, v = write_scalar t ct' ct v in
              let vs = Array.set vs' 0 v in
              {t with mem = M.add (base_of addr) (Array (ct', vs)) t.mem}
          | P.Displaced (_, i, s) ->
              let module ATC = CpAilTypeConstraint in
              if i >= 0 && i < Array.size vs' && compare_size ct' s then
                let t, v = write_scalar t ct' ct v in
                let vs = Array.set vs' i v in
                {t with mem = M.add (base_of addr) (Array (ct', vs)) t.mem}
              else
                raise (Undefined t)
          | _ -> raise (Undefined t)
      | _ -> raise (Undefined t)
    with Not_found -> raise (Undefined t)

  let event t ((_, e) as a) =
(*    CpDocument.print (Print.pp a); print_endline "";*)
    match e with
    | Id a ->
        let t, addr = address t a in
        if is_valid t addr then t else raise (Undefined t)
    | Same (a1, a2) ->
        let t, addr1 = address t a1 in
        let t, addr2 = address t a2 in
        if same_base t addr1 addr2 then t else raise (Undefined t)
    | Create (ct, a) when AT.is_scalar ct ->
        let t, addr = address t a in
        {t with mem = M.add (base_of addr) (Scalar (ct, Indeterminate)) t.mem}
    | Create (ct, a) when AT.is_array ct ->
        let t, addr = address t a in
        let value = Array.create (AT.size_of_array ct) Indeterminate in
        let obj = Array (AT.base_of_array ct, value) in
        {t with mem = M.add (base_of addr) obj t.mem}
    | Kill a ->
        let t, addr = address t a in
        {t with mem = M.remove (base_of addr) t.mem}
    | Load  (ct, a, v) -> load_event t ct a v
    | Store (ct, a, v) -> write_event t ct a v
    | FnStore (ct, a, v) -> write_event t ct a v
    | Modify (ct, a, v, v') ->
        let t = load_event t ct a v in
        write_event t ct a v'
    | Call -> assert (false)

  let replay p es =
    try
      let t = List.fold_left event {p = p; mem = M.empty} es in
      P.complete t.p
    with Undefined t ->
      P.complete (print_endline "UNDEF"; P.conj t.p AC.undef)
end
