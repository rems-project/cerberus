open CoqEqDec
open MetatheoryAtom

type 'x coq_AssocList = (AtomImpl.atom*'x) list

(** val updateAddAL :
    'a1 coq_AssocList -> AtomImpl.atom -> 'a1 -> 'a1 coq_AssocList **)

let rec updateAddAL m i gv =
  match m with
    | [] -> (i,gv)::[]
    | p::m' ->
        let i',gv' = p in
        if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i i'
        then (i',gv)::m'
        else (i',gv')::(updateAddAL m' i gv)

(** val updateAL :
    'a1 coq_AssocList -> AtomImpl.atom -> 'a1 -> 'a1 coq_AssocList **)

let rec updateAL m i gv =
  match m with
    | [] -> []
    | p::m' ->
        let i',gv' = p in
        if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i i'
        then (i',gv)::m'
        else (i',gv')::(updateAL m' i gv)

(** val lookupAL : 'a1 coq_AssocList -> AtomImpl.atom -> 'a1 option **)

let rec lookupAL m i =
  match m with
    | [] -> None
    | p::m' ->
        let i',gv' = p in
        if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i i'
        then Some gv'
        else lookupAL m' i

(** val deleteAL :
    'a1 coq_AssocList -> AtomImpl.atom -> 'a1 coq_AssocList **)

let rec deleteAL m i =
  match m with
    | [] -> []
    | p::m' ->
        let id0,gv0 = p in
        if eq_dec (coq_EqDec_eq_of_EqDec coq_EqDec_atom) i id0
        then deleteAL m' i
        else (id0,gv0)::(deleteAL m' i)

(** val rollbackAL :
    'a1 coq_AssocList -> AtomImpl.atom -> 'a1 coq_AssocList -> 'a1
    coq_AssocList **)

let rollbackAL locals i lc0 =
  match lookupAL lc0 i with
    | Some gv0 -> updateAL locals i gv0
    | None -> deleteAL locals i

