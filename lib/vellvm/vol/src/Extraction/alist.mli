open CoqEqDec
open MetatheoryAtom

type 'x coq_AssocList = (AtomImpl.atom*'x) list

val updateAddAL :
  'a1 coq_AssocList -> AtomImpl.atom -> 'a1 -> 'a1 coq_AssocList

val updateAL : 'a1 coq_AssocList -> AtomImpl.atom -> 'a1 -> 'a1 coq_AssocList

val lookupAL : 'a1 coq_AssocList -> AtomImpl.atom -> 'a1 option

val deleteAL : 'a1 coq_AssocList -> AtomImpl.atom -> 'a1 coq_AssocList

val rollbackAL :
  'a1 coq_AssocList -> AtomImpl.atom -> 'a1 coq_AssocList -> 'a1
  coq_AssocList

