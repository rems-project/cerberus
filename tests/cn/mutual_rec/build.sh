
set -ex
cn verify mutual_rec.c
cn verify --lemmata coq_lemmas/theories/Gen_Spec.v mutual_rec.c 
make -C coq_lemmas

