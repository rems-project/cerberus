
set -ex
cn mutual_rec.c
cn --lemmata coq_lemmas/theories/Gen_Spec.v mutual_rec.c 
make -C coq_lemmas

