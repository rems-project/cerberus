


all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn verify --lemmata theories/Gen_Spec.v ../mutual_rec.c
	make -f Makefile.coq

