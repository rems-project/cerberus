


all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn --lemmata theories/Gen_Spec.v ../mutual_rec.c
	make -f Makefile.coq

