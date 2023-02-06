


all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn --lemmata theories/Gen_Spec.v ../tree16.c
	make -f Makefile.coq

