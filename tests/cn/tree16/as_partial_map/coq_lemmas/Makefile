all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn verify ../tree16.c --lemmata theories/Gen_Spec.v &> /dev/null
	make -f Makefile.coq
