all:
	coq_makefile -f _CoqProject -o Makefile.coq
	cn verify ../mutual_rec2.c --lemmata theories/Gen_Spec.v &> /dev/null
	make -f Makefile.coq
