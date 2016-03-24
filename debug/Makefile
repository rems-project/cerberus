OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
MENHIR=menhir

DIRS=../parsers/cparser ../pprinters
VPATH=../parsers/cparser:../pprinters

INCLUDES=$(foreach D, $(DIRS), -I $(D))

OCAMLFLAGS=$(INCLUDES)
OCAMLOPTFLAGS=$(INCLUDES)

MENHIRFLAGS=--external-tokens Tokens --strict --explain


GENERATED=Parser.ml




cparser: debug_cparser.cmo
	$(OCAMLC) -o debug_cparser $(OCAMLFLAGS) debug_cparser.cmo


.SUFFIXES: .ml .mli .mly .cmo .cmi .cmx


.mly.ml:
	$(MENHIR) $(MENHIRFLAGS) $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

.depend: $(GENERATED)
	rm -f .depend
	ocamldep $(INCLUDES) ../parsers/cparser/*.ml *.ml *.mli > .depend

include .depend
