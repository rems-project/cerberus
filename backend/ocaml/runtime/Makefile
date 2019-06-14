# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

.PHONY: rt-ocaml clean

rt-ocaml: coreStd.ml _build/rt_ocaml.cmxa

coreStd.ml: ../driver/cerberus-ocaml
	@echo $(BOLD)BUILDING Core stdlib$(RESET)
	@../driver/cerberus-ocaml --nolibc --ocaml-corestd

_build/rt_ocaml.cmxa: $(wildcard src/*.ml) $(wildcard src/*.mli) $(wildcard *.ml)
	@OCAMLPATH=$(CERB_PATH)/_lib ocamlbuild $(OB_FLAGS) rt_ocaml.cma rt_ocaml.cmxa

clean:
	@rm -rf _build coreStd.ml
