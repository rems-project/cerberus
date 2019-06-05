# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

.PHONY: web clean

web:
	@OCAMLPATH=$(CERB_PATH)/_lib ocamlbuild $(OB_FLAGS) common/cerberus_cstubs.o
	@OCAMLPATH=$(CERB_PATH)/_lib ocamlbuild $(OB_FLAGS) web.native

clean:
	@rm -rf _build