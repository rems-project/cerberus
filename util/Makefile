# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common
.PHONY:  clean

util: _build/src/util.cmxa

_build/src/util.cmxa: $(wildcard src/*.ml) $(wildcard src/*.mli)
	@echo $(BOLD)BUILDING Util$(RESET)
	@ocamlbuild $(OB_FLAGS) util.cma util.cmxa

clean:
	@rm -rf _build
