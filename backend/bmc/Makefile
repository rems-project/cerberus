# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

.PHONY: cerberus-bmc clean

cerberus-bmc:
	@echo $(BOLD)BUILDING Cerberus-BMC$(RESET)
	@echo "(* Do not edit: automatically generated file *)" > main_.ml
	@sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ main.ml >> main_.ml
	@OCAMLPATH=$(CERB_PATH)/lib ocamlbuild $(OB_FLAGS) common/cerberus_cstubs.o
	@OCAMLPATH=$(CERB_PATH)/lib ocamlbuild $(OB_FLAGS) main_.native
	@cp -L main_.native cerberus-bmc

clean:
	@rm -rf _build main_.ml main_.native cerberus
