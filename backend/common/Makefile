# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

all:
	ocamlbuild $(OB_FLAGS) libcommon.cmxa

clean:
	rm -rf _build