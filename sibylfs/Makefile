# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

LEMFLAGS=-only_changed_output -wl_unused_vars ign \
				 -wl_rename err -wl_comp_message ign -wl_pat_exh ign

LEMSRC:=\
	list_array.lem \
	fs_prelude.lem \
	fs_spec.lem \
	dir_heap.lem \
	sibylfs.lem

.PHONY:  clean sibylfs

sibylfs: generated _build/sibylfs.cmxa

generated: $(wildcard src/*.lem) $(wildcard src/*.ml) $(wildcard src/*.mli)
	@echo $(BOLD)LEM SybilFS$(RESET)
	@mkdir -p generated
	@cp src/*.{ml,mli,lem} generated/
	@cp *.sed generated/
	@cp Makefile generated/
	@cp sibylfs.mllib generated/
	@cd generated; lem $(LEMFLAGS) -ocaml $(LEMSRC)
	@sed -i.bak -f patch_spec.sed generated/fs_spec.ml
	@sed -i.bak -f patch_prelude.sed generated/fs_prelude.ml
	@sed -i.bak -f patch_dir_heap.sed generated/dir_heap.ml
	@(for f in generated/*.ml; do sed -i.bak -f patch_gen_ml.sed $$f; done)
	@rm generated/*.bak

_build/sibylfs.cmxa: generated
	@echo $(BOLD)BUILDING SybilFS$(RESET)
	@ocamlbuild $(OB_FLAGS) sibylfs.cma sibylfs.cmxa

clean:
	@rm -rf generated
	@rm -rf _build
