LEMFLAGS=-only_changed_output -wl_unused_vars ign \
				 -wl_rename err -wl_comp_message ign -wl_pat_exh ign

LEMSRC:=\
	list_array.lem \
	fs_prelude.lem \
	fs_spec.lem \
	dir_heap.lem \
	sibylfs.lem

generated:
	mkdir generated
	cp *.{ml,mli,lem,sed} Makefile generated/
	make -C generated lem

.PHONY: lem clean ocaml

lem: $(wildcard *.lem)
	lem $(LEMFLAGS) -ocaml $(LEMSRC)
	sed -i.bak -f patch_spec.sed fs_spec.ml
	sed -i.bak -f patch_prelude.sed fs_prelude.ml
	sed -i.bak -f patch_dir_heap.sed dir_heap.ml
	(for f in *.ml; do sed -i.bak -f patch_gen_ml.sed $$f; done)
	rm *.bak

ocaml:
	touch _tags
	ocamlbuild -pkgs lem,sexplib,sha fs_interface.native

clean:
	rm -rf generated
