CPPO_ARGS=-D aspect_perms
LEMFLAGS=-only_changed_output -wl_unused_vars ign \
				 -wl_rename err -wl_comp_message ign -wl_pat_exh ign

LEMSRC:=\
	t_list_array.lem \
	t_fs_prelude.lem \
	t_fs_spec_properties.lem \
	t_fs_spec.lem \
	t_fs_spec_fs_command_properties.lem \
	t_fs_spec_properties_perms.lem \
	t_dir_heap.lem

.PHONY: cppo lem clean ocaml

all: build

build:
	mkdir build
	cp -vf *.{lem,lem_cppo,ml,mli,sed} Makefile build
	make -C build ocaml
	
cppo: $(wildcard *.lem_cppo) 
	(for f in *.lem_cppo; do cppo $(CPPO_ARGS) $$f -o $${f/.lem_cppo/.lem}; done)

lem: cppo $(wildcard *.lem)
	lem $(LEMFLAGS) -ocaml $(LEMSRC)
	echo `pwd`
	sed -i.bak -f patch_lem.sed t_fs_spec.ml
	sed -i.bak -f patch_prelude.sed t_fs_prelude.ml
	for f in t_*.ml; do cp $$f $${f/t_/}; sed -i.bak -f patch_gen_ml.sed $${f/t_/}; done
	touch _tags
	rm *.bak *.sed t_*.lem t_*.ml *.lem_cppo

ocaml: lem
	ocamlbuild -pkgs lem,sexplib fs_spec.native

clean:
	rm -rf build
