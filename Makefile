include Makefile.common

.PHONY: all sibylfs concrete symbolic clean cerberus

all: cerberus libc

sibylfs:
	@make -C sibylfs

concrete:
	@make -C memory/concrete

symbolic:
	@make -C memory/symbolic

libc:
	@make -C runtime/libc

lib:
	@mkdir lib

sibylfs/_build/sibylfs.cmxa: sibylfs

lib/sibylfs/sibylfs.cmxa: lib sibylfs/_build/sibylfs.cmxa
	@echo $(BOLD)INSTALLING SybilFS in ./lib$(RESET)
	@mkdir -p lib/sibylfs
	@cp sibylfs/META lib/sibylfs/
	@cp sibylfs/_build/sibylfs.{a,cma,cmxa} lib/sibylfs/
	@cp sibylfs/_build/generated/*.{cmi,cmx} lib/sibylfs/

concrete/_build/concrete.cmxa: concrete

lib/concrete/concrete.cmxa: lib/sibylfs/sibylfs.cmxa concrete/_build/concrete.cmxa
	@echo $(BOLD)INSTALLING Concrete memory model$(RESET)
	@mkdir -p lib/concrete
	@cp memory/concrete/META lib/concrete/
	@cp memory/concrete/_build/concrete.{a,cma,cmxa} lib/concrete
	@cp memory/concrete/_build/ocaml_generated/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/frontend/pprinters/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/src/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/common/*.{cmi,cmx} lib/concrete

cerberus: lib/concrete/concrete.cmxa
	@make -C backend/driver
	@cp backend/driver/cerberus cerberus

clean:
	@make -C sibylfs clean
	@make -C memory/concrete clean
	@make -C backend/driver clean
	@rm -rf lib
