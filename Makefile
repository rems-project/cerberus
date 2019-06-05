include Makefile.common

.PHONY: all default sibylfs concrete symbolic clean clear cerberus cerberus-concrete cerberus-bmc bmc cerberus-symbolic

cerberus: cerberus-concrete libc

all: cerberus-concrete cerberus-symbolic cerberus-bmc libc

sibylfs:
	@make -C sibylfs

concrete:
	@make -C memory/concrete

symbolic:
	@make -C memory/symbolic

libc:
	@make -C runtime/libc

_lib:
	@mkdir _lib

sibylfs/_build/sibylfs.cmxa: sibylfs

_lib/sibylfs/sibylfs.cmxa: _lib sibylfs/_build/sibylfs.cmxa
	@echo $(BOLD)INSTALLING SybilFS in ./_lib$(RESET)
	@mkdir -p _lib/sibylfs
	@cp sibylfs/META _lib/sibylfs/
	@cp sibylfs/_build/sibylfs.{a,cma,cmxa} _lib/sibylfs/
	@cp sibylfs/_build/generated/*.{cmi,cmx} _lib/sibylfs/

memory/concrete/_build/concrete.cmxa: concrete

_lib/concrete/concrete.cmxa: _lib/sibylfs/sibylfs.cmxa memory/concrete/_build/concrete.cmxa
	@echo $(BOLD)INSTALLING Concrete Memory Model in ./_lib$(RESET)
	@mkdir -p _lib/concrete
	@cp memory/concrete/META _lib/concrete/
	@cp memory/concrete/_build/src/concrete.{a,cma,cmxa} _lib/concrete
	@cp memory/concrete/_build/src/*.{cmi,cmx} _lib/concrete
	@cp memory/concrete/_build/ocaml_generated/*.{cmi,cmx} _lib/concrete
	@cp memory/concrete/_build/frontend/pprinters/*.{cmi,cmx} _lib/concrete
	@cp memory/concrete/_build/frontend/common/*.{cmi,cmx} _lib/concrete

memory/symbolic/_build/symbolic.cmxa: symbolic

_lib/symbolic/symbolic.cmxa: _lib/sibylfs/sibylfs.cmxa memory/symbolic/_build/symbolic.cmxa
	@echo $(BOLD)INSTALLING Symbolic Memory Model in ./_lib$(RESET)
	@mkdir -p _lib/symbolic
	@cp memory/symbolic/META _lib/symbolic/
	@cp memory/symbolic/_build/src/symbolic.{a,cma,cmxa} _lib/symbolic
	@cp memory/symbolic/_build/src/*.{cmi,cmx} _lib/symbolic
	@cp memory/symbolic/_build/ocaml_generated/*.{cmi,cmx} _lib/symbolic
	@cp memory/symbolic/_build/frontend/pprinters/*.{cmi,cmx} _lib/symbolic
	@cp memory/symbolic/_build/frontend/common/*.{cmi,cmx} _lib/symbolic

cerberus-concrete: _lib/concrete/concrete.cmxa
	@make -C backend/driver
	@cp backend/driver/cerberus cerberus

cerberus-symbolic: _lib/symbolic/symbolic.cmxa
	@make -C backend/symbolic-driver
	@cp backend/symbolic-driver/cerberus-symbolic cerberus-symbolic

cerberus-bmc: _lib/concrete/concrete.cmxa
	@make -C backend/bmc
	@cp backend/bmc/cerberus-bmc cerberus-bmc

bmc: cerberus-bmc

clean:
	@make -C sibylfs clean
	@make -C memory/concrete clean
	@make -C memory/symbolic clean
	@make -C backend/driver clean
	@make -C backend/bmc clean
	@make -C backend/symbolic-driver clean
	@rm -rf _lib

clear: clean
	@rm -rf cerberus cerberus-symbolic cerberus-bmc
