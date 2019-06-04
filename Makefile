include Makefile.common

.PHONY: all default sibylfs concrete symbolic clean clear \
	cerberus cerberus-bmc bmc cerberus-symbolic

default: cerberus libc

all: cerberus cerberus-symbolic cerberus-bmc

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

memory/concrete/_build/concrete.cmxa: concrete

lib/concrete/concrete.cmxa: lib/sibylfs/sibylfs.cmxa memory/concrete/_build/concrete.cmxa
	@echo $(BOLD)INSTALLING Concrete Memory Model$(RESET)
	@mkdir -p lib/concrete
	@cp memory/concrete/META lib/concrete/
	@cp memory/concrete/_build/src/concrete.{a,cma,cmxa} lib/concrete
	@cp memory/concrete/_build/src/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/ocaml_generated/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/frontend/pprinters/*.{cmi,cmx} lib/concrete
	@cp memory/concrete/_build/frontend/common/*.{cmi,cmx} lib/concrete

memory/symbolic/_build/symbolic.cmxa: symbolic

lib/symbolic/symbolic.cmxa: lib/sibylfs/sibylfs.cmxa memory/symbolic/_build/symbolic.cmxa
	@echo $(BOLD)INSTALLING Symbolic Memory Model$(RESET)
	@mkdir -p lib/symbolic
	@cp memory/symbolic/META lib/symbolic/
	@cp memory/symbolic/_build/src/symbolic.{a,cma,cmxa} lib/symbolic
	@cp memory/symbolic/_build/src/*.{cmi,cmx} lib/symbolic
	@cp memory/symbolic/_build/ocaml_generated/*.{cmi,cmx} lib/symbolic
	@cp memory/symbolic/_build/frontend/pprinters/*.{cmi,cmx} lib/symbolic
	@cp memory/symbolic/_build/frontend/common/*.{cmi,cmx} lib/symbolic

cerberus-bmc: lib/concrete/concrete.cmxa
	@make -C backend/driver
	@cp backend/driver/cerberus cerberus

bmc: cerberus-bmc

cerberus-symbolic: lib/symbolic/symbolic.cmxa
	@make -C backend/symbolic-driver
	@cp backend/symbolic-driver/cerberus-symbolic cerberus-symbolic

bmc: lib/concrete/concrete.cmxa
	@make -C backend/bmc
	@cp backend/bmc/cerberus-bmc cerberus-bmc

clean:
	@make -C sibylfs clean
	@make -C memory/concrete clean
	@make -C memory/symbolic clean
	@make -C backend/driver clean
	@make -C backend/bmc clean
	@make -C backend/symbolic-driver clean
	@rm -rf lib

clear: clean
	@rm -rf cerberus cerberus-symbolic cerberus-bmc
