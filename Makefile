include Makefile.common

.PHONY: all default sibylfs util concrete symbolic clean-non-mem clean clear cerberus cerberus-concrete cerberus-bmc cerberus-ocaml ocaml bmc cerberus-symbolic web ui

cerberus: cerberus-concrete libc

all: cerberus-concrete cerberus-symbolic cerberus-bmc libc web

sibylfs:
	@make -C sibylfs

util:
	@make -C util

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
	@cp sibylfs/_build/sibylfs.a sibylfs/_build/sibylfs.cma sibylfs/_build/sibylfs.cmxa _lib/sibylfs/
	@cp sibylfs/_build/generated/*.cmi _lib/sibylfs/
	@cp sibylfs/_build/generated/*.cmx _lib/sibylfs/

util/_build/src/util.cmxa: util

_lib/util/util.cmxa: _lib util/_build/src/util.cmxa
	@echo $(BOLD)INSTALLING Util in ./_lib$(RESET)
	@mkdir -p _lib/util
	@cp util/META _lib/util/
	@cp util/_build/src/util.a util/_build/src/util.cma util/_build/src/util.cmxa _lib/util/
	@cp util/_build/src/*.cmi _lib/util/
	@cp util/_build/src/*.cmx _lib/util/

memory/concrete/_build/src/concrete.cmxa: concrete

_lib/concrete/concrete.cmxa: _lib/util/util.cmxa _lib/sibylfs/sibylfs.cmxa memory/concrete/_build/src/concrete.cmxa
	@echo $(BOLD)INSTALLING Concrete Memory Model in ./_lib$(RESET)
	@mkdir -p _lib/concrete
	@cp memory/concrete/META _lib/concrete/
	@cp memory/concrete/_build/src/concrete.a memory/concrete/_build/src/concrete.cma memory/concrete/_build/src/concrete.cmxa _lib/concrete
	@cp memory/concrete/_build/src/*.cmi _lib/concrete
	@cp memory/concrete/_build/src/*.cmx _lib/concrete
	@cp memory/concrete/_build/ocaml_generated/*.cmi _lib/concrete
	@cp memory/concrete/_build/ocaml_generated/*.cmx _lib/concrete
	@cp memory/concrete/_build/frontend/pprinters/*.cmi _lib/concrete
	@cp memory/concrete/_build/frontend/pprinters/*.cmx _lib/concrete
	@cp memory/concrete/_build/frontend/common/*.cmi _lib/concrete
	@cp memory/concrete/_build/frontend/common/*.cmx _lib/concrete

memory/symbolic/_build/src/symbolic.cmxa: symbolic

_lib/symbolic/symbolic.cmxa: _lib/util/util.cmxa _lib/sibylfs/sibylfs.cmxa memory/symbolic/_build/src/symbolic.cmxa
	@echo $(BOLD)INSTALLING Symbolic Memory Model in ./_lib$(RESET)
	@mkdir -p _lib/symbolic
	@cp memory/symbolic/META _lib/symbolic/
	@cp memory/symbolic/_build/src/symbolic.a memory/symbolic/_build/src/symbolic.cma memory/symbolic/_build/src/symbolic.cmxa _lib/symbolic
	@cp memory/symbolic/_build/src/*.cmi _lib/symbolic
	@cp memory/symbolic/_build/src/*.cmx _lib/symbolic
	@cp memory/symbolic/_build/ocaml_generated/*.cmi _lib/symbolic
	@cp memory/symbolic/_build/ocaml_generated/*.cmx _lib/symbolic
	@cp memory/symbolic/_build/frontend/pprinters/*.cmi _lib/symbolic
	@cp memory/symbolic/_build/frontend/pprinters/*.cmx _lib/symbolic
	@cp memory/symbolic/_build/frontend/common/*.cmi _lib/symbolic
	@cp memory/symbolic/_build/frontend/common/*.cmx _lib/symbolic

cerberus-concrete: _lib/concrete/concrete.cmxa
	@make -C backend/driver
	@cp backend/driver/cerberus cerberus

cerberus-symbolic: _lib/symbolic/symbolic.cmxa
	@make -C backend/symbolic
	@cp backend/symbolic/cerberus-symbolic cerberus-symbolic

cerberus-bmc: _lib/concrete/concrete.cmxa
	@make -C backend/bmc
	@cp backend/bmc/cerberus-bmc cerberus-bmc

bmc: cerberus-bmc

cerberus-ocaml: _lib/concrete/concrete.cmxa
	@make -C backend/ocaml
	@cp backend/ocaml/driver/cerberus-ocaml cerberus-ocaml
	@echo $(BOLD)INSTALLING Ocaml Runtime in ./_lib$(RESET)
	@mkdir -p _lib/rt-ocaml
	@cp backend/ocaml/runtime/META _lib/rt-ocaml
	@cp backend/ocaml/runtime/_build/rt_ocaml.a backend/ocaml/runtime/_build/rt_ocaml.cma backend/ocaml/runtime/_build/rt_ocaml.cmxa _lib/rt-ocaml
	@cp backend/ocaml/runtime/_build/*.cmi _lib/rt-ocaml
	@cp backend/ocaml/runtime/_build/*.cmx _lib/rt-ocaml
	@cp backend/ocaml/runtime/_build/src/*.cmi _lib/rt-ocaml
	@cp backend/ocaml/runtime/_build/src/*.cmx _lib/rt-ocaml

ocaml: cerberus-ocaml

cbuild: tools/cbuild.ml
	@echo $(BOLD)BUILDING cbuild$(RESET)
	@ocamlfind ocamlopt -o cbuild tools/cbuild.ml -linkpkg -package cmdliner,str,unix
	@rm -rf tools/cbuild.cmx tools/cbuild.cmi tools/cbuild.o

tmp:
	@mkdir -p tmp

config.json:
	@cp $(CERB_PATH)/tools/config.json $(CERB_PATH)

web: _lib/concrete/concrete.cmxa _lib/symbolic/symbolic.cmxa tmp config.json
	@make -C backend/web
	@cp -L backend/web/concrete/_build/src/instance.native webcerb.concrete
	@cp -L backend/web/symbolic/_build/src/instance.native webcerb.symbolic
	@cp -L backend/web/server/_build/web.native cerberus-webserver

ui:
	make -C public

clean-non-mem:
	@make -C backend/driver clean
	@make -C backend/bmc clean
	@make -C backend/symbolic clean
	@make -C backend/web clean
	@make -C backend/ocaml clean

clean:
	@make -C sibylfs clean
	@make -C util clean
	@make -C memory/concrete clean
	@make -C memory/symbolic clean
	@make -C backend/driver clean
	@make -C backend/bmc clean
	@make -C backend/symbolic clean
	@make -C backend/web clean
	@make -C backend/ocaml clean
	@rm -rf tools/*.cmi tools/*.cmx tools/*.o
	@rm -rf _lib

clear: clean
	@rm -rf cerberus cerberus-* webcerb.*
