LEM=../lem/lem
LEM_LIB=../lem/library

BUILD_DIR=_build_ocaml

FILES=\
list.lem \
success.lem \
result.lem \
multiset.lem \
option.lem \
lexing.lem \
location.lem \
symbol.lem \
global.lem \
symbol_table.lem \
cabs.lem \
ail.lem \
types.lem \
ail_annotate.lem \
cabs_to_ail.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB) -ocaml $(foreach F, $(FILES), ../src/$(F))