LEM=../lem/lem
LEM_LIB=../lem/library

BUILD_DIR=_build_ocaml

FILES=\
pair.lem \
map.lem \
list.lem \
success.lem \
multiset.lem \
lexing.lem \
location.lem \
symbol.lem \
global.lem \
option.lem \
state.lem \
reader.lem \
result.lem \
symbol_table.lem \
cabs.lem \
ail.lem \
types.lem \
ail_annotate.lem \
cabs_to_ail.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB) -print_types -ocaml $(foreach F, $(FILES), ../src/$(F))