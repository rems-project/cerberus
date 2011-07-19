LEM=../lem/lem
LEM_LIB=../lem/library

BUILD_DIR=_build_ocaml

FILES=\
pair.lem \
map.lem \
list.lem \
multiset.lem \
lexing.lem \
location.lem \
symbol.lem \
global.lem \
option.lem \
state.lem \
symbol_state.lem \
exception.lem \
state_exception.lem \
symbol_table.lem \
cabs.lem \
ail.lem \
ail_types.lem \
ail_annotate.lem \
cabs_to_ail.lem \
ail_rewrite.lem \
ail_typing.lem \
range.lem \
constraint.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB) -print_types -ocaml $(foreach F, $(FILES), ../src/$(F))

clean:
	rm -R $(BUILD_DIR)
