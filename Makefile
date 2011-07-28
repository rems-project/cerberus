LEM=../lem/lem
LEM_LIB=../lem/library

BUILD_DIR=_build_ocaml

FILES=\
pair.lem \
map.lem \
list.lem \
set.lem \
braun.lem \
multiset.lem \
lexing.lem \
output.lem \
location.lem \
symbol.lem \
global.lem \
option.lem \
transitive_reduction.lem \
state.lem \
symbol_state.lem \
exception.lem \
state_exception.lem \
union_find.lem \
congruence_closure.lem \
pprint.lem \
document.lem \
symbol_table.lem \
cabs.lem \
ail.lem \
types.lem \
annotate.lem \
cabs_to_ail.lem \
ail_rewrite.lem \
typing.lem \
range.lem \
constraint.lem \
type_constraint.lem \
action.lem \
meaning.lem \
reduction.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB) -print_types -ocaml $(foreach F, $(FILES), ../src/$(F))

clean:
	rm -R $(BUILD_DIR)
