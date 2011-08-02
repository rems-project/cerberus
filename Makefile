LEM=../lem/lem
LEM_LIB=../lem/library

BUILD_DIR=_build_ocaml

FILES=\
Pair.lem \
Map.lem \
Braun.lem \
Multiset.lem \
Lexing.lem \
Output.lem \
Location.lem \
Symbol.lem \
Global.lem \
Option.lem \
Transitive_reduction.lem \
State.lem \
Symbol_state.lem \
Exception.lem \
State_exception.lem \
Union_find.lem \
Congruence_closure.lem \
Pprint.lem \
Document.lem \
Symbol_table.lem \
Cabs.lem \
Ail.lem \
Types.lem \
Annotate.lem \
Cabs_to_ail.lem \
Ail_rewrite.lem \
Typing.lem \
Range.lem \
Constraint.lem \
Type_constraint.lem \
Action.lem \
Meaning.lem \
Reduction.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB) -print_types -ocaml $(foreach F, $(FILES), ../src/$(F))

clean:
	rm -R $(BUILD_DIR)
