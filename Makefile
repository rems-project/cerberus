LEM=../lem/lem
LEM_LIB=../lem/library
OCAML_LIB=lib/ocaml
BUILD_DIR=_build_ocaml

FILES=\
Ord.lem \
Pair.lem \
Map_.lem \
List_.lem \
Set_.lem \
Braun.lem \
Multiset.lem \
Lexing.lem \
Output.lem \
Location.lem \
Symbol.lem \
Global.lem \
Option.lem \
Transitive_reduction.lem \
Exception.lem \
Program.lem \
State.lem \
Symbol_state.lem \
Symbol_state_program.lem \
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

OCAML_FILES=\
pprint.lem \
output.lem \
document.lem

all:
	mkdir -p $(BUILD_DIR)
	cd $(BUILD_DIR); ../$(LEM) -lib ../$(LEM_LIB)  $(foreach F, $(OCAML_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -ocaml $(foreach F, $(FILES), ../src/$(F))

clean:
	rm -R $(BUILD_DIR)
