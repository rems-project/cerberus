LEM_DIR=../lem
LEM=$(LEM_DIR)/lem
LEM_LIB=$(LEM_DIR)/library

OCAML_LIB=lib/ocaml

OCAML_BUILD_DIR=_build_ocaml

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

OCAML_LIB_FILES=\
pprint.lem \
output.lem \
document.lem

SPURIOUS_FILES=\
Pprint.ml \
Lexing.ml \
Document.ml

all: build_ocaml

build_ocaml: lem_ocaml
	rm -f $(foreach F, $(SPURIOUS_FILES), $(OCAML_BUILD_DIR)/$(F))
# Copy in Lem's OCaml library.
	cp lib/ocaml/*.ml lib/ocaml/*.mli $(OCAML_BUILD_DIR)
# Copy in our own OCaml libraries.
	cp $(LEM_DIR)/ocaml-lib/*.ml $(LEM_DIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)
# Working around the value restriction.
	sed -i 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/Multiset.ml
	sed -i 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/Transitive_reduction.ml
	sed -i 's/) emp /) (emp ()) /' $(OCAML_BUILD_DIR)/Multiset.ml
	sed -i "s/emp$$/(emp ())/" $(OCAML_BUILD_DIR)/Transitive_reduction.ml
# Open batteries to for List.take and List.drop.
	sed -i '1i open Batteries' $(OCAML_BUILD_DIR)/Braun.ml
# Fixing up OCaml syntax.
	sed -i 's/(if i1 <= i2 then True else False, p)/((if i1 <= i2 then True else False), p)/' $(OCAML_BUILD_DIR)/Constraint.ml
	sed -i 's/(if i1 <  i2 then True else False, p)/((if i1 <  i2 then True else False), p)/' $(OCAML_BUILD_DIR)/Constraint.ml
	sed -i 's/let sb = Set_.product/(let sb = Set_.product/' $(OCAML_BUILD_DIR)/Meaning.ml
	sed -i 's/d2.seq_before);/d2.seq_before));/' $(OCAML_BUILD_DIR)/Meaning.ml
	sed -i 's/let none/let none ()/' $(OCAML_BUILD_DIR)/Meaning.ml
	sed -i 's/M.none/M.none ()/' $(OCAML_BUILD_DIR)/Reduction.ml
	cd $(OCAML_BUILD_DIR); ocamlbuild -package batteries Reduction.cmo

lem_ocaml:
	mkdir -p $(OCAML_BUILD_DIR)
	cd $(OCAML_BUILD_DIR) && ../$(LEM) -lib ../$(LEM_LIB)  $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -ocaml $(foreach F, $(FILES), ../src/$(F)) && cd ..

clean:
	rm -R $(OCAML_BUILD_DIR)
