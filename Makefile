LEM_DIR=../lem
LEM=$(LEM_DIR)/lem
LEM_LIB=$(LEM_DIR)/library

OCAML_LIB=lib/ocaml

OCAML_BUILD_DIR=_build_ocaml
TEX_BUILD_DIR=_build_tex
HOL_BUILD_DIR=_build_hol

FILES=\
multiset.lem \
global.lem \
ord.lem \
string_.lem \
num.lem \
pair.lem \
map_.lem \
list_.lem \
set_.lem \
braun.lem \
lexing.lem \
output.lem \
location.lem \
symbol.lem \
option.lem \
transitive_reduction.lem \
exception.lem \
program.lem \
state.lem \
symbol_state.lem \
symbol_state_program.lem \
state_exception.lem \
union_find.lem \
congruence_closure.lem \
pprint.lem \
document.lem \
symbol_table.lem \
cabs.lem \
ail.lem \
ail_rewrite.lem \
types.lem \
annotate.lem \
cabs_to_ail.lem \
typing.lem \
range.lem \
constraint.lem \
type_constraint.lem \
action.lem \
meaning.lem \
reduction.lem

OCAML_LIB_FILES=\
pprint.lem \
output.lem \
document.lem

SPURIOUS_FILES=\
pprint.ml \
lexing.ml \
document.ml

default: ocaml

all: ocaml tex

ocaml: lem_ocaml
	rm -f $(foreach F, $(SPURIOUS_FILES), $(OCAML_BUILD_DIR)/$(F))
# Copy in Lem's OCaml library.
	cp lib/ocaml/src/* $(OCAML_BUILD_DIR)
# Copy in our own OCaml libraries.
	cp $(LEM_DIR)/ocaml-lib/*.ml $(LEM_DIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)
# Compare in module Transitive_reduction.
	sed -i 's/Pervasives\.compare/cmp/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/let emp/let emp cmp/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i "s/emp$$/(emp cmp)/" $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/ add/ add cmp/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/reachable_set/reachable_set cmp/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/make/make cmp/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/let reduce/let reduce cmp cmp2/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/let x2 = Pset.from_list cmp/let x2 = Pset.from_list cmp2/' $(OCAML_BUILD_DIR)/transitive_reduction.ml
	sed -i 's/reduce/reduce compare_int compare_pair_int/' $(OCAML_BUILD_DIR)/action.ml
# Working around the value restriction.
	sed -i 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/multiset.ml
	sed -i 's/) emp /) (emp ()) /' $(OCAML_BUILD_DIR)/multiset.ml
	sed -i 's/Multiset.emp/Multiset.emp ()/' $(OCAML_BUILD_DIR)/cparser.mly
# Open batteries to for List.take, List.drop, list.split_at.
	sed -i 's/List\.take/BatList.take/' $(OCAML_BUILD_DIR)/braun.ml
	sed -i 's/List\.drop/BatList.drop/' $(OCAML_BUILD_DIR)/braun.ml
	sed -i 's/List\.split_at/BatList.split_at/' $(OCAML_BUILD_DIR)/braun.ml
# Fixing up OCaml syntax.
	sed -i 's/(if i1 <= i2 then True else False, p)/((if i1 <= i2 then True else False), p)/' $(OCAML_BUILD_DIR)/constraint.ml
	sed -i 's/(if i1 <  i2 then True else False, p)/((if i1 <  i2 then True else False), p)/' $(OCAML_BUILD_DIR)/constraint.ml
#	sed -i 's/let sb = Set_.product/(let sb = Set_.product/' $(OCAML_BUILD_DIR)/meaning.ml
	sed -i 's/let sb = action_set_/(let sb = action_set_/' $(OCAML_BUILD_DIR)/meaning.ml
	sed -i 's/d2.seq_before);/d2.seq_before));/' $(OCAML_BUILD_DIR)/meaning.ml
	sed -i 's/let null/let null ()/' $(OCAML_BUILD_DIR)/meaning.ml
	sed -i 's/M.null/M.null ()/' $(OCAML_BUILD_DIR)/reduction.ml
# Removing module references introduced by Lem hack
	sed -i 's/Action\.compare_int/compare_int/g' $(OCAML_BUILD_DIR)/action.ml
	sed -i 's/Action\.ne/ne/g' $(OCAML_BUILD_DIR)/action.ml
	sed -i 's/Meaning\.compare_int/compare_int/g' $(OCAML_BUILD_DIR)/meaning.ml
	sed -i 's/Constraint\.compare_constr_int/compare_constr_int/g' $(OCAML_BUILD_DIR)/constraint.ml
# Write _tags
	echo "true: annot, debug" > $(OCAML_BUILD_DIR)/_tags
	cd $(OCAML_BUILD_DIR); ocamlbuild -use-menhir -tag annot -tag debug -package text -package batteries main.byte

lem_ocaml:
	mkdir -p $(OCAML_BUILD_DIR)
	cd $(OCAML_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -ocaml $(foreach F, $(FILES), ../src/$(F)) && cd ..

tex: lem_tex
	cp $(LEM_DIR)/tex-lib/lem.sty $(TEX_BUILD_DIR)

lem_tex:
	mkdir -p $(TEX_BUILD_DIR)
	cd $(TEX_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -tex $(foreach F, $(FILES), ../src/$(F)) && cd ..


hol: lem_hol

lem_hol:
	mkdir -p $(HOL_BUILD_DIR)
	cd $(HOL_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -hol $(foreach F, $(FILES), ../src/$(F)) && cd ..

clean:
	rm -R $(OCAML_BUILD_DIR)
	rm -R $(TEX_BUILD_DIR)
	rm -R $(HOL_BUILD_DIR)
