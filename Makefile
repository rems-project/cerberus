LEM_DIR=../lem
LEM=$(LEM_DIR)/lem
LEM_LIB=$(LEM_DIR)/library

OCAML_LIB=lib/ocaml

OCAML_BUILD_DIR=_build_ocaml
TEX_BUILD_DIR=_build_tex
HOL_BUILD_DIR=_build_hol
COQ_BUILD_DIR=_build_coq

OCAMLBUILD=ocamlbuild -use-menhir -tag annot -tag debug -package text

FILES=\
boot.lem \
type_error.lem \
multiset.lem \
global.lem \
ord.lem \
string_.lem \
pair.lem \
map_.lem \
list_.lem \
lexing.lem \
output.lem \
location.lem \
symbol.lem \
option.lem \
exception.lem \
state.lem \
symbol_state.lem \
state_exception.lem \
pprint.lem \
document.lem \
symbol_table.lem \
cabs_parser.lem \
cabs.lem \
ail.lem \
ail_aux.lem \
ail_rewrite.lem \
core.lem \
errors.lem \
core_typing.lem \
core_indet.lem \
types.lem \
memory.lem \
core_run.lem \
sb.lem \
annotate.lem \
cabs_transform.lem \
cabs_to_ail.lem \
typing.lem \
range.lem \
translation.lem

COQ_FILES=

OCAML_LIB_FILES=\
boot.lem \
pprint.lem \
output.lem \
document.lem

SPURIOUS_FILES=\
pprint.ml \
lexing.ml \
document.ml

default: ocaml_byte

all: ocaml tex

tex: lem_tex
	cp $(LEM_DIR)/tex-lib/lem.sty $(TEX_BUILD_DIR)

hol: lem_hol

coq: lem_coq

ocaml: lem_ocaml
	rm -f $(foreach F, $(SPURIOUS_FILES), $(OCAML_BUILD_DIR)/$(F))
# Copy in Lem's OCaml library.
	cp lib/ocaml/src/* $(OCAML_BUILD_DIR)
	cp boot/* $(OCAML_BUILD_DIR)
	cp parsing/* $(OCAML_BUILD_DIR)
# Copy in our own OCaml libraries.
	cp $(LEM_DIR)/ocaml-lib/*.ml $(LEM_DIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)
# Working around the value restriction.
	sed -i"" -e 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/multiset.ml
	sed -i"" -e 's/) emp /) (emp ()) /' $(OCAML_BUILD_DIR)/multiset.ml
	sed -i"" -e 's/Multiset.emp/Multiset.emp ()/' $(OCAML_BUILD_DIR)/c_parser.mly
# Fixing up OCaml syntax.
#	sed -i"" -e 's/(if i1 <= i2 then True else False, p)/((if i1 <= i2 then True else False), p)/' $(OCAML_BUILD_DIR)/constraint.ml
#	sed -i"" -e 's/(if i1 <  i2 then True else False, p)/((if i1 <  i2 then True else False), p)/' $(OCAML_BUILD_DIR)/constraint.ml
#	sed -i"" -e 's/let sb = Set_.product/(let sb = Set_.product/' $(OCAML_BUILD_DIR)/meaning.ml
#	sed -i"" -e 's/let sb = action_set_/(let sb = action_set_/' $(OCAML_BUILD_DIR)/meaning.ml
#	sed -i"" -e 's/d2.seq_before);/d2.seq_before));/' $(OCAML_BUILD_DIR)/meaning.ml
#	sed -i"" -e 's/let null/let null ()/' $(OCAML_BUILD_DIR)/meaning.ml
#	sed -i"" -e 's/M.null/M.null ()/' $(OCAML_BUILD_DIR)/reduction.ml
# Write _tags
	echo "true: annot, debug" > $(OCAML_BUILD_DIR)/_tags

ocaml_native: ocaml
	cd $(OCAML_BUILD_DIR); $(OCAMLBUILD) main.native
	-@[ ! -e "csem" ] || ln -s _build_ocaml/main.native csem

ocaml_byte: ocaml
	cd $(OCAML_BUILD_DIR); $(OCAMLBUILD) main.byte
	-@[ -e "csem" ] || ln -s _build_ocaml/main.byte csem

lem_ocaml:
	mkdir -p $(OCAML_BUILD_DIR)
	cd $(OCAML_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -ocaml $(foreach F, $(FILES), ../src/$(F)) && cd ..

lem_tex:
	mkdir -p $(TEX_BUILD_DIR)
	cd $(TEX_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -tex $(foreach F, $(FILES), ../src/$(F)) && cd ..

lem_hol:
	mkdir -p $(HOL_BUILD_DIR)
	cd $(HOL_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -hol $(foreach F, $(FILES), ../src/$(F)) && cd ..

lem_coq:
	mkdir -p $(COQ_BUILD_DIR)
	cd $(COQ_BUILD_DIR) && OCAMLRUNPARAM=b ../$(LEM) -lib ../$(LEM_LIB) -coq $(foreach F, $(COQ_FILES), ../src/$(F)) && cd ..

clean:
	rm -f csem
	rm -fR $(OCAML_BUILD_DIR)
	rm -fR $(TEX_BUILD_DIR)
	rm -fR $(HOL_BUILD_DIR)
