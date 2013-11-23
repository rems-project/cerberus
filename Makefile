# Looking for Lem
ifneq ($(wildcard $(PWD)/../lem-csem/lem),)
  LEMDIR=$(PWD)/../lem-csem
else ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  $(error could not find lem (please set the variable LEM_PATH))
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=$(LEMDIR)/lem -wl ign -lib $(LEMLIB_DIR)

# The directory of Mark's axiomatic model of concurrency in C11
CMMDIR=../../../rsem/cpp/axiomatic/ntc/


# Source directories
LEMDIRS=lib/ocaml ott/lem model
MLDIRS=\
  lib/ocaml/src \
  parsers/cparser parsers/cparser/coq_stdlib parsers/cparser/validator \
  parsers/coreparser \
  pprinters \
  src

VPATH=$(LEMDIRS) $(MLDIRS)


# Where and how ocamlbuild will be called
OCAML_BUILD_DIR=_ocaml_generated
OCAMLBUILD=ocamlbuild -use-menhir -menhir "menhir --external-tokens Core_parser_util" -tag annot -tag debug  -package pprint -libs nums


AIL_FILES=\
  Common.lem \
  Range.lem \
  AilTypes.lem \
  Implementation.lem \
  AilTypesAux.lem \
  Context.lem \
  AilSyntax.lem \
  GenTypes.lem \
  Annotation.lem \
  GenSyntax.lem \
  AilSyntaxAux.lem \
  AilWf.lem \
  AilTyping.lem \
  GenTypesAux.lem \
  GenTyping.lem


# TODO: fix this horror
MODEL_FILES1=\
  boot.lem \
  multiset.lem \
  global.lem \
  ord.lem \
  product.lem \
  map_.lem \
  lexing.lem \
  location.lem \
  symbol.lem \
  option.lem \
  exception.lem \
  state.lem \
  state_exception.lem \
  pprint_.lem \
  document.lem \
  symbol_table.lem \
  cabs0.lem

MODEL_FILES2=\
  undefined.lem \
  implementation_.lem \
  core.lem \
  debug.lem \
  core_aux.lem \
  errors.lem \
  core_simpl.lem \
  core_typing.lem \
  core_indet.lem \
  core_run.lem \
  sb.lem \
  decode.lem \
  cabs_to_ail.lem \
  translation_effect.lem \
  translation_aux.lem \
  translation.lem

OCAML_LIB=lib/ocaml

OCAML_LIB_FILES=\
  boot.lem \
  pprint_.lem \
  document.lem \
  decode.lem \

CMM_FILES=\
  cmm.lem

SPURIOUS_FILES=\
  pprint_.ml \
  lexing.ml \
  document.ml \
  cabs0.ml

CORE_PARSER_FILES=\
  core_parser_util.ml \
  core_parser.mly core_lexer.mll \
  core_parser_base.ml core_parser_base.mli

CPARSER_FILES=\
  Lexer.mll \
  $(notdir $(wildcard parsers/cparser/*.ml parsers/cparser/*.mli)) \
  $(notdir $(wildcard parsers/cparser/coq_stdlib/*.ml parsers/cparser/coq_stdlib/*.mli))

PPRINTERS_FILES=\
  colour.ml \
  pp_cabs0.ml pp_ail.ml pp_core.ml pp_sb.ml pp_run.ml


FILES=$(MODEL_FILES1) $(AIL_FILES) $(MODEL_FILES2) $(OCAML_LIB_FILES) $(SPURIOUS_FILES) $(CORE_PARSER_FILES) $(CPARSER_FILES) $(PPRINTERS_FILES)

default: ocaml_byte


ocaml_byte: lem_ocaml
	@rm -f $(foreach F, $(SPURIOUS_FILES), $(OCAML_BUILD_DIR)/$(F))
	@cp lib/ocaml/src/* $(OCAML_BUILD_DIR)
# YUCK
	@sed -i"" -e 's/Cabs0/Cparser.Cabs0/' $(OCAML_BUILD_DIR)/cabs_to_ail.ml
# Sort of YUCK
	@sed -i"" -e 's/<<HG-IDENTITY>>/$(shell hg id)/' $(OCAML_BUILD_DIR)/main.ml
	cd $(OCAML_BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.byte
	-@[ -e "csem" ] || ln -s $(OCAML_BUILD_DIR)/main.byte csem


lem_ocaml: $(addprefix $(OCAML_BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_FILES) $(PPRINTERS_FILES)) \
           $(addprefix $(OCAML_BUILD_DIR)/cparser/, $(CPARSER_FILES))
# (FUTURE) see comment below
#          $(FILES:%.lem=$(OCAML_BUILD_DIR)/%.ml)
	cd $(OCAML_BUILD_DIR) && OCAMLRUNPARAM=b $(LEM) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ../$(OCAML_LIB)/$(F)) -ocaml $(addprefix $(CMMDIR), $(CMM_FILES)) $(addprefix ../model/, $(MODEL_FILES1))  $(addprefix ../ott/lem/, $(AIL_FILES)) $(addprefix ../model/, $(MODEL_FILES2))
	sed -i"" -e 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/multiset.ml
	sed -i"" -e 's/) emp /) (emp ()) /' $(OCAML_BUILD_DIR)/multiset.ml
	@sed -i"" -e 's/Multiset.emp/Multiset.emp ()/' $(OCAML_BUILD_DIR)/cabs_to_ail.ml

# (FUTURE) this would be the way to go if there was a way to not have Lem recompiled
#          all the dependencies of a module
# Generates OCaml code from the Lem source files
# $(OCAML_BUILD_DIR)/%.ml : %.lem | $(OCAML_BUILD_DIR)
# 	@echo LEM-ocaml $<
# 	@cp FOO/_build/$*.ml $(OCAML_BUILD_DIR)
# ifeq ($<,src/multiset.ml)
#	sed -i"" -e 's/let emp/let emp ()/' $(OCAML_BUILD_DIR)/multiset.ml
#	sed -i"" -e 's/) emp /) (emp ()) /' $(OCAML_BUILD_DIR)/multiset.ml
# endif

# TODO: find if there is way to factor
# Move handwritten .ml .mli files
$(OCAML_BUILD_DIR)/%.ml : %.ml | $(OCAML_BUILD_DIR)
	@echo COPYING $<
	@cp $< $(OCAML_BUILD_DIR)

$(OCAML_BUILD_DIR)/%.mli : %.mli | $(OCAML_BUILD_DIR)
	@echo COPYING $<
	@cp $< $(OCAML_BUILD_DIR)

$(OCAML_BUILD_DIR)/%.mll : %.mll | $(OCAML_BUILD_DIR)
	@echo COPYING $<
	@cp $< $(OCAML_BUILD_DIR)

$(OCAML_BUILD_DIR)/%.mly : %.mly | $(OCAML_BUILD_DIR)
	@echo COPYING $<
	@cp $< $(OCAML_BUILD_DIR)


$(OCAML_BUILD_DIR)/cparser/% : % | $(OCAML_BUILD_DIR)
	-@[ -d $(OCAML_BUILD_DIR)/cparser ] || mkdir $(OCAML_BUILD_DIR)/cparser
	@echo COPYING $<
	@cp $< $(OCAML_BUILD_DIR)/cparser/
	-@(grep -s -e ^$(basename $*)$$ $(OCAML_BUILD_DIR)/cparser.mlpack || echo $(basename $*) >> $(OCAML_BUILD_DIR)/cparser.mlpack)



# Create the directory where ocamlbuild will be called, and copy the OCaml library files from Lem.
$(OCAML_BUILD_DIR):
	mkdir $(OCAML_BUILD_DIR)
	cp $(LEMDIR)/ocaml-lib/*.ml $(LEMDIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)




# Temporary rule while memory.lem is WIP
memory:
	OCAMLRUNPARAM=b $(LEM) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ./$(OCAML_LIB)/$(F)) $(addprefix ./model/, $(MODEL_FILES)) ./model/memory.lem


clean:
	rm -rf $(OCAML_BUILD_DIR)

clear:
	$(MAKE) clean
	rm -rf csem
