# Looking for Lem
ifneq ($(wildcard $(PWD)/../lem-csem/lem),)
  LEMDIR=$(PWD)/../lem-csem
else ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  $(error could not find lem (please set the variable LEM_PATH))
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=$(LEMDIR)/lem -wl ign -wl_rename warn -lib $(LEMLIB_DIR) -outdir $(OCAML_BUILD_DIR) -only_changed_output -add_loc_annots -ocaml

# The directory of Mark's axiomatic model of concurrency in C11
CMMDIR=../../rsem/cpp/axiomatic/ntc


# Source directories
# LEMDIRS= model $(CMMDIR) ott/lem
LEMDIRS= model ott/lem
MLDIRS=\
  lib/ocaml/src \
  parsers/cparser parsers/cparser/coq_stdlib parsers/cparser/validator \
  parsers/coreparser \
  pprinters \
  src

VPATH=$(LEMDIRS) $(MLDIRS)


# Where and how ocamlbuild will be called
OCAML_BUILD_DIR=_ocaml_generated
OCAMLBUILD=ocamlbuild -use-menhir -menhir "menhir --external-tokens Core_parser_util" -tag annot -tag debug -package pprint -libs nums


CMM_FILE=\
  cmm_csem.lem

AIL_FILES=\
  Common.lem \
  OptionMonad.lem \
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

MODEL_FILES=\
  boot.lem \
  core.lem \
  core_aux.lem \
  core_indet.lem \
  core_run.lem \
  core_run_effect.lem \
  core_simpl.lem \
  core_typing.lem \
  cabs_to_ail.lem \
  cabs_to_ail_effect.lem \
  cmm_aux.lem \
  debug.lem \
  decode.lem \
  errors.lem \
  exception.lem \
  global.lem \
  implementation_.lem \
  lexing_.lem \
  location.lem \
  multiset.lem \
  product.lem \
  sb.lem \
  state.lem \
  state_operators.lem \
  state_exception.lem \
  symbol.lem \
  symbol_table.lem \
  translation.lem \
  translation_aux.lem \
  translation_effect.lem \
  undefined.lem


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
  pp_errors.ml \
  pp_symbol.ml \
  pp_cabs0.ml pp_cabs.ml pp_ail.ml pp_core.ml pp_sb.ml pp_run.ml


default: ocaml_byte


# Create the directory where ocamlbuild will be called, and copy the OCaml library files from Lem.
$(OCAML_BUILD_DIR):
	@echo CREATING the build directory
	@mkdir $(OCAML_BUILD_DIR)
	@echo COPYING the Lem ocaml libraries
	@cp $(LEMDIR)/ocaml-lib/*.ml $(LEMDIR)/ocaml-lib/*.mli $(OCAML_BUILD_DIR)


# # Calling Lem on the C++11 concurrency model
# lem_cmm: $(CMM_FILES) | $(OCAML_BUILD_DIR)
# 	@echo LEM $^
# 	@OCAMLRUNPARAM="" $(LEM) $(foreach D, $(LEMDIRS), -lib $(D)) $(addprefix $(CMMDIR)/, $(CMM_FILES))

# # Calling Lem on the Ail syntax and typing
# lem_ail : $(AIL_FILES) | $(OCAML_BUILD_DIR)
# 	@echo LEM $^
# 	OCAMLRUNPARAM="" $(LEM) $(foreach D, $(LEMDIRS), -lib $(D)) $(addprefix ott/lem/, $(AIL_FILES))

# Calling Lem on the meat of Cerberus
lem_model: cabs0.lem $(MODEL_FILES) | $(OCAML_BUILD_DIR)
	@rm -rf _lem/
	@mkdir _lem/
	@cp $(CMMDIR)/cmm_csem.lem _lem/
	@cp $(addprefix model/, $(MODEL_FILES)) _lem/
	@cp model/cabs0.lem _lem/
	@cp $(addprefix ott/lem/, $(AIL_FILES)) _lem/
	OCAMLRUNPARAM="" $(LEM) $(foreach D, $(LEMDIRS), -lib $(D)) $(wildcard _lem/*.lem)


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


#$(OCAML_BUILD_DIR)/cparser/% : % | $(OCAML_BUILD_DIR)
#	-@[ -d $(OCAML_BUILD_DIR)/cparser ] || mkdir $(OCAML_BUILD_DIR)/cparser
#	@echo COPYING $<
#	@cp $< $(OCAML_BUILD_DIR)/cparser/
#	-@(grep -s -e ^$(basename $*)$$ $(OCAML_BUILD_DIR)/cparser.mlpack || echo $(basename $*) >> $(OCAML_BUILD_DIR)/cparser.mlpack)



# ocaml_byte: lem_cmm lem_ail lem_model \

# ocaml_byte: $(addprefix $(OCAML_BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_FILES) $(PPRINTERS_FILES)) \
            $(addprefix $(OCAML_BUILD_DIR)/cparser/, $(CPARSER_FILES)) | $(OCAML_BUILD_DIR)
ocaml_byte: $(addprefix $(OCAML_BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_FILES) $(PPRINTERS_FILES)) \
            $(addprefix $(OCAML_BUILD_DIR)/, $(CPARSER_FILES)) | $(OCAML_BUILD_DIR)
#	cd $(OCAML_BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.byte
	cd $(OCAML_BUILD_DIR); $(OCAMLBUILD) main.byte



# Temporary rule while memory.lem is WIP
memory:
	OCAMLRUNPARAM=b $(LEM) $(foreach F, $(OCAML_LIB_FILES), -ocaml_lib ./$(OCAML_LIB)/$(F)) $(addprefix ./model/, $(MODEL_FILES)) ./model/memory.lem


clean:
	rm -rf $(OCAML_BUILD_DIR) _lem

clear:
	$(MAKE) clean
	rm -rf csem
