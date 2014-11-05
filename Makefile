# Looking for Lem
ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  LEMDIR=~/bitbucket/lem
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=lem -wl ign -wl_rename warn -wl_unused_vars warn



# C11 related stuff
CMM_MODEL_DIR=../cpp/axiomatic/ntc
CMM_MODEL_LEM =\
  cmm_master.lem

CMM_EXEC_DIR=../cpp/newmm_op
CMM_EXEC_LEM =\
  executableOpsem.lem \
  minimalOpsem.lem \
  relationalOpsem.lem


# Ail syntax and type system
AIL_DIR=ott/lem
AIL_LEM=\
  Common.lem \
  ErrorMonad.lem \
  TypingError.lem \
  Range.lem \
  Implementation.lem \
  AilSyntax.lem \
  AilTypes.lem \
  AilTypesAux.lem \
  Context.lem \
  GenTypes.lem




# The cerberus model
CERBERUS_LEM=\
  cmm_aux.lem \
  boot.lem \
  core.lem \
  core_aux.lem \
  core_run2.lem \
  core_run2_aux.lem \
  errors.lem \
  exception.lem \
  global.lem \
  implementation_.lem \
  location.lem \
  product.lem \
  state.lem \
  state_operators.lem \
  state_exception.lem \
  symbol.lem \
  undefined.lem \
  core_ctype.lem \
  naive_memory.lem \
  symbolic.lem \
  driver_util.lem \
  driver.lem \
  exception_undefined.lem \
  state_exception_undefined.lem \
  nondeterminism.lem \
  thread.lem \
  uniqueId.lem \
  enum.lem \
  show.lem

# The collection of lem files
MODEL_LEM= $(CMM_MODEL_LEM) $(CMM_EXEC_LEM) $(AIL_LEM) $(CERBERUS_LEM)


CORE_PARSER_ML=\
  core_parser_util.ml \
  core_parser.mly core_lexer.mll \
  core_parser_base.ml core_parser_base.mli


CPARSER_ML=\
  Lexer.mll \
  $(notdir $(wildcard parsers/cparser/*.ml parsers/cparser/*.mli)) \
  $(notdir $(wildcard parsers/cparser/coq_stdlib/*.ml parsers/cparser/coq_stdlib/*.mli))


PPRINTERS_ML=\
  colour.ml \
  pp_errors.ml \
  pp_symbol.ml \
  pp_ail.ml pp_core.ml pp_run.ml \
  pp_cmm.ml


# TODO: these is AddaX specific
Z3_API_PATH=~/Applications/z3-git/build/api/ml
Z3_LIB=/Library/lib





# Where and how ocamlbuild will be called
BUILD_DIR=_ocaml_generated
OCAMLBUILD=ocamlbuild -use-menhir -menhir "menhir --external-tokens Core_parser_util --strict --explain --infer" -tag annot -tag debug -use-ocamlfind -pkgs pprint -libs nums,unix -cflags -bin-annot
# OCAMLBUILD=ocamlbuild -use-menhir -menhir "menhir --external-tokens Core_parser_util --strict --explain --infer --trace" -tag annot -tag debug -use-ocamlfind -pkgs pprint,z3 -libs nums,unix -cflags -bin-annot,-custom,-I,$(Z3_API_PATH) -lflags -cclib,-L$(Z3_LIB),-cclib,-lz3



default: lem_model




# Create the directory where ocamlbuild will be called, and copy the OCaml library files from Lem.
$(BUILD_DIR):
	@echo CREATING the OCaml build directory
	@mkdir $(BUILD_DIR)
	@echo COPYING the Lem ocaml libraries
	@cp $(LEMDIR)/ocaml-lib/*.ml $(LEMDIR)/ocaml-lib/*.mli $(BUILD_DIR)


# Copy the cmm model files to the build dir
copy_cmm: $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM)) | $(BUILD_DIR)
	@echo COPYING $(CMM_MODEL_LEM)
	@cp $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM)) $(BUILD_DIR)

# Copy the cmm executable model files to the build dir
copy_cmm_exec: $(addprefix $(CMM_EXEC_DIR)/, $(CMM_EXEC_LEM)) | $(BUILD_DIR)
	@echo COPYING $(CMM_EXEC_LEM)
	@cp $(addprefix $(CMM_EXEC_DIR)/, $(CMM_EXEC_LEM)) $(BUILD_DIR)

# Copy the Ail files to the build dir
copy_ail: $(addprefix $(AIL_DIR)/, $(AIL_LEM)) | $(BUILD_DIR)
	@echo COPYING $(AIL_LEM)
	@cp $(addprefix $(AIL_DIR)/, $(AIL_LEM)) $(BUILD_DIR)

# Copy the cerberus model files to the build dir
copy_cerberus: $(addprefix model/, $(CERBERUS_LEM)) | $(BUILD_DIR)
	@echo COPYING $(CERBERUS_LEM)
	@cp $(addprefix model/, $(CERBERUS_LEM)) $(BUILD_DIR)


lem_model: copy_cmm copy_cmm_exec copy_ail copy_cerberus
	OCAMLRUNPARAM="" $(LEM) -outdir $(BUILD_DIR) -only_changed_output -add_loc_annots -ocaml $(wildcard $(BUILD_DIR)/*.lem)
#	@echo "[CORRECTING LINE ANNOTATION]" # $(patsubst _lem/%.lem, $(BUILD_DIR)/%.ml, $(wildcard _lem/*.lem))
#	@./hack.sh $(BUILD_DIR)
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/core_run2.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/naive_memory.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/driver.ml


# lem_check:
# 	$(LEM) $(addprefix model/, $(MODEL_FILES)) $(addprefix ott/lem/, $(AIL_LEM))



$(BUILD_DIR)/%.ml : %.ml | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

$(BUILD_DIR)/%.mli : %.mli | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

$(BUILD_DIR)/%.mll : %.mll | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

$(BUILD_DIR)/%.mly : %.mly | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)





































#$(BUILD_DIR)/cparser/% : % | $(BUILD_DIR)
#	-@[ -d $(BUILD_DIR)/cparser ] || mkdir $(BUILD_DIR)/cparser
#	@echo COPYING $<
#	@cp $< $(BUILD_DIR)/cparser/
#	-@(grep -s -e ^$(basename $*)$$ $(BUILD_DIR)/cparser.mlpack || echo $(basename $*) >> $(BUILD_DIR)/cparser.mlpack)



# ocaml_byte: lem_cmm lem_ail lem_model \

# ocaml_byte: $(addprefix $(OCAML_BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_FILES) $(PPRINTERS_ML)) \
            $(addprefix $(OCAML_BUILD_DIR)/cparser/, $(CPARSER_FILES)) | $(OCAML_BUILD_DIR)
ocaml_byte: $(addprefix $(BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_ML) $(PPRINTERS_ML)) \
            $(addprefix $(BUILD_DIR)/, $(CPARSER_ML)) | $(BUILD_DIR)
#	cd $(BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.byte
	@sed -i"" -e "s/<<HG-IDENTITY>>/`hg id`/" $(BUILD_DIR)/main.ml
	cd $(BUILD_DIR); $(OCAMLBUILD) main.byte
	ln -fs _ocaml_generated/main.byte csem


ocaml_native: $(addprefix $(BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_ML) $(PPRINTERS_ML)) \
            $(addprefix $(BUILD_DIR)/, $(CPARSER_ML)) | $(BUILD_DIR)
#	cd $(BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.native
	@sed -i"" -e "s/<<HG-IDENTITY>>/`hg id`/" $(BUILD_DIR)/main.ml
	cd $(BUILD_DIR); $(OCAMLBUILD) main.native
	ln -fs _ocaml_generated/main.native csem



# Temporary rule while memory.lem is WIP
# memory:
# 	OCAMLRUNPARAM=b $(LEM) $(foreach F, $(LIB_FILES), -ocaml_lib ./$(OCAML_LIB)/$(F)) $(addprefix ./model/, $(MODEL_FILES)) ./model/memory.lem


check_memory:
	OCAMLRUNPARAM=b $(LEM) -lib ott/lem model/new_memory.lem













VPATH=src pprinters parsers/coreparser





cerbcore_byte: $(addprefix $(BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_ML) $(PPRINTERS_ML)) | $(BUILD_DIR)
#	cd $(BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.byte
	@sed -i"" -e "s/<<HG-IDENTITY>>/`hg id`/" $(BUILD_DIR)/cerbcore.ml
	cd $(BUILD_DIR); $(OCAMLBUILD) cerbcore.byte
	ln -fs _ocaml_generated/cerbcore.byte cerbcore


cerbcore_native: $(addprefix $(BUILD_DIR)/, $(notdir $(wildcard src/*)) $(CORE_PARSER_ML) $(PPRINTERS_ML)) | $(BUILD_DIR)
#	cd $(BUILD_DIR); $(OCAMLBUILD) -I cparser cparser.cmo main.byte
	@sed -i"" -e "s/<<HG-IDENTITY>>/`hg id`/" $(BUILD_DIR)/cerbcore.ml
	cd $(BUILD_DIR); $(OCAMLBUILD) cerbcore.native
	ln -fs _ocaml_generated/cerbcore.native cerbcore







.PHONY: coq coq-lem coq-coqc

LEM_FILES = \
 AilTypes.lem \
 AilTypesAux.lem \
 boot.lem \
 Common.lem \
 core.lem \
 core_aux.lem \
 core_ctype.lem \
 core_run.lem \
 core_run_effect.lem \
 core_run_inductive.lem \
 errors.lem \
 ErrorMonad.lem \
 exception.lem \
 global.lem \
 Implementation.lem \
 implementation_.lem \
 location.lem \
 naive_memory.lem \
 product.lem \
 Range.lem \
 state.lem \
 state_exception.lem \
 state_operators.lem \
 symbol.lem \
 TypingError.lem \
 undefined.lem

COQ_FILES := $(shell echo $(LEM_FILES:%.lem=%.v) | python -c $$'import sys\nfor word in sys.stdin.read().split(): sys.stdout.write(word[0].lower() + word[1:] + " ")')

LEM_DIR_FILES = $(addprefix _lem/,$(LEM_FILES))
COQ_DIR_FILES = $(addprefix _coq/,$(COQ_FILES))

coq-lem: lem_model_ coq.patch coq.issue118.patch
	mkdir -p _coq
	$(LEMDIR)/lem -outdir _coq -coq -auxiliary_level none -only_changed_output $(LEM_DIR_FILES)
	sed -E -i '' '/Require (Import|Export)  operators./d' _coq/*.v # Workaround for Lem issue #84.
	for f in _coq/*.v; do echo $$'\n(*\n*** Local Variables: ***\n*** coq-prog-name: "coqtop" ***\n*** coq-prog-args: ("-emacs-U" "-require" "coqharness" "-R" "." "Csem" "-I" "~/lem/coq-lib") ***\n*** End: ***\n*)' >> $$f; done
	rm -rf _coq-orig
	mkdir _coq-orig
	cp _coq/*.v _coq-orig/
	patch -d _coq -p1 < coq.patch
	rm -rf _coq-patched
	mkdir _coq-patched
	cp _coq/*.v _coq-patched/
	patch -d _coq -p1 < coq.issue118.patch

Makefile.coq: $(COQ_DIR_FILES)
	coq_makefile -arg "-require coqharness" -I $(LEMDIR)/coq-lib -R _coq Csem -install none $(COQ_DIR_FILES) -o Makefile.coq

coq-coqc: Makefile.coq
	$(MAKE) -f Makefile.coq

coq: coq-lem coq-coqc

clean:
	rm -rf $(BUILD_DIR) _lem _coq
	rm -f csem
	rm -f Makefile.coq

clear:
	$(MAKE) clean
	rm -rf csem


dot:
	cd $(BUILD_DIR) ;  ocamldoc -dot `ocamldep -sort *.ml *.mli`
