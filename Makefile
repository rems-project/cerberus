# Looking for Lem
ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  LEMDIR=~/bitbucket/lem
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=lem -wl ign -wl_rename warn -wl_unused_vars warn -wl_pat_red err



# C11 related stuff
#CMM_MODEL_DIR=../cpp/axiomatic/ntc
CMM_MODEL_DIR=concurrency
CMM_MODEL_LEM =\
  cmm_master.lem

#CMM_EXEC_DIR=../cpp/newmm_op
CMM_EXEC_DIR=concurrency
CMM_EXEC_LEM =\
  cmm_op.lem
#  executableOpsem.lem \
#  minimalOpsem.lem \
#  relationalOpsem.lem


# Ail syntax and type system
AIL_DIR=ott/lem
AIL_LEM=\
  Common.lem \
  ErrorMonad.lem \
  TypingError.lem \
  Range.lem \
  Implementation.lem \
  AilSyntax.lem \
  AilSyntaxAux.lem \
  AilTypes.lem \
  AilTypesAux.lem \
  AilTyping.lem \
  AilWf.lem \
  Context.lem \
  Annotation.lem \
  GenTypes.lem \
  GenTypesAux.lem \
  GenTyping.lem


# The cerberus model
CERBERUS_LEM=\
  cabs.lem \
  dlist.lem \
  constraints.lem \
  cmm_aux.lem \
  boot.lem \
  cabs_to_ail.lem \
  cabs_to_ail_aux.lem \
  cabs_to_ail_effect.lem \
  scope_table.lem \
  std.lem \
  decode.lem \
  multiset.lem \
  core.lem \
  core_aux.lem \
  translation.lem \
  translation_aux.lem \
  translation_effect.lem \
  core_indet.lem \
  core_rewrite.lem \
  core_run.lem \
  core_run_aux.lem \
  errors.lem \
  exception.lem \
  global.lem \
  implementation_.lem \
  loc.lem \
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
  builtins.lem

# The collection of lem files
MODEL_LEM= $(CMM_MODEL_LEM) $(CMM_EXEC_LEM) $(AIL_LEM) $(CERBERUS_LEM)




# Where and how ocamlbuild will be called
BUILD_DIR=_ocaml_generated


OCAML_DIRS=\
  $(BUILD_DIR) \
  src \
  pprinters \
  parsers/coreparser \
  parsers/cparser


.PHONY: default copy_cmm copy_cmm_exec copy_ail copy_cerberus copy_pprint lem_model cparser coreparser ocaml_native clean clear

default: lem_model ocaml_native



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

copy_pprint: $(wildcard ./dependencies/pprint-20140424/src/*) | $(BUILD_DIR)
	@echo COPYING pprint source
	@cp ./dependencies/pprint-20140424/src/*.ml{,i} $(BUILD_DIR)

lem_model: copy_cmm copy_cmm_exec copy_ail copy_cerberus
	OCAMLRUNPARAM=b $(LEM) -outdir $(BUILD_DIR) -only_changed_output -add_loc_annots -ocaml $(wildcard $(BUILD_DIR)/*.lem)
#	@echo "[CORRECTING LINE ANNOTATION]" # $(patsubst _lem/%.lem, $(BUILD_DIR)/%.ml, $(wildcard _lem/*.lem))
#	@./hack.sh $(BUILD_DIR)
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/core_run.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/naive_memory.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/driver.ml
#	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/executableOpsem.ml
	rm -f $(BUILD_DIR)/*.lem


dependencies:
	mkdir dependencies
	cd dependencies; make -f ../Makefile.dependencies


.SUFFIXES: .ml .mli .cmo .cmi .cmx

depend: parsers/coreparser/core_lexer.ml parsers/cparser/Lexer.ml | $(BUILD_DIR)
	ocamldep $(addprefix -I , $(OCAML_DIRS)) $(addsuffix /*.ml, $(OCAML_DIRS)) \
		 $(addsuffix /*.mli, $(OCAML_DIRS)) > depend

-include depend


OCAML_LIBS=\
  ./dependencies/cmdliner-0.9.7/_build/src \
  ./dependencies/zarith-1.3 \
  ./dependencies/pprint-20140424/src/_build


%.cmi: %.mli
	@echo OCAMLC $<
	@ocamlc -c $(LIBS) $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS)) $<

%.cmx: %.ml
	@echo OCAMLOPT $<
	ocamlopt -c $(LIBS) $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS)) $<

%.ml %.mli: %.mll
	@echo OCAMLLEX $<
	@ocamllex $<



cparser:
	make -C parsers/cparser

coreparser:
	@echo MENHIR parsers/coreparser/core_parser.mly
	@menhir --external-tokens Core_parser_util --strict --explain --infer --ocamlc "ocamlc $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS))" parsers/coreparser/core_parser.mly



CMXS=\
  $(patsubst %.ml, %.cmx, $(shell ocamldep -sort $(patsubst %.cmx, %.ml, $(wildcard $(addsuffix /*.cmx, $(OCAML_DIRS))))))

foo:
	echo $(CMXS)

ocaml_native: | depend dependencies
# TODO: surely this is wrong ...
	make src/main.cmx
	ocamlopt unix.cmxa str.cmxa nums.cmxa -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cmxa, $(OCAML_LIBS))) $(CMXS) -o cerberus




clean:
	rm -f depend parsers/cparser/Lexer.ml parsers/coreparser/core_lexer.ml
	rm -f $(addsuffix /*.o, $(OCAML_DIRS))
	rm -f $(addsuffix /*.cmi, $(OCAML_DIRS))
	rm -f $(addsuffix /*.cmx, $(OCAML_DIRS))

clear: clean
	rm -f cerberus
	rm -rf $(BUILD_DIR) dependencies
