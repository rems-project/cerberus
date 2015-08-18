BOLD="\x1b[1m"
NOCOLOUR="\x1b[0m"



# Looking for Lem
ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  LEMDIR=~/bitbucket/lem
endif

LEMLIB_DIR=$(LEMDIR)/library
LEM=lem -wl ign -wl_rename warn -wl_unused_vars warn -wl_pat_red err -wl_pat_exh warn



# C11 related stuff
#CMM_MODEL_DIR=../cpp/axiomatic/ntc
CMM_MODEL_DIR=concurrency
CMM_MODEL_LEM =\
  cmm_csem.lem

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
  defacto_memory.lem \
  naive_memory.lem \
  mem.lem \
  mem_aux.lem \
  mem_common.lem \
  symbolic.lem \
  driver_util.lem \
  driver_effect.lem \
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

rebuild:
	make clear
	make lem_model
	make dependencies
	rm depend
	make depend
	make ocaml_native; make ocaml_native

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

DOC_BUILD_DIR=generated_doc

lem_model_tex alldoc.tex: copy_cmm copy_cmm_exec copy_ail copy_cerberus
	OCAMLRUNPARAM=b $(LEM) -outdir $(DOC_BUILD_DIR) -only_changed_output -html -tex_all alldoc.tex -html $(wildcard $(BUILD_DIR)/*.lem)

lem_model.pdf: alldoc.tex
	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex

lem_model_pdf: 
	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex


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
	@echo ${BOLD}OCAMLC${NOCOLOUR}"   "$<
	@ocamlc -c $(LIBS) $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS)) $<

%.cmx: %.ml
	@echo ${BOLD}OCAMLOPT${NOCOLOUR} $<
	@ocamlopt -g -c $(LIBS) $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS)) $<

%.ml %.mli: %.mll
	@echo ${BOLD}OCAMLLEX${NOCOLOUR} $<
	@ocamllex $<



cparser:
	make -C parsers/cparser

coreparser:
	@echo ${BOLD}MENHIR{NOCOLOUR} parsers/coreparser/core_parser.mly
	@menhir --external-tokens Core_parser_util --strict --explain --infer --ocamlc "ocamlc $(addprefix -I , $(OCAML_LIBS) $(OCAML_DIRS))" parsers/coreparser/core_parser.mly



CMXS=\
  $(patsubst %.ml, %.cmx, $(shell ocamldep -sort $(patsubst %.cmx, %.ml, $(wildcard $(addsuffix /*.cmx, $(OCAML_DIRS))))))

CMOS=\
  $(patsubst %.ml, %.cmo, $(shell ocamldep -sort $(patsubst %.cmo, %.ml, $(wildcard $(addsuffix /*.cmo, $(OCAML_DIRS))))))


ocaml_native: | depend dependencies
# TODO: surely this is wrong ...
#	@sed -i ".sed" -e "s/<<HG-IDENTITY>>/`hg id`/" src/main.ml
#	TIME=`date "+%y/%m/%d@%H:%M"`
#	@echo $(TIME)
#	@$(shell sed -i ".sed" -e "s/<<HG-IDENTITY>>/$(echo `hg id` \(\) | sed -e 's/\\/\\\\/g' -e 's/\//\\\//g' -e 's/&/\\\&/g')/g" src/main.ml)
	make src/main.cmx
	ocamlopt -g unix.cmxa str.cmxa nums.cmxa -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cmxa, $(OCAML_LIBS))) $(CMXS) -o cerberus
#	mv src/main.ml.sed src/main.ml



native: src/main.cmx | depend dependencies
	ocamlopt unix.cmxa str.cmxa nums.cmxa -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cmxa, $(OCAML_LIBS))) $(filter-out src/main.cmx, $(CMXS)) src/main.cmx -o cerberus


byte: src/main.cmo | depend dependencies
	ocamlc unix.cma str.cma nums.cma -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cma, $(OCAML_LIBS))) $(filter-out src/main.cmo, $(CMOS)) src/main.cmo -o cerberus.byte



_wip: src/wip.ml
	ocamlopt unix.cmxa str.cmxa nums.cmxa -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cmxa, $(OCAML_LIBS))) $(filter-out src/main.cmx src/wip.cmx, $(CMXS)) src/wip.cmx -o wip



memory_test: wip/memory_test.cmx
	rm -f _ocaml_generated/{mem_aux.cmx,mem.cmx}
	make _ocaml_generated/mem_aux.cmx
	make _ocaml_generated/mem.cmx
	ocamlopt unix.cmxa str.cmxa nums.cmxa -cclib "-L./dependencies/zarith-1.3" \
	$(wildcard $(addsuffix /*.cmxa, $(OCAML_LIBS))) _ocaml_generated/nat_num.cmx _ocaml_generated/big_int_impl.cmx _ocaml_generated/nat_big_num.cmx _ocaml_generated/lem_bool.cmx _ocaml_generated/lem.cmx _ocaml_generated/lem_basic_classes.cmx _ocaml_generated/lem_num.cmx _ocaml_generated/lem_function.cmx _ocaml_generated/lem_maybe.cmx _ocaml_generated/lem_tuple.cmx _ocaml_generated/lem_list.cmx _ocaml_generated/lem_word.cmx _ocaml_generated/xstring.cmx _ocaml_generated/lem_string.cmx _ocaml_generated/lem_show.cmx _ocaml_generated/pset.cmx _ocaml_generated/lem_set_helpers.cmx _ocaml_generated/lem_set.cmx _ocaml_generated/pmap.cmx _ocaml_generated/lem_map.cmx _ocaml_generated/either.cmx _ocaml_generated/lem_either.cmx _ocaml_generated/lem_pervasives.cmx _ocaml_generated/enum.cmx _ocaml_generated/uniqueId.cmx _ocaml_generated/thread.cmx pprinters/colour.cmx src/debug.cmx _ocaml_generated/global.cmx _ocaml_generated/state.cmx _ocaml_generated/lem_relation.cmx _ocaml_generated/lem_show_extra.cmx _ocaml_generated/symbol.cmx _ocaml_generated/lem_assert_extra.cmx _ocaml_generated/lem_list_extra.cmx _ocaml_generated/lem_string_extra.cmx _ocaml_generated/implementation_.cmx _ocaml_generated/ailTypes.cmx _ocaml_generated/core_ctype.cmx _ocaml_generated/symbolic.cmx src/location_ocaml.cmx _ocaml_generated/loc.cmx _ocaml_generated/cabs.cmx _ocaml_generated/mem_common.cmx pprinters/pp_utils.cmx pprinters/pp_prelude.cmx pprinters/pp_symbol.cmx pprinters/pp_cabs.cmx _ocaml_generated/typingError.cmx _ocaml_generated/exception.cmx _ocaml_generated/errorMonad.cmx _ocaml_generated/common.cmx _ocaml_generated/context.cmx _ocaml_generated/range.cmx _ocaml_generated/implementation.cmx _ocaml_generated/ailSyntax.cmx _ocaml_generated/ailTypesAux.cmx pprinters/pp_ail.cmx pprinters/pp_core_ctype.cmx pprinters/pp_defacto_memory.cmx pprinters/pp_mem.cmx pprinters/string_core_ctype.cmx _ocaml_generated/defacto_memory.cmx _ocaml_generated/mem.cmx _ocaml_generated/mem_aux.cmx wip/memory_test.cmx -o memory_test



clean:
	rm -f depend parsers/cparser/Lexer.ml parsers/coreparser/core_lexer.ml
	rm -f $(addsuffix /*.o, $(OCAML_DIRS))
	rm -f $(addsuffix /*.cmi, $(OCAML_DIRS))
	rm -f $(addsuffix /*.cmx, $(OCAML_DIRS))

clear: clean
	rm -f cerberus
	rm -rf $(BUILD_DIR) dependencies
