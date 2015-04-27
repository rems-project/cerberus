BUILD_DIR           = _bin
CPP_BUILD_DIR       = _bin_cppmem
OCAML_LIB_DIR       = ../../../bitbucket/lem/ocaml-lib
CMM_MODEL_DIR       = ../axiomatic/ntc
CPP_SRC_DIR         = ../src
CPP_INTEGRATION_DIR = cppmem-integration

CMM_MODEL_LEM_EXT = \
  cmm_master.lem \
  cmm_aux.lem \

CMM_MODEL_LEM = \
  cmm_master.lem \
  cmm_aux.lem \
  language.lem \
  examples.lem

# Ocaml and isa variants of CMM_MODEL_LEM
CMM_MODEL_GEN = \
  Cmm_master.thy \
  Cmm_aux.thy \
  Language.thy \
  Examples.thy \
  cmm_master.ml \
  cmm_aux.ml \
  language.ml \
  examples.ml \

AXIOM_BEH_LEM = \
  axiomaticBehaviour.lem \

AXIOM_BEH_GEN = \
  AxiomaticBehaviour.thy \
  axiomaticBehaviour.ml \

MIN_OPSEM_LEM = \
  minimalOpsem.lem \

# Isa and ocaml variants of MIN_OPSEM_LEM
MIN_OPSEM_GEN = \
  MinimalOpsem.thy \
  minimalOpsem.ml \
  MinimalOpsem-inc.tex \

REL_OPSEM_LEM = \
  relationalOpsem.lem \

# Isa and ocaml variants of REL_OPSEM_LEM
REL_OPSEM_GEN = \
  RelationalOpsem.thy \
  relationalOpsem.ml \
  RelationalOpsem-inc.tex \

EXE_OPSEM_LEM = \
  executableOpsem.lem \

# Isa and ocaml variants of EXE_OPSEM_LEM
EXE_OPSEM_GEN = \
  ExecutableOpsem.thy \
  executableOpsem.ml \
  ExecutableOpsem-inc.tex \

TEST_LEM = \
  test.lem

TEST_GEN = \
  test.ml

OPSEM_ML = \
  pp.ml \
  main.ml \

default: $(BUILD_DIR)/AxiomaticBehaviour.thy \
         $(BUILD_DIR)/axiomaticBehaviourAuxiliary.byte \
         $(BUILD_DIR)/RelationalOpsem.thy \

# The model depends on some external files. Copies of those files are
# included in the repository so we can choose when we want to merge
# changes. The rule update_dependencies updates the copies with the
# most up to date version.
update_dependencies: $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM_EXT)) \
                     $(BUILD_DIR)
        # Copy the cmm model files to the top level directory
	@echo COPYING $(CMM_MODEL_LEM_EXT)
	@cp $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM_EXT)) .

# Generate byte files from ml
$(BUILD_DIR)/main.byte: $(addprefix $(BUILD_DIR)/, $(OPSEM_ML)) \
                        $(addprefix $(BUILD_DIR)/, $(TEST_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(EXE_OPSEM_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(REL_OPSEM_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN)) \
        # We copy the library files, because I can't get ocamlbuild to look into the lib directory
	cp $(OCAML_LIB_DIR)/*.ml  $(BUILD_DIR)
	cp $(OCAML_LIB_DIR)/*.mli $(BUILD_DIR)
	cd $(BUILD_DIR); ocamlbuild -lib nums main.byte

# Generate byte files from generated tests
$(BUILD_DIR)/axiomaticBehaviourAuxiliary.byte: $(addprefix $(BUILD_DIR)/, $(AXIOM_BEH_GEN)) \
                                               $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN)) \
        # We copy the library files, because I can't get ocamlbuild to look into the lib directory
	cp $(OCAML_LIB_DIR)/*.ml  $(BUILD_DIR)
	cp $(OCAML_LIB_DIR)/*.mli $(BUILD_DIR)
	cd $(BUILD_DIR); ocamlbuild -lib nums axiomaticBehaviourAuxiliary.byte


# Build the test files to ocaml
$(addprefix $(BUILD_DIR)/, $(TEST_GEN)): $(addprefix $(BUILD_DIR)/, $(TEST_LEM)) \
                                         $(addprefix $(BUILD_DIR)/, $(EXE_OPSEM_GEN)) \
                                         $(addprefix $(BUILD_DIR)/, $(REL_OPSEM_GEN)) \
                                         $(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_GEN)) \
                                         $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(TEST_LEM) -ocaml

# Build the executable opsem to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(EXE_OPSEM_GEN)): $(addprefix $(BUILD_DIR)/, $(EXE_OPSEM_LEM)) \
                                              $(addprefix $(BUILD_DIR)/, $(REL_OPSEM_GEN)) \
                                              $(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_GEN)) \
                                              $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(EXE_OPSEM_LEM) -isa -ocaml -tex

# Build the relational opsem to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(REL_OPSEM_GEN)): $(addprefix $(BUILD_DIR)/, $(REL_OPSEM_LEM)) \
                                              $(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_GEN)) \
                                              $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(REL_OPSEM_LEM) -isa -ocaml -tex

# Build the minimal opsem to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_GEN)): $(addprefix $(BUILD_DIR)/, $(MIN_OPSEM_LEM)) \
                                              $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(MIN_OPSEM_LEM) -isa -ocaml -tex

# Build the AxiomaticBehaviour to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(AXIOM_BEH_GEN)): $(addprefix $(BUILD_DIR)/, $(AXIOM_BEH_LEM)) \
                                              $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(AXIOM_BEH_LEM) -isa -ocaml -tex

# Build cmm (the axiomatic memory model) to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN)): $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_LEM))
        # We don't want to see the warnings (-wl ign)
	cd $(BUILD_DIR); lem $(CMM_MODEL_LEM) -wl ign -isa -ocaml

# Generate lem files from ott
$(BUILD_DIR)/language.lem $(BUILD_DIR)/examples.lem: $(BUILD_DIR)/language.ott $(BUILD_DIR)/examples.ott
	cd $(BUILD_DIR); ott -i language.ott -o language.lem -lem_filter examples.ott examples.lem

# Copy the lem files to the build dir
$(BUILD_DIR)/%.lem: %.lem | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

# Copy the ml files to the build dir
$(BUILD_DIR)/%.ml: %.ml | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

# Copy the ott files to the build dir
$(BUILD_DIR)/%.ott: %.ott | $(BUILD_DIR)
	@echo COPYING $<
	@cp $< $(BUILD_DIR)

# Create the build directory
$(BUILD_DIR):
	mkdir $(BUILD_DIR)




# Build integration with cppmem
cppmem: $(CPP_BUILD_DIR)/main.ml $(CPP_BUILD_DIR)
	cp -R $(CPP_INTEGRATION_DIR)/* $(CPP_BUILD_DIR)
	make -C $(CPP_BUILD_DIR)

# Copy the cppmem files to the build directory
$(CPP_BUILD_DIR)/main.ml: $(CPP_SRC_DIR)/main.ml | $(CPP_BUILD_DIR)
        # Actually this rule depends on all files in cppmem (not only main.ml)
        # So changes in other cppmem-files are not detected if main.ml does not change
	cp -R $(CPP_SRC_DIR)/* $(CPP_BUILD_DIR)

# Create the cppmem-build directory
$(CPP_BUILD_DIR):
	mkdir $(CPP_BUILD_DIR)




# Delete the build directories
clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(CPP_BUILD_DIR)