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

# Ocaml and isa variants of CMM_MODEL_LEM
CMM_MODEL_GEN = \
  Cmm_master.thy \
  Cmm_aux.thy \
  cmm_master.ml \
  cmm_aux.ml \

AXIOM_BEH_LEM = \
  axiomaticBehaviour.lem \

AXIOM_BEH_GEN = \
  AxiomaticBehaviour.thy \
  axiomaticBehaviour.ml \

OPSEM_LEM = \
  cmm_op.lem \

# Isa and ocaml variants of OPSEM_LEM
OPSEM_GEN = \
  Cmm_op.thy \
  cmm_op.ml \
  Cmm_op-inc.tex \


default: $(BUILD_DIR)/Cmm_op.thy \

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
$(BUILD_DIR)/main.byte: $(addprefix $(BUILD_DIR)/, $(OPSEM_GEN)) \
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

# Build the opsem to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(OPSEM_GEN)): $(addprefix $(BUILD_DIR)/, $(OPSEM_LEM)) \
                                          $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(OPSEM_LEM) -isa -ocaml -tex

# Build the AxiomaticBehaviour to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(AXIOM_BEH_GEN)): $(addprefix $(BUILD_DIR)/, $(AXIOM_BEH_LEM)) \
                                              $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(AXIOM_BEH_LEM) -isa -ocaml -tex

# Build cmm (the axiomatic memory model) to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN)): $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_LEM))
        # We don't want to see the warnings (-wl ign)
	cd $(BUILD_DIR); lem $(CMM_MODEL_LEM) -wl ign -isa -ocaml

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