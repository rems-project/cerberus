BUILD_DIR     = _bin
OCAML_LIB_DIR = ../../../../bitbucket/lem/ocaml-lib

CMM_MODEL_LEM = \
  cmm_master.lem \
  cmm_aux.lem \

# Ocaml and isa variants of CMM_MODEL_LEM and cmm_aux
CMM_MODEL_GEN = \
  cmm_master.ml \
  Cmm_master.thy \
  cmm_aux.ml \
  Cmm_aux.thy \

CMM_SRC_ML = \
  value.ml \

OPSEM_LEM = \
  language.lem \
  examples.lem \
  opsem_aux.lem \
  opsem.lem \
  twop.lem \
#  opsem_exe.lem \

# Ocaml and isa variants of OPSEM_LEM
OPSEM_GEN = \
  language.ml \
  Language.thy \
  examples.ml \
  Examples.thy \
  opsem_aux.ml \
  Opsem_aux.thy \
  opsem.ml \
  Opsem.thy \
  twop.ml \
  Twop.thy \
#  opsem_exe.ml \
#  Opsem_exe.thy

OPSEM_ML = \
  pp.ml \
  main.ml \

default: $(BUILD_DIR)/Twop.thy 

# Doesn't build anything, but only typechecks the lem-files
typecheck: $(addprefix $(BUILD_DIR)/, $(OPSEM_LEM)) \
           $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_LEM)) 
	cd $(BUILD_DIR); lem $(OPSEM_LEM) 

# Generate byte files from ml
$(BUILD_DIR)/main.byte: $(addprefix $(BUILD_DIR)/, $(OPSEM_ML)) \
                        $(addprefix $(BUILD_DIR)/, $(OPSEM_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN)) \
                        $(addprefix $(BUILD_DIR)/, $(CMM_SRC_ML)) \
        # We copy the library files, because I can't get ocamlbuild to look into the lib directory
	cp $(OCAML_LIB_DIR)/*.ml  $(BUILD_DIR)
	cp $(OCAML_LIB_DIR)/*.mli $(BUILD_DIR)
	cd $(BUILD_DIR); ocamlbuild -lib nums main.byte 

# Build the lem source files to ocaml and isa
$(addprefix $(BUILD_DIR)/, $(OPSEM_GEN)): $(addprefix $(BUILD_DIR)/, $(OPSEM_LEM)) \
                                          $(addprefix $(BUILD_DIR)/, $(CMM_MODEL_GEN))
	cd $(BUILD_DIR); lem $(OPSEM_LEM) -isa -ocaml

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

# Delete the build directory
clean:
	rm -rf $(BUILD_DIR) 
