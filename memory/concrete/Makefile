# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

BUILD_DIR = ocaml_generated

MODEL_DIR = $(FRONTEND)/model
MODEL_LEM = $(addprefix $(MODEL_DIR)/, $(CERBERUS_LEM_SOURCES))

CONC_LEM_SOURCES = cmm_csem.lem cmm_op.lem linux.lem
CONC_LEM = $(addprefix $(FRONTEND)/concurrency/, $(CONC_LEM_SOURCES))

include Makefile-source

.PHONY: concrete lem clean

concrete: $(BUILD_DIR)
	@echo $(BOLD)BUILDING Concrete Memory Model$(RESET)
	@OCAMLPATH=$(CERB_PATH)/_lib ocamlbuild $(OB_FLAGS) concrete.cma concrete.cmxa

$(BUILD_DIR): $(CONC_LEM) $(MODEL_LEM)
	@make clean
	@make -C $(CERB_PATH) clean-non-mem
	@echo $(BOLD)LEM Concrete$(RESET)
	@mkdir -p $(BUILD_DIR)
	@cp $(CONC_LEM) $(BUILD_DIR)
	@cp $(MODEL_LEM) $(BUILD_DIR)
	@make lem

lem: $(BUILD_DIR)
	@echo $(BOLD)LEM$(RESET) -ocaml *.lem
	@ulimit -n 7168
	@OCAMLRUNPARAM=b $(CERB_PATH)/tools/colours.sh $(LEM) -ocaml $(wildcard $(BUILD_DIR)/*.lem) $(wildcard $(BUILD_DIR)/ail/*.lem)
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/core_run.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/driver.ml
	@sed -i"" -e "s/Debug.DB_/Debug_ocaml.DB_/g" $(BUILD_DIR)/*.ml

clean:
	@rm -rf ocaml_generated _build