BOLD="\033[1m"
RED="\033[31m"
YELLOW="\033[33m"
RESET="\033[0m"

# Looking for Lem
ifdef LEM_PATH
  LEMDIR=$(LEM_PATH)
else
  LEMDIR=~/bitbucket/lem
endif

LEM := $(LEMDIR)/lem
LEM_FLAGS = -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
        -only_changed_output 

# Where HOL files will be created
HOL_DIR = ../hol/

# Where auxiliary scripts will be created (these are not compiled automatically)
AUX_DIR = ../hol/auxScripts/

# Where LEM files are located
CMM_DIR = ../concurrency/
MODEL_DIR =../model/
AIL_DIR = ../model/ail/

# Util
UTIL_DIR = util/
UTIL = utilScript.sml \
 tagsScript.sml \
 pp_coreScript.sml \
 pp_memScript.sml \
 pp_ailScript.sml

# Patches
PATCH_DIR = patches/
PATCH = # defacto_memoryScript.patch
# memScript.patch \
# builtinsScript.patch \
# cabs_to_ail_auxScript.patch
# cabs_to_ailScript.patch

# Cerberus model files
CMM = \
 cmm_aux.lem \
 cmm_csem.lem \
  cmm_op.lem

UTILS =\
  boot.lem \
  decode.lem \
  dlist.lem \
  driver_util.lem \
  enum.lem \
  errors.lem \
  exception.lem \
  exception_undefined.lem \
  global.lem \
  loc.lem \
  multiset.lem \
  product.lem \
  state_exception.lem \
  state_exception_undefined.lem \
  state.lem \
  state_operators.lem \
  symbol.lem \
  cthread.lem \
  uniqueId.lem \
  std.lem \
  monadic_parsing.lem \
  formatted.lem \
 undefined.lem \
 implementation_.lem \
 symbolic.lem \
 pp.lem \
 bimap.lem \
 debug.lem

DEFACTO =\
 defacto_memory.lem \
 defacto_memory_types.lem \
 mem_common.lem \
 mem.lem \
  mem_aux.lem \

CABS = \
 cabs.lem \
  builtins.lem \
  cabs_to_ail_aux.lem \
  cabs_to_ail_effect.lem \
  cabs_to_ail.lem \
  scope_table.lem 

AIL = \
 AilTypes.lem \
 AilSyntax.lem \
  GenTypes.lem \
  AilSyntaxAux.lem \
  AilTypesAux.lem \
  AilTyping.lem \
  AilWf.lem \
  Annotation.lem \
  Common.lem \
  Context.lem \
  ErrorMonad.lem \
  GenTypesAux.lem \
  Range.lem \
  TypingError.lem \
  Implementation.lem 
  #GenTyping.lem \

CORE = \
 core_ctype_aux.lem \
 core_ctype.lem \
 core.lem \
  core_aux.lem \
  core_typing.lem \
  constraints.lem \
  nondeterminism.lem \
  core_eval.lem \
  core_run.lem \
  core_run_aux.lem
  #translation_aux.lem \
  translation_effect.lem \
  translation.lem \


MODEL := $(UTILS) $(CABS) $(CORE) $(DEFACTO)
SOURCE := $(MODEL) $(AIL) $(CMM)

HOL_SCRIPTS := $(addsuffix Script.sml, $(basename $(SOURCE))))

# Create the directory where HOL files will be generated
$(HOL_DIR):
	@echo $(BOLD)CREATING the HOL build directory$(RESET)
	@mkdir $(HOL_DIR)

# Copy the mem concurrency files to the build dir
$(CMM): $(addprefix $(CMM_DIR), $(CMM)) | $(HOL_DIR)
	@echo $(BOLD)COPYING cmm .lem files$(RESET)
	@cp $^ $(HOL_DIR)

# Copy the ail files to the build dir
$(AIL): $(addprefix $(AIL_DIR), $(AIL)) | $(HOL_DIR)
	@echo $(BOLD)COPYING cerberus ail .lem files$(RESET)
	@cp $^ $(HOL_DIR)

# Copy the cerberus model files to the build dir
$(MODEL): $(addprefix $(MODEL_DIR), $(MODEL)) | $(HOL_DIR)
	@echo $(BOLD)COPYING cerberus model .lem files$(RESET)
	@cp $^ $(HOL_DIR)

# Copy the cerberus files to the build dir
cerberus: $(addprefix $(HOL_DIR), $(CMM)) \
          $(addprefix $(HOL_DIR), $(AIL)) \
          $(addprefix $(HOL_DIR), $(MODEL))

model: $(SOURCE)

# Create auxiliary folder
$(AUX_DIR): $(HOL_DIR)
	@echo $(BOLD)CREATING the auxiliary script directory$(RESET)
	@mkdir $(AUX_DIR) || true

$(HOL_SCRIPTS): | $(SOURCE) $(AUX_DIR)
	@echo $(BOLD)"Generating HOL Script files"$(RESET)
	$(LEM) -hol $(LEM_FLAGS) $(SOURCE)
	@echo $(BOLD)"Moving auxiliary scripts to aux directory"
	@cd $(HOL_DIR); mv -f *AuxiliaryScript.sml $(AUX_DIR) || true

$(UTIL): $(addprefix $(UTIL_DIR), $(UTIL))
	@echo $(BOLD)Copying util script files...$(RESET)
	@cp $^ .

.PHONY: patch name_patch
name_patch:
	sed -i.bck 's|impl\$$||g' memScript.sml
	sed -i.bck 's|atypes\$$|ailTypes\$$|g' builtinsScript.sml
	sed -i.bck 's|a\$$|ailSyntax\$$|g' builtinsScript.sml
	sed -i.bck 's|atypes\$$|ailTypes\$$|g' cabs_to_ail_auxScript.sml
	sed -i.bck 's|atypes\$$||g' cabs_to_ail_effectScript.sml
	sed -i.bck 's|a\$$||g' cabs_to_ail_effectScript.sml
	sed -i.bck 's|atypes\$$||g' cabs_to_ailScript.sml
	sed -i.bck 's|e\$$||g' cabs_to_ailScript.sml
	sed -i.bck 's|cty\$$||g' core_typingScript.sml
#	sed -i.bck 's|e\$$||g' genTypingScript.sml
	sed -i.bck 's|cty\$$||g' outputScript.sml
	sed -i.bck 's|u\$$||g' outputScript.sml
	sed -i.bck 's|caux\$$||g' core_evalScript.sml
	sed -i.bck 's|eu\$$||g' core_evalScript.sml
	sed -i.bck 's|seu\$$||g' core_runScript.sml
	sed -i.bck 's|eu\$$||g' core_runScript.sml
	sed -i.bck 's|caux\$$||g' core_runScript.sml
	sed -i.bck 's|cmm\$$||g' core_runScript.sml
	sed -i.bck 's|e\$$||g' core_runScript.sml
#	sed -i.bck 's|core\$$||g' core_indent.sml

# val _ = PmatchHeuristics.set_classic_heuristic ();

patch: $(addprefix $(PATCH_DIR), $(PATCH)) | name_patch
	@echo $(BOLD)Applying patch $<...$(RESET)
	for p in $^; do patch < $$p; done

lem: $(UTIL) | $(HOL_SCRIPTS) $(AUX_DIR)

# Run Holmake
hol: lem name_patch
	@echo $(BOLD)Running Holmake$(RESET)
	Holmake

.PHONY: clean clean-all
# Cleaning stuff
clean:
	@echo $(BOLD)"Cleaning up files generated by Holmake"$(RESET)
	@rm -f *.ui *.uo *Theory.sml *.sig util/*.Theory util/*.ui util/*.uo
	@rm -rf $(AUX_DIR)

clean-all: clean
	@echo $(BOLD)"Cleaning up everything..."$(RESET)
	@Holmake cleanAll
	@rm -f *.sml *.lem
