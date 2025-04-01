# Checking for required tools.
ifeq (,$(shell command -v dune 2> /dev/null))
$(error "Compilation requires [dune].")
endif
ifeq (,$(shell command -v lem 2> /dev/null))
$(error "Compilation requires [lem].")
endif

# GNU vs BSD
ifeq (GNU,$(shell sed --version 2>&1 > /dev/null && echo GNU))
SEDI = sed -i
else
SEDI = sed -i ''
endif

# Trick to avoid printing the commands.
# To enable the printing of commands, use [make Q= ...],
Q = @

ifdef PROFILING
    DUNEFLAGS=--workspace=dune-workspace.profiling
else
    DUNEFLAGS=
endif

.PHONY: normal
normal: cerberus

.PHONY: all
all: cerberus cerberus-bmc cerberus-web #rustic

.PHONY: full-build
full-build: prelude-src
	@echo "[DUNE] full build"
	$(Q)dune build $(DUNEFLAGS)

.PHONY: util
util:
	@echo "[DUNE] library [$@]"
	$(Q)dune build $(DUNEFLAGS) _build/default/$@/$@.cma _build/default/$@/$@.cmxa
	ifdef PROFILING
		$(Q)dune build $(DUNEFLAGS) _build/profiling/$@/$@.cma _build/profiling/$@/$@.cmxa
		$(Q)dune build $(DUNEFLAGS) _build/profiling-auto/$@/$@.cma _build/profiling-auto/$@/$@.cmxa
	endif

.PHONY: sibylfs
sibylfs: sibylfs-src
	@echo "[DUNE] library [$@]"
	$(Q)dune build $(DUNEFLAGS) _build/default/$@/$@.cma _build/default/$@/$@.cmxa
	ifdef PROFILING
		$(Q)dune build $(DUNEFLAGS) _build/profiling/$@/$@.cma _build/profiling/$@/$@.cmxa
		$(Q)dune build $(DUNEFLAGS) _build/profiling/$@/$@.cma _build/profiling-auto/$@/$@.cmxa
	endif

.PHONY: cerberus
cerberus: prelude-src
	@echo "[DUNE] cerberus"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install

.PHONY: test
test: prelude-src
	@echo "testing"
	dune exec coq/coqcaptest.exe

.PHONY: cerberus-bmc bmc
bmc: cerberus-bmc
cerberus-bmc: prelude-src
	@echo "[DUNE] cerberus-bmc"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus-bmc.install

# .PHONY: rustic
# rustic: prelude-src
# 	@echo "[DUNE] $@"
# 	$(Q)dune build $(DUNEFLAGS) cerberus.install rustic.install

cheri: prelude-src
	@echo "[DUNE] cerberus-cheri"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus-cheri.install

# combined goal to build both cerberus and cheri together as single dune run.
# building them separately form makefile causes them to run two confilcting
# dune builds in parallel
.PHONY: cerberus-with-cheri
cerberus-with-cheri: prelude-src
	@echo "[DUNE] cerberus-with-cheri"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install cerberus-cheri.install

# .PHONY: cerberus-ocaml ocaml
# ocaml: cerberus-ocaml
# cerberus-ocaml: prelude-src
# 	@echo "[DUNE] $@"
# 	$(Q)dune build _build/default/backend/ocaml/driver/main.exe
# 	FIXME does not compile
# 	FIXME should generate rt-ocaml as a library
# 	@echo $(BOLD)INSTALLING Ocaml Runtime in ./_lib$(RESET)
# 	@mkdir -p _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/META _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/rt_ocaml.a \
# 		   backend/ocaml/runtime/_build/rt_ocaml.cma \
# 			 backend/ocaml/runtime/_build/rt_ocaml.cmxa _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/*.cmi _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/*.cmx _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/src/*.cmi _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/src/*.cmx _lib/rt-ocaml

tmp/:
	@echo "[MKDIR] tmp"
	$(Q)mkdir -p tmp

config.json: tools/config.json
	@echo "[CP] $< → $@"
	@cp $< $@

.PHONY: cerberus-web web
web: cerberus-web
cerberus-web: prelude-src config.json tmp/
	@echo "[DUNE] web"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install cerberus-web.install
#	@cp -L _build/default/backend/web/instance.exe webcerb.concrete
#	@cp -L _build/default/backend/web/instance_symbolic.exe webcerb.symbolic
#	@cp -L _build/default/backend/web/instance_vip.exe webcerb.vip
#	@cp -L _build/default/backend/web/web.exe cerberus-webserver

.PHONY: ui
ui:
	make -C public

#### LEM sources for the frontend
LEM_RENAMED = global.lem loc.lem debug.lem decode.lem

LEM_PRELUDE       = utils.lem annot.lem bimap.lem \
                    dlist.lem enum.lem state.lem symbol.lem \
                    exception.lem product.lem float.lem any.lem
LEM_CABS          = cabs.lem undefined.lem constraint.lem integerType.lem ctype.lem
LEM_AIL           = typingError.lem errorMonad.lem ailSyntax.lem genTypes.lem
LEM_CTYPE_AUX     = ctype_aux.lem
LEM_CORE          = core.lem errors.lem core_aux.lem core_linking.lem
LEM_CORE_TYPING   = core_typing.lem core_typing_aux.lem core_typing_effect.lem
LEM_UTILS         = boot.lem exception_undefined.lem multiset.lem \
                    state_exception.lem state_exception_undefined.lem \
                    std.lem monadic_parsing.lem fs.lem trace_event.lem \
										cerb_attributes.lem
LEM_AIL_TYPING    = range.lem integerImpl.lem ailTypesAux.lem \
                    ailSyntaxAux.lem ailWf.lem ailTyping.lem genTypesAux.lem \
                    genTyping.lem
LEM_CABS_TO_AIL   = cabs_to_ail_aux.lem scope_table.lem \
                    desugaring_init.lem cabs_to_ail_effect.lem cabs_to_ail.lem mini_pipeline.lem
LEM_CORE_TO_CORE  = core_sequentialise.lem core_indet.lem core_rewrite.lem \
                    core_unstruct.lem
LEM_CORE_DYNAMICS = core_run_aux.lem core_eval.lem core_run.lem core_reduction.lem core_reduction_aux.lem driver.lem
LEM_ELABORATION   = translation_effect.lem translation_aux.lem translation.lem 
LEM_DEFACTO       = mem_common.lem defacto_memory_types.lem \
                    defacto_memory_aux.lem defacto_memory.lem mem.lem \
                    mem_aux.lem
LEM_CONC_INTERF   = cmm_aux.lem
LEM_CONC          = cmm_csem.lem cmm_op.lem linux.lem

LEM_CN            = cn.lem cn_desugaring.lem

LEM_SRC_AUX       = $(LEM_PRELUDE) \
                    $(LEM_CN) \
                    $(LEM_CABS) \
                    $(addprefix ail/, $(LEM_AIL)) \
                    $(LEM_CTYPE_AUX) \
                    builtins.lem formatted.lem pp.lem implementation.lem \
                    $(LEM_DEFACTO) \
                    $(LEM_UTILS) \
                    nondeterminism.lem \
                    $(LEM_CONC_INTERF) \
                    $(LEM_CORE) \
                    $(LEM_CORE_TYPING) \
                    $(addprefix ail/, $(LEM_AIL_TYPING)) \
                    $(LEM_CABS_TO_AIL) \
                    $(LEM_CORE_TO_CORE) \
                    $(LEM_CORE_DYNAMICS) \
                    $(LEM_ELABORATION)

LEM_SRC_RENAMED = $(addprefix frontend/model/, $(LEM_RENAMED))

LEM_SRC_NOT_RENAMED = $(addprefix frontend/model/, $(LEM_SRC_AUX)) \
					$(addprefix frontend/concurrency/, $(LEM_CONC))

LEM_SRC = $(LEM_SRC_RENAMED) \
					$(LEM_SRC_NOT_RENAMED)
####

PRELUDE_SRC_DIR = ocaml_frontend/generated
OCAML_SRC = $(addprefix $(PRELUDE_SRC_DIR)/, $(addsuffix .ml, $(notdir $(basename $(LEM_SRC_NOT_RENAMED))))) \
						$(addprefix $(PRELUDE_SRC_DIR)/lem_, $(addsuffix .ml, $(notdir $(basename $(LEM_RENAMED)))))

# All targets generated at once thanks to [&:].
$(OCAML_SRC)&: $(LEM_SRC)
	@echo "[MKDIR] $(PRELUDE_SRC_DIR)"
	$(Q)mkdir -p $(PRELUDE_SRC_DIR)
	@echo "[LEM] generating files in [$(PRELUDE_SRC_DIR)] (log in [ocaml_frontend/lem.log])"
	$(Q)lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
    -outdir $(PRELUDE_SRC_DIR) -cerberus_pp -ocaml \
    $(LEM_SRC) 2> ocaml_frontend/lem.log || (>&2 cat ocaml_frontend/lem.log; exit 1)
	@echo "[SED] patching things up in [$(PRELUDE_SRC_DIR)]"
	$(Q)$(SEDI) -e "s/open Operators//" $(PRELUDE_SRC_DIR)/core_run.ml
	$(Q)$(SEDI) -e "s/open Operators//" $(PRELUDE_SRC_DIR)/driver.ml
	$(Q)$(SEDI) -e "s/Lem_debug.DB_/Cerb_debug.DB_/g" $(OCAML_SRC)
	$(Q)$(SEDI) -e "1 s/.*/&[@@@warning \"-8\"]/" $(PRELUDE_SRC_DIR)/cmm_csem.ml
	$(Q)$(SEDI) -e "1 s/.*/&[@@@warning \"-8\"]/" $(PRELUDE_SRC_DIR)/cmm_op.ml

# Elaboration PP stuff
elab_pp:
	@echo "[MKDIR] $(PRELUDE_SRC_DIR)"
	$(Q)mkdir -p generated_tex
	$(Q)lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
	-outdir generated_tex -cerberus_pp -tex \
	$(addprefix -i ,$(filter-out frontend/model/translation.lem,$(LEM_SRC))) frontend/model/translation.lem
	cd generated_tex; lualatex Translation.tex


#### LEM sources for sibylfs
SIBYLFS_LEM = dir_heap.lem fs_prelude.lem fs_spec.lem list_array.lem \
              sibylfs.lem
SIBYLFS_ML  = abstract_string.ml fs_dict_wrappers.ml fs_interface.ml \
              fs_dump.ml fs_printer.ml lem_support.ml
SIBYLFS_MLI = abstract_string.mli fs_dict_wrappers.mli fs_interface.mli \
              lem_support.mli

SIBYLFS_LEM_ML  = $(addsuffix .ml, $(basename $(SIBYLFS_LEM)))

SIBYLFS_LEM_SRC = $(addprefix sibylfs/src/, $(SIBYLFS_LEM))
SIBYLFS_ML_SRC  = $(addprefix sibylfs/src/, $(SIBYLFS_ML))
SIBYLFS_MLI_SRC = $(addprefix sibylfs/src/, $(SIBYLFS_MLI))

SIBYLFS_LEM_TRG = $(addprefix sibylfs/generated/, $(SIBYLFS_LEM_ML))
SIBYLFS_ML_TRG  = $(addprefix sibylfs/generated/, $(SIBYLFS_ML))
SIBYLFS_MLI_TRG = $(addprefix sibylfs/generated/, $(SIBYLFS_MLI))

SIBYLFS_SRC = $(SIBYLFS_LEM_SRC) $(SIBYLFS_ML_SRC) $(SIBYLFS_MLI_SRC)
SIBYLFS_TRG = $(SIBYLFS_LEM_TRG) $(SIBYLFS_ML_TRG) $(SIBYLFS_MLI_TRG)

SIBYLFS_SED = sibylfs/patch_all_ml.sed sibylfs/patch/dir_heap.sed \
              sibylfs/patch/fs_prelude.sed sibylfs/patch/fs_spec.sed
####

SIBYLFS_SRC_DIR = sibylfs/generated

# All targets generated at once thanks to [&:].
$(SIBYLFS_TRG)&: $(SIBYLFS_SRC) $(SIBYLFS_SED)
	@echo "[MKDIR] $(SIBYLFS_SRC_DIR)"
	$(Q)mkdir -p $(SIBYLFS_SRC_DIR)
	@echo "[LEM] generating files in [$(SIBYLFS_SRC_DIR)] (log in [sibylfs/lem.log])"
	$(Q)lem -wl_unused_vars ign -wl_rename err -wl_comp_message ign \
	  -wl_pat_exh ign -outdir $(SIBYLFS_SRC_DIR) -ocaml \
    $(SIBYLFS_LEM_SRC) 2> sibylfs/lem.log
	@echo "[CP] $(SIBYLFS_MLI_TRG)"
	$(Q)cp $(SIBYLFS_MLI_SRC) $(SIBYLFS_SRC_DIR)
	@echo "[CP] $(SIBYLFS_ML_TRG)"
	$(Q)cp $(SIBYLFS_ML_SRC) $(SIBYLFS_SRC_DIR)
	@echo "[SED] patching things up in [$(SIBYLFS_SRC_DIR)]"
	$(Q)$(SEDI) -f sibylfs/patch/dir_heap.sed   sibylfs/generated/dir_heap.ml
	$(Q)$(SEDI) -f sibylfs/patch/fs_prelude.sed sibylfs/generated/fs_prelude.ml
	$(Q)$(SEDI) -f sibylfs/patch/fs_spec.sed    sibylfs/generated/fs_spec.ml
	$(Q)$(SEDI) -f sibylfs/patch_all_ml.sed $(SIBYLFS_LEM_TRG) $(SIBYLFS_ML_TRG)

.PHONY: prelude-src
prelude-src: $(OCAML_SRC) sibylfs-src

.PHONY: sibylfs-src
sibylfs-src: $(SIBYLFS_TRG)

.PHONY: clean-prelude-src
clean-prelude-src:
	$(Q)rm -rf $(PRELUDE_SRC_DIR)

.PHONY: clean-sibylfs-src
clean-sibylfs-src:
	$(Q)rm -rf $(SIBYLFS_SRC_DIR)

.PHONY: clean
clean:
	$(Q)rm -f coq/*.{glob,vo,vok}
	$(Q)rm -f webcerb.concrete webcerb.symbolic cerberus-webserver
	$(Q)rm -rf _build/

.PHONY: distclean
distclean: clean clean-prelude-src clean-sibylfs-src
	$(Q)rm -rf tmp config.json

.PHONY: cerberus-lib
cerberus-lib:
	@echo "[DUNE] cerberus-lib"
	$(Q)dune build -p cerberus-lib

.PHONY: install_lib
install_lib: cerberus-lib
	@echo "[DUNE] install cerberus-lib"
	$(Q)dune install cerberus-lib

.PHONY: install
install: install_lib cerberus
	@echo "[DUNE] install cerberus"
	$(Q)dune install cerberus

.PHONY: install-cheri
install-cheri: install_lib
	@echo "[DUNE] install cerberus-cheri"
	$(Q)dune install cerberus-cheri

.PHONY: uninstall
uninstall: cerberus
	@echo "[DUNE] uninstall cerberus"
	$(Q)dune uninstall cerberus
