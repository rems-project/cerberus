# Checking for required tools.
ifeq (,$(shell which dune 2> /dev/null))
$(error "Compilation requires [dune].")
endif
ifeq (,$(shell which lem 2> /dev/null))
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

.PHONY: normal
normal: cerberus-concrete libc

.PHONY: all
all: cerberus-concrete cerberus-symbolic cerberus-bmc libc web

.PHONY: full-build
full-build: prelude-src
	@echo "[DUNE] full build (no libc)"
	$(Q)dune build

.PHONY: util
util:
	@echo "[DUNE] library [$@]"
	$(Q)dune build _build/default/$@/$@.cma _build/default/$@/$@.cmxa

.PHONY: sibylfs
sibylfs: sibylfs-src
	@echo "[DUNE] library [$@]"
	$(Q)dune build _build/default/$@/$@.cma _build/default/$@/$@.cmxa

.PHONY: cerberus-concrete
cerberus-concrete: prelude-src
	@echo "[DUNE] cerberus (concrete)"
	$(Q)dune build _build/default/backend/driver/main.exe

.PHONY: cerberus-symbolic
cerberus-symbolic: prelude-src
	@echo "[DUNE] cerberus-symbolic"
	$(Q)dune build _build/default/backend/driver/main_symbolic.exe

.PHONY: cerberus-bmc bmc
bmc: cerberus-bmc
cerberus-bmc: prelude-src
	@echo "[DUNE] cerberus-bmc"
	$(Q)dune build _build/default/backend/bmc/main.exe
	# FIXME does not compile

LIBC_TARGETS = runtime/libc/libc.co runtime/libc/libm.co

.PHONY: libc
libc: prelude-src
	$(Q)dune build $(addprefix _build/default/,$(LIBC_TARGETS))

.PHONY: ail_playground
ail_playground: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/$@/main.exe

.PHONY: ail_to_coq
ail_to_coq: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/$@/main.exe

.PHONY: rustic
rustic: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/$@/main.exe

.PHONY: absint
absint: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/$@/main.exe

.PHONY: csrt
csrt: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/$@/main.exe

.PHONY: cerberus-ocaml ocaml
ocaml: cerberus-ocaml
cerberus-ocaml: prelude-src
	@echo "[DUNE] $@"
	$(Q)dune build _build/default/backend/ocaml/driver/main.exe
	# FIXME does not compile
	# FIXME should generate rt-ocaml as a library
	#@echo $(BOLD)INSTALLING Ocaml Runtime in ./_lib$(RESET)
	#@mkdir -p _lib/rt-ocaml
	#@cp backend/ocaml/runtime/META _lib/rt-ocaml
	#@cp backend/ocaml/runtime/_build/rt_ocaml.a \
		   backend/ocaml/runtime/_build/rt_ocaml.cma \
			 backend/ocaml/runtime/_build/rt_ocaml.cmxa _lib/rt-ocaml
	#@cp backend/ocaml/runtime/_build/*.cmi _lib/rt-ocaml
	#@cp backend/ocaml/runtime/_build/*.cmx _lib/rt-ocaml
	#@cp backend/ocaml/runtime/_build/src/*.cmi _lib/rt-ocaml
	#@cp backend/ocaml/runtime/_build/src/*.cmx _lib/rt-ocaml

tmp/:
	@echo "[MKDIR] tmp"
	$(Q)mkdir -p tmp

config.json: tools/config.json
	@echo "[CP] $< → $@"
	@cp $< $@

.PHONY: web
web: prelude-src config.json tmp/
	@echo "[DUNE] web"
	$(Q)dune build _build/default/backend/web/web.exe
	$(Q)dune build _build/default/backend/web/instance.exe
	$(Q)dune build _build/default/backend/web/instance_symbolic.exe
	@cp -L _build/default/backend/web/instance.exe webcerb.concrete
	@cp -L _build/default/backend/web/instance_symbolic.exe webcerb.symbolic
	@cp -L _build/default/backend/web/web.exe cerberus-webserver

.PHONY: ui
ui:
	make -C public

#### LEM sources for the frontend
LEM_PRELUDE       = utils.lem global.lem loc.lem annot.lem bimap.lem \
                    dlist.lem debug.lem enum.lem state.lem symbol.lem \
                    exception.lem product.lem float.lem any.lem
LEM_CABS          = cabs.lem undefined.lem constraint.lem ctype.lem
LEM_AIL           = typingError.lem errorMonad.lem ailSyntax.lem genTypes.lem
LEM_CORE_CTYPE    = core_ctype_aux.lem
LEM_CORE          = core.lem mucore.lem errors.lem core_aux.lem \
                    core_anormalise.lem core_linking.lem
LEM_CORE_TYPING   = core_typing.lem core_typing_aux.lem core_typing_effect.lem
LEM_UTILS         = boot.lem decode.lem exception_undefined.lem multiset.lem \
                    state_exception.lem state_exception_undefined.lem \
                    std.lem monadic_parsing.lem fs.lem trace_event.lem
LEM_AIL_TYPING    = range.lem integerImpl.lem ailTypesAux.lem \
                    ailSyntaxAux.lem ailWf.lem ailTyping.lem genTypesAux.lem \
                    genTyping.lem
LEM_CABS_TO_AIL   = cabs_to_ail_aux.lem scope_table.lem \
                    cabs_to_ail_effect.lem cabs_to_ail.lem wipFrontend.lem
LEM_CORE_TO_CORE  = core_sequentialise.lem core_indet.lem core_rewrite.lem \
                    core_unstruct.lem
LEM_CORE_DYNAMICS = core_run_aux.lem core_eval.lem core_run.lem driver.lem
LEM_ELABORATION   = translation_effect.lem translation_aux.lem translation.lem 
LEM_DEFACTO       = mem_common.lem defacto_memory_types.lem \
                    defacto_memory_aux.lem defacto_memory.lem mem.lem \
                    mem_aux.lem
LEM_CONC_INTERF   = cmm_aux.lem
LEM_CONC          = cmm_csem.lem cmm_op.lem linux.lem

LEM_SRC_AUX       = $(LEM_PRELUDE) \
                    $(LEM_CABS) \
                    $(addprefix ail/, $(LEM_AIL)) \
                    $(LEM_CORE_CTYPE) \
                    builtins.lem output.lem pp.lem implementation.lem \
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

LEM_SRC = $(addprefix frontend/model/, $(LEM_SRC_AUX)) \
					$(addprefix frontend/concurrency/, $(LEM_CONC))
####

PRELUDE_SRC_DIR = ocaml_frontend/generated
OCAML_SRC = $(addprefix $(PRELUDE_SRC_DIR)/, $(addsuffix .ml, $(notdir $(basename $(LEM_SRC)))))

# All targets generated at once thanks to [&:].
$(OCAML_SRC)&: $(LEM_SRC)
	@echo "[MKDIR] $(PRELUDE_SRC_DIR)"
	$(Q)mkdir -p $(PRELUDE_SRC_DIR)
	@echo "[LEM] generating files in [$(PRELUDE_SRC_DIR)] (log in [ocaml_frontend/lem.log])"
	$(Q)lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
    -outdir $(PRELUDE_SRC_DIR) -ocaml \
    $(LEM_SRC) 2> ocaml_frontend/lem.log || (>&2 cat ocaml_frontend/lem.log; exit 1)
	@echo "[SED] patching things up in [$(PRELUDE_SRC_DIR)]"
	$(Q)$(SEDI) -e "s/open Operators//" $(PRELUDE_SRC_DIR)/core_run.ml
	$(Q)$(SEDI) -e "s/open Operators//" $(PRELUDE_SRC_DIR)/driver.ml
	$(Q)$(SEDI) -e "s/Debug.DB_/Debug_ocaml.DB_/g" $(OCAML_SRC)

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
	$(Q)rm -f webcerb.concrete webcerb.symbolic cerberus-webserver
	$(Q)rm -f $(LIBC_TARGETS)
	$(Q)dune clean

.PHONY: distclean
distclean: clean clean-prelude-src clean-sibylfs-src
	$(Q)rm -rf tmp config.json
