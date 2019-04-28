# We need ocamlfind
ifeq (, $(shell which ocamlfind))
$(error "ocamlfind is required to build the executable part of Cerberus")
endif

# Deal with Z3 package installed by opam
ifeq ($(shell ocamlfind query -qe -qo Z3; echo $$?), 0)
Z3="Z3"
else
Z3="z3"
endif

Z3_PATH   := $(shell ocamlfind query z3)
CERB_PATH ?= $(shell pwd)
DYLD_LIBRARY_PATH = ${Z3_PATH}
LD_LIBRARY_PATH   = ${Z3_PATH}

BOLD   := "\033[1m"
RED    := "\033[31m"
YELLOW := "\033[33m"
RESET  := "\033[0m"

# Looking for Lem
LEM_PATH ?= ~/bitbucket/lem

LEM0 = lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
	-only_changed_output
 #       -report_default_instance_invocation -only_changed_output 

LEM = $(LEM0) -outdir $(BUILD_DIR) # -add_loc_annots


# C11 related stuff
CMM_MODEL_DIR=concurrency
CMM_MODEL_LEM =\
  cmm_csem.lem

CMM_EXEC_DIR=concurrency
CMM_EXEC_LEM =\
  cmm_op.lem

LINUX_MODEL_DIR=concurrency
LINUX_MODEL_LEM =\
  linux.lem

include Makefile-source

all: lem ocaml_native libc

# Where and how ocamlbuild will be called
BUILD_DIR=ocaml_generated

# Create the directory where ocamlbuild will be called, and copy the OCaml library files from Lem.
$(BUILD_DIR):
	@echo $(BOLD)CREATING the OCaml build directory$(RESET)
	@mkdir $(BUILD_DIR)
#	@echo $(BOLD)COPYING the Lem ocaml libraries$(RESET)
#	@cp $(LEM_PATH)/ocaml-lib/*.ml $(LEM_PATH)/ocaml-lib/*.mli $(BUILD_DIR)

# Copy the cmm model files to the build dir
copy_cmm: $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM)) | $(BUILD_DIR)
	@echo $(BOLD)COPYING$(RESET) $(CMM_MODEL_LEM)
	@cp $(addprefix $(CMM_MODEL_DIR)/, $(CMM_MODEL_LEM)) $(BUILD_DIR)

# Copy the cmm executable model files to the build dir
copy_cmm_exec: $(addprefix $(CMM_EXEC_DIR)/, $(CMM_EXEC_LEM)) | $(BUILD_DIR)
	@echo $(BOLD)COPYING$(RESET) $(CMM_EXEC_LEM)
	@cp $(addprefix $(CMM_EXEC_DIR)/, $(CMM_EXEC_LEM)) $(BUILD_DIR)

copy_linux_model: $(addprefix $(LINUX_MODEL_DIR)/, $(LINUX_MODEL_LEM)) | $(BUILD_DIR)
	@echo $(BOLD)COPYING$(RESET) $(LINUX_MODEL_LEM)
	@cp $(addprefix $(LINUX_MODEL_DIR)/, $(LINUX_MODEL_LEM)) $(BUILD_DIR)

# Copy the cerberus model files to the build dir
copy_cerberus: $(addprefix model/, $(CERBERUS_LEM_SOURCES)) | $(BUILD_DIR)
	@echo $(BOLD)COPYING cerberus .lem files$(RESET)
	@cp $(addprefix model/, $(CERBERUS_LEM_SOURCES)) $(BUILD_DIR)

.PHONY: dependencies
dependencies:
#	@if [ "2" == "$(shell ocamlfind query pprint > /dev/null 2>&1; echo $$?)" ]; then \
# #	  $(error "Please install pprint"); \
# #	fi
	mkdir -p dependencies
	cd dependencies; make -f ../Makefile.dependencies


lem: copy_cmm copy_cmm_exec copy_linux_model copy_cerberus sibylfs
	@echo $(BOLD)LEM$(RESET) -ocaml *.lem
	@ulimit -n 7168
	@OCAMLRUNPARAM=b ./tools/colours.sh $(LEM) -ocaml $(wildcard $(BUILD_DIR)/*.lem)
#	@OCAMLRUNPARAM=b $(LEM) -ocaml $(wildcard $(BUILD_DIR)/*.lem)
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/core_run.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/driver.ml
	@sed -i"" -e "s/Debug.DB_/Debug_ocaml.DB_/g" $(BUILD_DIR)/*.ml



DOC_BUILD_DIR = generated_doc

$(DOC_BUILD_DIR):
	mkdir $(DOC_BUILD_DIR)

alldoc.tex: copy_cmm copy_cmm_exec copy_linux_model copy_cerberus | $(DOC_BUILD_DIR)
        # @OCAMLRUNPARAM=b $(LEM0) -no_dep_reorder -outdir $(DOC_BUILD_DIR) -cerberus_pp -html -tex_all alldoc.tex -html $(wildcard $(BUILD_DIR)/*.lem) 
	@OCAMLRUNPARAM=b $(LEM0) -no_dep_reorder -outdir $(DOC_BUILD_DIR) -cerberus_pp -html -tex_all alldoc.tex -html $(addprefix $(BUILD_DIR)/,$(CERBERUS_LEM_FLAT_SOURCES))

alldoc.pdf: alldoc.tex
	pdflatex alldoc.tex
	pdflatex alldoc.tex
#	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex
#	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex




smt:
	./tools/colours.sh ocamlbuild -no-plugin -j 4 -use-ocamlfind -pkgs cmdliner,pprint,zarith,${Z3} -libs unix,str smt.native

test:
	ocamlbuild -j 4 -use-ocamlfind -pkgs unix,lem,cmdliner,pprint,yojson,angstrom,${Z3},ppx_sexp_conv,sexplib,sha -libs str test.native


new_main:
	./tools/colours.sh ocamlbuild -no-plugin -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,zarith,${Z3} -libs unix,str main2.native

sb:
	./tools/colours.sh ocamlbuild -no-plugin -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,zarith,${Z3} -libs unix,str sb.native

simpl:
	./tools/colours.sh ocamlbuild -no-plugin -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,zarith,${Z3} -libs unix,str simpl.native

playground:
	./tools/colours.sh ocamlbuild -no-plugin -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,zarith,${Z3} -libs unix,str playground.native

.PHONY: sibylfs
sibylfs: ${BUILD_DIR}
	@echo $(BOLD)BUILDING SilbylFS$(RESET)
	@make -C sibylfs
	@echo $(BOLD)COPYING SibylFS .ml files$(RESET)
	@cp -vf ./sibylfs/generated/*.ml ${BUILD_DIR}
	@cp -vf ./sibylfs/generated/*.mli ${BUILD_DIR}

ocaml_native:
	@if ! (ocamlfind query cmdliner pprint zarith angstrom >/dev/null 2>&1); then \
	  echo "Please first do a 'make -f Makefile.dependencies'" ; \
	else \
	  echo $(BOLD)OCAMLBUILD$(RESET) main.native; \
	  echo "(* Do not edit: automatically generated file *)" > src/main_.ml; \
	  sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ src/main.ml >> src/main_.ml; \
	  ocamlbuild src/cerberus_cstubs.o && \
	  ocamlbuild -j 4 -use-ocamlfind -pkgs unix,lem,cmdliner,pprint,yojson,angstrom,${Z3},ppx_sexp_conv,sexplib,sha,apron,apron.boxD,apron.octD,apron.polkaMPQ,apron.t1pMPQ -libs str main_.native && \
	  cp -L main_.native cerberus; \
	fi

ocaml: ocaml_native libc

ocaml_profiling:
	@if ! (ocamlfind query cmdliner pprint zarith >/dev/null 2>&1); then \
	  echo "Please first do a 'make -f Makefile.dependencies'" ; \
	else \
	  echo $(BOLD)OCAMLBUILD$(RESET) main.native; \
	  sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ src/main.ml > src/main_.ml; \
	  ocamlbuild src/cerberus_cstubs.o && \
	  BISECT_COVERAGE=YES ocamlbuild -j 4 -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)' -pkgs unix,lem,cmdliner,pprint,yojson,${Z3} -libs str main_.native && \
	  cp -L main_.native cerberus-prof; \
	fi


instance_profiling:
	ocamlbuild -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)'  src/cerberus_cstubs.o;
	BISECT_COVERAGE=YES ocamlbuild -j 4 -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)' -pkgs pprint,lem,yojson,${Z3},cmdliner,sha,sexplib,ppx_sexp_conv,angstrom -libs str instance.native
	cp -L instance.native cerb.concrete 

instance: src/instance.ml
	ocamlbuild src/cerberus_cstubs.o;
	ocamlbuild -j 4 -use-ocamlfind -pkgs pprint,lem,yojson,${Z3},cmdliner,sha,sexplib,ppx_sexp_conv,angstrom -libs str instance.native
	cp -L instance.native cerb.concrete 
	sed 's/ref \`MemConcrete/ref \`MemSymbolic/' src/prelude.ml > src/prelude.ml.aux
	cp src/prelude.ml.aux src/prelude.ml
	ocamlbuild -j 4 -use-ocamlfind -pkgs pprint,lem,yojson,${Z3},cmdliner,sha,sexplib,ppx_sexp_conv,angstrom -libs str instance.native
	sed 's/ref \`MemSymbolic/ref \`MemConcrete/' src/prelude.ml > src/prelude.ml.aux
	mv src/prelude.ml.aux src/prelude.ml
	cp -L instance.native cerb.symbolic

web: src/web.ml
	ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,lem,pprint,lwt,cohttp,cohttp.lwt,yojson,base64,ezgzip -libs str -tag thread web.native

web_profiling: src/web.ml
	BISECT_COVERAGE=YES ocamlbuild -j 4 -use-ocamlfind -plugin-tag 'package(bisect_ppx-ocamlbuild)' -pkgs cmdliner,lem,pprint,lwt,cohttp,cohttp.lwt,yojson,base64,ezgzip web.native

web.byte: src/web.ml
	ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,lem,pprint,lwt,cohttp,cohttp.lwt,yojson,base64 web.d.byte

analyse:
	ocamlbuild -pkgs cmdliner -libs str,unix tools/analyse.native

transformN1570:
	ocamlbuild -pkgs lambdasoup,yojson -lib str tools/transformN1570.native

.PHONY: libc
libc:
	make -C libc clean
	make -C libc

.PHONY: cbuild clink
cbuild:
	ocamlbuild -pkg cmdliner -libs str,unix tools/cbuild.native
	cp -L cbuild.native cbuild
	rm cbuild.native

clink:
	ocamlbuild -lib str tools/clink.native
	cp -L clink.native clink
	rm clink.native

# LOS-count the spec
los:
	./mysloc   $(addprefix model/,$(SOURCE_ail) )
	./mysloc   $(addprefix model/,$(SOURCE_ail_typing) )
	./mysloc   $(addprefix model/,$(SOURCE_cabs) )
	./mysloc   $(addprefix model/,$(SOURCE_cabs_to_ail) )
	./mysloc   $(addprefix model/,$(SOURCE_core) )
	./mysloc   $(addprefix model/,$(SOURCE_core_to_core) )
	./mysloc   $(addprefix model/,$(SOURCE_core_dynamics) )
	./mysloc   $(addprefix model/,$(SOURCE_elaboration) )
	./mysloc   $(addprefix model/,$(SOURCE_utils) )
	./mysloc   $(addprefix model/,$(SOURCE_defacto)) 
	./mysloc   $(addprefix model/,$(SOURCE_concurrency_interface))


losparser:
	./mysloc \
# 	parsers/cparser/Cparser_driver.ml  \
# 	parsers/cparser/Parser_errors.ml   \
# 	parsers/cparser/Parser_errors.mli  \
# 	parsers/cparser/tokens.ml
	wc \
# 	parsers/cparser/Lexer.mll	       \
# 	parsers/cparser/Parser.mly \
# 	parsers/cparser/pre_parser.mly    

losconc:
	./mysloc \
# 	~/rsem/cpp/newmm_op/executableOpsem.lem \
# 	~/rsem/cpp/newmm_op/minimalOpsem.lem \
# 	~/rsem/cpp/newmm_op/relationalOpsem.lem 
	wc ~/rsem/cpp/newmm_op/*.thy


los_snapshot-2015-11-20.txt:
	$(MAKE) los > los_snapshot-2015-11-20.txt 


clean:
	rm -rf _build
	rm -rf {src,pprinters}/*.{cmx,cmi}
	rm -rf alldoc*
	rm -rf generated_doc/*.html
	make -C sibylfs clean

clear: clean
	rm -rf cerberus cerb.* main.native instance.native web.native
	rm -rf $(BUILD_DIR)

