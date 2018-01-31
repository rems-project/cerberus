# We need ocamlfind
ifeq (, $(shell which ocamlfind))
$(warning "ocamlfind is required to build the executable part of Cerberus")
endif

# Deal with Z3 package installed by opam
Z3="Z3"
ifeq (, $(shell ocamlfind query Z3))
Z3="z3"
endif


BOLD="\033[1m"
RED="\033[31m"
YELLOW="\033[33m"
RESET="\033[0m"

# Looking for Lem
ifndef LEM_PATH
LEM_PATH=~/bitbucket/lem
endif

LEM0=lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
	-only_changed_output
 #       -report_default_instance_invocation -only_changed_output 

LEM=$(LEM0) -outdir $(BUILD_DIR) -add_loc_annots


# C11 related stuff
CMM_MODEL_DIR=concurrency
CMM_MODEL_LEM =\
  cmm_csem.lem

CMM_EXEC_DIR=concurrency
CMM_EXEC_LEM =\
  cmm_op.lem

include Makefile-source

all: lem ocaml_native

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


lem: copy_cmm copy_cmm_exec copy_cerberus
	@echo $(BOLD)LEM$(RESET) -ocaml *.lem
	@OCAMLRUNPARAM=b ./tools/colours.sh $(LEM) -ocaml $(wildcard $(BUILD_DIR)/*.lem)
#	@OCAMLRUNPARAM=b $(LEM) -ocaml $(wildcard $(BUILD_DIR)/*.lem)
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/core_run.ml
	@sed -i"" -e "s/open Operators//" $(BUILD_DIR)/driver.ml
	@sed -i"" -e "s/Debug.DB_/Debug_ocaml.DB_/g" $(BUILD_DIR)/*.ml



DOC_BUILD_DIR = generated_doc

$(DOC_BUILD_DIR):
	mkdir $(DOC_BUILD_DIR)

alldoc.tex: copy_cmm copy_cmm_exec copy_cerberus | $(DOC_BUILD_DIR)
        # @OCAMLRUNPARAM=b $(LEM0) -no_dep_reorder -outdir $(DOC_BUILD_DIR) -cerberus_pp -html -tex_all alldoc.tex -html $(wildcard $(BUILD_DIR)/*.lem) 
	@OCAMLRUNPARAM=b $(LEM0) -no_dep_reorder -outdir $(DOC_BUILD_DIR) -cerberus_pp -html -tex_all alldoc.tex -html $(addprefix $(BUILD_DIR)/,$(CERBERUS_LEM_FLAT_SOURCES))

alldoc.pdf: alldoc.tex
	pdflatex alldoc.tex
	pdflatex alldoc.tex
#	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex
#	TEXINPUTS=../lem/tex-lib:$(TEXINPUTS) pdflatex alldoc.tex




smt:
	./tools/colours.sh ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,pprint,zarith,${Z3} -libs unix,str smt.native

test:
	./tools/colours.sh ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,pprint,zarith,${Z3} -libs unix,str test.native


new_main:
	./tools/colours.sh ocamlbuild -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,zarith,${Z3} -libs unix,str main2.native

ocaml_native:
	@if ! (ocamlfind query cmdliner pprint zarith >/dev/null 2>&1); then \
	  echo "Please first do a 'make -f Makefile.dependencies'" ; \
	else \
	  echo $(BOLD)OCAMLBUILD$(RESET) main.native; \
	  sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ src/main.ml > src/main_.ml; \
	  ocamlbuild -j 4 -use-ocamlfind -pkgs lem,cmdliner,pprint,${Z3} -libs unix,str main_.native; \
	  cp -L main_.native cerberus; \
	fi
##	@./tools/colours.sh ocamlbuild -no-hygiene -j 4 -use-ocamlfind -pkgs cmdliner,pprint,zarith -libs unix,nums,str main_.native

#cmdliner,

ocaml_profiling:
	@if ! (ocamlfind query cmdliner pprint zarith >/dev/null 2>&1); then \
	  echo "Please first do a 'make -f Makefile.dependencies'" ; \
	else \
	  echo $(BOLD)OCAMLBUILD$(RESET) main.native; \
	  sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ src/main.ml > src/main_.ml; \
	  ./tools/colours.sh ocamlbuild -j 4 -use-ocamlfind -pkgs landmarks.ppx,landmarks -pkgs cmdliner,pprint,zarith -libs unix,nums,str main_.native; \
	  cp -L main_.native cerberus; \
	fi


ocaml_byte:
	@if ! (ocamlfind query cmdliner pprint zarith >/dev/null 2>&1); then \
	  echo "Please first do a 'make -f Makefile.dependencies'" ; \
	else \
	  echo $(BOLD)OCAMLBUILD$(RESET) main.d.byte; \
	  sed s/"<<GIT-HEAD>>"/"`git rev-parse --short HEAD` -- `date "+%d\/%m\/%Y@%H:%M"`"/ src/main.ml > src/main_.ml; \
	  ./tools/colours.sh ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,pprint,zarith,${Z3} -libs unix,nums,str main_.d.byte; \
	  cp -L main_.d.byte cerberus; \
	fi

web: src/web.ml
	ocamlbuild -j 4 -use-ocamlfind -pkgs cmdliner,pprint,lem,${Z3},lwt,cohttp,cohttp.lwt -libs str web.native


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

clear: clean
	rm -rf $(BUILD_DIR)

