.PHONY : bin/main web/cppmem.js install-web install-svr tar test headers clean version.ml cppmem-archive.tar.gz batch

SVR=svr-pes20-cppmem.cl.cam.ac.uk

PWD=$(shell pwd)

LEMDIR=../../../../bitbucket/lem/
LEMOCAMLLIBDIR=$(LEMDIR)ocaml-lib

ATOMICDIR=../../axiomatic/ntc

OPSEMDIR = ..

OPSEMFILES = 

JSOFOCAMLDIR=js_of_ocaml-1.3.2
JSOFOCAML=$(JSOFOCAMLDIR)/local-install/bin/js_of_ocaml

MYOCAMLRUNPARAM=bp  # add p to get parse debug output

WEBROOTDIR=~/public_html/
WEBDIR=$(WEBROOTDIR)/cppmem

all : cppmem
all-server : cpmmem web/cppmem.js


#include batch.mk
batch : bin/main.opt ./run.sh ./fixup.sh # $(DOTTESTS) $(NEATOTESTS)
	rm -f generated/*
	@for TEST in $(EXCTESTS); do \
	  ./run.sh $$TEST.exc dot; done
	@for TEST in $(NEATOTESTS); do \
	  ./run.sh $$TEST.c neato; done
	@for TEST in $(DOTTESTS); do \
	  ./run.sh $$TEST.c dot; done


executableOpsem.lem : $(OPSEMDIR)/executableOpsem.lem
	cat $^ | sed 's/Cmm_master/Cmm/g' > $@

relationalOpsem.lem : $(OPSEMDIR)/relationalOpsem.lem
	cat $^ | sed 's/Cmm_master/Cmm/g' > $@

minimalOpsem.lem : $(OPSEMDIR)/minimalOpsem.lem
	cat $^ | sed 's/Cmm_master/Cmm/g' > $@

executableOpsem.ml : executableOpsem.lem relationalOpsem.lem minimalOpsem.lem cmm.lem cmm_aux.lem
	$(LEMDIR)lem $(LEMFLAGS) -ocaml executableOpsem.lem relationalOpsem.lem minimalOpsem.lem


#$(ATOMICDIR)/cmm.lem : $(ATOMICDIR)/cmm_master.lem
#	make -C $(ATOMICDIR) cmm.lem


LEMFLAGS= -wl_unused_vars ign -wl_pat_exh ign


cmm.lem : $(ATOMICDIR)/cmm_master.lem
	rm -f $@
	cp $^ $@

# cmm_aux.lem : $(ATOMICDIR)/cmm_aux.lem
# 	cp $^ $@

cmm.ml cmm.html cmm_aux.ml : cmm_aux.lem cmm.lem
	rm -f $@
	$(LEMDIR)lem $(LEMFLAGS) -html -ocaml $^
	chmod u-w $@

cmm_aux_ocaml.ml : $(ATOMICDIR)/cmm_aux_ocaml.ml
	rm -f cmm_aux_ocaml.ml
	cp $(ATOMICDIR)/cmm_aux_ocaml.ml cmm_aux_ocaml.ml

cppmem : bin/main.opt
	rm -rf cppmem
	ln -s bin/main.opt cppmem

bin/main bin/main.opt :  cmm.ml cmm_aux.ml cmm_aux_ocaml.ml version.ml executableOpsem.ml
	ocamlbuild -libs nums,extract $(OBCFLAGS) $(OBLFLAGS) $(OBXFLAGS) $(OBMISCFLAGS) main.otarget
	mkdir -p bin
	cp _build/main.d.byte bin/main
	cp _build/main.native bin/main.opt

OBCFLAGS=-cflags -g,-I,../$(LEMOCAMLLIBDIR)/_build/
OBLFLAGS=-lflags -g,-I,../$(LEMOCAMLLIBDIR)/_build/
OBXFLAGS=-X bin -X doc -X $(JSOFOCAMLDIR) -X web
OBMISCFLAGS=-no-links -classic-display

$(JSOFOCAML) :
	cd $(JSOFOCAMLDIR); make; make install

cgi/dot.cgi : cgi/dot.ml
	ocamlbuild $(OBXFLAGS) $(OBMISCFLAGS) cgi/dot.d.byte
	cp _build/cgi/dot.d.byte $@

web/cppmem.js : $(JSOFOCAML)
	export OCAMLPATH=$(PWD)/$(JSOFOCAMLDIR)/local-install/site-lib; \
	           ocamlbuild -build-dir _build_js -use-ocamlfind -libs nums,extract,js_of_ocaml \
                   $(OBCFLAGS) $(OBLFLAGS) $(OBXFLAGS) $(OBMISCFLAGS) \
                   main_js.d.byte
	export OCAMLPATH=$(PWD)/$(JSOFOCAMLDIR)/local-install/site-lib; \
		   $(JSOFOCAML) _build_js/main_js.d.byte -pretty
	cp _build_js/main_js.d.js $@

version.ml :
	printf "let version = \"%s\"\n" `svnversion -n` > $@

##########################################################

WEBBASEFILES=web/index.html web/help.html web/cppmem.css web/compat.js web/cppmem_js.css
WEBFILES=$(WEBBASEFILES) web/cppmem.js

# TODO: jp: this is very ad hoc
CPPMEMDIR=cppmem-archive
tar : cppmem-archive.tar.gz
cppmem-archive.tar.gz : clean cmm.ml cmm_aux_ocaml.ml version.ml
	rm -rf $(CPPMEMDIR)
	mkdir $(CPPMEMDIR)
	cp -R lem-ocaml-lib-for-cmm $(CPPMEMDIR)/lem-ocaml-lib-for-cmm
	cp _tags $(CPPMEMDIR)
	cp render_script.sh $(CPPMEMDIR)
	cp $(ATOMICDIR)/cmm.lem $(CPPMEMDIR)
	cp *.ml $(CPPMEMDIR)
	cp *.mli $(CPPMEMDIR)
	cp *.mll $(CPPMEMDIR)
	cp *.mly $(CPPMEMDIR)
	cp Makefile $(CPPMEMDIR)
	cp main.itarget $(CPPMEMDIR)
	cd $(JSOFOCAMLDIR); make clean
	cp -R $(JSOFOCAMLDIR) $(CPPMEMDIR)/$(JSOFOCAMLDIR)
	rm -rf $(CPPMEMDIR)/$(JSOFOCAMLDIR)/local-install
	cp $(LEMDIR)ocaml-lib/*.ml $(CPPMEMDIR)
	cp $(LEMDIR)ocaml-lib/*.mli $(CPPMEMDIR)
	cp $(LEMDIR)ocaml-lib/*.mllib $(CPPMEMDIR)
	mkdir $(CPPMEMDIR)/cgi
	cp cgi/*.ml $(CPPMEMDIR)/cgi
	cp cgi/*.mli $(CPPMEMDIR)/cgi
	mkdir $(CPPMEMDIR)/web
	cp Cmm.html $(CPPMEMDIR)/cmm.html
	cp $(WEBBASEFILES) $(CPPMEMDIR)/web
	mkdir $(CPPMEMDIR)/cil-parser
#	cp cil-parser/*.{ml,mli,mll,mly} $(CPPMEMDIR)/cil-parser
	cp cil-parser/*.ml $(CPPMEMDIR)/cil-parser
	cp cil-parser/*.mli $(CPPMEMDIR)/cil-parser
	cp cil-parser/*.mll $(CPPMEMDIR)/cil-parser
	cp cil-parser/*.mly $(CPPMEMDIR)/cil-parser
	bash fixmakefilefortar.sh $(CPPMEMDIR)/Makefile
	cp -R examples $(CPPMEMDIR) 
	cp revision.txt $(CPPMEMDIR)
	cp README.txt $(CPPMEMDIR)
	cp LICENCE.txt $(CPPMEMDIR)
	cat INSTALL.txt | sed '/= From SVN =/,//d' > $(CPPMEMDIR)/INSTALL.txt
	cp server/lighttpd.conf $(CPPMEMDIR)
	tar cvzf $@ $(CPPMEMDIR)

RUNUTILITY=ocaml str.cma unix.cma

# to install the JavaScript and web page material in the local $(WEBDIR)
install-web : web/cppmem.js cgi/dot.cgi cmm.html
	rm -rf $(WEBDIR)/*
	mkdir -p $(WEBDIR)
	cp $(WEBFILES) $(WEBDIR)
	cp cmm.html $(WEBDIR)
	cp cgi/dot.cgi $(WEBDIR)
	cp revision.txt $(WEBDIR)
	$(RUNUTILITY) makeexamplesdir.ml examples $(WEBDIR)
	#mv $(WEBDIR)/examples/examples.json $(WEBDIR)

# to build and copy the tarball to the server
install-svr : cppmem-archive.tar.gz
	scp server/install-cppmem.sh $(SVR):~
	scp $^ $(SVR):~

# tests
test : bin/main
	$(RUNUTILITY) maketest.ml bin/main test


################### headers #######################

HEADEDFILES=\
atomic.ml auxl.ml constraints.ml error.ml error.mli eval.ml execfile.ml \
execlexer.mll execparser.mly executions.ml globals.ml ids.ml ids.mli \
interact.ml iso.ml location.ml main.ml main_js.ml makeexamplesdir.ml \
pp.ml runOpsem.ml solver.ml types.ml value.ml value.mli

headers :
	echo 'Adding headers to the files...'
	headache -c cppmem_ha_cfg -h cppmem_ha_hdr $(HEADEDFILES)
	echo 'Done.'


####################################################

FORCE:
clean::
	/bin/rm -f *.byte *.native
	rm -rf out.*
	rm -rf doc.dvi doc.ps doc.pdf doc.log doc.aux
	rm -rf cmm.ml cmm.lem Cmm.html web/cppmem.js
	rm -rf *~
	rm -rf execparser.ml execparser.output execparser.mli
	rm -rf executableOpsem.lem executableOpsem.ml 
	rm -rf relationalOpsem.lem relationalOpsem.ml 
	rm -rf minimalOpsem.lem minimalOpsem.ml
	rm -rf out.* out2.* exectest.dot 
	rm -rf generated/*
	rm -rf bin/main*
	ocamlbuild -classic-display -clean
	rm -rf _build
	rm -rf _build_js
	rm -rf cppmem
	rm -rf examples.json
	make -C $(ATOMICDIR) clean

