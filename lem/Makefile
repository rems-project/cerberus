#OTTLIB=/Users/sowens/ott/hol
OTTLIB=$(dir $(shell which ott))../hol
LEMVERSION=0.2
DDIR=lem-$(LEMVERSION)

#all: il.pdf build-main ilTheory.uo
all: lem.pdf build-lem
build-doc:
	make -C doc
do-tests:
	make -C tests

test-other:
	make -C ../ppcmem/system model
	make -C ../ppcmem/system depend_text
	make -C ../ppcmem/system text
	make -C ../cpp/axiomatic/ntc atomic.cmx AtomicTheory.uo
#	make -C ../cpp/opsem
#	make -C ../cppppc all

MACHINEFILES=\
MachineDefUtils.lem \
MachineDefFreshIds.lem \
MachineDefValue.lem \
MachineDefTypes.lem \
MachineDefInstructionSemantics.lem \
MachineDefStorageSubsystem.lem \
MachineDefThreadSubsystem.lem \
MachineDefSystem.lem

test-tex:  lem
	rm -rf tests/test-tex/*
	cp ../WeakMemory/ppc-abstract-machine/*.lem tests/test-tex
	cp tests/test-tex-inc-wrapper.tex tests/test-tex 
	chmod ugo-w tests/test-tex/*.lem
	cd tests/test-tex; ../../lem -hol -tex -ocaml -lib ../../library $(MACHINEFILES)
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex alldoc.tex; dvips alldoc
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefUtils.tex; dvips MachineDefUtils
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefFreshIds.tex; dvips MachineDefFreshIds
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefValue.tex; dvips MachineDefValue
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefTypes.tex; dvips MachineDefTypes
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefInstructionSemantics.tex; dvips MachineDefInstructionSemantics
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefStorageSubsystem.tex; dvips MachineDefStorageSubsystem
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefThreadSubsystem.tex; dvips MachineDefThreadSubsystem
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefSystem.tex; dvips MachineDefSystem

test-texg:
	g tests/test-tex/alldoc
	#g tests/test-tex/MachineDefStorageSubsystem

test-texw:
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper


test-texgw:
	g tests/test-tex/test-tex-inc-wrapper

debug: src/ast.ml 
	rm -f library/lib_cache
	make -C src debug
	ln -sf src/main.d.byte lem


build-lem: src/ast.ml
	rm -f library/lib_cache
	make -C ocaml-lib all
	make -C src all
	ln -sf src/main.native lem

lem: build-lem

lem.pdf: lem.tex
	pdflatex lem.tex

lemTheory.uo: lemScript.sml
	Holmake --qof -I $(OTTLIB) lemTheory.uo

lem.tex src/ast.ml lemScript.sml: lem.ott
	rm -f src/ast.ml
	ott -ocaml_include_terminals true -o lem.tex -o src/ast.ml -o lemScript.sml -picky_multiple_parses true lem.ott
	chmod a-w src/ast.ml

lem_unwrapped.tex: lem.ott
	ott -tex_wrap false -o lem_unwrapped.tex lem.ott

install_lem_unwrapped: lem_unwrapped.tex
	cp lem_unwrapped.tex ../../ott/examples/ich/generated/lem_unwrapped.tex

distrib: src/ast.ml headache
	rm -rf $(DDIR)
	rm -rf $(DDIR).tar.gz
	mkdir $(DDIR)
	mkdir $(DDIR)/src
	cp src/*.ml $(DDIR)/src/
	chmod a+w $(DDIR)/src/ast.ml
	cp src/*.mli $(DDIR)/src/
	cp src/*.mll $(DDIR)/src/
	cp src/*.mly $(DDIR)/src/
	cp src/_tags $(DDIR)/src/
	mkdir $(DDIR)/library
	mkdir $(DDIR)/library/hol
	mkdir $(DDIR)/library/isabelle
	mkdir $(DDIR)/library/ocaml
	cp library/isa_fixes.thy $(DDIR)/library
	cp library/*.lem $(DDIR)/library/
	cp library/isabelle/constants $(DDIR)/library/isabelle/
	cp library/isabelle/*.lem $(DDIR)/library/isabelle/
	cp library/hol/constants $(DDIR)/library/hol/
	cp library/hol/*.lem $(DDIR)/library/hol/
	cp library/ocaml/*.lem $(DDIR)/library/ocaml/
	mkdir $(DDIR)/ocaml-lib
	cp ocaml-lib/*.ml $(DDIR)/ocaml-lib	
	cp ocaml-lib/*.mli $(DDIR)/ocaml-lib	
	cp ocaml-lib/*.mllib $(DDIR)/ocaml-lib	
	cp ocaml-lib/Makefile $(DDIR)/ocaml-lib	
	mkdir $(DDIR)/tex-lib
	cp tex-lib/lem.sty $(DDIR)/tex-lib
	cp Makefile-distrib $(DDIR)/Makefile
	cp src/Makefile-distrib $(DDIR)/src/Makefile
	cp README $(DDIR)
	cp LICENSE $(DDIR)
	./headache -h header `ls $(DDIR)/src/*.ml`
	./headache -h header `ls $(DDIR)/src/*.mli`
	./headache -h header `ls $(DDIR)/src/*.mly`
	./headache -h header `ls $(DDIR)/src/*.mll`
	./headache -c head_config -h header `ls $(DDIR)/tex-lib/*.sty`
	./headache -c head_config -h header `ls $(DDIR)/library/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/hol/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/isabelle/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/ocaml/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/isa_fixes.thy`
	tar cf $(DDIR).tar $(DDIR)
	gzip $(DDIR).tar
	rm -rf $(DDIR)

clean:
	-make -C src clean
	-rm -rf *.uo *.ui lemTheory.sig lemTheory.sml lem.tex src/ast.ml lemScript.sml lem.aux lem.log lem.pdf lem.dvi lem.ps lem_unwrapped.tex .HOLMK lem.sys lem library/lib_cache

cleanall: clean
	-make -C doc clean
	-make -C slides clean
	-make -C manual clean
	-make -C ocaml-lib clean
	-make -C tests clean
	-rm -rf lem-$(LEMVERSION) lem-$(LEMVERSION).tar.gz
