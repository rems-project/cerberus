

INPUTS=../itp11/llncs2e:../../tex-lib



LATEX = TEXINPUTS=$(INPUTS):$(TEXINPUTS)  pdflatex

BIBTEX = BSTINPUTS=$(INPUTS):$(BSTINPUTS) bibtex

all: vstte12.pdf

vstte12.pdf: vstte12.tex vstte12.bib
	$(LATEX) vstte12
	$(BIBTEX) vstte12
	$(LATEX) vstte12
	$(LATEX) vstte12

quick: vstte12.tex
	$(LATEX) vstte12

vstte12.zip: vstte12.pdf
	rm -rf vstte12-dir
	mkdir vstte12-dir
	cp vstte12-stripped.tex vstte12-dir/vstte12.tex
	cp ../tex-lib/lem.sty vstte12-dir
	cp llncs2e/llncs.cls vstte12-dir
	cd vstte12-dir && latex vstte12 && latex vstte12 && zip -r vstte12.zip *
	mv vstte12-dir/vstte12.zip .

clean:
	-rm -rf vstte12.aux vstte12.bbl vstte12.pdf vstte12.log vstte12.blg vstte12.idx vstte12.out Machine-extract.tmp* vstte12-dir vstte12.zip

#Machine-extract.tmp2-tex: Machine-extractScript.sml
#	$(WEAKMEMORYDIR)/HOLDoc_Net/hol_to_latex   $(WEAKMEMORYDIR)/ppc-abstract-machine/alldoc/glommed-imn.checkpoint.imn Machine-extractScript.sml > Machine-extract.tmp2-tex

#Machine-extract.tmp3-tex: Machine-extractScript.sml
#	$(WEAKMEMORYDIR)/HOLDoc_Net/lts_to_latex  -cmds   -texprefix ""  -nomerge  Machine-extract.imn  Machine-extractScript.sml > Machine-extract.tmp3-tex

#$(WEAKMEMORYDIR)/ppc-abstract-machine/alldoc/glommed-imn.checkpoint.imn
