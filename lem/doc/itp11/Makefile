

INPUTS=llncs2e:../../tex-lib



LATEX = TEXINPUTS=$(INPUTS):$(TEXINPUTS)  pdflatex

BIBTEX = BSTINPUTS=$(INPUTS):$(BSTINPUTS) bibtex

all: itp11.pdf

itp11.pdf: itp11.tex itp11.bib
	$(LATEX) itp11
	$(BIBTEX) itp11
	$(LATEX) itp11
	$(LATEX) itp11
	
quick: itp11.tex
	$(LATEX) itp11

itp11.zip: itp11.pdf
	rm -rf itp11-dir
	mkdir itp11-dir
	cp itp11-stripped.tex itp11-dir/itp11.tex
	cp ../tex-lib/lem.sty itp11-dir
	cp llncs2e/llncs.cls itp11-dir
	cd itp11-dir && latex itp11 && latex itp11 && zip -r itp11.zip *
	mv itp11-dir/itp11.zip .

clean:
	-rm -rf itp11.aux itp11.bbl itp11.pdf itp11.log itp11.blg itp11.idx itp11.out Machine-extract.tmp* itp11-dir itp11.zip

#Machine-extract.tmp2-tex: Machine-extractScript.sml
#	$(WEAKMEMORYDIR)/HOLDoc_Net/hol_to_latex   $(WEAKMEMORYDIR)/ppc-abstract-machine/alldoc/glommed-imn.checkpoint.imn Machine-extractScript.sml > Machine-extract.tmp2-tex

Machine-extract.tmp3-tex: Machine-extractScript.sml
	$(WEAKMEMORYDIR)/HOLDoc_Net/lts_to_latex  -cmds   -texprefix ""  -nomerge  Machine-extract.imn  Machine-extractScript.sml > Machine-extract.tmp3-tex

#$(WEAKMEMORYDIR)/ppc-abstract-machine/alldoc/glommed-imn.checkpoint.imn
