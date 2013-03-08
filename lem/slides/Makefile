FIG_OPTS =

itp11.ps: itp11.dvi
	dvips itp11.dvi

itp11.dvi: itp11.tex lem_trans.pstex lem_trans.pstex_t
	latex itp11

%.pstex %.pstex_t : %.fig Makefile
	fig2dev -L pstex               $(FIG_OPTS) $< $*.pstex
	fig2dev -L pstex_t -p $*.pstex $(FIG_OPTS) $< $*.pstex_t

clean: 
	rm -f itp11.dvi itp11.ps itp11.pdf itp11.aux itp11.log itp11.out lem_trans.pstex lem_trans.pstex_t
