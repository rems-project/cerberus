ail:
	ott -tex_wrap false ail.ott common.ott -o ail.tex
	xelatex top_ail.tex


top:
	ott -tex_wrap false core.ott common.ott -o core.tex
	xelatex top.tex

clean:
	rm -f core.tex
	rm -f *.aux
	rm -f *.log
	rm -f *.toc
	rm -f *.out

