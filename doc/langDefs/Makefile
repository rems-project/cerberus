all: top

ail:
	ott -tex_wrap false ail.ott common.ott -o ail.tex
	xelatex top_ail.tex


top:
	ott -tex_wrap false ail.ott core.ott common.ott -o core.tex
	xelatex -interaction=nonstopmode top.tex

clean:
	rm -f ail.tex core.tex
	rm -f *.aux *.log *.out *.toc

