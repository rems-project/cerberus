all:
	ott -o core.lem -o core.tex core.ott
	ott -o core-inc.tex -tex_wrap false core.ott
	pdflatex core.tex

push:
	$(MAKE)
	cp core-inc.tex ../../../rsem/csem/pldi2016-submission-sequential
