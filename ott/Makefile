all: all.pdf
core: core.pdf

all.tex: AilAux.ott  AilTypes.ott      AilTyping.ott  Common.ott Ail.ott     AilTypingAux.ott  AilWf.ott 
	ott -merge true  \
	-i Common.ott	 \
	-i AilAux.ott	 \
	-i Ail.ott		 \
	-i AilTypes.ott	 \
	-i AilTypingAux.ott \
	-i AilTyping.ott	 \
	-i AilWf.ott        \
	-o all.tex

core.tex: AilTypes.ott Common.ott Ail.ott Core.ott
	ott -merge true  \
	-i Common.ott	 \
	-i AilTypes.ott	 \
	-i Core.ott \
	-o core.tex
#	-i Ail.ott		 \
#	-i AilAux.ott	 \
#	-i AilTypingAux.ott \
#	-i AilTyping.ott	 \


all.pdf: all.tex
	pdflatex all.tex

core.pdf: core.tex
	  pdflatex core.tex

clean:
	rm -rf all.pdf all.tex all.lem all.v core.pdf core.tex
