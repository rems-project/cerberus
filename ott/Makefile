all: all.pdf

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


all.pdf: all.tex
	pdflatex all.tex

clean:
	rm -rf all.pdf all.tex all.lem all.v
