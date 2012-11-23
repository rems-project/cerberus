all: all.pdf
core: core.pdf

all.tex: AilAux.ott AilTypes.ott AilTyping.ott Common.ott Ail.ott AilTypingAux.ott AilWf.ott
	ott -merge true     \
	-i Common.ott       \
	-i AilAux.ott       \
	-i Ail.ott          \
	-i AilTypes.ott     \
	-i AilTypingAux.ott \
	-i AilTyping.ott    \
	-i AilWf.ott        \
	-o all.tex

core.tex: AilTypes.ott Common.ott Ail.ott Core.ott
	ott -merge true -tex_wrap false \
	-i Common.ott                   \
	-i AilTypes.ott                 \
	-i Core.ott                     \
	-o core.tex

all.pdf: all.tex
	pdflatex all.tex

core.pdf: core.tex top.tex
	xelatex top.tex

core.lem: AilTypes.ott Common.ott Ail.ott Core.ott
	ott -merge true \
	-i Common.ott   \
	-i AilTypes.ott \
	-i Core.ott \
	-o core.lem

parser: AilTypes.ott Common.ott Ail.ott Core.ott
	ott -merge true \
	-i Common.ott   \
	-i AilTypes.ott \
	-i Core.ott \
	-o core.mll

clean:
	rm -rf all.pdf all.tex all.aux all.log all.v
	rm -rf top.pdf top.aux top.log
	rm -rf core.pdf core.tex core.aux core.log
	rm -rf core.lem
