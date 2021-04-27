all:
	ott -o mucore.ml mucore.ott
	ott -tex_suppress_category X -o mucore.tex mucore.ott 2>&1 > /dev/null
	pdflatex mucore.tex

clean:
	rm -rf *~
	rm -rf mucore.aux
	rm -rf mucore-inc.tex
	rm -rf mucore.lem
	rm -rf mucore.log
	rm -rf mucore.pdf
	rm -rf mucore.tex
