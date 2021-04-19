all:
	ott -o mucore.lem -o mucore.tex mucore.ott
	ott -o mucore-inc.tex -tex_wrap false mucore.ott
	pdflatex mucore.tex

clean:
	rm -rf *~
	rm -rf mucore.aux
	rm -rf mucore-inc.tex
	rm -rf mucore.lem
	rm -rf mucore.log
	rm -rf mucore.pdf
	rm -rf mucore.tex
