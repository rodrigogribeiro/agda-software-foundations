default: sf

sf:
	lhs2TeX --agda Sf.lagda > Sf.tex
	pdflatex Sf.tex
	pdflatex Sf.tex
clean:
	rm *.tex
	rm *.pdf
	rm *.aux
	rm *.log
	rm *.ptb
	rm *.agdai
	rm *.toc
	rm *.out
view: sf
	evince Sf.pdf &
