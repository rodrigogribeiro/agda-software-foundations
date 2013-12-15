default: sf

sf: Sf.lagda Preface.lagda Basics.lagda
	lhs2TeX --agda Sf.lagda > Sf.tex
	pdflatex Sf.tex
clean:
	rm *.tex
	rm *.pdf
	rm *.aux
	rm *.log
	rm *.ptb
view: sf
	evince Sf.pdf &
