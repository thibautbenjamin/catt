all: notes.pdf idee.pdf

ci:
	git ci . -m "Notes."
	git push

%.pdf: %.tex $(wildcard *.sty)
	if [ -e /usr/bin/rubber ] ; then rubber -d $< ; else pdflatex $< ; fi
