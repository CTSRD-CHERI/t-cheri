t-cheri.pdf: t-cheri.tex references.bib
	pdflatex t-cheri.tex
	bibtex t-cheri
	pdflatex t-cheri.tex
	pdflatex t-cheri.tex

install: t-cheri.pdf
	cp t-cheri.pdf built_doc
