TEXFILES = $(wildcard lecture[0-9][0-9].tex)
PDFS = $(TEXFILES:.tex=.pdf)

all: $(PDFS)

%.pdf: %.tex notation.tex zk-notation.tex environments.tex lecture-macros.tex
	latexmk -pdf -interaction=nonstopmode $<

clean:
	latexmk -C

.PHONY: all clean
