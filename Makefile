
PANDOC=--standalone --table-of-contents --number-sections --bibliography bibliography.json --from markdown+raw_tex --pdf-engine=xelatex

all: arbeit.pdf #notizen.pdf essay.pdf 

%.latex : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.pdf : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.html : %.md Makefile
	pandoc $(PANDOC) -t html $< > $@
