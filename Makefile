
PANDOC=--standalone --table-of-contents --number-sections --bibliography bibliography.json --from markdown+raw_tex --pdf-engine=xelatex --variable papersize=a4

all: arbeit.pdf #notizen.pdf essay.pdf 

spell:
	aspell check arbeit.md -t --add-tex-command="Begin p" --add-tex-command="End p"

%.latex : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.pdf : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.html : %.md Makefile
	pandoc $(PANDOC) -t html $< > $@
