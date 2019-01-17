
PANDOC=--standalone --number-sections --bibliography bibliography.json --from markdown+raw_tex --pdf-engine=xelatex --variable papersize=a4 --variable documentclass=report

all: arbeit.pdf #notizen.pdf essay.pdf 

spell:
	aspell check arbeit.md -t --add-tex-command="Begin p" --add-tex-command="End p"

%.latex : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.pdf : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --include-in-header header.tex -t latex $< -o $@

%.twoside.pdf : %.md Makefile header.tex bibliography.json
	pandoc $(PANDOC) --variable classoption=twoside,openright --include-in-header header.tex -t latex $< -o $@

%.html : %.md Makefile
	pandoc $(PANDOC) -t html $< > $@
