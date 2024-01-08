.PHONY: default clean


default: manual.html


grammar.md: ../../../parsers/c/c_parser.mly
	echo "## Grammar" > $@
	echo '```' >> $@
	obelisk $< | awk '/prim\_expr/, 0' >> $@
	echo '```' >> $@


manual.html: manual.md grammar.md
	pandoc --standalone --highlight-style=tango --embed-resources manual.md grammar.md -t html5 -o $@


clean:
	rm grammar.md
	rm manual.html
