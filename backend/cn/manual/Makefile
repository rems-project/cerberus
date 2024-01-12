.PHONY: default clean


default: manual.html


grammar.md: ../../../parsers/c/c_parser.mly
	echo "## Grammar" > $@
	echo '```' >> $@
	obelisk $< | awk '/prim\_expr/, 0' >> $@
	echo '```' >> $@

PANDOC_EMBED_RESOURCES_CHECK=$(shell pandoc -h | grep embed.resources)

ifneq (${PANDOC_EMBED_RESOURCES_CHECK}, )
PANDOC_EMBED_RESOURCES= --embed-resources
else
PANDOC_EMBED_RESOURCES= --self-contained
endif

PANDOC_OPTS= --standalone --highlight-style=tango ${PANDOC_EMBED_RESOURCES}

manual.html: manual.md grammar.md
	pandoc ${PANDOC_OPTS} manual.md grammar.md -t html5 -o $@


clean:
	rm grammar.md
	rm manual.html
