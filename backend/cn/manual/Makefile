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



grammar.tex: ../../../parsers/c/c_parser.mly
	touch $@
	obelisk latex -tabular $< -o $@


latex-build:
	mkdir -p latex-build

latex-build/grammar.pdf: grammar.tex latex-build 
	pdflatex --output-directory latex-build $< 


more_readable_grammar.md: grammar.md
	cat grammar.md \
	  | sed "s#<##g" \
	  | sed "s#>##g" \
	  | sed "s#\[#[[#g" \
	  | sed "s#\]#]]\?#g" \
	  | sed "s#(#[[#g" \
	  | sed "s#)#]]#g" \
	  | sed "s#CN\_NULL#null#g" \
	  | sed "s#CN\_TRUE#true#g" \
	  | sed "s#CN\_FALSE#false#g" \
	  | sed "s#CN_ARRAY_SHIFT#array_shift#g" \
	  | sed "s#CN_MEMBER_SHIFT#member_shift#g" \
	  | sed "s#CN_UNCHANGED#unchanged#g" \
	  | sed "s#CN_INV#inv#g" \
	  | sed "s#CN_WILD#_#g" \
	  | sed "s#IF#if#g" \
	  | sed "s#ELSE#else#g" \
	  | sed "s#CN_EACH#each#g" \
	  | sed "s#CN_MATCH#match#g" \
	  | sed "s#CN_LET#let#g" \
	  | sed "s#VOID#void#g" \
	  | sed "s#CN_BOOL#boolean#g" \
	  | sed "s#CN_INTEGER#integer#g" \
	  | sed "s#CN_BITS#bits#g" \
	  | sed "s#CN_REAL#real#g" \
	  | sed "s#CN_POINTER#pointer#g" \
	  | sed "s#CN_ALLOC_ID#alloc_id#g" \
	  | sed "s#STRUCT#struct#g" \
	  | sed "s#CN_DATATYPE#datatype#g" \
	  | sed "s#CN_MAP#map#g" \
	  | sed "s#CN_LIST#cn_list#g" \
	  | sed "s#CN_TUPLE#cn_tuple#g" \
	  | sed "s#CN_set#cn_set#g" \
	  | sed "s#CN_GOOD#good#g" \
	  | sed "s#CN_FUNCTION#function#g" \
	  | sed "s#CN_LEMMA#lemma#g" \
	  | sed "s#CN_TYPE_SYNONYM#type_synonym#g" \
	  | sed "s#CN_PREDICATE#predicate#g" \
	  | sed "s#CN_SPEC#spec#g" \
	  | sed "s#CN_REQUIRES#requires#g" \
	  | sed "s#CN_ENSURES#ensures#g" \
	  | sed "s#CN_TRUSTED#trusted#g" \
	  | sed "s#CN_ACCESSES#accesses#g" \
	  | sed "s#CN_PACK#pack#g" \
	  | sed "s#CN_UNPACK#unpack#g" \
	  | sed "s#CN_EXTRACT#extract#g" \
	  | sed "s#CN_HAVE#cn_have#g" \
	  | sed "s#CN_INSTANTIATE#instantiate#g" \
	  | sed "s#CN_SPLIT_CASE#split_case#g" \
	  | sed "s#CN_UNFOLD#unfold#g" \
	  | sed "s#CN_APPLY#apply#g" \
	  | sed "s#INLINE#inline#g" \
	  | sed "s#CN_PRINT#cn_print#g" \
	  | sed "s#CN_OWNED#Owned#g" \
	  | sed "s#CN_BLOCK#Block#g" \
	  | sed "s#ASSERT#assert#g" \
	  | sed "s#SIZEOF#sizeof#g" \
	  | sed "s#OFFSETOF#offsetof#g" \
	  | sed "s#DEFAULT#default#g" \
	  | sed "s#RETURN#return#g" \
	  | sed "s#DOT DOT#..#g" \
	  | sed "s#DOT#.#g" \
	  | sed "s#PERCENT#%#g" \
	  | sed "s#COMMA#,#g" \
	  | sed "s#STAR#*#g" \
	  | sed "s#SLASH#/#g" \
	  | sed "s#AMPERSAND_AMPERSAND#\&\&#g" \
	  | sed "s#PIPE_PIPE#||#g" \
	  | sed "s#AMPERSAND#\&#g" \
	  | sed "s#SEMICOLON#;#g" \
	  | sed "s#COLON#:#g" \
	  | sed "s#QUESTION#?#g" \
	  | sed "s#CN_IMPLIES#==>#g" \
	  | sed "s#EQ GT#=>#g" \
	  | sed "s#GT_EQ#>=#g" \
	  | sed "s#LT_EQ#<=#g" \
	  | sed "s#EQ_EQ#==#g" \
	  | sed "s#EQ#=#g" \
	  | sed "s#MINUS_GT#->#g" \
	  | sed "s#MINUS#-#g" \
	  | sed "s#PLUS#+#g" \
	  | sed "s#BANG_EQ#!=#g" \
	  | sed "s#BANG#!#g" \
	  | sed "s/LBRACK/[/g" \
	  | sed "s/RBRACK/]/g" \
	  | sed "s#LT#<#g" \
	  | sed "s#GT#>#g" \
	  | sed "s#LPAREN#(#g" \
	  | sed "s#RPAREN#)#g" \
	  | sed "s#LBRACE#{#g" \
	  | sed "s#RBRACE#}#g" \
          > $@

