NAME = chickenpox
#VERSION := $(shell sed -n 's/^[\ ]*version[\ ]*=[\ ]*\"\([0-9\.]*\)\"/\1/p' META)
VERSION := $(hg log -r tip --template '{latesttag}.{latesttagdistance}-{node|short}')

NATIVE ?= no
IGNORE_DIRS = playground

OCAMLBUILD ?= ocamlbuild -package text -cflag -rectypes -I src -I lib/frontc -I lib/pprint -classic-display -Xs $(IGNORE_DIRS)

TARGETS = src/chickenpox.byte
#TEST_TARGETS = testsuite/main.byte

#ifeq ($(NATIVE), yes)
#  TARGETS += native.otarget
#  TEST_TARGETS += testsuite/main.native
#endif

.PHONY: all clean #test doc install uninstall release

all:
#	ls -1 src/*.ml | sed -n 's/\(.*\)\.ml$$/\1\.byte/p' > byte.itarget
#	test -e src/_build || ln -s ../_build/src src/_build
	$(OCAMLBUILD) $(TARGETS)

clean:
	rm -Rf docs
	rm -Rf src/_build
	$(OCAMLBUILD) -clean

%.byte:
	test -e src/_build || ln -s ../_build/src src/_build
	$(OCAMLBUILD) src/$@

%.top:
	$(OCAMLBUILD) $@.top
#	find _build -regex .*cmo | sed 's/_build\///; s/.cmo//' > $@.mltop && 

#doc:
#	$(OCAMLBUILD) docdir/index.html
#	test -e docs || ln -s _build/docdir docs

#install: all
#	ocamlfind install $(OCAMLFIND_DEST) $(NAME) $(INSTALL_FILES)

#uninstall:
#	ocamlfind remove $(OCAMLFIND_DEST) $(NAME)
#	rm -rf $(DOCROOT)

#install-doc: doc
#	mkdir -p $(DOCROOT)
#	cp -r doc/* $(DOCROOT)
#	# deal with symlink that will break
#	mkdir -p $(DOCROOT)/
#	cp docs/* $(DOCROOT)/

#test: 
#	$(OCAMLBUILD) $(TARGETS) $(TEST_TARGETS)
#	$(foreach TEST, $(TEST_TARGETS), _build/$(TEST); )

#release: test
#	test -e releases || ln -s _build/docdir docs
#	hg archive --type=tar --prefix chickenpox-$(VERSION)/ --rev tip releases /\
#	  | gzip > chickenpox-$(VERSION).tar.gz
