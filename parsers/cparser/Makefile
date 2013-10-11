VALIDATOR_EXTRACTED := $(foreach f, $(foreach f, $(shell find validator/ -name '*.v'), $(shell basename $f .v)), $f.ml $f.mli)
EXTRACTED := $(VALIDATOR_EXTRACTED) Cabs0.ml Cabs0.mli Parser.ml Parser.mli

COQC= coqc

default: pre_parser.ml Parser.v Cabs0.vo
	make -C validator/
	$(COQC) -noglob -I validator Parser extraction
#	make -C coq_stdlib/

pre_parser.ml : pre_parser.mly
	menhir pre_parser.mly

Parser.v : Parser.vy
	menhir --coq --coq-no-complete Parser.vy
	@sed -i"" -e 's/Main/Validator_main/' Parser.v

Cabs0.vo : Cabs0.v
	$(COQC) -noglob Cabs0

clean:
	rm -rf *.vo

clear:
	rm -rf *.vo $(EXTRACTED)
	rm -rf _build Parser.v pre_parser.ml pre_parser.mli
