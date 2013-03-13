VALIDATOR_EXTRACTED := $(foreach f, $(foreach f, $(shell find validator/ -name '*.v'), $(shell basename $f .v)), $f.ml $f.mli)
EXTRACTED := $(VALIDATOR_EXTRACTED) Cabs0.ml Cabs0.mli Parser.ml Parser.mli

extraction:
	make -C validator/
	menhir --coq Parser.vy
	coqc -noglob Cabs0
	coqc -noglob -I validator Parser extraction
	make -C coq_stdlib/

clean:
	make -C validator/ clean
	make -C coq_stdlib/ clean
	rm -rf *.vo

clear:
	make -C validator/ clean
	make -C coq_stdlib/ clear
	rm -rf *.vo $(EXTRACTED)
	rm -rf _build Parser.v pre_parser.ml pre_parser.mli
