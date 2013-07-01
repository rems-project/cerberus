FILES= Alphabet.v Tuples.v Grammar.v Automaton.v Validator_complete.v \
       Interpreter.v Interpreter_complete.v Interpreter_correct.v \
       Validator_safe.v Interpreter_safe.v \
       Validator_main.v

COQC=/usr/local/bin/coqc # TODO: this is local to AddaX (to get coq 8.3pl3)


default: $(FILES:.v=.vo)

%.vo : %.v
	@echo COQC $<
	@$(COQC) -noglob $<

clean:
	rm -rf *.vo
