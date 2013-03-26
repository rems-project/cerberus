FILES= Alphabet.v Tuples.v Grammar.v Automaton.v Validator_complete.v \
       Interpreter.v Interpreter_complete.v Interpreter_correct.v \
       Validator_safe.v Interpreter_safe.v \
       Validator_main.v

default: $(FILES:.v=.vo)

%.vo : %.v
	@echo COQC $<
	@coqc -noglob $<

clean:
	rm -rf *.vo
