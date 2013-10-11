Require Parser.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)" [ "(,)" ].

Extraction Blacklist List (* String *) Int.

Extraction Library Parser.
Extraction Library Cabs0.
Extraction Library Alphabet.
Extraction Library Automaton.
Extraction Library Grammar.
Extraction Library Interpreter.
Extraction Library Interpreter_safe.
Extraction Library Interpreter_correct.
Extraction Library Interpreter_complete.
Extraction Library Validator_safe.
Extraction Library Validator_complete.
Extraction Library Validator_main.
Extraction Library Tuples.
