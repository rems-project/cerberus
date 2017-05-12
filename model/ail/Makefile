LEM= OCAMLRUNPARAM="" /Users/catzilla/University/PhD/lem-git/lem -lib /Users/catzilla/University/PhD/lem-git/library -lib ../../model \
-wl_amb_code err -wl_pat_comp err -wl_pat_exh err -wl_pat_fail err -wl_pat_red err  -wl_unused_vars err


FILES=\
  ctype.lem \
  AilSyntax.lem \
  AilTypesAux.lem \
  ErrorMonad.lem \
  GenTypesAux.lem \
  OptionMonad.lem \
  AilSyntaxAux.lem \
  AilTyping.lem \
  Common.lem \
  GenSyntax.lem \
  GenTyping.lem \
  Range.lem \
  AilTypes.lem \
  AilWf.lem \
  Context.lem \
  GenTypes.lem \
  Implementation.lem \
  TypingError.lem


all:
	@$(LEM) $(FILES)

wip:
	@$(LEM) ctype.lem AilSyntax2.lem AilTypes2.lem GenTypes2.lem
