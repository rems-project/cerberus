/* https://ocaml.org/releases/4.07/htmlman/lexyacc.html */
/* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html */
/* https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param */
/* and from the c and core parsers */


/* todo: fix locations */

%parameter <Arg:Parse_ast.ParserArg>


%type <Parse_ast.parsed_spec> spec_entry
%start spec_entry



%{

  open Parse_ast
  open Locations
  open IndexTerms
  open Tokens
  open Cerb_frontend

  let pit (start_p, end_p) pit_ = IndexTerm (region (start_p, end_p) None, pit_)

%}


%%





spec_entry:
  | o = resource EOF                   { o }
  | e = expr EOF                       { C e }


;



basename:
  | id = ID AT label = ID            { {label; v = id} }
  | id = ID                          { {label = Arg.default_label; v = id} }


/* stealing from Core parser */
/* todo */
integer_base_type:
| ICHAR
    { Ctype.Ichar }
| SHORT
    { Ctype.Short }
| INT
    { Ctype.Int_ }
| LONG
    { Ctype.Long }
| LONG_LONG
    { Ctype.LongLong }
;

integer_type:
| CHAR
    { Ctype.Char }
| BOOL
    { Ctype.Bool }
| INT8_T
    { Ctype.Signed (Ctype.IntN_t 8) }
| INT16_T
    { Ctype.Signed (Ctype.IntN_t 16) }
| INT32_T
    { Ctype.Signed (Ctype.IntN_t 32) }
| INT64_T
    { Ctype.Signed (Ctype.IntN_t 64) }
| UINT8_T
    { Ctype.Unsigned (Ctype.IntN_t 8) }
| UINT16_T
    { Ctype.Unsigned (Ctype.IntN_t 16) }
| UINT32_T
    { Ctype.Unsigned (Ctype.IntN_t 32) }
| UINT64_T
    { Ctype.Unsigned (Ctype.IntN_t 64) }
| INTMAX_T
    { Ctype.(Signed Intmax_t) }
| INTPTR_T
    { Ctype.(Signed Intptr_t) }
| UINTMAX_T
    { Ctype.(Unsigned Intmax_t) }
| UINTPTR_T
    { Ctype.(Unsigned Intptr_t) }
| SIGNED ibty= integer_base_type
    { Ctype.Signed ibty }
| UNSIGNED ibty= integer_base_type
    { Ctype.Unsigned ibty }
| SIZE_T
    { Ctype.Size_t }
| PTRDIFF_T
    { Ctype.Ptrdiff_t }
;

/* floating_type: */
/* | FLOAT */
/*     { Ctype.(RealFloating Float) } */
/* | DOUBLE */
/*     { Ctype.(RealFloating Double) } */
/* | LONG_DOUBLE */
/*     { Ctype.(RealFloating LongDouble) } */
/* ; */

/* basic_type: */
/* | ity= integer_type */
/*     { Ctype.Integer ity } */
/* | fty= floating_type */
/*     { Ctype.Floating fty } */
/* ; */

/* ctype: */
/* | VOID */
/*     { Ctype.void } */
/* | bty= basic_type */
/*   { Ctype.Ctype ([], Ctype.Basic bty) } */
/* | ty= ctype LBRACKET n_opt= NUM? RBRACKET */
/*     { Ctype.Ctype ([], Ctype.Array (ty, n_opt)) } */
/* | ty= ctype tys= delimited(LPAREN, separated_list(COMMA, ctype), RPAREN) */
/*     { Ctype.Ctype ([], Function (false, (Ctype.no_qualifiers, ty), List.map (fun ty -> (Ctype.no_qualifiers, ty, false)) tys, false)) } */
/* | ty= ctype STAR */
/*     { Ctype.Ctype ([], Ctype.Pointer (Ctype.no_qualifiers, ty)) } */
/* | ATOMIC ty= delimited(LPAREN, ctype, RPAREN) */
/*     { Ctype.Ctype ([], Ctype.Atomic ty) } */
/* | STRUCT tag= ID */
/*     { Ctype.Ctype ([], Ctype.Struct (Sym.fresh_named tag)) } */
/* ; */

/* end */

/* pred:  */
/*   | OWNED                               { Owned }  */
/*   | REGION LBRACKET i = NUM RBRACKET    { Region (Z.of_int i) }  */
/*   | BLOCK                               { Block }  */
/*   | id = ID                             { Pred (Id.parse Location_ocaml.unknown id) }  */

/* looking at core parser */
pred_with_args:
  | pr = ID ps = delimited(LPAREN, separated_list(COMMA, predarg), RPAREN)   { (pr,ps) }

predarg:
  | p = path { Path.PathArg p }
  | z = NUM  { Path.NumArg (Z.of_int z) }

path: 
  | LPAREN pr_ps = pred_with_args RPAREN DOT id = ID   { Path.PredArg (fst pr_ps, snd pr_ps, id) }
  | AMPERSAND bn = basename          { Path.Addr bn }
  | STAR p = path                    { Path.Pointee p }
  | bn = basename                    { Path.Var bn }

%inline resource:
  | pr_ps = pred_with_args         { R (fst pr_ps, snd pr_ps) }





expr_or_path:
  | p = path                { pit ($startpos, $endpos) (Path p) }
  | e = expr                { e }

expr:
  | TRUE                                    { pit ($startpos, $endpos) (Bool true) }
  | FALSE                                   { pit ($startpos, $endpos) (Bool false) }
  | i = NUM                                 { pit ($startpos, $endpos) (Num (Z.of_int i)) }
  | MIN LPAREN it = integer_type RPAREN     { pit ($startpos, $endpos) (MinInteger it) }
  | MAX LPAREN it = integer_type RPAREN     { pit ($startpos, $endpos) (MaxInteger it) }
  | POINTER_TO_INTEGER expr_or_path        { pit ($startpos, $endpos) (PointerToIntegerCast ($2)) }
  | INTEGER_TO_POINTER expr_or_path        { pit ($startpos, $endpos) (IntegerToPointerCast ($2)) }
  | expr_or_path LT expr_or_path            { pit ($startpos, $endpos) (LT ($1,$3)) }
  | expr_or_path GT expr_or_path            { pit ($startpos, $endpos) (GT ($1,$3)) }
  | expr_or_path LE expr_or_path            { pit ($startpos, $endpos) (LE ($1,$3)) }
  | expr_or_path GE expr_or_path            { pit ($startpos, $endpos) (GE ($1,$3)) }
  | expr_or_path EQEQ expr_or_path          { pit ($startpos, $endpos) (EQ ($1,$3)) }
  | expr_or_path NE expr_or_path            { pit ($startpos, $endpos) (NE ($1,$3)) }
  | expr_or_path PLUS expr_or_path          { pit ($startpos, $endpos) (Add ($1,$3)) }
  | expr_or_path MINUS expr_or_path         { pit ($startpos, $endpos) (Sub ($1,$3)) }
  | expr_or_path STAR expr_or_path          { pit ($startpos, $endpos) (Mul ($1,$3)) }
  | expr_or_path DIV expr_or_path           { pit ($startpos, $endpos) (Div ($1,$3)) }
  | MIN LPAREN i1 = expr_or_path COMMA i2 = expr_or_path RPAREN    { pit ($startpos, $endpos) (Min (i1,i2)) }
  | MAX LPAREN i1 = expr_or_path COMMA i2 = expr_or_path RPAREN    { pit ($startpos, $endpos) (Max (i1,i2)) }
  | LPAREN expr RPAREN { $2 }
;


