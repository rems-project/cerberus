%{
(* 
  There are 3 ambiguities that OCaml solves with the first letter case 
  distinction for identifiers:
   - In a long identifier a.b.c.d.e, which dots are record projections and
     which are module projections
   - In type t = u, whether u should refer to an existing type constructor, or 
     be defined as a nullary data constructor 
   - In let x y = exp, whether a function x of 1 argument is declared, or if
     x y is taken to be a constructor pattern, so a value is bound for y.

   In the first case, I assume all module projections and let the type system
   disambiguate

   In the other two cases I default to type constructor, and function respectively.  
   I believe these should be the common case.  In the latter, parens allow the other 
   meaning, as in let (x y) = exp.  In the former, a bar allows the other
   meaning, as in type t = | u .

   TODO: BquoteX

   *)
let r = Ulib.Text.of_latin1

open Ast

let loc () = Range(Parsing.symbol_start_pos(),Parsing.symbol_end_pos())
let locn m n = Range(Parsing.rhs_start_pos m,Parsing.rhs_end_pos n)

let tloc t = Typ_l(t,loc ())
let lloc l = Lit_l(l,loc ())
let ploc p = Pat_l(p,loc ())
let eloc e = Expr_l(e,loc ())
let lbloc lb = Letbind(lb,loc ())
let dloc d = Def_l(d,loc ())
let irloc ir = Rule_l(ir,loc())
let reclloc fcl = Rec_l(fcl,loc())

let pat_to_let p =
  match p with
    | Pat_l(P_app(Id([],v,_),(arg::args as a)),_) ->
        Some((v,a))
    | _ ->
        None

let pat_to_letfun p =
  match p with
    | Pat_l(P_app(Id([],v,_),(arg::args as a)),_) ->
        (v,a)
    | Pat_l(_,l) -> 
        raise (Parse_error_locn(l,"Bad pattern for let binding of a function"))

let get_target (s1,n) =
  if Ulib.Text.compare n (r"hol") = 0 then
    Target_hol(s1)
  else if Ulib.Text.compare n (r"ocaml") = 0 then
    Target_ocaml(s1)
  else if Ulib.Text.compare n (r"coq") = 0 then
    Target_coq(s1)
  else if Ulib.Text.compare n (r"isabelle") = 0 then
    Target_isa(s1)
  else if Ulib.Text.compare n (r"tex") = 0 then
    Target_tex(s1)
  else
    raise (Parse_error_locn(loc (),"Expected substitution target in {hol; isabelle; ocaml; coq; tex}, given " ^ Ulib.Text.to_string n))

let build_fexp (Expr_l(e,_)) l =
  match e with
    | Infix(Expr_l(Ident(i), l'),SymX_l((stx,op),l''),e2) when Ulib.Text.compare op (r"=") = 0 ->
        Fexp(i, stx, e2, l)
    | _ ->
        raise (Parse_error_locn(l,"Invalid record field assignment (should be id = exp)"))

let mod_cap n =
  if not (Name.starts_with_upper_letter (Name.strip_lskip (Name.from_x n))) then
    raise (Parse_error_locn(Ast.xl_to_l n, "Module name must begin with an upper-case letter"))
  else
    ()


%}

%token <Ast.terminal> Dot Lparen Rparen Comma Under Arrow As Colon Lcurly Rcurly
%token <Ast.terminal> Semi Lsquare Rsquare Fun_ Function_ Bar With Match Let_ And
%token <Ast.terminal> In Of Rec Type Module_ Struct End Open_ SemiSemi Eof
%token <Ast.terminal> True False Begin_ If_ Then Else Val
%token <Ast.terminal * Ulib.Text.t> AmpAmp BarBar ColonColon Star Eq
%token <Ast.terminal * Ulib.Text.t> X Tyvar BquoteX
%token <Ast.terminal * Ulib.Text.t> StarstarX StarX PlusX AtX EqualX 
%token <Ast.terminal * int> Num
%token <Ast.terminal * string> String

%token <Ast.terminal> Indreln Forall EqEqGt Inline LtBar BarGt Exists EqGt
%token <Ast.terminal * Ulib.Text.t> IN MEM MinusMinusGt
%token <Ast.terminal> Class_ Inst

%start file
%type <Ast.defs> defs
%type <Ast.typ> typ
%type <Ast.pat> pat
%type <Ast.exp> exp
%type <Ast.defs * Ast.terminal> file


%%

x:
  | X
    { X_l($1, loc ()) }
  | Lparen Eq Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen IN Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen MEM Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen MinusMinusGt Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen AmpAmp Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen BarBar Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen ColonColon Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen Star Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen PlusX Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen StarX Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen EqualX Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen StarstarX Rparen
    { PreX_l($1, $2, $3, loc ()) }
  | Lparen AtX Rparen
    { PreX_l($1, $2, $3, loc ()) }

id:
  | id_help
    { Id(fst $1, snd $1, loc ()) }

id_help:
  | x
    { ([],$1) }
  | x Dot id_help
    { let (l,last) = $3 in
        (($1,$2)::l, last) }

tyvar:
  | Tyvar
    { A_l((fst $1, snd $1), loc ()) }

atomic_typ:
  | Under
    { tloc (Typ_wild($1)) }
  | tyvar
    { tloc (Typ_var($1)) }
  | id
    { tloc (Typ_app(None,[],None,$1)) }
  | Lparen comma_typs Rparen id
    { tloc (Typ_app($1,$2,$3,$4)) }
  | Lparen typ Rparen
    { tloc (Typ_paren($1,$2,$3)) }

app_typ:
  | atomic_typ
    { $1 }
  | app_typ id
    { tloc (Typ_app(None,[($1,None)],None,$2)) }
  

star_typ_list:
  | app_typ
    { [($1,None)] }
  | app_typ Star star_typ_list
    { ($1,fst $2)::$3 }

star_typ:
  | star_typ_list
    { match $1 with
        | [] -> assert false
        | [(t,None)] -> t
        | [(t,Some _)] -> assert false
        | ts -> tloc (Typ_tup(ts)) }

typ:
  | star_typ
    { $1 }
  | star_typ Arrow typ
    { tloc (Typ_fn($1,$2,$3)) }

comma_typs:
  | typ Comma typ
  { [($1,$2);($3,None)] }
  | typ Comma comma_typs
    { ($1,$2)::$3 }

lit:
  | True
    { lloc (L_true($1)) }
  | False
    { lloc (L_false($1)) }
  | Num
    { lloc (L_num(fst $1, snd $1)) }
  | String
    { lloc (L_string(fst $1, snd $1)) }
  | Lparen Rparen
    { lloc (L_unit($1,$2)) }

atomic_pat:
  | Under
    { ploc (P_wild($1)) }
  | id
    { ploc (P_app($1,[])) }
  | Lparen pat Colon typ Rparen
    { ploc (P_typ($1,$2,$3,$4,$5)) }
  | LtBar fpats BarGt
    { ploc (P_record($1,fst $2,fst (snd $2),snd (snd $2),$3)) }
  | Lparen comma_pats Rparen
    { ploc (P_tup($1,$2,$3)) }
  | Lparen pat Rparen
    { ploc (P_paren($1,$2,$3)) }
  | Lsquare semi_pats Rsquare
    { ploc (P_list($1,fst $2,fst (snd $2),snd (snd $2),$3)) }
  | lit
    { ploc (P_lit($1)) }

left_atomic_pat:
  | pat As x
    { ploc (P_as($1,$2,$3)) }

atomic_pats:
  | atomic_pat
    { [$1] }
  | atomic_pat atomic_pats
    { $1::$2 }

app_pat:
  | atomic_pat
    { $1 }
  | id atomic_pats
    { ploc (P_app($1,$2)) }

cons_pat:
  | app_pat
    { $1 }
  | app_pat ColonColon cons_pat
    { ploc (P_cons($1,fst $2,$3)) } 

left_cons_pat:
  | left_atomic_pat
    { $1 }
  | left_atomic_pat ColonColon cons_pat
    { ploc (P_cons($1,fst $2,$3)) } 

pat:
  | cons_pat
    { $1 }
  | left_cons_pat
    { $1 }

semi_pats_help:
  | pat
    { ([($1,None)], (None,false)) }
  | pat Semi
    { ([($1,None)], ($2,true)) }
  | pat Semi semi_pats_help
    { (($1,$2)::fst $3, snd $3) }

semi_pats:
  |
    { ([], (None, false)) }
  | semi_pats_help
    { $1 }


comma_pats:
  | pat Comma pat
    { [($1,$2);($3,None)] }
  | pat Comma comma_pats
    { ($1,$2)::$3 }

fpat:
  | id Eq pat
    { Fpat($1,fst $2,$3,loc ()) }

fpats:
  | fpat
    { ([($1,None)], (None,false)) }
  | fpat Semi
    { ([($1,None)], ($2,true)) }
  | fpat Semi fpats
    { (($1,$2)::fst $3, snd $3) }

atomic_exp:
  | LtBar fexps BarGt
    { eloc (Record($1,$2,$3)) }
  | LtBar at_exp With fexps BarGt
    { eloc (Recup($1,$2,$3,$4,$5)) }
  | Lparen exp Colon typ Rparen
    { eloc (Typed($1,$2,$3,$4,$5)) }
  | Lsquare semi_exps Rsquare
    { eloc (List($1,fst $2,fst (snd $2), snd (snd $2), $3)) }
  | Lparen comma_exps Rparen
    { eloc (Tup($1,$2,$3)) }
  | Lparen exp Rparen
    { eloc (Paren($1,$2,$3)) }
  | Begin_ exp End
    { eloc (Begin($1,$2,$3)) }
  | lit
    { eloc (Lit($1)) }
  | Lcurly exp Bar exp Rcurly
    { eloc (Setcomp($1,$2,$3,$4,$5)) }
  | Lcurly exp Bar Forall quant_bindings Bar exp Rcurly
    { eloc (Setcomp_binding($1,$2,$3,$4,$5,$6,$7,$8)) }
  | Lcurly semi_exps Rcurly
    { eloc (Set($1,fst $2,fst (snd $2), snd (snd $2),$3)) }
  | Lsquare exp Bar Forall quant_bindings Bar exp Rsquare
    { eloc (Listcomp($1,$2,$3,$4,$5,$6,$7,$8)) }
  | Function_ patexps End
    { eloc (Function($1,None,false,$2,$3)) }
  | Function_ Bar patexps End
    { eloc (Function($1,$2,true,$3,$4)) }
  | Match exp With patexps End
    { eloc (Case($1,$2,$3,None,false,$4,locn 4 4,$5)) }
  | Match exp With Bar patexps End
    { eloc (Case($1,$2,$3,$4,true,$5,locn 5 5,$6)) }

field_exp:
  | atomic_exp
    { $1 }
  | atomic_exp Dot id
    { eloc (Field($1,$2,$3)) }
  | id
    { eloc (Ident($1)) }

app_exp:
  | field_exp
    { $1 }
  | app_exp field_exp
    { eloc (App($1,$2)) }

right_atomic_exp:
  | Forall quant_bindings Dot exp
    { eloc (Quant(Q_forall($1), $2,$3,$4)) }
  | Exists quant_bindings Dot exp
    { eloc (Quant(Q_exists($1), $2,$3,$4)) }
  | If_ exp Then exp Else exp
    { eloc (If($1,$2,$3,$4,$5,$6)) }
  | Fun_ patsexp
    { eloc (Fun($1,$2)) }
  | Let_ letbind In exp
    { eloc (Let($1,$2,$3,$4)) }

starstar_exp:
  | app_exp
    { $1 }
  | app_exp StarstarX starstar_exp
    { eloc (Infix($1, SymX_l($2, locn 2 2), $3)) }

starstar_right_atomic_exp:
  | right_atomic_exp
    { $1 }
  | app_exp StarstarX starstar_right_atomic_exp
    { eloc (Infix($1, SymX_l($2, locn 2 2), $3)) }

star_exp:
  | starstar_exp
    { $1 }
  | star_exp Star starstar_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | star_exp StarX starstar_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

star_right_atomic_exp:
  | starstar_right_atomic_exp
    { $1 }
  | star_exp Star starstar_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | star_exp StarX starstar_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

plus_exp:
  | star_exp
    { $1 }
  | plus_exp PlusX star_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

plus_right_atomic_exp:
  | star_right_atomic_exp
    { $1 }
  | plus_exp PlusX star_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

cons_exp:
  | plus_exp
    { $1 }
  | plus_exp ColonColon cons_exp
    { eloc (Cons($1,fst $2,$3)) }

cons_right_atomic_exp:
  | plus_right_atomic_exp
    { $1 }
  | plus_exp ColonColon cons_right_atomic_exp
    { eloc (Cons($1,fst $2,$3)) }

at_exp:
  | cons_exp
    { $1 }
  | cons_exp AtX at_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

at_right_atomic_exp:
  | cons_right_atomic_exp
    { $1 }
  | cons_exp AtX at_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

eq_exp:
  | at_exp
    { $1 }
  | eq_exp Eq at_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp EqualX at_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp IN at_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp MEM at_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

eq_right_atomic_exp:
  | at_right_atomic_exp
    { $1 }
  | eq_exp Eq at_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp EqualX at_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp IN at_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }
  | eq_exp MEM at_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

and_exp:
  | eq_exp
    { $1 }
  | eq_exp AmpAmp and_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

and_right_atomic_exp:
  | eq_right_atomic_exp
    { $1 }
  | eq_exp AmpAmp and_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

or_exp:
  | and_exp
    { $1 }
  | and_exp BarBar or_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

or_right_atomic_exp:
  | and_right_atomic_exp
    { $1 }
  | and_exp BarBar or_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

imp_exp:
  | or_exp
    { $1 }
  | or_exp MinusMinusGt imp_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

imp_right_atomic_exp:
  | or_right_atomic_exp
    { $1 }
  | or_exp MinusMinusGt imp_right_atomic_exp
    { eloc (Infix($1,SymX_l($2, locn 2 2), $3)) }

exp:
  | imp_right_atomic_exp
    { $1 }
  | imp_exp
    { $1 }

comma_exps:
  | exp Comma exp
    { [($1,$2);($3,None)] }
  | exp Comma comma_exps
    { ($1,$2)::$3 }
 
semi_exps_help:
  | exp
    { ([($1,None)], (None,false)) }
  | exp Semi
    { ([($1,None)], ($2,true)) }
  | exp Semi semi_exps_help
    { (($1,$2)::fst $3, snd $3) }

semi_exps:
  |
    { ([], (None, false)) }
  | semi_exps_help
    { $1 }

quant_bindings:
  | x
    { [Qb_var($1)] }
  | Lparen pat IN exp Rparen
    { [Qb_restr($1,$2,fst $3,$4,$5)] }
  | Lparen pat MEM exp Rparen
    { [Qb_list_restr($1,$2,fst $3,$4,$5)] }
  | x quant_bindings
    { Qb_var($1)::$2 }
  | Lparen pat IN exp Rparen quant_bindings
    { Qb_restr($1,$2,fst $3,$4,$5)::$6 }
  | Lparen pat MEM exp Rparen quant_bindings
    { Qb_list_restr($1,$2,fst $3,$4,$5)::$6 }

patsexp:
  | atomic_pats1 Arrow exp
    { Patsexp($1,$2,$3,loc ()) }

opt_typ_annot:
  | 
    { Typ_annot_none }
  | Colon typ
    { Typ_annot_some($1,$2) }

atomic_pats1:
  | atomic_pat
    { [$1] }
  | atomic_pat atomic_pats1
    { $1::$2 }

patexps:
  | pat Arrow exp
    { [(Patexp($1,$2,$3,loc ()),None)] }
  | pat Arrow exp Bar patexps
    { (Patexp($1,$2,$3,locn 1 3),$4)::$5 }

fexp:
  | id Eq exp
    { Fexp($1,fst $2,$3,loc()) }

fexps:
  | fexps_help
    { Fexps(fst $1, fst (snd $1), snd (snd $1), loc ()) }

fexps_help:
  | fexp
    { ([($1,None)], (None,false)) }
  | fexp Semi
    { ([($1,None)], ($2,true)) }
  | fexp Semi fexps_help
    { (($1,$2)::fst $3, snd $3) }

letbind:
  | pat opt_typ_annot Eq exp
    { match pat_to_let $1 with
        | Some((v,pats)) ->
            lbloc (Let_fun(Funcl(v,pats,$2,fst $3,$4)))
        | None ->
            lbloc (Let_val($1,$2,fst $3,$4)) }


funcl: 
  | x atomic_pats1 opt_typ_annot Eq exp
    { reclloc (Funcl($1,$2,$3,fst $4,$5)) }

funcls:
  | x atomic_pats1 opt_typ_annot Eq exp
    { [(reclloc (Funcl($1,$2,$3,fst $4,$5)),None)] }
  | funcl And funcls
    { ($1,$2)::$3 }

xs:
  |
    { [] }
  | x xs
    { $1::$2 }

exps:
  |
    { [] }
  | field_exp exps
    { $1::$2 }
 
indreln_clause:
  | Forall xs Dot exp EqEqGt x exps
    { irloc (Rule($1,$2,$3,$4,$5,$6,$7)) }


and_indreln_clauses:
  | indreln_clause
    { [($1,None)] }
  | indreln_clause And and_indreln_clauses
    { ($1,$2)::$3 }

tvs:
  |
    { [] }
  | tyvar tvs
    { $1::$2 }

c:
  | Lparen id tyvar Rparen
    { C($1,$2,$3,$4) }

cs:
  | c
    { [$1] }
  | c cs
    { $1::$2 }

c2:
  | Lparen id typ Rparen
    { 
      match $3 with
        | Typ_l(Typ_var(a_l),_) ->
            C($1,$2,a_l,$4) 
        | _ -> 
          raise (Parse_error_locn(loc (),"Invalid class constraint"))
    }

cs2:
  | c2
    { [$1] }
  | c2 cs2
    { $1::$2 }

typschm:
  | typ
    { Ts(C_pre_empty, $1) }
  | Forall tvs Dot typ
    { Ts(C_pre_forall($1,$2,$3,Cs_empty),$4) }
  | Forall tvs Dot cs EqGt typ
    { Ts(C_pre_forall($1,$2,$3,Cs_list($4,$5)), $6) }

instschm:
  | Lparen id typ Rparen
    { Is(C_pre_empty, $1,$2,$3,$4) }
  | Forall tvs Dot Lparen id typ Rparen
    { Is(C_pre_forall($1,$2,$3,Cs_empty),$4,$5,$6,$7) }
  | Forall tvs Dot cs2 EqGt Lparen id typ Rparen
    { Is(C_pre_forall($1,$2,$3,Cs_list($4,$5)),$6,$7,$8,$9) }

val_spec:
  | Val x Colon typschm
    { Val_spec($1,$2,$3,$4) }

class_val_spec:
  | Val x Colon typ
    { ($1,$2,$3,$4) }

class_val_specs:
  | class_val_spec
    { [(fun (a,b,c,d) -> (a,b,c,d,loc())) $1] }
  | class_val_spec class_val_specs
    { ((fun (a,b,c,d) -> (a,b,c,d,loc())) $1)::$2 }

targets:
  | X
    { [(get_target $1,None)] }
  | X Semi targets
    { (get_target $1, $2)::$3 }

targets_opt:
  |
    { None }
  | Lcurly Rcurly
    { Some(Targets_concrete($1,[],$2)) }
  | Lcurly targets Rcurly
    { Some(Targets_concrete($1,$2,$3)) }
    
val_def:  
  | Let_ targets_opt letbind
    { Let_def($1,$2,$3) }
  | Let_ Rec targets_opt funcls
    { Let_rec($1,$2,$3,$4) }
  | Let_ Inline targets_opt letbind
    { Let_inline($1,$2,$3,$4) }

val_defs:
  | val_def
    { [($1,loc())] }
  | val_def val_defs
    { ($1,loc ())::$2 }

def:
  | Type tds
    { dloc (Type_def($1,$2)) }
  | val_def
    { dloc (Val_def($1)) }
  | Module_ x Eq Struct defs End
    { mod_cap $2; dloc (Module($1,$2,fst $3,$4,$5,$6)) }
  | Module_ x Eq id
    { mod_cap $2; dloc (Rename($1,$2,fst $3,$4)) }
  | Open_ id
    { dloc (Open($1,$2)) }
  | Indreln targets_opt and_indreln_clauses
    { dloc (Indreln($1,$2,$3)) }
  | val_spec
    { dloc (Spec_def($1)) }
  | Class_ Lparen x tyvar Rparen class_val_specs End
    { dloc (Class($1,$2,$3,$4,$5,$6,$7)) }
  | Inst instschm val_defs End
    { dloc (Instance($1,$2,$3,$4)) }

xtyp:
  | x Colon typ
    { ($1,$2,$3) }
   
xtyps:
  | xtyp
    { ([($1,None)], (None, false)) }
  | xtyp Semi
    { ([($1,None)], ($2, true)) }
  | xtyp Semi xtyps
    { (($1,$2)::fst $3, snd $3) }

ctor_texp:
  | x Of star_typ_list
    { Cte($1,$2,$3) }
  | x
    { Cte($1,None,[]) }

ctor_single_texp:
  | x Of star_typ_list
    { Cte($1,$2,$3) }
    
ctor_texps:
  | ctor_texp
    { [($1,None)] }
  | ctor_texp Bar ctor_texps
    { ($1,$2)::$3 }

texp:
  | typ
    { Te_abbrev($1) }
  | LtBar xtyps BarGt
    { Te_record($1,fst $2, fst (snd $2), snd (snd $2), $3) }    
  | Bar ctor_texps
    { Te_variant($1,true,$2) }
  | ctor_texp Bar ctor_texps
    { Te_variant(None,false,($1,$2)::$3) }
  | ctor_single_texp
    { Te_variant(None,false,[($1,None)]) }
 
comma_tvs:
  | tyvar Comma tyvar
    { [($1,$2);($3,None)] }
  | tyvar Comma comma_tvs
    { ($1,$2)::$3 }

td:
  | x
    { Td_opaque(None,[],None,$1) }
  | x Eq texp
    { Td(None,[],None,$1,fst $2,$3) }
  | tyvar x
    { Td_opaque(None,[($1,None)],None,$2) }
  | tyvar x Eq texp
    { Td(None,[($1,None)],None,$2,fst $3,$4) }
  | Lparen comma_tvs Rparen x
    { Td_opaque($1,$2,$3,$4) }
  | Lparen comma_tvs Rparen x Eq texp
    { Td($1,$2,$3,$4,fst $5,$6) }

tds:
  | td
    { [($1,None)] }
  | td And tds
    { ($1,$2)::$3 }

defs_help:
  | def
    { [($1,None,false)] }
  | def SemiSemi
    { [($1,$2,true)] }
  | def defs_help
    { ($1,None,false)::$2 }
  | def SemiSemi defs_help
    { ($1,$2,true)::$3 }

defs:
  | defs_help
    { Defs($1) }

file:
  | defs Eof
    { ($1,$2) }

