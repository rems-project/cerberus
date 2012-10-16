%{


type expr =
  | Kskip
  | Kconst of int
(*  | Kaddr of Core.mem_addr *)
  | Ksym of string
  | Kop of Core.binop * expr * expr
  | Ktrue
  | Kfalse
  | Knot of expr
  | Kctype of Ail.ctype
  | Klet of string * expr * expr
  | Kif of expr * expr * expr
  | Kcall of string * expr list
  | Ksame of expr * expr
  | Kundef
  | Kerror
  | Kaction of paction
  | Kunseq of expr list
  | Kwseq of (string option) list * expr * expr
  | Ksseq of (string option) list * expr * expr
  | Kaseq of string option * action * paction
  | Kindet of expr (* TODO: add unique indices *)
  | Kbound of int * expr
  | Ksave of string * expr
  | Krun of string

and action =
  | Kcreate of expr
  | Kalloc of expr
  | Kkill of expr
  | Kstore of expr * expr * expr
  | Kload of expr * expr
and paction = Core.polarity * action


(* TODO *)
let convert e arg_syms fsyms =
  let rec f ((count, syms) as st) = function
    | Kskip                     -> Core.Kskip
    | Kconst n                  -> Core.Kconst n
    | Ksym a                    -> Core.Ksym (Pmap.find a syms) (* Error handling *)
    | Kop (binop, e1, e2)       -> Core.Kop (binop, f st e1, f st e2)
    | Ktrue                     -> Core.Ktrue
    | Kfalse                    -> Core.Kfalse
    | Knot e                    -> Core.Knot (f st e)
    | Kctype ty                 -> Core.Kctype ty
    | Klet (a, e1, e2)          -> let _a = (count, Some a) in Core.Klet (_a, f st e1, f (count+1, Pmap.add a _a syms) e2)
    | Kif (e1, e2, e3)          -> Core.Kif (f st e1, f st e2, f st e3)
    | Kcall (func, args)        -> Core.Kcall (Pmap.find func fsyms, List.map (f st) args)
    | Ksame (e1, e2)            -> Core.Ksame (f st e1, f st e2)
    | Kundef                    -> Core.Kundef
    | Kerror                    -> Core.Kerror
    | Kaction pact              -> Core.Kaction (g st pact)
    | Kunseq es                 -> Core.Kunseq (List.map (f st) es)
    | Kwseq (_as, e1, e2)      -> let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
                                     match sym_opt with
                                       | Some sym -> let _a = (c, Some sym) in (c+1, Some _a :: _as, Pmap.add sym _a syms)
                                       | None     -> (c+1, None :: _as, syms)) (count, [], Pmap.empty compare) _as in
                                   
                                   Core.Kwseq (_as', f st e1, f (count', syms') e2)
    | Ksseq (_as, e1, e2)       -> let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
                                     match sym_opt with
                                       | Some sym -> let _a = (c, Some sym) in (c+1, Some _a :: _as, Pmap.add sym _a syms)
                                       | None     -> (c+1, None :: _as, syms)) (count, [], Pmap.empty compare) _as in
                                   
                                   Core.Ksseq (_as', f st e1, f (count', syms') e2)
    | Kaseq (_a_opt, act, pact) -> failwith "TODO: aseq"
    | Kindet e                  -> Core.Kindet (f st e)
    | Kbound (i, e)             -> failwith "TODO: bound"
    | Ksave (k, e)              -> failwith "TODO: save"
    | Krun k                    -> failwith "TODO: run"
  and g st (p, act) =(p,
    match act with
      | Kcreate e_ty            -> (Pset.empty compare, Core.Kcreate (f st e_ty))
      | Kalloc e_n              -> (Pset.empty compare, Core.Kalloc (f st e_n))
      | Kkill e_o               -> (Pset.empty compare, Core.Kkill (f st e_o))
      | Kstore (e_ty, e_o, e_n) -> (Pset.empty compare, Core.Kstore (f st e_ty, f st e_o, f st e_n))
      | Kload (e_ty, e_o)       -> (Pset.empty compare, Core.Kload (f st e_ty, f st e_o)))
  in f (0, arg_syms) e


let mk_file funs =
  let (main, _, fsyms, fun_map) =
    List.fold_left (fun (main, count, fsyms, fun_map) (fname, fdef) ->
      (* TODO: better error *)
      if Pmap.mem fname fsyms then failwith ("duplicate definition of `" ^ fname ^ "'")
      else
        let a_fun = (count, Some fname) in
        ((if fname = "main" then Some a_fun else main), count+1,
         Pmap.add fname a_fun fsyms,
         Pmap.add a_fun fdef fun_map)
    ) (None, 0, Pmap.empty compare, Pmap.empty compare) funs
  in
  match main with
    | Some a_main -> { Core.main=    a_main;
                       Core.fun_map= Pmap.map (fun (coreTy_ret, args, fbody) ->
                                       let (_, arg_syms, args') = List.fold_left (fun (i, m, args') (x, ty) ->
                                          let _a = (i, Some x) in (i+1, Pmap.add x _a m, (_a, ty) :: args'))
                                          (0, Pmap.empty compare, []) args in
                                       (coreTy_ret, args', convert fbody arg_syms fsyms)) fun_map }
    | None        -> (* TODO: better error *) failwith "found no main function"



%}

%token CREATE ALLOC KILL STORE LOAD

%token <int> CONST
  
%token <string> SYM

%token SKIP

%token NOT

%token TRUE FALSE

%token LET IN

%token FUN END

%token PLUS MINUS STAR SLASH PERCENT
%token EQ LT
%token SLASH_BACKSLASH BACKSLASH_SLASH

%token TILDE

%token EXCLAM

%token PIPE_PIPE SEMICOLON PIPE_GT GT_GT

%token LPAREN_RPAREN UNDERSCORE
  
%token LT_MINUS

%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA COLON COLON_EQ

%token SAME

%token UNDEF ERROR

%token IF THEN ELSE

%token INTEGER BOOLEAN ADDRESS CTYPE UNIT

(* TODO: hack *)
%token SIGNED INT


%token EOF


%right GT_GT SEMICOLON
%nonassoc PIPE_PIPE


%start start
%type <Global.zero Core.file> start

%%

separated_nonempty_nonsingleton_list(separator, X):
  x1 = X separator x2 = X
    { [ x1; x2 ] }
| x = X; separator; xs = separated_nonempty_nonsingleton_list(separator, X)
    { x :: xs }


start:
| funs = nonempty_list(fun_declaration) EOF
    { mk_file funs }

core_base_type:
| INTEGER
    { Core.Integer }
| BOOLEAN
    { Core.Boolean }
| ADDRESS
    { Core.Address }
| CTYPE
    { Core.Ctype }
| UNIT
    { Core.Unit }
| baseTys = delimited (LPAREN, separated_nonempty_list(COMMA, core_base_type) , RPAREN)
    { Core.Tuple baseTys }


core_type:
| baseTy = core_base_type
    { Core.TyBase baseTy }
| baseTy = delimited(LBRACKET, core_base_type, RBRACKET)
    { Core.TyEffect baseTy }

(* TODO: find how to use the defs in cparser.mly *)
type_name:
| SIGNED INT
    { Ail.BASIC (Pset.empty Pervasives.compare, (Ail.INTEGER (Ail.SIGNED Ail.INT))) }




binary_operator:
| PLUS            { Core.OpAdd }
| MINUS           { Core.OpSub }
| STAR            { Core.OpMul }
| SLASH           { Core.OpDiv }
| PERCENT         { Core.OpMod }
| EQ              { Core.OpEq  }
| LT              { Core.OpLt  }
| SLASH_BACKSLASH { Core.OpAnd }
| BACKSLASH_SLASH { Core.OpOr  }




action:
| CREATE ty = delimited(LBRACE, expr, RBRACE)
    { Kcreate ty }
| ALLOC n = expr
    { Kalloc n }
| KILL e = expr
    { Kkill e }
| STORE ty = delimited(LBRACE, expr, RBRACE) x = expr n = expr
    { Kstore (ty, x, n) }
| LOAD ty = delimited(LBRACE, expr, RBRACE) x = expr
    { Kload (ty, x) }
;

paction:
| act = action
    { (Core.Pos, act) }
| TILDE act = action
    { (Core.Neg, act) }
;

pattern_elem:
| UNDERSCORE    { None   }
| LPAREN_RPAREN { None   } (* TODO: add a new constructor in the Ast for better type/syntax checking *)
| a = SYM       { Some a }
;

pattern:
| UNDERSCORE { [None] }
| a = SYM       { [Some a] }
| _as = delimited(LPAREN, separated_nonempty_nonsingleton_list(COMMA, pattern_elem), RPAREN) { _as }
;



%inline unseq_expr:
| es = separated_nonempty_nonsingleton_list(PIPE_PIPE, seq_expr)
    { Kunseq es }

| p = paction
    { Kaction p }

;


seq_expr:
| _as = pattern LT_MINUS e1 = unseq_expr GT_GT e2 = seq_expr
    { Kwseq (_as, e1, e2) }
| e1 = unseq_expr GT_GT e2 = seq_expr
    { Kwseq ([], e1, e2) }
| e1 = unseq_expr SEMICOLON e2 = seq_expr
    { Ksseq ([], e1, e2) }

| _as = pattern LT_MINUS e1 = unseq_expr SEMICOLON e2 = seq_expr
    { Ksseq (_as, e1, e2) }

| alpha = SYM LT_MINUS a = action PIPE_GT p = paction
    { Kaseq (Some alpha, a, p) }

| p = paction
    { Kaction p }

| e = expr
    { e }
;


expr:
| e = delimited(LPAREN, expr, RPAREN)
    { e }

| SKIP
    { Kskip }

| n = CONST
    { Kconst n }

| a = SYM
    { Ksym a }

| e1 = expr op = binary_operator e2 = expr
    { Kop (op, e1, e2) }

| TRUE
    { Ktrue }

| FALSE
    { Kfalse }

| NOT e = expr
    { Knot e }

| ty = type_name
    { Kctype ty }

| LET a = SYM EQ e1 = expr IN e2 = seq_expr (* TODO: may need to also allow unseq_expr *)
    { Klet (a, e1, e2) }

| IF b = expr THEN e1 = expr ELSE e2 = expr (* TODO: may need to also allow unseq_expr *)
    { Kif (b, e1, e2) }

| f = SYM es = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Kcall (f, es) }

| SAME e1 = expr e2 = expr
    { Ksame (e1, e2) }

| UNDEF
    { Kundef }
| ERROR
    { Kerror }

| e = delimited(LBRACKET, seq_expr, RBRACKET) (* TODO: may need to also allow unseq_expr *)
    { Kindet e } (* TODO: the index *)




fun_argument:
| x = SYM COLON ty = core_base_type
    { (x, ty) }

fun_declaration:
| FUN fname = SYM LPAREN_RPAREN COLON coreTy_ret = core_type COLON_EQ fbody = seq_expr END (* and unseq_expr ? *)
  { print_endline fname; (fname, (coreTy_ret, [], fbody)) }
| FUN fname = SYM args = delimited(LPAREN, separated_list(COMMA, fun_argument), RPAREN) COLON coreTy_ret = core_type COLON_EQ fbody = seq_expr END
  { (fname, (coreTy_ret, args, fbody)) }

%%
