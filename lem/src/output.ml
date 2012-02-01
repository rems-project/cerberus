exception Backend of string

let (^^) = BatRope.(^^^)

type id_annot =  (* kind annotation for latex'd identifiers *)
  | Term_const
  | Term_ctor
  | Term_field 
  | Term_method 
  | Term_var 
  | Term_var_toplevel
  | Term_spec 
  | Type_ctor
  | Type_var
  | Module_name
  | Class_name
  | Target

type t = 
  | Empty                          (* Empty output *)
  | Kwd of string                  (* Keyword *)
  | Ident of id_annot * BatRope.t  (* Identifier *)
  | Num of int                     (* Literal int *)
  | Inter of Ast.lex_skip          (* Interstitial: Comment (currently including (* *), Pure whitespace [' ''\t']+, or Newline *)
  | Str of BatRope.t               (* String literal, without surrounding "" *)
  | Err of string                  (* Causes to_rope to raise an exception *) 
  | Meta of string                 (* Data that is not subject to the target lexical convention *)
  | Texspace                       (* Force latex space except at start or end of line *)
  | Cons of t * t                  (* Cons *)

type t' =
  | Kwd' of string
  | Ident' of BatRope.t
  | Num' of int

let emp = Empty

let kwd t = Kwd(t)

let id a t = Ident(a,t)

let num t = Num(t)

let ws = function
  | None -> Empty
  | Some([]) -> Empty
  | Some (ts) -> 
      List.fold_left (fun o1 o2 -> Cons(o1,o2)) Empty 
        (List.map 
           (fun t -> Inter t)
           (List.rev ts))

let str s = Str(s)

let err s = Err(s)

let meta s = Meta(s)

let texspace = Texspace
              
let (^) o1 o2 = 
  match (o1,o2) with
    | (Empty, _) -> o2
    | (_, Empty) -> o1
    | _ -> Cons(o1,o2)

let rec flat = function
  | [] -> Empty
  | x::y -> x ^ flat y

let rec concat o1 = function
  | [] -> Empty
  | [x] -> x
  | x::y -> x ^ o1 ^ concat o1 y

let quote_string quote_char s = quote_char ^^ s ^^ quote_char

let conv = function
  | Kwd(s) -> Kwd'(s)
  | Ident(a,r) -> Ident'(r)
  | Num(i) -> Num'(i)
  | _ -> assert false

let ns need_space t1 t2 =
  match (t1,t2) with
    | ((Empty | Inter _ | Str _ | Err _ | Meta _ | Texspace), _) -> false
    | (_, (Empty | Inter _ | Str _ | Err _ | Meta _ | Texspace)) -> false
    | _ -> need_space (conv t1) (conv t2)
    

let to_rope quote_char lex_skips_to_rope need_space t = 
  let rec to_rope_help t = match t with
    | Empty -> (t,r"",t)
    | Kwd(s) -> (t, BatRope.of_latin1 s, t)
    | Ident(a,r) -> (t, r, t)
    | Num(i) -> (t, BatRope.of_latin1 (BatInt.to_string i), t)
    | Inter(i) -> (t,lex_skips_to_rope i,t)
(*
    | Ws(ws) -> 
        let r = BatRope.concat r"" (List.map lex_skips_to_rope (List.rev ws)) in
          if BatRope.compare r r"" = 0 then
            raise (Backend("non-empty Ast.lex_skips to empty rope"));
          (t,r,t)
*)
    | Str(s) -> (t, quote_string quote_char s, t)
    | Err(s) -> raise (Backend(s))
    | Meta(s) -> (t,BatRope.of_latin1 s,t)
    | Texspace -> (t,r"",t)   (* placeholder *)
    | Cons(Texspace,t) -> to_rope_help t
    | Cons(t,Texspace) -> to_rope_help t
    | Cons(t1,t2) -> 
        let (t1',r1,t2') = to_rope_help t1 in
        let (t3',r2,t4') = to_rope_help t2 in
        let sp = if ns need_space t2' t3' then r" " else r"" in
          (t1',r1 ^^ sp ^^ r2,t4')
  in
  let (_,r,_) = to_rope_help t in
    r

let rec ml_comment_to_rope = function
  | Ast.Chars(r) -> r
  | Ast.Comment(coms) -> r"(*" ^^ BatRope.concat r"" (List.map ml_comment_to_rope coms) ^^ r"*)"


(* ******** *)
(* Debug pp *)
(* ******** *)


let pp_raw_id_annot = function
  | Term_const         -> r"Term_const"       
  | Term_ctor          -> r"Term_ctor"        
  | Term_field         -> r"Term_field"       
  | Term_method        -> r"Term_method"      
  | Term_var           -> r"Term_var"         
  | Term_var_toplevel  -> r"Term_var_toplevel"
  | Term_spec          -> r"Term_spec"        
  | Type_ctor          -> r"Type_ctor"        
  | Type_var           -> r"Type_var"         
  | Module_name        -> r"Module_name"      
  | Class_name         -> r"Class_name"       
  | Target             -> r"Target"           

let rec pp_raw_t t = 
  match t with
  | Empty -> r"Empty"
  | Kwd(s) -> r"Kwd(" ^^ BatRope.of_latin1 s ^^r")"
  | Ident(a,r) -> r"Ident(" ^^ pp_raw_id_annot a ^^ r"," ^^ r ^^ r")"
  | Num(i) -> r"Num(" ^^  BatRope.of_latin1 (BatInt.to_string i) ^^ r")"
  | Inter(Ast.Com(r)) -> r"Inter(Ast.Com(" ^^ ml_comment_to_rope r ^^ r")"
  | Inter(Ast.Ws(r)) -> r"Inter(Ast.Ws(" ^^ r ^^ r")"
  | Inter(Ast.Nl) -> r"Inter(Ast.Nl)"
  | Str(s) -> r"Str(" ^^ s ^^ r")"
  | Err(s) -> r"Str(" ^^ BatRope.of_latin1 s ^^ r")"
  | Meta(s) -> r"Str(" ^^ BatRope.of_latin1 s ^^ r")"
  | Texspace -> r"Texspace"
  | Cons(t1,t2) -> r"Cons(" ^^ pp_raw_t t1 ^^ r"," ^^ pp_raw_t t2 ^^ r")"


(* ************* *)
(* LaTeX backend *)
(* ************* *)

let tex_command_prefix = r"LEM"  (* for LaTeX commands in generated .tex and -inc.tex files *)
let tex_label_prefix   = r"lem:" (* for LaTeX labels in generated .tex and -inc.tex files *)
let tex_sty_prefix     = r"lem"  (* for LaTeX commands in the lem.sty file *)

(* escaping of Lem source names to use in LaTeX command names
 (probably it needs to be more aggressive)
 (and it isn't injective, so we should do some global check or rename too...) *)
let tex_command_escape r = 
  BatRope.concat
    BatRope.empty
    (List.map
       (fun c -> 
       if c=BatCamomile.UChar.of_char '_'  then r"T"     else
       if c=BatCamomile.UChar.of_char '#'  then r"H"     else
       if c=BatCamomile.UChar.of_char '\'' then r"P"     else
       if c=BatCamomile.UChar.of_char '0'  then r"Zero"  else
       if c=BatCamomile.UChar.of_char '1'  then r"One"   else
       if c=BatCamomile.UChar.of_char '2'  then r"Two"   else
       if c=BatCamomile.UChar.of_char '3'  then r"Three" else
       if c=BatCamomile.UChar.of_char '4'  then r"Four"  else
       if c=BatCamomile.UChar.of_char '5'  then r"Five"  else
       if c=BatCamomile.UChar.of_char '6'  then r"Six"   else
       if c=BatCamomile.UChar.of_char '7'  then r"Seven" else
       if c=BatCamomile.UChar.of_char '8'  then r"Eight" else
       if c=BatCamomile.UChar.of_char '9'  then r"Nine"  else
       BatRope.of_uchar c)
       (BatRope.explode r))

let tex_command_name r = r"\\" ^^ tex_command_prefix ^^ tex_command_escape r 
let tex_command_label r =  tex_label_prefix ^^ tex_command_escape r 

(* escaping of Lem source identifiers to appear in LaTeX *)
let tex_escape r = 
  BatRope.concat
    BatRope.empty
    (List.map
       (fun c ->  
         if c=BatCamomile.UChar.of_char '_'  then r"\\_" else 
         if c=BatCamomile.UChar.of_char '%'  then r"\\%" else 
         if c=BatCamomile.UChar.of_char '$'  then r"\\$" else 
         if c=BatCamomile.UChar.of_char '#'  then r"\\#" else 
         if c=BatCamomile.UChar.of_char '?'  then r"\\mbox{?}" else 
         if c=BatCamomile.UChar.of_char '^'  then r"\\mbox{$\\uparrow$}" else 
         if c=BatCamomile.UChar.of_char '{'  then r"\\{" else 
         if c=BatCamomile.UChar.of_char '}'  then r"\\}" else 
         if c=BatCamomile.UChar.of_char '<'  then r"\\mbox{$<$} " else 
         if c=BatCamomile.UChar.of_char '>'  then r"\\mbox{$>$} " else 
         if c=BatCamomile.UChar.of_char '&'  then r"\\&" else 
         if c=BatCamomile.UChar.of_char '\\' then r"\\mbox{$\\backslash{}$}" else 
         if c=BatCamomile.UChar.of_char '|'  then r"\\mbox{$\\mid$}" else 
         BatRope.of_uchar c)
       (BatRope.explode r))

let tex_id_wrap = function
  | Term_const         -> r"\\" ^^ tex_sty_prefix ^^ r"TermConst"        
  | Term_ctor          -> r"\\" ^^ tex_sty_prefix ^^ r"TermCtor"         
  | Term_field         -> r"\\" ^^ tex_sty_prefix ^^ r"TermField"        
  | Term_method        -> r"\\" ^^ tex_sty_prefix ^^ r"TermMethod"       
  | Term_var           -> r"\\" ^^ tex_sty_prefix ^^ r"TermVar"          
  | Term_var_toplevel  -> r"\\" ^^ tex_sty_prefix ^^ r"TermVarToplevel" 
  | Term_spec          -> r"\\" ^^ tex_sty_prefix ^^ r"TermSpec"         
  | Type_ctor          -> r"\\" ^^ tex_sty_prefix ^^ r"TypeCtor"         
  | Type_var           -> r"\\" ^^ tex_sty_prefix ^^ r"TypeVar"          
  | Module_name        -> r"\\" ^^ tex_sty_prefix ^^ r"ModuleName"       
  | Class_name         -> r"\\" ^^ tex_sty_prefix ^^ r"ClassName"        
  | Target             -> r"\\" ^^ tex_sty_prefix ^^ r"Target"            

let split_suffix s =
  let regexp = Str.regexp "\\(.*[^'0-9]\\)\\([0-9]*\\)\\('*\\)\\(.*\\)" in
  if Str.string_match regexp s 0 then
    (Str.matched_group 1 s, 
     let (^) = Pervasives.(^) in
     let numeric_suffix = Str.matched_group 2 s in 
     let prime_suffix = Str.matched_group 3 s in
     let remaining_suffix = Str.matched_group 4 s in
     (if numeric_suffix = "" then "" 
     else if String.length numeric_suffix = 1 then "_" ^ numeric_suffix
     else "_{"^numeric_suffix^"}") ^
     prime_suffix ^
     remaining_suffix)       
  else
    raise (Failure "split_suffix")

let split_suffix_rope r = 
  let (s1,s2) = split_suffix (BatRope.to_string r) in
  (BatRope.of_string s1, BatRope.of_string s2)

(* flatten into a list of Cons-free and Emp-free t *)
(* poor complexity *)
let flatten_to_list : t -> t list = 
  let rec f = function
    | Cons(o1,o2) -> f o1 @ f o2
    | Empty -> []
    | (_ as o1) -> [o1] in
  f

(* the Nl-separated lists of t, including start and end *)
(* poor complexity *)
let line_break : t list -> t list list  = 
  function os -> 
    let rec f acc1 acc2 os = 
      match os with 
      | [] -> acc2@[acc1]
      | Inter(Ast.Nl)::os' -> f [] (acc2@[acc1]) os'
      | o1::os' -> f (acc1@[o1]) acc2 os' in
    f [] [] os

let debug = false

let to_rope_ident a r =
  let (r1,r2) = split_suffix_rope r in
  tex_id_wrap a ^^ r"{" ^^ tex_escape r1 ^^ r"}" ^^ r2

let quote_char = r"\""

let rec to_rope_single t = 
  match t with
  | Empty -> r""
  | Kwd(s) ->  BatRope.of_latin1 s
  | Ident(a,r) -> to_rope_ident a r
  | Num(i) ->  BatRope.of_latin1 (BatInt.to_string i)
  | Inter(Ast.Com(r)) -> r"\\tsholcomm{" ^^ tex_escape (ml_comment_to_rope r)  ^^ r"}" 
  | Inter(Ast.Ws(r)) -> r
  | Inter(Ast.Nl) -> raise (Failure "Nl in to_rope_tex")
  | Str(s) ->  quote_string quote_char s
  | Err(s) -> raise (Backend(s))
  | Meta(s) -> BatRope.of_latin1 s
  | Texspace -> r"\\ "   
  | Cons(t1,t2) -> raise (Failure "Cons in to_rope_tex") 


let make_indent r = 
  let n = BatRope.length r in
  let single_indent = "\\ " in
  let rec n_of x n = if n=0 then [] else x::n_of x (n-1) in
  BatRope.of_string (String.concat "" (n_of single_indent n)) 

let strip_initial_and_final_texspace ts =
  let rec strip_initial_texspace ts = match ts with
  | [] -> [] 
  | Texspace :: ts' -> strip_initial_texspace ts'
  | _ :: ts' -> ts in
  List.rev (strip_initial_texspace (List.rev (strip_initial_texspace ts))) 
    

(* returns None if all whitespace or texspace, otherwise Some of the indented rope *)
let to_rope_option_line : t list -> BatRope.t option 
    = function ts -> 
      let rec f indent_acc ts = 
        match ts with
        | [] -> None
        | Inter(Ast.Ws(r))::ts' -> f (indent_acc ^^ r) ts'
        | _ :: ts' when List.for_all (fun o1 -> o1=Texspace) ts ->
            None
        | _ :: ts' -> 
            Some ( make_indent indent_acc ^^ 
                   BatRope.concat (r"") 
                     (List.map to_rope_single 
                        (strip_initial_and_final_texspace ts))) in
      f (r"") ts 

let strip_initial_and_final_blank_lines tss =
  let rec strip_initial tss = match tss with
  | [] -> []
  | None::tss' -> strip_initial tss'
  | _ :: _ -> tss in
  let dummy_space tso = match tso with 
  | None -> r"\\ "  (* to workaround latex tabbing sensitivity *)
  | Some r -> r in
  List.map dummy_space (List.rev (strip_initial (List.rev (strip_initial tss)))) 

let rec to_rope_lines strip_blanks tss = 
  let rs = if strip_blanks then 
    strip_initial_and_final_blank_lines 
      (List.map to_rope_option_line tss)
  else
    List.map
      (function | None -> r"" | Some r -> r) 
      (List.map to_rope_option_line tss) in

  let rec f rs = 
    match rs with
    | [] -> r""
    | [r] -> r
    | r :: rs' -> r ^^ r"\\\\{}\n" ^^ f rs' in
  
  match rs with 
  | [] -> None
  | _ -> Some (f rs) 


let to_rope_option_tex term need_space strip_blanks t = 

  if debug then Printf.printf "\n\n\nto_rope_tex input:\n%s" (BatRope.to_string (pp_raw_t t));

  let lines = line_break (flatten_to_list t) in
  
  let ro = to_rope_lines strip_blanks lines in
  
  (if debug then Printf.printf "\n\nto_rope_tex output:\n%s" (BatRope.to_string (match ro with None -> r"None" | Some r -> r"Some(" ^^ r ^^ r")")));
  
  ro



