open Format
open Pp

exception No_type of Ast.l * string

let raise_error l msg pp n =
  let pp ppf = Format.fprintf ppf "%s: %a" msg pp n in
    raise (No_type(l, Pp.pp_to_string pp))

(* None of the Name.lskips_t can actually have any lskips, but the last one
 * might have parentheses, so Name.t isn't suitable *)
type t = Ast.lex_skips * Name.lskips_t list * Name.lskips_t

let pp ppf (sk,ns,n) =
  fprintf ppf "%a" 
    (Pp.lst "." Name.lskip_pp) (ns @ [n])

let mk_ident m n l : t = 
  let ms = List.map (fun (n,sk) -> n) m in
  let prelim_id = (None, ms, n) in
    List.iter (fun (_, sk) ->
                 if sk <> None && sk <> Some([]) then
                   raise_error l "illegal whitespace in identifier"
                     pp prelim_id)
      m;
    match ms with
      | [] ->
          (None, [], n)
      | m'::ms' ->
          List.iter 
            (fun n ->
               if Name.get_lskip n <> None && Name.get_lskip n <> Some([]) then
                 raise_error l "illegal whitespace in identifier"
                   pp prelim_id 
               else
                 ())
            (ms' (* TODO: we'd like to add this check, but have to support 
                          "X.( * )" to avoid accidentally parsing as a comment
                          opener/closer 
                 @ [n]*));
          (Name.get_lskip m', Name.replace_lskip m' None::ms', n)

let from_id (Ast.Id(m,xl,l)) : t =
  mk_ident 
    (List.map (fun (xl,l) -> (Name.from_x xl, l)) m)
    (Name.from_x xl)
    l

let get_name (_,_,x) = x

let (^) = Output.(^)

let to_output a sep ((sk,ns,n):t) = 
  Output.ws sk ^ 
  Output.concat sep (List.map (Name.to_output a) (ns@[n])) 

let drop_parens gp ((sk,ns,n):t) =
  if ns = [] then
    (sk, [], Name.drop_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (sk,ns,Name.add_parens n)
  else
    (sk,ns,Name.drop_parens n)

let add_parens gp ((sk,ns,n):t) =
  if ns = [] then
    (sk, [], Name.add_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (sk,ns,Name.add_parens n)
  else
    (sk,ns,Name.drop_parens n)

      (*
let capitalize (ns,n) = (ns,Name.capitalize n)

let uncapitalize (ns,n) = (ns,Name.uncapitalize n)

let starts_with_lower_letter (ns,n) = Name.starts_with_lower_letter n

let starts_with_upper_letter (ns,n) = Name.starts_with_upper_letter n

       *)

let replace_first_lskip ((sk,ns,n):t) s = 
  (s,ns,n)

let get_first_lskip ((sk,ns,n):t) =
  sk
                  
let get_prec gp (sk,l,i) =
  if l = [] then
    Name.get_prec gp i
  else
    Precedence.not_infix

let to_name_list ((sk,ns,n):t) =
  (List.map Name.strip_lskip ns, Name.strip_lskip n)

let strip_path name ((sk,ns,n) :t) : t =
  match ns with
    | [] -> 
        (sk,[],n)
    | (h::t) ->
        if Name.compare name (Name.strip_lskip h) = 0 then
          (sk,t, n)
        else
          (sk,ns,n)
