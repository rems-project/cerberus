open Format
open Pp

type t = (Name.lskips_t, Ast.lex_skips) Seplist.t * Name.lskips_t

let from_id (Ast.Id(m,xl,_)) : t =
  let rec f = function
    | [] -> Seplist.empty
    | (xl,s)::y ->
        Seplist.cons_entry (Name.from_x xl) (Seplist.cons_sep s (f y))
  in
    (f m, Name.from_x xl)

let pp ppf (ns,n) =
  fprintf ppf "%a%a" 
    (Seplist.pp Name.lskip_pp (fun ppf x -> fprintf ppf ".")) ns
    Name.lskip_pp n

let get_name (_,x) = x

let mk_ident ns n = 
  (Seplist.from_list_suffix 
     (List.map (fun n -> (n,None)) ns)
     None
     (ns <> []),
   n)

let mk_ident_skips ns n = 
  let rec f = function
    | [] -> Seplist.empty
    | (xl,s)::y ->
        Seplist.cons_entry xl (Seplist.cons_sep s (f y))
  in
    (f ns, n)


let (^) = Output.(^)

let to_output a sep (ns,n) = 
  Output.flat (Seplist.to_sep_list
                 (Name.to_output a)
                 (fun s -> Output.ws s ^ sep)
                 ns) ^ 
  Name.to_output a n

let drop_parens gp (ns,n) =
  if Seplist.is_empty ns then
    (Seplist.empty, Name.drop_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (ns,Name.add_parens n)
  else
    (ns,Name.drop_parens n)

let add_parens gp (ns,n) =
  if Seplist.is_empty ns then
    (Seplist.empty, Name.add_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (ns,Name.add_parens n)
  else
    (ns,Name.drop_parens n)

      (*
let capitalize (ns,n) = (ns,Name.capitalize n)

let uncapitalize (ns,n) = (ns,Name.uncapitalize n)

let starts_with_lower_letter (ns,n) = Name.starts_with_lower_letter n

let starts_with_upper_letter (ns,n) = Name.starts_with_upper_letter n

       *)
let replace_first_lskip (ns,n) s = 
  if Seplist.is_empty ns then
    (Seplist.empty, Name.replace_lskip n s)
  else
    let n' = Seplist.hd ns in
    let ns' = Seplist.tl ns in
      (Seplist.cons_entry (Name.replace_lskip n' s) ns',
       n)

let get_first_lskip (ns,n) =
  if Seplist.is_empty ns then
    Name.get_lskip n
  else
    Name.get_lskip (Seplist.hd ns)
                  
let get_prec gp (l,i) =
  if Seplist.is_empty l then
    Name.get_prec gp i
  else
    Precedence.not_infix

let to_name_list (ns,n) =
  (Seplist.to_list_map Name.strip_lskip ns, Name.strip_lskip n)
