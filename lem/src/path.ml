open Format
open Pp

type t = 
  | Path_def of Name.t list * Name.t
  | Path_list
  | Path_bool
  | Path_num
  | Path_set
  | Path_string
  | Path_unit

let mk_path ns n = Path_def(ns,n)

let from_id id = 
  let (x,y) = Ident.to_name_list id in 
    Path_def(x,y)

let compare p1 p2 = 
  match (p1,p2) with
    | (Path_def(ns1,n1), Path_def(ns2,n2)) ->
        let c = Name.compare n1 n2 in
          if c = 0 then
            Util.compare_list Name.compare ns1 ns2
          else
            c
    | (Path_def _, _) -> 1
    | (_, Path_def _) -> -1
    | (Path_list,Path_list) -> 0
    | (Path_list,_) -> 1
    | (_, Path_list _) -> -1
    | (Path_bool, Path_bool) -> 0
    | (Path_bool,_) -> 1
    | (_, Path_bool _) -> -1
    | (Path_num, Path_num) -> 0
    | (Path_num,_) -> 1
    | (_, Path_num _) -> -1
    | (Path_set, Path_set) -> 0
    | (Path_set,_) -> 1
    | (_, Path_set _) -> -1
    | (Path_string _, Path_string _) -> 0
    | (Path_string,_) -> 1
    | (_, Path_string _) -> -1
    | (Path_unit _, Path_unit _) -> 0

let pp ppf p =
  match p with
    | Path_def([],v) ->
        Name.pp ppf v
    | Path_def(vs,v) ->
        fprintf ppf "%a.%a" 
          (lst "." Name.pp) vs
          Name.pp v
    | Path_list ->
        fprintf ppf "list"
    | Path_bool ->
        fprintf ppf "bool"
    | Path_num ->
        fprintf ppf "num"
    | Path_set ->
        fprintf ppf "set"
    | Path_string ->
        fprintf ppf "string"
    | Path_unit ->
        fprintf ppf "unit"

let flat = function
  | [] -> r""
  | r2 -> BatRope.concat r"" r2

let (^) = BatRope.(^^^)

let to_ident p =  match p with 
    | Path_def([],v) -> Ident.mk_ident [] (Name.add_lskip v)
    | Path_def(vs,v) -> Ident.mk_ident (List.map Name.add_lskip vs) (Name.add_lskip v)
    | Path_list -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"list"))
    | Path_bool -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"bool"))
    | Path_num -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"num"))
    | Path_set -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"set"))
    | Path_string -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"string"))
    | Path_unit -> Ident.mk_ident [] (Name.add_lskip (Name.from_rope r"unit"))

let numpath = Path_num

let boolpath = Path_bool

let listpath = Path_list

let setpath = Path_set

let stringpath = Path_string

let unitpath = Path_unit

let get_name = function
  | Path_def(_,x) -> x
  | _ -> assert false

let check_prefix n p = match p with
  | Path_def(n2::_,_) ->
      Name.compare n n2 = 0
  | _ -> false
           
let to_name = function
  | Path_list ->
      Name.from_rope r"list"
  | Path_bool ->
      Name.from_rope r"bool"
  | Path_num ->
      Name.from_rope r"num"
  | Path_set ->
      Name.from_rope r"set"
  | Path_string ->
      Name.from_rope r"string"
  | Path_unit ->
      Name.from_rope r"unit"
  | Path_def([],n) -> n
  | Path_def(ns,n) ->
      Name.from_rope 
        (BatRope.concat r"_" (List.map Name.to_rope ns @ [Name.to_rope n]))




