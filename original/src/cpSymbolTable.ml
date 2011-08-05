type ('a, 'b) t = ('a, 'b) BatMap.t list

let empty = []

let add a b = function
  | t::ts -> BatMap.add a b t :: ts
  | [] -> invalid_arg "Symbol table is empty: Cannot add symbol.\n"

let rec find a = function
  | m::ms ->
      begin
        try
          BatMap.find a m
        with Not_found ->
          find a ms
      end
  | [] -> raise Not_found

let mem a t = try let (_ : 'b) = find a t in true with Not_found -> false

let symbols t =
  let to_list m = BatMap.fold (fun b l -> b::l) m [] in
  List.fold_left (fun l m -> to_list m @ l) [] t

let create_scope t = BatMap.empty::t

let destroy_scope = function
  | _::ms -> ms
  | [] -> invalid_arg "Symbol table is empty: Cannot destroy scope.\n"

let return_scope = function
  | m::_ -> [m]
  | [] -> invalid_arg "Symbol table is empty: Cannot return scope.\n"

let push_table t1 t2 = t1 @ t2
