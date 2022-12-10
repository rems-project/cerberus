module N = struct
  include Nat_big_num
  let of_float = Z.of_float
end

module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = Nat_big_num.compare
end)




let serialise_prefix = function
  | Symbol.PrefOther s ->
      (* TODO: this should not be possible anymore *)
      `Assoc [("kind", `String "other"); ("name", `String s)]
  | Symbol.PrefMalloc ->
      `Assoc [("kind", `String "malloc");
              ("scope", `Null);
              ("name", `String "malloc'd");
              ("loc", `Null)]
  | Symbol.PrefStringLiteral (loc, _) ->
      `Assoc [("kind", `String "string literal");
              ("scope", `Null);
              ("name", `String "literal");
              ("loc", Location_ocaml.to_json loc)]
  | Symbol.PrefCompoundLiteral (loc, _) ->
      `Assoc [("kind", `String "compound literal");
              ("scope", `Null);
              ("name", `String "literal");
              ("loc", Location_ocaml.to_json loc)]
  | Symbol.PrefFunArg (loc, _, n) ->
      `Assoc [("kind", `String "arg");
              ("scope", `Null);
              ("name", `String ("arg" ^ string_of_int n));
              ("loc", Location_ocaml.to_json loc)]
  | Symbol.PrefSource (_, []) ->
      failwith "serialise_prefix: PrefSource with an empty list"
  | Symbol.PrefSource (loc, [name]) ->
        `Assoc [("kind", `String "source");
                ("name", `String (Pp_symbol.to_string_pretty name));
                ("scope", `Null);
                ("loc", Location_ocaml.to_json loc);]
  | Symbol.PrefSource (loc, [scope; name]) ->
      `Assoc [("kind", `String "source");
              ("name", `String (Pp_symbol.to_string_pretty name));
              ("scope", `String (Pp_symbol.to_string_pretty scope));
              ("loc", Location_ocaml.to_json loc);]
  | Symbol.PrefSource (_, _) ->
      failwith "serialise_prefix: PrefSource with more than one scope"


let serialise_int_map (f: int -> 'a -> Json.json) (m: 'a IntMap.t) : Json.json =
  let serialise_entry (k, v) = (Z.to_string k, f (Z.to_int k) v) in
  `Assoc (List.map serialise_entry (IntMap.bindings m))
 