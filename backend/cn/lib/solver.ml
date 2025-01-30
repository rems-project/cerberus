module SMT = Simple_smt
module IT = IndexTerms
open IT
module LC = LogicalConstraints

module Int_BT_Table = Map.Make (struct
    type t = int * BT.t

    let compare (int1, bt1) (int2, bt2) =
      let cmp = Int.compare int1 int2 in
      if cmp != 0 then cmp else BT.compare bt1 bt2
  end)

module IntWithHash = struct
  (* For compatability with older ocamls *)
  include Int

  let hash x = x
end

module Int_Table = Hashtbl.Make (IntWithHash)
module CTypeMap = Map.Make (Sctypes)
open Global
open Pp

(** Functions that pick names for things. *)
module CN_Names = struct
  let var_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let named_expr_name = "_cn_named"

  let uninterpreted_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let struct_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let struct_con_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let struct_field_name x = Id.get_string x ^ "_struct_fld"

  let datatype_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let datatype_con_name x = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let datatype_field_name x = Id.get_string x ^ "_data_fld"
end

(** Names for constants that may be uninterpreted.  See [bt_uninterpreted] *)
module CN_Constant = struct
  let default = ("default_uf", 0)

  let mul = ("mul_uf", 1)

  let div = ("div_uf", 2)

  let exp = ("exp_uf", 3)

  let rem = ("rem_uf", 4)

  let mod' = ("mod_uf", 5)

  let nth_list = ("nth_list_uf", 6)

  let array_to_list = ("array_to_list_uf", 7)
end

type solver_frame =
  { mutable commands : SMT.sexp list; (** Ack-style SMT commands, most recent first. *)
    mutable uninterpreted : SMT.sexp Sym.Map.t;
    (** Uninterpreted functions and variables that we've declared. *)
    mutable bt_uninterpreted : SMT.sexp Int_BT_Table.t;
    (** Uninterpreted constants, indexed by base type. *)
    mutable ctypes : int CTypeMap.t
    (** Declarations for C types. Each C type is assigned a unique integer. *)
  }

let empty_solver_frame () =
  { commands = [];
    uninterpreted = Sym.Map.empty;
    bt_uninterpreted = Int_BT_Table.empty;
    ctypes = CTypeMap.empty
  }


let copy_solver_frame f = { f with commands = f.commands }

type solver =
  { smt_solver : SMT.solver; (** The SMT solver connection. *)
    cur_frame : solver_frame ref;
    prev_frames : solver_frame list ref;
    (** Push/pop model. Current frame, and previous frames. *)
    name_seed : int ref; (** Used to generate names. *)
    (* ISD: This could, perhaps, go in the frame. Then when we pop frames, we'd go back to
       the old numbers, which should be OK, I think? *)
    globals : Global.t
  }

module Debug = struct
  let dump_frame (f : solver_frame) =
    let to_string = Sexplib.Sexp.to_string_hum in
    let append str doc = doc ^/^ !^str in
    let dump_sym k v rest = rest ^/^ bar ^^^ Sym.pp k ^^^ !^"|->" ^^^ !^(to_string v) in
    let dump_bts (_, k) v rest =
      rest ^/^ bar ^^^ BT.pp k ^^^ !^"|->" ^^^ !^(to_string v)
    in
    !^"# Symbols"
    |> Sym.Map.fold dump_sym f.uninterpreted
    |> append "# Basetypes "
    |> Int_BT_Table.fold dump_bts f.bt_uninterpreted
    |> append "+---------------------------------"


  let dump_solver solver =
    !^"\n|~~~~~~ Start Solver Dump ~~~~~~~|"
    ^/^ separate_map hardline dump_frame (!(solver.cur_frame) :: !(solver.prev_frames))
    ^/^ !^"|~~~~~~ End Solver Dump ~~~~~~~~~|"
end

(** Lookup something in one of the existing frames *)
let search_frames s f = List.find_map f (!(s.cur_frame) :: !(s.prev_frames))

(** Lookup the `int` corresponding to a C type in the current stack.
    If it is not found, add it to the current frame, and return the new int. *)
let find_c_type s ty =
  let rec search count frames =
    match frames with
    | f :: more ->
      (match CTypeMap.find_opt ty f.ctypes with
       | Some n -> n
       | None -> search (CTypeMap.cardinal f.ctypes + count) more)
    | [] ->
      let f = !(s.cur_frame) in
      f.ctypes <- CTypeMap.add ty count f.ctypes;
      count
  in
  search 0 (!(s.cur_frame) :: !(s.prev_frames))


(** Compute a table mapping ints to C types.  We use this to map SMT results
    back to terms. *)
let get_ctype_table s =
  let table = Int_Table.create 50 in
  let add_entry t n = Int_Table.add table n t in
  let do_frame f = CTypeMap.iter add_entry f.ctypes in
  List.iter do_frame (!(s.cur_frame) :: !(s.prev_frames));
  table


let debug_ack_command s cmd =
  try SMT.ack_command s.smt_solver cmd with
  | SMT.UnexpectedSolverResponse r ->
    debug 10 (lazy (!^"failed to ack:" ^/^ !^(Sexplib.Sexp.to_string_hum cmd)));
    debug 10 (lazy (Debug.dump_solver s));
    raise (SMT.UnexpectedSolverResponse r)


(** Start a new scope. *)
let push s =
  debug_ack_command s (SMT.push 1);
  s.prev_frames := !(s.cur_frame) :: !(s.prev_frames);
  s.cur_frame := empty_solver_frame ()


(** Return to the previous scope.  Assumes that there is a previous scope. *)
let pop s n =
  if n = 0 then
    ()
  else (
    debug_ack_command s (SMT.pop n);
    let rec drop count xs =
      match xs with
      | new_cur :: new_rest ->
        if count = 1 then (
          s.cur_frame := new_cur;
          s.prev_frames := new_rest)
        else
          drop (count - 1) new_rest
      | _ -> assert false
    in
    drop n !(s.prev_frames))


let num_scopes s = List.length !(s.prev_frames)

(** Do an ack_style command. These are logged. *)
let ack_command s cmd =
  debug_ack_command s cmd;
  let f = !(s.cur_frame) in
  f.commands <- cmd :: f.commands


(** Generate a fersh name *)
let fresh_name s x =
  let n = !(s.name_seed) in
  s.name_seed := n + 1;
  let res = x ^ "_" ^ string_of_int n in
  res


(** Declare an uninterpreted function. *)
let declare_uninterpreted s name args_ts res_t =
  let check f = Sym.Map.find_opt name f.uninterpreted in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = CN_Names.uninterpreted_name name in
    ack_command s (SMT.declare_fun sname args_ts res_t);
    let e = SMT.atom sname in
    let f = !(s.cur_frame) in
    f.uninterpreted <- Sym.Map.add name e f.uninterpreted;
    e


(** Declare an uninterpreted function, indexed by a base type. *)
let declare_bt_uninterpreted s (name, k) bt args_ts res_t =
  let check f = Int_BT_Table.find_opt (k, bt) f.bt_uninterpreted in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = fresh_name s name in
    ack_command s (SMT.declare_fun sname args_ts res_t);
    let e = SMT.atom sname in
    let top_map = !(s.cur_frame).bt_uninterpreted in
    !(s.cur_frame).bt_uninterpreted <- Int_BT_Table.add (k, bt) e top_map;
    e


(* Note: CVC5 has support for arbitrary tuples without declaring them. Also, instead of
   declaring a fixed number of tuples ahead of time, we could declare the types on demand
   when we need them, with another piece of state in the solver to track which ones we
   have declared. *)
module CN_Tuple = struct
  let max_arity = 15

  let name arity =
    assert (arity <= max_arity);
    "cn_tuple_" ^ string_of_int arity


  let selector arity field =
    assert (arity <= max_arity);
    "cn_get_" ^ string_of_int field ^ "_of_" ^ string_of_int arity


  (** A tuple type with the given name *)
  let t tys =
    let arity = List.length tys in
    SMT.app_ (name arity) tys


  (** Declare a datatype for a struct *)
  let declare s =
    for arity = 0 to max_arity do
      let name = name arity in
      let param i = "a" ^ string_of_int i in
      let params = List.init arity param in
      let field i = (selector arity i, SMT.atom (param i)) in
      let fields = List.init arity field in
      ack_command s (SMT.declare_datatype name params [ (name, fields) ])
    done


  (** Make a tuple value *)
  let con es =
    let arity = List.length es in
    assert (arity <= max_arity);
    SMT.app_ (name arity) es


  (** Get a field of a tuple *)
  let get arity field tup = SMT.app_ (selector arity field) [ tup ]
end

module CN_AllocId = struct
  (** The type to use  for allocation ids *)
  let t () = if !use_vip then SMT.t_int else CN_Tuple.t []

  (** Parse an allocation id from an S-expression *)
  let from_sexp s = if !use_vip then SMT.to_z s else Z.zero

  (** Convert an allocation id to an S-expression *)
  let to_sexp s = if !use_vip then SMT.int_zk s else CN_Tuple.con []
end

module CN_MemByte = struct
  let name = "mem_byte"

  let alloc_id_name = "alloc_id"

  let value_name = "value"

  let alloc_id_value_name = "AiV"

  (** Bit-width of memory bytes *)
  let width = Memory.bits_per_byte

  (** The name of the pointer type *)
  let t = SMT.atom name

  (** Make a allocation ID & address pair pointer value *)
  let con ~alloc_id ~value = SMT.app_ alloc_id_value_name [ alloc_id; value ]

  let declare s =
    ack_command
      s
      (SMT.declare_datatype
         name
         []
         [ ( alloc_id_value_name,
             [ (alloc_id_name, CN_AllocId.t ()); (value_name, SMT.t_bits width) ] )
         ])
end

module CN_Pointer = struct
  let name = "pointer"

  let null_name = "NULL"

  let alloc_id_addr_name = "AiA"

  let alloc_id_name = "alloc_id"

  let addr_name = "addr"

  (** Bit-width of pointers *)
  let width =
    match Memory.uintptr_bt with Bits (_, w) -> w | _ -> failwith "Pointer is not bits"


  (** The name of the pointer type *)
  let t = SMT.atom name

  (** Using a match is more robust to changes in the pointer representation,
      i.e. adding a [functpr] constructor. *)
  let match_ptr scrutinee ~null_case ~alloc_id_addr_case =
    SMT.(
      match_datatype
        scrutinee
        [ (PCon (null_name, []), null_case);
          ( PCon (alloc_id_addr_name, [ alloc_id_name; addr_name ]),
            alloc_id_addr_case
              ~alloc_id:(SMT.atom alloc_id_name)
              ~addr:(SMT.atom addr_name) )
        ])


  let ptr_shift_name = "ptr_shift"

  let copy_alloc_id_name = "copy_alloc_id"

  let alloc_id_of_name = "alloc_id_of"

  let bits_to_ptr_name = "bits_to_ptr"

  let addr_of_name = "addr_of"

  (** Make a null pointer value *)
  let con_null = SMT.app_ null_name []

  (** Make a allocation ID & address pair pointer value *)
  let con_aia ~alloc_id ~addr = SMT.app_ alloc_id_addr_name [ alloc_id; addr ]

  let declare s =
    ack_command
      s
      (SMT.declare_datatype
         name
         []
         [ (null_name, []);
           ( alloc_id_addr_name,
             [ (alloc_id_name, CN_AllocId.t ()); (addr_name, SMT.t_bits width) ] )
         ]);
    ack_command
      s
      (SMT.define_fun
         ptr_shift_name
         [ ("p", t); ("offset", SMT.t_bits width); ("null_case", t) ]
         t
         (match_ptr
            (SMT.atom "p")
            ~null_case:(SMT.atom "null_case")
            ~alloc_id_addr_case:(fun ~alloc_id ~addr ->
              con_aia ~alloc_id ~addr:(SMT.bv_add addr (SMT.atom "offset")))));
    ack_command
      s
      (SMT.define_fun
         copy_alloc_id_name
         [ ("p", t); ("new_addr", SMT.t_bits width); ("null_case", t) ]
         t
         (match_ptr
            (SMT.atom "p")
            ~null_case:(SMT.atom "null_case")
            ~alloc_id_addr_case:(fun ~alloc_id ~addr:_ ->
              con_aia ~alloc_id ~addr:(SMT.atom "new_addr"))));
    ack_command
      s
      (SMT.define_fun
         alloc_id_of_name
         [ ("p", t); ("null_case", CN_AllocId.t ()) ]
         (CN_AllocId.t ())
         (match_ptr
            (SMT.atom "p")
            ~null_case:(SMT.atom "null_case")
            ~alloc_id_addr_case:(fun ~alloc_id ~addr:_ -> alloc_id)));
    ack_command
      s
      (SMT.define_fun
         bits_to_ptr_name
         [ ("bits", SMT.t_bits width); ("alloc_id", CN_AllocId.t ()) ]
         t
         (SMT.ite
            (SMT.eq (SMT.atom "bits") (SMT.bv_k width Z.zero))
            con_null
            (con_aia ~addr:(SMT.atom "bits") ~alloc_id:(SMT.atom "alloc_id"))));
    ack_command
      s
      (SMT.define_fun
         addr_of_name
         [ ("p", t) ]
         (SMT.t_bits width)
         (match_ptr
            (SMT.atom "p")
            ~null_case:(SMT.bv_k width Z.zero)
            ~alloc_id_addr_case:(fun ~alloc_id:_ ~addr -> addr)))


  let ptr_shift ~ptr ~offset ~null_case =
    SMT.app_ ptr_shift_name [ ptr; offset; null_case ]


  let copy_alloc_id ~ptr ~addr ~null_case =
    SMT.app_ copy_alloc_id_name [ ptr; addr; null_case ]


  let alloc_id_of ~ptr ~null_case = SMT.app_ alloc_id_of_name [ ptr; null_case ]

  let bits_to_ptr ~bits ~alloc_id = SMT.app_ bits_to_ptr_name [ bits; alloc_id ]

  let addr_of ~ptr = SMT.app_ addr_of_name [ ptr ]
end

module CN_List = struct
  let name = "cn_list"

  let nil_name = "cn_nil"

  let cons_name = "cn_cons"

  let head_name = "cn_head"

  let tail_name = "cn_tail"

  let t a = SMT.app_ name [ a ]

  let declare s =
    let a = SMT.atom "a" in
    ack_command
      s
      (SMT.declare_datatype
         name
         [ "a" ]
         [ (nil_name, []); (cons_name, [ (head_name, a); (tail_name, t a) ]) ])


  let nil elT = SMT.as_type (SMT.atom nil_name) (t elT)

  let cons x xs = SMT.app_ cons_name [ x; xs ]

  let head xs orelse =
    SMT.ite (SMT.is_con cons_name xs) (SMT.app_ head_name [ xs ]) orelse


  let tail xs orelse =
    SMT.ite (SMT.is_con cons_name xs) (SMT.app_ tail_name [ xs ]) orelse
end

(** {1 Type to SMT} *)

(** Translate a base type to SMT *)
let rec translate_base_type = function
  | BT.Unit -> CN_Tuple.t []
  | Bool -> SMT.t_bool
  | Integer -> SMT.t_int
  | MemByte -> CN_MemByte.t
  | Bits (_, n) -> SMT.t_bits n
  | Real -> SMT.t_real
  | Loc () -> CN_Pointer.t
  | Alloc_id -> CN_AllocId.t ()
  | CType -> SMT.t_int
  | List bt -> CN_List.t (translate_base_type bt)
  | Set bt -> SMT.t_set (translate_base_type bt)
  | Map (k, v) -> SMT.t_array (translate_base_type k) (translate_base_type v)
  | Tuple bts -> CN_Tuple.t (List.map translate_base_type bts)
  | Struct tag -> SMT.atom (CN_Names.struct_name tag)
  | Datatype tag -> SMT.atom (CN_Names.datatype_name tag)
  | Record members ->
    let get_val (_, v) = v in
    translate_base_type (Tuple (List.map get_val members))


(** {1 SMT to Term} *)

(** Translate an SMT value to a CN term *)
let rec get_ivalue gs ctys bt sexp =
  IT (get_value gs ctys bt sexp, bt, Cerb_location.unknown)


and get_value gs ctys bt (sexp : SMT.sexp) =
  match bt with
  | BT.Unit -> Const Unit
  | Bool -> Const (Bool (SMT.to_bool sexp))
  | Integer -> Const (Z (SMT.to_z sexp))
  | Bits (sign, n) ->
    let signed = BT.(equal_sign sign Signed) in
    Const (Bits ((sign, n), SMT.to_bits n signed sexp))
  | Real -> Const (Q (SMT.to_q sexp))
  | MemByte ->
    (match SMT.to_con sexp with
     | con, [ salloc_id; svalue ] when String.equal con CN_MemByte.alloc_id_value_name ->
       let alloc_id = CN_AllocId.from_sexp salloc_id in
       let value =
         match get_value gs ctys (BT.Bits (Unsigned, CN_MemByte.width)) svalue with
         | Const (Bits (_, z)) -> z
         | _ -> failwith "Memory byte value is not bits"
       in
       Const (MemByte { alloc_id; value })
     | _ -> failwith "MemByte")
  | Loc () ->
    (match SMT.to_con sexp with
     | con, [] when String.equal con CN_Pointer.null_name -> Const Null
     | con, [ sbase; saddr ] when String.equal con CN_Pointer.alloc_id_addr_name ->
       let base = CN_AllocId.from_sexp sbase in
       let addr =
         match get_value gs ctys Memory.uintptr_bt saddr with
         | Const (Bits (_, z)) -> z
         | _ -> failwith "Pointer value is not bits"
       in
       Const (Pointer { alloc_id = base; addr })
     | _ -> failwith "Loc")
  | Alloc_id -> Const (Alloc_id (CN_AllocId.from_sexp sexp))
  | CType ->
    (try Const (CType_const (Int_Table.find ctys (Z.to_int (SMT.to_z sexp)))) with
     | Not_found -> Const (Default bt))
  | List elT ->
    (match SMT.to_con sexp with
     | con, [] when String.equal con CN_List.nil_name -> Nil elT
     | con, [ h; t ] when String.equal con CN_List.cons_name ->
       Cons (get_ivalue gs ctys elT h, get_ivalue gs ctys bt t)
     | _ -> failwith "List")
  | Set _bt -> Const (Default bt) (* FIXME *)
  | Map (kt, vt) ->
    let els, dflt = SMT.to_array sexp in
    let base = MapConst (kt, get_ivalue gs ctys vt dflt) in
    let add_el (k, v) a =
      MapSet
        ( IT (a, bt, Cerb_location.unknown),
          get_ivalue gs ctys kt k,
          get_ivalue gs ctys vt v )
    in
    List.fold_right add_el els base
  | Tuple bts ->
    let _con, vals = SMT.to_con sexp in
    Tuple (List.map2 (get_ivalue gs ctys) bts vals)
  | Struct tag ->
    let _con, vals = SMT.to_con sexp in
    let decl = Sym.Map.find tag gs.struct_decls in
    let fields = List.filter_map (fun x -> x.Memory.member_or_padding) decl in
    let mk_field (l, t) v = (l, get_ivalue gs ctys (Memory.bt_of_sct t) v) in
    Struct (tag, List.map2 mk_field fields vals)
  | Datatype tag ->
    let con, vals = SMT.to_con sexp in
    let cons = (Sym.Map.find tag gs.datatypes).constrs in
    let do_con c =
      let fields = (Sym.Map.find c gs.datatype_constrs).params in
      let mk_field (l, t) v = (l, get_ivalue gs ctys t v) in
      Constructor (c, List.map2 mk_field fields vals)
    in
    let try_con c =
      if String.equal con (CN_Names.datatype_con_name c) then
        Some (do_con c)
      else
        None
    in
    (match List.find_map try_con cons with
     | Some yes -> yes
     | None -> failwith "Missing constructor")
  | Record members ->
    let _con, vals = SMT.to_con sexp in
    let mk_field (l, bt) e = (l, get_ivalue gs ctys bt e) in
    Record (List.map2 mk_field members vals)


(** {1 Term to SMT} *)

(** Translate a constant to SMT *)
let translate_const s co =
  match co with
  | Z z -> SMT.int_zk z
  | Bits ((_, w), z) -> SMT.bv_k w z
  | Q q -> SMT.real_k q
  | MemByte b ->
    CN_MemByte.con
      ~alloc_id:(CN_AllocId.to_sexp b.alloc_id)
      ~value:(SMT.bv_k CN_MemByte.width b.value)
  | Pointer p ->
    CN_Pointer.con_aia
      ~alloc_id:(CN_AllocId.to_sexp p.alloc_id)
      ~addr:(SMT.bv_k CN_Pointer.width p.addr)
  | Alloc_id z -> CN_AllocId.to_sexp z
  | Bool b -> SMT.bool_k b
  | Unit -> SMT.atom (CN_Tuple.name 0)
  | Null -> CN_Pointer.con_null
  | CType_const ct -> SMT.int_k (find_c_type s ct)
  | Default t ->
    declare_bt_uninterpreted s CN_Constant.default t [] (translate_base_type t)


(** Casting between bit-vector types *)
let bv_cast ~to_ ~from x =
  let bits_info bt =
    match BT.is_bits_bt bt with
    | Some (sign, sz) -> (BT.equal_sign sign BT.Signed, sz)
    | None -> failwith ("mk_bv_cast: non-bv type: " ^ Pp.plain (BT.pp bt))
  in
  let _to_signed, to_sz = bits_info to_ in
  let from_signed, from_sz = bits_info from in
  match () with
  | _ when to_sz = from_sz -> x
  | _ when to_sz < from_sz -> SMT.bv_extract (to_sz - 1) 0 x
  | _ when from_signed -> SMT.bv_sign_extend (to_sz - from_sz) x
  | _ -> SMT.bv_zero_extend (to_sz - from_sz) x


(** [bv_clz rw w e] counts the leading zeroes in [e], which should
    be a bit-vector of width [w].  The result is a bit-vector of width [rw].
    Note that this duplicates [e]. *)
let bv_clz result_w =
  let result k = SMT.bv_k result_w k in
  let eq_0 w e = SMT.eq e (SMT.bv_k w Z.zero) in
  let rec count w e =
    if w = 1 then
      SMT.ite (eq_0 w e) (result Z.one) (result Z.zero)
    else (
      let top_w = w / 2 in
      let bot_w = w - top_w in
      let top = SMT.bv_extract (w - 1) (w - top_w) e in
      let bot = SMT.bv_extract (bot_w - 1) 0 e in
      SMT.ite
        (eq_0 top_w top)
        (SMT.bv_add (count bot_w bot) (result (Z.of_int top_w)))
        (count top_w top))
  in
  count


(** [bv_ctz rw w e] counts the tailing zeroes in [e], which should
    be a bit-vector of width [w].  The result is a bit-vector of width [rw].
    Note that this duplicates [e]. *)
let bv_ctz result_w =
  let result k = SMT.bv_k result_w k in
  let eq_0 w e = SMT.eq e (SMT.bv_k w Z.zero) in
  let rec count w e =
    if w = 1 then
      SMT.ite (eq_0 w e) (result Z.one) (result Z.zero)
    else (
      let top_w = w / 2 in
      let bot_w = w - top_w in
      let top = SMT.bv_extract (w - 1) (w - top_w) e in
      let bot = SMT.bv_extract (bot_w - 1) 0 e in
      SMT.ite
        (eq_0 bot_w bot)
        (SMT.bv_add (count top_w top) (result (Z.of_int bot_w)))
        (count bot_w bot))
  in
  count


(** Translate a variable to SMT.  Declare if needed. *)
let translate_var s name bt =
  let check f = Sym.Map.find_opt name f.uninterpreted in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = CN_Names.var_name name in
    ack_command s (SMT.declare sname (translate_base_type bt));
    let e = SMT.atom sname in
    let f = !(s.cur_frame) in
    f.uninterpreted <- Sym.Map.add name e f.uninterpreted;
    e


(** Translate a CN term to SMT *)
let rec translate_term s iterm =
  let loc = IT.get_loc iterm in
  let struct_decls = s.globals.struct_decls in
  let maybe_name e k =
    if SMT.is_atom e then
      k e
    else (
      let x = fresh_name s CN_Names.named_expr_name in
      SMT.let_ [ (x, e) ] (k (SMT.atom x)))
  in
  let default bt =
    let here = Locations.other __LOC__ in
    translate_term s (IT.default_ bt here)
  in
  match IT.get_term iterm with
  | Const c -> translate_const s c
  | Sym x -> translate_var s x (IT.get_bt iterm)
  | Unop (op, e1) ->
    (match op with
     | BW_FFS_NoSMT ->
       (* NOTE: This desugaring duplicates e1 *)
       let intl i = int_lit_ i (IT.get_bt e1) loc in
       translate_term
         s
         (ite_
            ( eq_ (e1, intl 0) loc,
              intl 0,
              add_ (arith_unop BW_CTZ_NoSMT e1 loc, intl 1) loc )
            loc)
     | BW_FLS_NoSMT ->
       (* copying and adjusting BW_FFS_NoSMT rule *)
       (* NOTE: This desugaring duplicates e1 *)
       let sz = match IT.get_bt e1 with Bits (_sign, n) -> n | _ -> assert false in
       let intl i = int_lit_ i (IT.get_bt e1) loc in
       translate_term
         s
         (ite_
            ( eq_ (e1, intl 0) loc,
              intl 0,
              sub_ (intl sz, arith_unop BW_CLZ_NoSMT e1 loc) loc )
            loc)
     | Not -> SMT.bool_not (translate_term s e1)
     | Negate ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_neg (translate_term s e1)
        | BT.Integer | BT.Real -> SMT.num_neg (translate_term s e1)
        | _ -> failwith (__LOC__ ^ ":Unop (Negate, _)"))
     | BW_Compl ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_compl (translate_term s e1)
        | _ -> failwith (__LOC__ ^ ":Unop (BW_Compl, _)"))
     | BW_CLZ_NoSMT ->
       (match IT.get_bt iterm with
        | BT.Bits (_, w) -> maybe_name (translate_term s e1) (bv_clz w w)
        | _ -> failwith "solver: BW_CLZ_NoSMT: not a bitwise type")
     | BW_CTZ_NoSMT ->
       (match IT.get_bt iterm with
        | BT.Bits (_, w) -> maybe_name (translate_term s e1) (bv_ctz w w)
        | _ -> failwith "solver: BW_CTZ_NoSMT: not a bitwise type"))
  | Binop (op, e1, e2) ->
    let s1 = translate_term s e1 in
    let s2 = translate_term s e2 in
    (* binary uninterpreted function, same type for arguments and result. *)
    let uninterp_same_type k =
      let bt = IT.get_bt iterm in
      let smt_t = translate_base_type bt in
      let f = declare_bt_uninterpreted s k bt [ smt_t; smt_t ] smt_t in
      SMT.app f [ s1; s2 ]
    in
    (match op with
     | And -> SMT.bool_and s1 s2
     | Or -> SMT.bool_or s1 s2
     | Implies -> SMT.bool_implies s1 s2
     | Add ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_add s1 s2
        | BT.Integer | BT.Real -> SMT.num_add s1 s2
        | _ -> failwith "Add")
     | Sub ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_sub s1 s2
        | BT.Integer | BT.Real -> SMT.num_sub s1 s2
        | _ -> failwith "Sub")
     | Mul ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_mul s1 s2
        | BT.Integer | BT.Real -> SMT.num_mul s1 s2
        | _ -> failwith "Mul")
     | MulNoSMT -> uninterp_same_type CN_Constant.mul
     | Div ->
       (match IT.get_bt iterm with
        | BT.Bits (BT.Signed, _) -> SMT.bv_sdiv s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_udiv s1 s2
        | BT.Integer | BT.Real -> SMT.num_div s1 s2
        | _ -> failwith "Div")
     | DivNoSMT -> uninterp_same_type CN_Constant.div
     | Exp ->
       (match (get_num_z e1, get_num_z e2) with
        | Some z1, Some z2 when Z.fits_int z2 ->
          translate_term s (num_lit_ (Z.pow z1 (Z.to_int z2)) (IT.get_bt e1) loc)
        | _, _ -> failwith "Exp")
     | ExpNoSMT -> uninterp_same_type CN_Constant.exp
     | Rem ->
       (match IT.get_bt iterm with
        | BT.Bits (BT.Signed, _) -> SMT.bv_srem s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_urem s1 s2
        | BT.Integer -> SMT.num_rem s1 s2 (* CVC5 ?? *)
        | _ -> failwith "Rem")
     | RemNoSMT -> uninterp_same_type CN_Constant.rem
     | Mod ->
       (match IT.get_bt iterm with
        | BT.Bits (BT.Signed, _) -> SMT.bv_smod s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_urem s1 s2
        | BT.Integer -> SMT.num_mod s1 s2
        | _ -> failwith "Mod")
     | ModNoSMT -> uninterp_same_type CN_Constant.mod'
     | BW_Xor ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_xor s1 s2
        | _ -> failwith "BW_Xor")
     | BW_And ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_and s1 s2
        | _ -> failwith "BW_And")
     | BW_Or ->
       (match IT.get_bt iterm with BT.Bits _ -> SMT.bv_or s1 s2 | _ -> failwith "BW_Or")
     (* Shift amount should be positive? *)
     | ShiftLeft ->
       (match IT.get_bt iterm with
        | BT.Bits _ -> SMT.bv_shl s1 s2
        | _ -> failwith "ShiftLeft")
     (* Amount should be positive? *)
     | ShiftRight ->
       (match IT.get_bt iterm with
        | BT.Bits (BT.Signed, _) -> SMT.bv_ashr s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_lshr s1 s2
        | _ -> failwith "ShiftRight")
     | LT ->
       (match IT.get_bt e1 with
        | BT.Bits (BT.Signed, _) -> SMT.bv_slt s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_ult s1 s2
        | BT.Integer | BT.Real -> SMT.num_lt s1 s2
        | _ -> failwith "LT")
     | LE ->
       (match IT.get_bt e1 with
        | BT.Bits (BT.Signed, _) -> SMT.bv_sleq s1 s2
        | BT.Bits (BT.Unsigned, _) -> SMT.bv_uleq s1 s2
        | BT.Integer | BT.Real -> SMT.num_leq s1 s2
        | ty ->
          Pp.print stdout (!^"LE" ^^^ BT.pp ty);
          failwith "LE")
     (* NOTE: duplicates terms *)
     | Min -> translate_term s (ite_ (le_ (e1, e2) loc, e1, e2) loc)
     (* NOTE: duplicates terms *)
     | Max -> translate_term s (ite_ (ge_ (e1, e2) loc, e1, e2) loc)
     | EQ -> SMT.eq s1 s2
     | LTPointer ->
       let uintptr_cast = cast_ Memory.uintptr_bt in
       translate_term s (lt_ (uintptr_cast e1 loc, uintptr_cast e2 loc) loc)
     | LEPointer ->
       let uintptr_cast = cast_ Memory.uintptr_bt in
       translate_term s (le_ (uintptr_cast e1 loc, uintptr_cast e2 loc) loc)
     | SetUnion -> SMT.set_union s.smt_solver.config.exts s1 s2
     | SetIntersection -> SMT.set_intersection s.smt_solver.config.exts s1 s2
     | SetDifference -> SMT.set_difference s.smt_solver.config.exts s1 s2
     | SetMember -> SMT.set_member s.smt_solver.config.exts s1 s2
     | Subset -> SMT.set_subset s.smt_solver.config.exts s1 s2)
  | ITE (b, e1, e2) ->
    SMT.ite (translate_term s b) (translate_term s e1) (translate_term s e2)
  | EachI ((i1, (x, bt), i2), t) ->
    let rec aux i =
      if i <= i2 then (
        let su = make_subst [ (x, num_lit_ (Z.of_int i) bt loc) ] in
        let t1 = IT.subst su t in
        if i = i2 then t1 else IT.and2_ (t1, aux (i + 1)) loc)
      else
        failwith "EachI"
    in
    if i1 > i2 then
      translate_term s (IT.bool_ true loc)
    else
      translate_term s (aux i1)
  (* Tuples *)
  | Tuple es -> CN_Tuple.con (List.map (translate_term s) es)
  | NthTuple (n, e1) ->
    (match IT.get_bt e1 with
     | Tuple ts -> CN_Tuple.get (List.length ts) n (translate_term s e1)
     | _ -> failwith "NthTuple: not a tuple")
  (* Structs *)
  (* assumes that the fileds are in the correct order *)
  | Struct (tag, fields) ->
    let con = CN_Names.struct_con_name tag in
    let field (_, e) = translate_term s e in
    SMT.app_ con (List.map field fields)
  | StructMember (e1, f) ->
    SMT.app_ (CN_Names.struct_field_name f) [ translate_term s e1 ]
  | StructUpdate ((t, member), v) ->
    let tag = BT.struct_bt (IT.get_bt t) in
    let layout = Sym.Map.find (BT.struct_bt (IT.get_bt t)) struct_decls in
    let members = Memory.member_types layout in
    let str =
      List.map
        (fun (member', sct) ->
          let value =
            if Id.equal member member' then
              v
            else
              member_ ~member_bt:(Memory.bt_of_sct sct) (t, member') loc
          in
          (member', value))
        members
    in
    translate_term s (struct_ (tag, str) loc)
  | OffsetOf (tag, member) ->
    let decl = Sym.Map.find tag struct_decls in
    let v = Option.get (Memory.member_offset decl member) in
    translate_term s (int_lit_ v (IT.get_bt iterm) loc)
  (* Records *)
  | Record members ->
    let field (_, e) = translate_term s e in
    CN_Tuple.con (List.map field members)
  | RecordMember (e1, f) ->
    (match IT.get_bt e1 with
     | Record members ->
       let check (x, _) = Id.equal f x in
       let arity = List.length members in
       (match List.find_index check members with
        | Some n -> CN_Tuple.get arity n (translate_term s e1)
        | None -> failwith "Missing record field.")
     | _ -> failwith "RecordMemmber")
  | RecordUpdate ((t, member), v) ->
    let members = BT.record_bt (IT.get_bt t) in
    let str =
      List.map
        (fun (member', bt) ->
          let value =
            if Id.equal member member' then
              v
            else
              IT (RecordMember (t, member'), bt, loc)
          in
          (member', value))
        members
    in
    translate_term s (IT (Record str, IT.get_bt t, loc))
  | MemberShift (t, tag, member) ->
    CN_Pointer.ptr_shift
      ~ptr:(translate_term s t)
      ~null_case:(default (Loc ()))
      ~offset:(translate_term s (IT (OffsetOf (tag, member), Memory.uintptr_bt, loc)))
  | ArrayShift { base; ct; index } ->
    CN_Pointer.ptr_shift
      ~ptr:(translate_term s base)
      ~null_case:(default (Loc ()))
      ~offset:
        (let el_size = int_lit_ (Memory.size_of_ctype ct) Memory.uintptr_bt loc in
         (* locations don't matter here - we are translating straight away *)
         let ix =
           if BT.equal (IT.get_bt index) Memory.uintptr_bt then
             index
           else
             cast_ Memory.uintptr_bt index loc
         in
         translate_term s (mul_ (el_size, ix) loc))
  | CopyAllocId { addr; loc } ->
    CN_Pointer.copy_alloc_id
      ~ptr:(translate_term s loc)
      ~null_case:(default (Loc ()))
      ~addr:(translate_term s addr)
  | HasAllocId loc -> SMT.is_con CN_Pointer.alloc_id_addr_name (translate_term s loc)
  (* Lists *)
  | Nil bt -> CN_List.nil (translate_base_type bt)
  | Cons (e1, e2) -> CN_List.cons (translate_term s e1) (translate_term s e2)
  | Head e1 ->
    maybe_name (translate_term s e1) (fun xs ->
      CN_List.head xs (translate_term s (default_ (IT.get_bt iterm) loc)))
  | Tail e1 ->
    maybe_name (translate_term s e1) (fun xs ->
      CN_List.tail xs (translate_term s (default_ (IT.get_bt iterm) loc)))
  | NthList (x, y, z) ->
    let arg x = (translate_base_type (IT.get_bt x), translate_term s x) in
    let arg_ts, args = List.split (List.map arg [ x; y; z ]) in
    let bt = IT.get_bt iterm in
    let res_t = translate_base_type bt in
    let f = declare_bt_uninterpreted s CN_Constant.nth_list bt arg_ts res_t in
    SMT.app f args
  | ArrayToList (x, y, z) ->
    let arg x = (translate_base_type (IT.get_bt x), translate_term s x) in
    let arg_ts, args = List.split (List.map arg [ x; y; z ]) in
    let bt = IT.get_bt iterm in
    let res_t = translate_base_type bt in
    let f = declare_bt_uninterpreted s CN_Constant.array_to_list bt arg_ts res_t in
    SMT.app f args
  | SizeOf ct ->
    translate_term s (IT.int_lit_ (Memory.size_of_ctype ct) (IT.get_bt iterm) loc)
  | Representable (ct, t) -> translate_term s (representable struct_decls ct t loc)
  | Good (ct, t) -> translate_term s (good_value struct_decls ct t loc)
  | Aligned t ->
    let addr = addr_ t.t loc in
    assert (BT.equal (IT.get_bt addr) (IT.get_bt t.align));
    translate_term s (divisible_ (addr, t.align) loc)
  (* Maps *)
  | MapConst (bt, e1) ->
    (match IT.get_term e1 with
     (* This is a work-around for the fact the CVC5 only supports `const` on
        value, not vairables (see #11485 in the CVC5 repo).  Until this is
        fixed, with translate `MapConst Default` as just `Default`.  Hopefully,
        this is OK, as we are getting a weaker term (i.e., we can't assume that
        all elements of the array are the same, but they might be). *)
     | Const (Default t) -> default (BT.make_map_bt bt t)
     | _ ->
       let kt = translate_base_type bt in
       let vt = translate_base_type (IT.get_bt e1) in
       SMT.arr_const kt vt (translate_term s e1))
  | MapSet (mp, k, v) ->
    SMT.arr_store (translate_term s mp) (translate_term s k) (translate_term s v)
  | MapGet (mp, k) -> SMT.arr_select (translate_term s mp) (translate_term s k)
  | MapDef _ -> failwith "MapDef"
  | Apply (name, args) ->
    let def = Option.get (get_logical_function_def s.globals name) in
    (match def.body with
     | Def body -> translate_term s (Definition.Function.open_ def.args body args)
     | _ ->
       let do_arg arg = translate_base_type (IT.get_bt arg) in
       let args_ts = List.map do_arg args in
       let res_t = translate_base_type def.return_bt in
       let fu = declare_uninterpreted s name args_ts res_t in
       SMT.app fu (List.map (translate_term s) args))
  | Let ((x, e1), e2) ->
    let se1 = translate_term s e1 in
    let name = CN_Names.var_name x in
    let se2 = translate_term s e2 in
    SMT.let_ [ (name, se1) ] se2
  (* Datatypes *)
  (* Assumes the fields are in the correct order *)
  | Constructor (c, fields) ->
    let con = CN_Names.datatype_con_name c in
    let field (_, e) = translate_term s e in
    SMT.app_ con (List.map field fields)
    (* CN supports nested patterns, while SMTLIB does not, so we compile patterns to a
       optional predicate, and defined variables. *)
  | Match (e1, alts) ->
    let rec match_pat v (Pat (pat, _, _)) =
      match pat with
      | PSym x -> (None, [ (CN_Names.var_name x, v) ])
      | PWild -> (None, [])
      | PConstructor (c, fs) ->
        let field (f, nested) =
          let new_v = SMT.app_ (CN_Names.datatype_field_name f) [ v ] in
          match_pat new_v nested
        in
        let conds, defs = List.split (List.map field fs) in
        let nested_cond = SMT.bool_ands (List.filter_map (fun x -> x) conds) in
        let cname = CN_Names.datatype_con_name c in
        let cond = SMT.bool_and (SMT.is_con cname v) nested_cond in
        (Some cond, List.concat defs)
    in
    let rec do_alts v alts =
      match alts with
      | [] -> translate_term s (default_ (IT.get_bt iterm) loc)
      | (pat, rhs) :: more ->
        let mb_cond, binds = match_pat v pat in
        let k = SMT.let_ binds (translate_term s rhs) in
        (match mb_cond with Some cond -> SMT.ite cond k (do_alts v more) | None -> k)
    in
    let x = fresh_name s "match" in
    SMT.let_ [ (x, translate_term s e1) ] (do_alts (SMT.atom x) alts)
  (* Casts *)
  | WrapI (ity, arg) ->
    bv_cast
      ~to_:(Memory.bt_of_sct (Sctypes.Integer ity))
      ~from:(IT.get_bt arg)
      (translate_term s arg)
  | Cast (cbt, t) ->
    let smt_term = translate_term s t in
    (match (IT.get_bt t, cbt) with
     | Bits _, Loc () ->
       let addr =
         if BT.equal (IT.get_bt t) Memory.uintptr_bt then
           smt_term
         else
           bv_cast ~to_:Memory.uintptr_bt ~from:(IT.get_bt t) smt_term
       in
       CN_Pointer.bits_to_ptr ~bits:addr ~alloc_id:(default Alloc_id)
     | Loc (), Bits _ ->
       let maybe_cast x =
         if BT.equal cbt Memory.uintptr_bt then
           x
         else
           bv_cast ~to_:cbt ~from:Memory.uintptr_bt x
       in
       maybe_cast (CN_Pointer.addr_of ~ptr:smt_term)
     | Loc (), Alloc_id ->
       CN_Pointer.alloc_id_of ~ptr:smt_term ~null_case:(default Alloc_id)
     | MemByte, Bits _ ->
       let maybe_cast x =
         if BT.equal cbt (BT.Bits (Unsigned, 8)) then
           x
         else
           bv_cast ~to_:cbt ~from:(BT.Bits (Unsigned, 8)) x
       in
       maybe_cast (SMT.app_ CN_MemByte.value_name [ smt_term ])
     | MemByte, Alloc_id -> SMT.app_ CN_MemByte.alloc_id_name [ smt_term ]
     | Real, Integer -> SMT.real_to_int smt_term
     | Integer, Real -> SMT.int_to_real smt_term
     | Bits _, Bits _ -> bv_cast ~to_:cbt ~from:(IT.get_bt t) smt_term
     | _ -> assert false)


(** Add an assertion.  Quantified predicates are ignored. *)
let add_assumption solver global lc =
  let s1 = { solver with globals = global } in
  match lc with
  | LC.T it -> ack_command solver (SMT.assume (translate_term s1 it))
  | Forall _ -> ()


(** Goals are translated to this type *)
type reduction =
  { expr : SMT.sexp; (* translation of `it` *)
    qs : (Sym.t * BT.t) list; (* quantifier instantiation *)
    extra : SMT.sexp list (* additional assumptions *)
  }

let translate_goal solver assumptions lc =
  let here = Locations.other __LOC__ in
  let instantiated =
    match lc with
    | LC.T it -> { expr = translate_term solver it; qs = []; extra = [] }
    | Forall ((s, bt), it) ->
      let v_s, v = IT.fresh_same bt s here in
      let it = IT.subst (make_subst [ (s, v) ]) it in
      { expr = translate_term solver it; qs = [ (v_s, bt) ]; extra = [] }
  in
  let add_asmps acc0 (s, bt) =
    let v = sym_ (s, bt, here) in
    let check_asmp lc acc =
      match lc with
      | LC.Forall ((s', bt'), it') when BT.equal bt bt' ->
        let new_asmp = IT.subst (make_subst [ (s', v) ]) it' in
        translate_term solver new_asmp :: acc
      | _ -> acc
    in
    LC.Set.fold check_asmp assumptions acc0
  in
  { instantiated with extra = List.fold_left add_asmps [] instantiated.qs }


(* as similarly suggested by Robbert *)
let shortcut simp_ctxt lc =
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  match lc with LC.T (IT (Const (Bool true), _, _)) -> `True | _ -> `No_shortcut lc


(** {1 Solver Initialization} *)

(** Declare a group of (possibly) mutually recursive datatypes *)
let declare_datatype_group s names =
  let mk_con_field (l, t) = (CN_Names.datatype_field_name l, translate_base_type t) in
  let mk_con c =
    let ci = Sym.Map.find c s.globals.datatype_constrs in
    (CN_Names.datatype_con_name c, List.map mk_con_field ci.params)
  in
  let cons (info : BT.dt_info) = List.map mk_con info.constrs in
  let to_smt (x : Sym.t) =
    let info = Sym.Map.find x s.globals.datatypes in
    (CN_Names.datatype_name x, [], cons info)
  in
  ack_command s (SMT.declare_datatypes (List.map to_smt names))


(** Declare a struct type and all struct types that it depends on.
    The `done_struct` keeps track of which structs we've already declared. *)
let rec declare_struct s done_struct name decl =
  let mp = !done_struct in
  if Sym.Set.mem name mp then
    ()
  else (
    done_struct := Sym.Set.add name mp;
    let mk_field (l, t) =
      let rec declare_nested ty =
        match ty with
        | BT.Struct name' ->
          let decl = Sym.Map.find name' s.globals.struct_decls in
          declare_struct s done_struct name' decl
        | Map (_, el) -> declare_nested el
        | _ -> ()
      in
      let ty = Memory.bt_of_sct t in
      declare_nested ty;
      (CN_Names.struct_field_name l, translate_base_type ty)
    in
    let mk_piece (x : Memory.struct_piece) = Option.map mk_field x.member_or_padding in
    ack_command
      s
      (SMT.declare_datatype
         (CN_Names.struct_name name)
         []
         [ (CN_Names.struct_con_name name, List.filter_map mk_piece decl) ]))


(** Declare various types always available to the solver. *)
let declare_solver_basics s =
  CN_Tuple.declare s;
  CN_List.declare s;
  CN_MemByte.declare s;
  CN_Pointer.declare s;
  (* structs may depend only on other structs. datatypes may depend on other datatypes and
     structs. *)
  let done_structs = ref Sym.Set.empty in
  Sym.Map.iter (declare_struct s done_structs) s.globals.struct_decls;
  List.iter (declare_datatype_group s) (Option.get s.globals.datatype_order)


(* Logging *)

module Logger = struct
  let to_file = ref false

  (** NOTE: this interferes with line numbers *)
  let include_solver_responses = ref false

  let dir = ref (None : string option)

  let log_counter = ref 0 (* Names of SMT files *)

  (** Pick a logger based on the above settings *)
  let make prefix =
    let log_id = !log_counter in
    log_counter := log_id + 1;
    let get_file suf =
      let dir =
        match !dir with
        | Some dir -> dir
        | None ->
          let nm = Printf.sprintf "cn_%.3f" (Unix.gettimeofday ()) in
          let d = Filename.concat (Filename.get_temp_dir_name ()) nm in
          dir := Some d;
          d
      in
      if not (Sys.file_exists dir) then Sys.mkdir dir 0o700 else ();
      open_out (Filename.concat dir (prefix ^ suf ^ string_of_int log_id ^ ".smt"))
    in
    if !to_file then (
      let out = get_file "_send_" in
      if !include_solver_responses then
        { SMT.send = Printf.fprintf out "[->] %s\n%!";
          SMT.receive = Printf.fprintf out "[<-] %s\n%!";
          SMT.stop = (fun _ -> close_out out)
        }
      else
        { SMT.send = Printf.fprintf out "%s\n%!";
          SMT.receive = (fun _ -> ());
          SMT.stop = (fun _ -> close_out out)
        })
    else
      { SMT.send = (fun _ -> ()); SMT.receive = (fun _ -> ()); SMT.stop = (fun _ -> ()) }
end

let solver_path = ref (None : string option)

let solver_type = ref (None : SMT.solver_extensions option)

let solver_flags = ref (None : string list option)

(** Make a new solver instance *)
let make globals =
  let cfg =
    ref
      (match !solver_type with
       | Some t ->
         (match t with
          | SMT.Z3 -> SMT.z3
          | SMT.CVC5 -> SMT.cvc5
          | SMT.Other -> failwith "Unsupported solver.")
       | None ->
         (match !solver_path with
          | None -> SMT.z3
          | Some path ->
            (match Filename.basename path with
             | "z3" -> SMT.z3
             | "cvc5" -> SMT.cvc5
             | _ -> failwith "Please specify solver type")))
  in
  (match !solver_path with Some path -> cfg := { !cfg with SMT.exe = path } | None -> ());
  (match !solver_flags with Some opts -> cfg := { !cfg with SMT.opts } | None -> ());
  cfg
  := { !cfg with
       log =
         Logger.make
           (match !cfg.exts with
            | SMT.Z3 -> "z3"
            | SMT.CVC5 -> "cvc5"
            | SMT.Other -> "other")
     };
  let s =
    { smt_solver = SMT.new_solver !cfg;
      cur_frame = ref (empty_solver_frame ());
      prev_frames = ref [];
      name_seed = ref 0;
      globals
    }
  in
  declare_solver_basics s;
  s


(* ---------------------------------------------------------------------------*)
(* GLOBAL STATE: Models *)
(* ---------------------------------------------------------------------------*)

type model = int

type model_fn = IT.t -> IT.t option

type model_with_q = model * (Sym.t * BaseTypes.t) list

type model_table = (model, model_fn) Hashtbl.t

let models_tbl : model_table = Hashtbl.create 1

let empty_model =
  let model = Option.some in
  Hashtbl.add models_tbl 0 model;
  0


type model_state =
  | Model of model_with_q
  | No_model

let model_state = ref No_model

let model () = match !model_state with No_model -> assert false | Model mo -> mo

(** Evaluate terms in the context of a model computed by the solver. *)
let model_evaluator, reset_model_evaluator_state =
  (* internal state for the model evaluator, reuses the solver across consecutive calls for efficiency *)
  let model_evaluator_solver : Simple_smt.solver option ref = ref None in
  let currently_loaded_model = ref 0 in
  let model_id = ref 0 in
  let new_model_id () =
    (* Start with 1, as 0 is the id of the empty model *)
    model_id := !model_id + 1;
    !model_id
  in
  let reset_model_evaluator_state () =
    currently_loaded_model := 0;
    model_evaluator_solver := None;
    model_id := 0
  in
  let model_evaluator solver mo =
    match SMT.to_list mo with
    | None -> failwith "model is an atom"
    | Some defs ->
      let scfg = solver.smt_solver.config in
      let cfg = { scfg with log = Logger.make "model" } in
      let smt_solver, new_solver =
        match !model_evaluator_solver with
        | Some smt_solver -> (smt_solver, false)
        | None ->
          let s = SMT.new_solver cfg in
          model_evaluator_solver := Some s;
          (s, true)
      in
      let model_id = new_model_id () in
      let gs = solver.globals in
      let evaluator =
        { smt_solver;
          cur_frame = ref (empty_solver_frame ());
          prev_frames =
            ref
              (List.map copy_solver_frame (!(solver.cur_frame) :: !(solver.prev_frames)))
            (* We keep the prev_frames because things that were declared, would now be
               defined by the model. Also, we need the infromation about the C type
               mapping. *);
          name_seed = solver.name_seed;
          globals = gs
        }
      in
      if new_solver then (
        declare_solver_basics evaluator;
        push evaluator);
      let model_fn e =
        if not (!currently_loaded_model = model_id) then (
          currently_loaded_model := model_id;
          pop evaluator 1;
          push evaluator;
          List.iter (debug_ack_command evaluator) defs);
        let inp = translate_term evaluator e in
        match SMT.check smt_solver with
        | SMT.Sat ->
          let res = SMT.get_expr smt_solver inp in
          let ctys = get_ctype_table evaluator in
          Some (get_ivalue gs ctys (get_bt e) (SMT.no_let res))
        | _ -> None
      in
      Hashtbl.add models_tbl model_id model_fn;
      model_id
  in
  (model_evaluator, reset_model_evaluator_state)


(* ---------------------------------------------------------------------------*)

module TryHard = struct

  let translate_forall solver qs body = 
    let rec alpha_rename qs body = 
      match qs with
      | [] -> ([],body)
      | (s, bt) :: qs' ->
        let qs',body = alpha_rename qs' body in
        let s, body = IT.alpha_rename s body in
        (((s, bt) :: qs'), body)
    in
    let qs, body = alpha_rename qs body in
    let body_ = translate_term solver body in
    let qs_ = 
      List.map (fun (s, bt) ->
        let name = CN_Names.var_name s in
        let sort = translate_base_type bt in
        (SMT.atom name, sort)
        ) qs
    in
    SMT.forall qs_ body_

  let translate_lc solver = function
    | LC.T it -> translate_term solver it
    | LC.Forall ((s, bt), body) -> translate_forall solver [(s, bt)] body


  let translate_function solver f args rbt body =
    let loc = Locations.other __LOC__ in
    let arg_exprs = List.map (fun (s,bt) -> IT.sym_ (s, bt, loc)) args in
    translate_forall solver args (eq_ (apply_ f arg_exprs rbt loc, body) loc)

  let translate_functions solver =
    let open Definition.Function in
    List.filter_map (fun (f, def) ->
      match def.body with
      | Rec_Def body -> 
          (* Normally this would require the relevant functions,
             including `f`, to already have been declared. Here this
             happens lazily (in the `Apply` case), including for `f`. *)
          Some (translate_function solver f def.args def.return_bt body)
      | Def _ -> None
      | Uninterp -> None
      ) (Sym.Map.bindings solver.globals.logical_functions)


  let translate_foralls solver assumptions =
    List.map (translate_lc solver) (List.filter LC.is_forall assumptions)

end

let try_hard = ref false


(** The main way to query the solver. *)
let provable ~loc ~solver ~global ~assumptions ~simp_ctxt lc =
  let _ = loc in
  let _ = global in
  let set_model smt_solver qs =
    let defs = SMT.get_model smt_solver in
    let model = model_evaluator solver defs in
    model_state := Model (model, qs)
  in
  match shortcut simp_ctxt lc with
  | `True -> 
    model_state := No_model;
    `True
  | `No_shortcut lc ->
    let { expr; qs; extra } = translate_goal solver assumptions lc in
    let nexpr = SMT.bool_not expr in
    let inc = solver.smt_solver in
    debug_ack_command solver (SMT.push 1);
    debug_ack_command solver (SMT.assume (SMT.bool_ands (nexpr :: extra)));
    (match SMT.check inc with
     | SMT.Unsat ->
       debug_ack_command solver (SMT.pop 1);
       model_state := No_model;
       `True
     | SMT.Sat when !try_hard ->
       debug_ack_command solver (SMT.pop 1);
       let assumptions = LC.Set.to_list assumptions in
       let foralls = TryHard.translate_foralls solver assumptions in
       let functions = TryHard.translate_functions solver in
       debug_ack_command solver (SMT.push 1);
       debug_ack_command solver (SMT.assume (SMT.bool_ands (nexpr :: foralls @ functions)));
       Pp.(debug 3 (lazy !^"***** try-hard *****"));
       (match SMT.check inc with
        | SMT.Unsat ->
            debug_ack_command solver (SMT.pop 1);
            model_state := No_model;
            Pp.(debug 3 (lazy !^"***** try-hard: provable *****"));
            `True
        | SMT.Sat ->
            set_model inc qs;
            debug_ack_command solver (SMT.pop 1);
            Pp.(debug 3 (lazy !^"***** try-hard: unprovable *****"));
            `False
        | SMT.Unknown ->
            set_model inc qs;
            debug_ack_command solver (SMT.pop 1);
            Pp.(debug 3 (lazy !^"***** try-hard: unknown *****"));
            `False)
     | SMT.Sat ->
       set_model inc qs;
       debug_ack_command solver (SMT.pop 1);
       `False
     | SMT.Unknown ->
       debug_ack_command solver (SMT.pop 1);
       failwith "Unknown")







(* ISD: Could these globs be different from the saved ones? *)
let eval mo t =
  let model_fn = Hashtbl.find models_tbl mo in
  model_fn t
