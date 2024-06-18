module SMT = Simple_smt
module IT = IndexTerms
open IndexTerms
module BT = BaseTypes
open BaseTypes
module LC = LogicalConstraints
open LogicalConstraints
module SymMap = Map.Make(Sym)
module BT_Table = Hashtbl.Make(BT)
module Int_Table = Hashtbl.Make(Int)
module LCSet = Set.Make(LC)
open Global
open Pp

(* XXX: probably should add some prefixes to try to avoid name collisions. *)
(** Functions that pick names for things. *)
module CN_Names = struct
  let var_name x            = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)
  let named_expr_name       = "_cn_named"
  let uninterpreted_name x  = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)

  let struct_name x         = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)
  let struct_con_name x     = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)
  let struct_field_name x   = Id.pp_string x ^ "_fld"

  let datatype_name x       = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)
  let datatype_con_name x   = Sym.pp_string x ^ "_" ^ string_of_int (Sym.num x)
  let datatype_field_name x = Id.pp_string x ^ "_fld"
end



(** Names for constants that may be uninterpreted.  See [bt_uninterpreted] *)
module CN_Constant = struct
  let default       = ("default_uf",  0)
  let mul           = ("mul_uf",      1)
  let div           = ("div_uf",      2)
  let exp           = ("exp_uf",      3)
  let rem           = ("rem_uf",      4)
  let mod'          = ("mod_uf",      5)
  let nth_list      = ("nth_list_uf", 6)
  let array_to_list = ("array_to_list_uf", 7)
end


type solver_frame =
  { mutable commands: SMT.sexp list
    (** Ack-style SMT commands, most recent first. *)

  ; mutable uninterpreted: SMT.sexp SymMap.t
    (** Uninterpreted functions and variables that we've declared. *)

  ; bt_uninterpreted: (SMT.sexp BT_Table.t) Int_Table.t
    (** Uninterpreted constants, indexed by base type. *)
  }

let empty_solver_frame () =
  { commands          = []
  ; uninterpreted     = SymMap.empty
  ; bt_uninterpreted  = Int_Table.create 50
  }


type solver =
  { smt_solver: SMT.solver
    (** The SMT solver connection. *)

  ; cur_frame:   solver_frame ref
  ; prev_frames: (solver_frame list) ref
    (** Push/pop model. Current frame, and previous frames. *)

  ; name_seed: int ref
    (** Used to generate names. *)
    (* XXX: This could, perhaps, go in the frame.  Then when we pop frames,
       we'd go back to the old numbers, which should be OK, I think? *)

  ; globals: Global.t
  }

module Debug = struct
  let dump_frame (f: solver_frame) =
    let dump k v = Printf.printf "| %s\n%!" (Sym.pp_string k) in
    SymMap.iter dump f.uninterpreted;
    Printf.printf "+--------------------\n%!"

  let _dump_solver solver =
    Printf.printf "| Start Solver Dump\n%!";
    dump_frame !(solver.cur_frame);
    List.iter dump_frame !(solver.prev_frames);
    Printf.printf "| End Solver Dump\n%!"
end

(** Lookup something in one of the existing frames *)
let search_frames s f = List.find_map f (!(s.cur_frame) :: !(s.prev_frames))


(** Start a new scope. *)
let push s =
  SMT.ack_command s.smt_solver (SMT.push 1);
  s.prev_frames := !(s.cur_frame) :: !(s.prev_frames);
  s.cur_frame   := empty_solver_frame ()

(** Return to the previous scope.  Assumes that there is a previous scope. *)
let pop s n =
  if n == 0
    then ()
    else begin
      SMT.ack_command s.smt_solver (SMT.pop n);
      let rec drop count xs =
                match xs with
                | new_cur :: new_rest ->
                  if count = 1
                    then begin
                      s.cur_frame := new_cur;
                      s.prev_frames := new_rest
                    end else drop (count - 1) new_rest
                | _ -> assert false
      in
      drop n !(s.prev_frames)
    end

let num_scopes s = List.length !(s.prev_frames)

(** Do an ack_style command. These are logged. *)
let ack_command s cmd =
  SMT.ack_command s.smt_solver cmd;
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
  let check f = SymMap.find_opt name f.uninterpreted in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = CN_Names.uninterpreted_name name in
    ack_command s (SMT.declare_fun sname args_ts res_t);
    let e = SMT.atom sname in
    let f = !(s.cur_frame) in
    f.uninterpreted <- SymMap.add name e f.uninterpreted;
    e

 
(** Declare an uninterpreted function, indexed by a base type. *)
let declare_bt_uninterpreted s (name,k) bt args_ts res_t =
  let check f = Option.bind (Int_Table.find_opt f.bt_uninterpreted k)
                            (fun m -> BT_Table.find_opt m bt) in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = fresh_name s name in
    ack_command s (SMT.declare_fun sname args_ts res_t);
    let e = SMT.atom sname in
    let top_map = !(s.cur_frame).bt_uninterpreted in
    let mp = match Int_Table.find_opt top_map k with
             | Some m -> m
             | None   ->
               let m = BT_Table.create 20 in
               Int_Table.add top_map k m;
               m in
    BT_Table.add mp bt e;
    e






(* Note: CVC5 has support for arbitrary tuples without declaring them.
   Also, instead of declaring a fixed number of tuples ahead of time,
   we could declare the types on demand when we need them, with another
   piece of state in the solver to track which ones we have declared. *)
module CN_Tuple = struct
  let name arity = "cn_tuple_" ^ string_of_int arity

  let selector arity field =
    "cn_get_" ^ string_of_int field ^ "_of_" ^ string_of_int arity

  (** A tuple type with the given name *)
  let t tys =
    let arity = List.length tys in
    SMT.app_ (name arity) tys

  (** Declare a datatype for a struct *)
  let declare s arity =
    let name    = name arity in
    let param i = "a" ^ string_of_int i in
    let params  = List.init arity param in
    let field i = (selector arity i, SMT.atom (param i)) in
    let fields  = List.init arity field in
    ack_command s (SMT.declare_datatype name params [ (name, fields) ])

  (** Make a tuple value *)
  let con es =
    let arity = List.length es in
    SMT.app_ (name arity) es

  (** Get a field of a tuple *)
  let get arity field tup = SMT.app_ (selector arity field) [tup]
end


module CN_AllocId = struct
  (** The type to use  for allocation ids *)
  let t           = if !use_vip then SMT.t_int else CN_Tuple.t []

  (** Parse an allocation id from an S-expression *)
  let from_sexp s = if !use_vip then SMT.to_z s else Z.zero

  (** Convert an allocation id to an S-expression *)
  let to_sexp s   = if !use_vip then SMT.int_zk s else CN_Tuple.con []
end


module CN_Pointer = struct
  let name        = "cn_pointer"
  let alloc_name  = "cn_pointer_alloc"
  let addr_name   = "cn_pointer_addr"

  (** Bit-width of pointers *)
  let width = match Memory.intptr_bt with
              | Bits (_,w) -> w
              | _ -> failwith "Ponter is not bits"

  (** The name of the pointer type *)
  let t = SMT.atom name

  (** Add the declaration for the pointer type *)
  let declare s =
    ack_command s (
      SMT.declare_datatype
        name []
        [ (name,
            [ (alloc_name, CN_AllocId.t)
            ; (addr_name, SMT.t_bits width)
            ]
          )
        ]
    )

  (** Make a pointer value *)
  let con base offset = SMT.app_ name [base;offset]

  (** Get the allocation id of a pointer *)
  let get_alloc pt    = SMT.app_ alloc_name [pt]

  (** Get the adderss of a pointer *)
  let get_addr pt     = SMT.app_ addr_name [pt]
end

module CN_List = struct
  let name      = "cn_list"
  let nil_name  = "cn_nil"
  let cons_name = "cn_cons"
  let head_name = "cn_head"
  let tail_name = "cn_tail"

  let t a = SMT.app_ name [a]

  let declare s =
    let a = SMT.atom "a" in
    ack_command s (SMT.declare_datatype name ["a"]
      [ (nil_name, [])
      ; (cons_name, [ (head_name, a); (tail_name, t a) ])
      ])

  let nil elT   = SMT.as_type (SMT.atom nil_name) (t elT)
  let cons x xs = SMT.app_ cons_name [x;xs]

  let head xs orelse = SMT.ite (SMT.is_con cons_name xs)
                               (SMT.app_ head_name [xs]) orelse

  let tail xs orelse = SMT.ite (SMT.is_con cons_name xs)
                               (SMT.app_ tail_name [xs]) orelse
end


(** {1 Type to SMT } *)

(** Translate a base type to SMT *)
let rec translate_base_type = function
  | Unit            -> CN_Tuple.t []
  | Bool            -> SMT.t_bool
  | Integer         -> SMT.t_int
  | Bits (_, n)     -> SMT.t_bits n
  | Real            -> SMT.t_real
  | Loc             -> CN_Pointer.t
  | Alloc_id        -> CN_AllocId.t
  | CType           -> CN_Tuple.t []
  | List bt         -> CN_List.t (translate_base_type bt)
  | Set bt          -> SMT.t_set (translate_base_type bt)
  | Map (k, v)      -> SMT.t_array (translate_base_type k)
                                   (translate_base_type v)
  | Tuple bts       -> CN_Tuple.t (List.map translate_base_type bts)
  | Struct tag      -> SMT.atom (CN_Names.struct_name tag)
  | Datatype tag    -> SMT.atom (CN_Names.datatype_name tag)
  | Record members  ->
    let get_val (_,v) = v in
    translate_base_type (Tuple (List.map get_val members))



(** {1 SMT to Term} *)


(** Translate an SMT value to a CN term *)
let rec
  get_ivalue bt sexp = IT (get_value bt sexp, bt, Cerb_location.unknown)
and
  get_value bt (sexp: SMT.sexp) =
  match bt with
  | Unit            -> Const Unit
  | Bool            -> Const (Bool (SMT.to_bool sexp))
  | Integer         -> Const (Z (SMT.to_z sexp))

  | Bits (sign, n)  ->
    let signed = equal_sign sign Signed in
    Const (Bits ((sign,n), SMT.to_bits n signed sexp))

  | Real            -> Const (Q (SMT.to_q sexp))

  | Loc ->
      begin match SMT.to_con sexp with
      | (_con, [sbase;saddr]) ->
        let base = CN_AllocId.from_sexp sbase in
        let addr = match get_value Memory.intptr_bt saddr with
                   | Const (Bits (_,z)) -> z
                   | _ -> failwith "Pointer value is not bits"
        in Const (if Z.equal base Z.zero && Z.equal addr Z.zero
                    then Null
                    else Pointer { alloc_id = base; addr = addr }
                 )
      | _ -> failwith "Loc"
      end

  | Alloc_id        -> Const (Alloc_id (CN_AllocId.from_sexp sexp))

  | CType           -> Const (Default CType)

  | List elT ->
    begin match SMT.to_con sexp with
    | (con,[])    when String.equal con CN_List.nil_name -> Nil elT
    | (con,[h;t]) when String.equal con CN_List.cons_name ->
        Cons (get_ivalue elT h, get_ivalue bt t)
    | _ -> failwith "List"
    end

  | Set bt          -> Const (Default bt) (* XXX *)
  | Map (k, v)      -> Const (Default bt) (* XXX *)

  | Tuple bts ->
    let (_con,vals) = SMT.to_con sexp in
    Tuple (List.map2 get_ivalue bts vals)

  | Struct tag      -> Const (Default bt) (* XXX *)
  | Datatype tag    -> Const (Default bt) (* XXX *)

  | Record members  ->
    let (_con,vals) = SMT.to_con sexp in
    let mk_field (l,bt) e = (l, get_ivalue bt e) in
    Record (List.map2 mk_field members vals)


(** {1 Term to SMT} *)


(** Translate a constant to SMT *)
let rec translate_const s co =
  match co with
  | Z z             -> SMT.int_zk z
  | Bits ((_,w), z) -> SMT.bv_k w z
  | Q q             -> SMT.real_k q

  | Pointer p ->
    begin match Memory.intptr_bt with
    | Bits (_,w) ->
        CN_Pointer.con (CN_AllocId.to_sexp p.alloc_id) (SMT.bv_k w p.addr)
    | _ -> failwith "translate_const: Pointer is not Bits."
    end

  | Alloc_id z -> CN_AllocId.to_sexp z
  | Bool b     -> SMT.bool_k b
  | Unit       -> SMT.atom (CN_Tuple.name 0)

  | Null ->
    translate_const s (Pointer { alloc_id = Z.of_int 0; addr = Z.of_int 0 })

  | CType_const _ -> SMT.atom (CN_Tuple.name 0)

  | Default t ->
    declare_bt_uninterpreted s CN_Constant.default t [] (translate_base_type t)

(** Casting between bit-vector types *)
let bv_cast to_bt from_bt x =
  let bits_info bt = match BT.is_bits_bt bt with
    | Some (sign, sz) -> (BT.equal_sign sign BT.Signed, sz)
    | None -> failwith ("mk_bv_cast: non-bv type: " ^ Pp.plain (BT.pp bt))
  in
  let (to_signed,   to_sz)   = bits_info to_bt in
  let (from_signed, from_sz) = bits_info from_bt in
  match () with
  | _ when to_sz == from_sz -> x
  | _ when to_sz < from_sz  -> SMT.bv_extract (to_sz - 1) 0 x
  | _ when from_signed      -> SMT.bv_sign_extend (to_sz - from_sz) x
  | _                       -> SMT.bv_zero_extend (to_sz - from_sz) x


(** [bv_clz rw w e] counts the leading zeroes in [e], which should
be a bit-vector of width [w].  The result is a bit-vector of width [rw].
Note that this duplicates [e]. *)
let bv_clz result_w =
  let result k  = SMT.bv_k result_w k in
  let eq_0 w e  = SMT.eq e (SMT.bv_k w Z.zero) in

  let rec count w e =
    if w == 1
    then SMT.ite (eq_0 w e) (result Z.one) (result Z.zero)
    else
      let top_w = w / 2 in
      let bot_w = w - top_w in
      let top    = SMT.bv_extract (w - 1) (w - top_w) e in
      let bot    = SMT.bv_extract (bot_w - 1) 0 e in
      SMT.ite (eq_0 top_w top)
        (SMT.bv_add (count bot_w bot) (result (Z.of_int top_w)))
        (count top_w top)
  in count


(** [bv_ctz rw w e] counts the tailing zeroes in [e], which should
be a bit-vector of width [w].  The result is a bit-vector of width [rw].
Note that this duplicates [e]. *)
let bv_ctz result_w =
  let result k  = SMT.bv_k result_w k in
  let eq_0 w e  = SMT.eq e (SMT.bv_k w Z.zero) in

  let rec count w e =
    if w == 1
      then SMT.ite (eq_0 w e) (result Z.one) (result Z.zero)
      else
        let top_w = w / 2 in
        let bot_w = w - top_w in
        let top = SMT.bv_extract (w - 1) (w - top_w) e in
        let bot = SMT.bv_extract (bot_w - 1) 0 e in
        SMT.ite (eq_0 bot_w bot)
          (SMT.bv_add (count top_w top) (result (Z.of_int bot_w)))
          (count bot_w bot)
  in count

(** Translate a vraible to SMT.  Declare if needed. *)
let translate_var s name bt =
  let check f = SymMap.find_opt name f.uninterpreted in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = CN_Names.var_name name in
    ack_command s (SMT.declare sname (translate_base_type bt));
    let e = SMT.atom sname in
    let f = !(s.cur_frame) in
    f.uninterpreted <- SymMap.add name e f.uninterpreted;
    e


(** Translat a CN term to SMT *)
let rec translate_term s iterm =
  let here          = IT.loc iterm in
  let struct_decls  = s.globals.struct_decls in
  let maybe_name e k =
        if SMT.is_atom e
          then k e
          else let x = fresh_name s CN_Names.named_expr_name in
               SMT.let_ [(x,e)] (k (SMT.atom x)) in


  match IT.term iterm with
  | Const c -> translate_const s c

  | Sym x -> translate_var s x (IT.basetype iterm)

  | Unop (op,e1) ->
    begin match op with

    | BWFFSNoSMT ->
      (* XXX: This desugaring duplicates e1 *)
      let intl i = int_lit_ i (IT.bt e1) here in
      translate_term s
        (ite_ ( eq_ (e1, intl 0) here
              , intl 0
              , add_ (arith_unop BWCTZNoSMT e1 here, intl 1) here
              ) here
        )

    | Not        -> SMT.bool_not (translate_term s e1)

    | Negate ->
      begin match IT.basetype iterm with
      | BT.Bits _ -> SMT.bv_neg (translate_term s e1)
      | BT.Integer
      | BT.Real   -> SMT.num_neg (translate_term s e1)
      | _ -> failwith (__FUNCTION__ ^ ":Unop (Negate, _)")
      end

    | BWCLZNoSMT ->
      begin match IT.basetype iterm with
      | BT.Bits (_,w) -> maybe_name (translate_term s e1) (bv_clz w w)
      | _             -> failwith "solver: BWCLZNoSMT: not a bitwise type"
      end

    | BWCTZNoSMT ->
      begin match IT.basetype iterm with
      | BT.Bits (_,w) -> maybe_name (translate_term s e1) (bv_ctz w w)
      | _             -> failwith "solver: BWCTZNoSMT: not a bitwise type"
      end
    end

  | Binop (op,e1,e2) ->
    let s1 = translate_term s e1 in
    let s2 = translate_term s e2 in

    (* binary uninterpreted function, same type for arguments and result. *)
    let uninterp_same_type k =
      let bt    = IT.basetype iterm in
      let smt_t = translate_base_type bt in
      let f     = declare_bt_uninterpreted s k bt [smt_t;smt_t] smt_t in
      SMT.app f [s1;s2]
    in

    begin match op with
    | And   -> SMT.bool_and s1 s2
    | Or    -> SMT.bool_or s1 s2
    | Impl  -> SMT.bool_implies s1 s2

    | Add -> begin match IT.basetype iterm with
      | BT.Bits _            -> SMT.bv_add s1 s2
      | BT.Integer | BT.Real -> SMT.num_add s1 s2
      | _ -> failwith "Add"
      end

    | Sub -> begin match IT.basetype iterm with
      | BT.Bits _            -> SMT.bv_sub s1 s2
      | BT.Integer | BT.Real -> SMT.num_sub s1 s2
      | _ -> failwith "Sub"
      end

    | Mul -> begin match IT.basetype iterm with
      | BT.Bits _            -> SMT.bv_mul s1 s2
      | BT.Integer | BT.Real -> SMT.num_mul s1 s2
      | _  -> failwith "Mul"
      end

    | MulNoSMT -> uninterp_same_type CN_Constant.mul

    | Div -> begin match IT.basetype iterm with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_sdiv s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_udiv s1 s2
      | BT.Integer | BT.Real    -> SMT.num_div s1 s2
      | _  -> failwith "Div"
      end

    | DivNoSMT -> uninterp_same_type CN_Constant.div

    | Exp -> begin match get_num_z e1, get_num_z e2 with
      | Some z1, Some z2 when Z.fits_int z2 ->
        translate_term s (num_lit_ (Z.pow z1 (Z.to_int z2)) (IT.bt e1) here)
      | _, _ -> failwith "Exp"
      end

    | ExpNoSMT -> uninterp_same_type CN_Constant.exp

    | Rem -> begin match IT.basetype iterm with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_srem s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_urem s1 s2
      | BT.Integer              -> SMT.num_rem s1 s2 (* CVC5 ?? *)
      | _                       -> failwith "Rem"
      end

    | RemNoSMT -> uninterp_same_type CN_Constant.rem

    | Mod -> begin match IT.basetype iterm with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_smod s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_urem s1 s2
      | BT.Integer              -> SMT.num_mod s1 s2
      | _                       -> failwith "Mod"
      end

    | ModNoSMT -> uninterp_same_type CN_Constant.mod'

    (* XXX: Should this be names BWXor instead? *)
    | XORNoSMT -> begin match IT.basetype iterm with
      | BT.Bits _ -> SMT.bv_xor s1 s2
      | _         -> failwith "XORNoSMT"
      end

    (* XXX: Why no SMT? *)
    | BWAndNoSMT -> begin match IT.basetype iterm with
      | BT.Bits _ -> SMT.bv_and s1 s2
      | _         -> failwith "BWAndNoSMT"
      end

    (* XXX: Why no SMT? *)
    | BWOrNoSMT -> begin match IT.basetype iterm with
      | BT.Bits _ -> SMT.bv_or s1 s2
      | _         -> failwith "BWOrNoSMT"
      end

    (* Shift amount should be positive? *)
    | ShiftLeft -> begin match IT.basetype iterm with
      | BT.Bits _ -> SMT.bv_shl s1 s2
      | _         -> failwith "ShiftLeft"
      end

    (* Amount should be positive? *)
    | ShiftRight -> begin match IT.basetype iterm with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_ashr s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_lshr s1 s2
      | _                       -> failwith "ShiftRight"
      end

    | LT -> begin match IT.basetype e1 with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_slt s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_ult s1 s2
      | BT.Integer | BT.Real    -> SMT.num_lt s1 s2
      | _  -> failwith "LT"
      end

    | LE -> begin match IT.basetype e1 with
      | BT.Bits (BT.Signed,_)   -> SMT.bv_sleq s1 s2
      | BT.Bits (BT.Unsigned,_) -> SMT.bv_uleq s1 s2
      | BT.Integer | BT.Real    -> SMT.num_leq s1 s2
      | ty  -> Pp.print stdout (!^ "LE" ^^^ BT.pp ty); failwith "LE"
      end

    (* XXX: duplicates terms *)
    | Min -> translate_term s (ite_ (le_ (e1, e2) here, e1, e2) here)

    (* XXX: duplicates terms *)
    | Max -> translate_term s (ite_ (ge_ (e1, e2) here, e1, e2) here)

    | EQ -> SMT.eq s1 s2

    | LTPointer ->
      let intptr_cast = cast_ Memory.intptr_bt in
      translate_term s (lt_ (intptr_cast e1 here, intptr_cast e2 here) here)

    | LEPointer ->
      let intptr_cast = cast_ Memory.intptr_bt in
      translate_term s (le_ (intptr_cast e1 here, intptr_cast e2 here) here)

    | SetUnion -> SMT.set_union s.smt_solver.config.exts s1 s2
    | SetIntersection ->
      SMT.set_intersection s.smt_solver.config.exts s1 s2

    | SetDifference ->
      SMT.set_difference s.smt_solver.config.exts s1 s2

    | SetMember ->
      SMT.set_member s.smt_solver.config.exts s1 s2

    | Subset ->
      SMT.set_subset s.smt_solver.config.exts s1 s2
    end


  | ITE (b,e1,e2) ->
    SMT.ite (translate_term s b) (translate_term s e1) (translate_term s e2)

  | EachI ((i1, (x,bt), i2), t) ->
    let rec aux i =
           if i <= i2
           then
             let su = make_subst [(x, num_lit_ (Z.of_int i) bt here)] in
             let t1 = IT.subst su t in
             if i == i2
              then t1
              else IT.and2_ (t1, aux (i + 1)) here
           else failwith "EachI"
         in
         if i1 > i2 then translate_term s (IT.bool_ true here)
                    else translate_term s (aux i1)


  (* Tuples *)

  | Tuple es -> CN_Tuple.con (List.map (translate_term s) es)
  | NthTuple (n, e1) ->
    begin match IT.basetype e1 with
    | Tuple ts ->  CN_Tuple.get (List.length ts) n (translate_term s e1)
    | _ -> failwith "NthTuple: not a tuple"
    end


  (* Structs *)

    (* assumes that the fileds are in the correct order *)
  | Struct (tag, fields) ->
    let con         = CN_Names.struct_con_name tag in
    let field (_,e) = translate_term s e in
    SMT.app_ con (List.map field fields)

  | StructMember (e1,f) ->
    SMT.app_ (CN_Names.struct_field_name f) [translate_term s e1]

  | StructUpdate ((t, member), v) ->
    let tag     = BT.struct_bt (IT.bt t) in
    let layout  = SymMap.find (struct_bt (IT.bt t)) struct_decls in
    let members = Memory.member_types layout in
    let str =
      List.map (fun (member', sct) ->
          let value =
            if Id.equal member member' then v
            else member_ ~member_bt:(Memory.bt_of_sct sct) (tag, t, member') here
          in
          (member', value)
        ) members
    in translate_term s (struct_ (tag, str) here)

  | OffsetOf (tag,member) ->
    let decl = SymMap.find tag struct_decls in
    let v    = Option.get (Memory.member_offset decl member) in
    translate_term s (int_lit_ v (IT.basetype iterm) here)


  (* Records *)
  | Record members ->
    let field (_,e) = translate_term s e in
    CN_Tuple.con (List.map field members)

  | RecordMember (e1,f) ->
    begin match IT.basetype e1 with
    | Record members ->
        let check (x,_) = Id.equal f x in
        let arity       = List.length members in
        begin match List.find_index check members with
        | Some n -> CN_Tuple.get arity n (translate_term s e1)
        | None -> failwith "Missing record field."
        end
    | _ -> failwith "RecordMemmber"
    end

  | RecordUpdate ((t, member),v) ->
    let members = BT.record_bt (IT.bt t) in
    let str =
      List.map (fun (member', bt) ->
          let value =
            if Id.equal member member' then v
            else IT ((RecordMember (t, member')), bt, here)
          in
          (member', value)
        ) members
    in
    translate_term s (IT ((Record str), IT.bt t, here))

  (* Offset of a field in a struct *)
  | MemberShift (t, tag, member) ->
    let x = fresh_name s "cn_member_ptr" in
    ack_command s (SMT.define x CN_Pointer.t (translate_term s t));
    let x     = SMT.atom x in
    let alloc = CN_Pointer.get_alloc x in
    let addr  = CN_Pointer.get_addr x in
    let off   = translate_term s
                  (IT (OffsetOf (tag,member), Memory.intptr_bt, here)) in
    CN_Pointer.con alloc (SMT.bv_add addr off)

  (* Offset of an array element *)
  | ArrayShift { base; ct; index } ->
    let x = fresh_name s "cn_array_ptr" in
    ack_command s (SMT.define x CN_Pointer.t (translate_term s base));
    let x       = SMT.atom x in
    let alloc   = CN_Pointer.get_alloc x in
    let addr    = CN_Pointer.get_addr x in

    let el_size = int_lit_ (Memory.size_of_ctype ct) Memory.intptr_bt here in
    let ix      = cast_ Memory.intptr_bt index here in
    let off     = translate_term s (mul_ (el_size,ix) here) in
    CN_Pointer.con alloc (SMT.bv_add addr off)

  (* Change the offset of a pointer *)
  | CopyAllocId { addr; loc } ->
    let smt_addr = translate_term s addr in
    let smt_loc  = translate_term s loc in
    CN_Pointer.con (CN_Pointer.get_alloc smt_loc) smt_addr

  (* Lists *)
  | Nil bt       -> CN_List.nil (translate_base_type bt)
  | Cons (e1,e2) -> CN_List.cons (translate_term s e1) (translate_term s e2)
  | Head e1 ->
    maybe_name (translate_term s e1) (fun xs ->
    CN_List.head xs (translate_term s (default_ (IT.basetype iterm) here)))

  | Tail e1 ->
    maybe_name (translate_term s e1) (fun xs ->
    CN_List.tail xs (translate_term s (default_ (IT.basetype iterm) here)))

  | NthList (x,y,z) ->
    let arg x   = (translate_base_type (IT.basetype x), translate_term s x) in
    let (arg_ts,args) = List.split (List.map arg [x;y;z]) in
    let bt      = IT.basetype iterm in
    let res_t   = translate_base_type bt in
    let f = declare_bt_uninterpreted s CN_Constant.nth_list bt arg_ts res_t in
    SMT.app f args

  | ArrayToList (x,y,z) ->
    let arg x   = (translate_base_type (IT.basetype x), translate_term s x) in
    let (arg_ts,args) = List.split (List.map arg [x;y;z]) in
    let bt      = IT.basetype iterm in
    let res_t   = translate_base_type bt in
    let f = declare_bt_uninterpreted s
                                CN_Constant.array_to_list bt arg_ts res_t in
    SMT.app f args

  | SizeOf ct ->
    translate_term s
      (IT.int_lit_ (Memory.size_of_ctype ct) (IT.basetype iterm) here)

  | Representable (ct, t) ->
    translate_term s (representable struct_decls ct t here)

  | Good (ct,t) ->
    translate_term s (good_value struct_decls ct t here)

  | Aligned t ->
    let addr = pointerToIntegerCast_ t.t here in
    assert (BT.equal (IT.bt addr) (IT.bt t.align));
    translate_term s (divisible_ (addr, t.align) here)

  (* Maps *)
  | MapConst (bt,e1) ->
    let kt = translate_base_type bt in
    let vt = translate_base_type (IT.basetype e1) in
    SMT.arr_const kt vt (translate_term s e1)

  | MapSet (mp,k,v) -> SMT.arr_store (translate_term s mp)
                                     (translate_term s k)
                                     (translate_term s v)

  | MapGet (mp,k) -> SMT.arr_select (translate_term s mp) (translate_term s k)

  | MapDef _ -> failwith "MapDef"

  | Apply (name, args) ->
    let def = Option.get (get_logical_function_def s.globals name) in
    begin match def.definition with
    | Def body ->
      translate_term s (LogicalFunctions.open_fun def.args body args)
    | _ ->
      let do_arg arg = translate_base_type (IT.basetype arg) in
      let args_ts    = List.map do_arg args in
      let res_t      = translate_base_type def.return_bt in
      let fu         = declare_uninterpreted s name args_ts res_t in
      SMT.app fu (List.map (translate_term s) args)
    end

  | Let ((x,e1),e2) ->
    let se1  = translate_term s e1 in
    let name = CN_Names.var_name x in
    let se2  = translate_term s e2 in
    SMT.let_ [(name,se1)] se2


  (* Datatypes *)

  (* Assumes the fields are in the correct order *)
  | Constructor (c,fields) ->
    let con = CN_Names.datatype_con_name c in
    let field (_,e) = translate_term s e in
    SMT.app_ con (List.map field fields)

    (* CN supports nested patterns, while SMTLIB does not,
       so we compile patterns to a optional predicate, and defined variables.
    *)
  | Match (e1,alts) ->

    let rec match_pat v (Pat (pat,_,_)) =
      match pat with
      | PSym x  -> (None, [(CN_Names.var_name x,v)])
      | PWild   -> (None, [])
      | PConstructor (c,fs) ->
        let field (f,nested) =
          let new_v = SMT.app_ (CN_Names.datatype_field_name f) [v] in
          match_pat new_v nested in

        let (conds,defs) = List.split (List.map field fs) in
        let nested_cond = SMT.bool_ands (List.filter_map (fun x -> x) conds) in
        let cname = CN_Names.datatype_con_name c in
        let cond  = SMT.bool_and (SMT.is_con cname v) nested_cond in
        (Some cond, List.concat defs)
    in
    let rec do_alts v alts =
      match alts with
      | [] -> translate_term s (default_ (IT.basetype iterm) here)
      | (pat,rhs) :: more ->
        let (mb_cond,binds) = match_pat v pat in
        let k               = SMT.let_ binds (translate_term s rhs) in
        match mb_cond with
        | Some cond -> SMT.ite cond k (do_alts v more)
        | None      -> k
    in
    let x = fresh_name s "match" in
    SMT.let_ [(x, translate_term s e1)] (do_alts (SMT.atom x) alts)




  (* Casts *)
  | WrapI (ity, arg) ->
    bv_cast (Memory.bt_of_sct (Sctypes.Integer ity))
            (IT.bt arg)
            (translate_term s arg)

  | Cast (cbt, t) ->
    let smt_term = translate_term s t in
    begin match IT.bt t, cbt with

    | Bits _, Loc ->
      CN_Pointer.con (CN_AllocId.to_sexp Z.zero)
                     (bv_cast Memory.intptr_bt (IT.bt t) smt_term)

    | Loc, Bits _ ->
      bv_cast cbt Memory.intptr_bt (CN_Pointer.get_addr smt_term)

    | Loc, Alloc_id  -> CN_Pointer.get_alloc smt_term

    | Real, Integer  -> SMT.real_to_int smt_term
    | Integer, Real  -> SMT.int_to_real smt_term
    | Bits _, Bits _ -> bv_cast cbt (IT.bt t) smt_term

    | _ ->
       assert false
    end



let add_assumption solver global lc =
  let s1 = { solver with globals = global } in
  match lc with
    | T it -> ack_command solver (SMT.assume (translate_term s1 it))
    | Forall _ -> ()


(** Goals are translated to this type *)
type reduction = {
  expr  : SMT.sexp;             (* translation of `it` *)
  qs    : (Sym.t * BT.t) list;  (* quantifier instantiation *)
  extra : SMT.sexp list;        (* additional assumptions *)
}

(* XXX: `pointer_facts` are unused? *)
let translate_goal solver assumptions pointer_facts lc =
  let here =  Locations.other __FUNCTION__ in

  let instantiated =
        match lc with
        | T it -> { expr = translate_term solver it; qs = []; extra = [] }
        | Forall ((s, bt), it) ->
          let v_s, v = IT.fresh_same bt s here in
          let it = IT.subst (make_subst [(s, v)]) it in
          { expr = translate_term solver it; qs = [(v_s, bt)]; extra = [] }
  in
  let add_asmps acc0 (s,bt) =
        let v = sym_ (s, bt, here) in
        let check_asmp lc acc =
            match lc with
            | Forall ((s', bt'), it') when BT.equal bt bt' ->
              let new_asmp = IT.subst (make_subst [(s', v)]) it' in
              translate_term solver new_asmp :: acc
            | _ -> acc
        in LCSet.fold check_asmp assumptions acc0
  in
  { instantiated with extra = List.fold_left add_asmps [] instantiated.qs }






(* as similarly suggested by Robbert *)
let shortcut simp_ctxt lc =
  let lc = Simplify.LogicalConstraints.simp simp_ctxt lc in
  match lc with
  | LC.T (IT (Const (Bool true), _, _)) -> `True
  | _ -> `No_shortcut lc





(** {1 Solver Initialization} *)

let declare_datatype_group s names =
  let mk_con_field (l,t) =
        (CN_Names.datatype_field_name l, translate_base_type t) in
  let mk_con c =
    let ci = SymMap.find c s.globals.datatype_constrs in
    (CN_Names.datatype_con_name c, List.map mk_con_field ci.c_params) in
  let cons info = List.map mk_con info.dt_constrs in
  let to_smt (x: Sym.t) =
        let info = SymMap.find x s.globals.datatypes in
        (CN_Names.datatype_name x, [], cons info)
  in
  ack_command s (SMT.declare_datatypes (List.map to_smt names))



let declare_struct s name decl =
  let mk_field (l,t) =
        (CN_Names.struct_field_name l, translate_base_type (Memory.bt_of_sct t))
  in
  let mk_piece (x: Memory.struct_piece) =
        Option.map mk_field x.member_or_padding
  in
  ack_command s
    (SMT.declare_datatype
       (CN_Names.struct_name name) []
         [ (CN_Names.struct_con_name name, List.filter_map mk_piece decl) ]
    )


let declare_solver_basics s =
  for arity = 0 to 8 do
    CN_Tuple.declare s arity
  done;
  CN_List.declare s;
  CN_Pointer.declare s;

  (* structs should go before datatypes *)
  SymMap.iter (declare_struct s) s.globals.struct_decls;
  List.iter (declare_datatype_group s) (Option.get s.globals.datatype_order)


let logger base lab =
  { SMT.send    = (fun s -> base.SMT.send (lab ^ s))
  ; SMT.receive = (fun s -> base.SMT.receive (lab ^ s))
  }


let make globals =
  let cfg = { SMT.cvc5 with log = logger SMT.quiet_log "z3: " } in
  let s = { smt_solver  = SMT.new_solver cfg
          ; cur_frame   = ref (empty_solver_frame ())
          ; prev_frames = ref []
          ; name_seed   = ref 0
          ; globals     = globals
          }
  in declare_solver_basics s; s


let model_evaluator solver mo =
  match None with
  | None -> fun _ -> None
  | _ ->
  match SMT.to_list mo with
  | None -> failwith "model is an atom"
  | Some defs ->
    let scfg = solver.smt_solver.config in
    let cfg = { scfg with log = logger scfg.log ":model: " } in
    let s = SMT.new_solver cfg in
    let evaluator = { smt_solver = s
                    ; cur_frame = ref (empty_solver_frame ())
                    ; prev_frames = ref (!(solver.cur_frame) ::
                                         !(solver.prev_frames))
                      (* we keep the prev_frames because things that were
                         declared, would now be defined by the model.
                         Do we need to copy?
                       *)
                    ; name_seed = solver.name_seed
                    ; globals = solver.globals
                    } in
    declare_solver_basics evaluator;
    List.iter (SMT.ack_command s) defs;

    fun e ->
      push evaluator;
      let inp = translate_term evaluator e in
      match SMT.check s with
      | SMT.Sat ->
          let res = SMT.get_expr s inp in
          pop evaluator 1;
          Some (get_ivalue (basetype e) res)
      | _ ->
          pop evaluator 1;
          None

(* ---------------------------------------------------------------------------*)
(* GLOBAL STATE: Models *)
(* ---------------------------------------------------------------------------*)

type model = IT.t -> IT.t option
type model_with_q = model * (Sym.t * LogicalSorts.t) list

type model_state =
  | Model of model_with_q
  | No_model

let model_state =
  ref No_model

let model () =
  match !model_state with
  | No_model ->
     assert false
  | Model mo -> mo

(* ---------------------------------------------------------------------------*)



let provable ~loc ~solver ~global ~assumptions ~simp_ctxt ~pointer_facts lc =
  let s1 = { solver with globals = global } in
  let rtrue () = model_state := No_model; `True in
  match shortcut simp_ctxt lc with
  | `True -> rtrue ()

  | `No_shortcut lc ->
     let {expr; qs; extra} = translate_goal s1 assumptions pointer_facts lc
     in
     let model_from sol =
           let defs = SMT.get_model sol in
           let mo   = model_evaluator s1 defs in
           model_state := Model (mo, qs)
     in

     let nlc = SMT.bool_not expr in

     let inc = s1.smt_solver in
     SMT.ack_command inc (SMT.push 1);
     SMT.ack_command inc (SMT.assume (SMT.bool_ands (nlc :: extra)));
     let res = SMT.check inc in
     match res with
     | SMT.Unsat   -> SMT.ack_command inc (SMT.pop 1); rtrue ()
     | SMT.Sat -> model_from inc; SMT.ack_command inc (SMT.pop 1); `False
     | SMT.Unknown ->
      SMT.ack_command inc (SMT.pop 1);
      failwith "Unknown"
(*
        let () = Z3.Solver.reset solver.non_incremental in
        let () =
          List.iter (fun lc ->
            Z3.Solver.add solver.non_incremental [lc]
            ) (nlc :: extra @ existing_scs)
        in
        let (elapsed2, res2) =
          time_f_elapsed (time_f_logs loc 5 "Z3(non-inc)"
              (Z3.Solver.check solver.non_incremental))
            []
        in
        maybe_save_slow_problem (res_short_string res2)
            loc lc expr smt2_doc elapsed2 solver.non_incremental;
        match res2 with
        | Z3.Solver.UNSATISFIABLE ->
           rtrue ()
        | Z3.Solver.SATISFIABLE ->
           rfalse qs solver.non_incremental
        | Z3.Solver.UNKNOWN ->
          let reason = Z3.Solver.get_reason_unknown solver.non_incremental in
          failwith ("SMT solver returned 'unknown'; reason: " ^ reason)
*)





let eval globs mo t = mo t


(* Dummy implementations *)
let random_seed = ref 0
let log_to_temp = ref false
let set_slow_smt_settings _ _ = ()
let debug_solver_to_string _ = ()
let debug_solver_query _ _ _ _ _ = ()




