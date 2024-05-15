module SMT = Simple_smt
module IT = IndexTerms
open IndexTerms
module BT = BaseTypes
open BaseTypes
module SymMap = Map.Make(Sym)
module BT_Table = Hashtbl.Make(BT)
open Global

(* XXX: probably should add some prefixes to try to avoid name collisions. *)
(** Functions that pick names for things. *)
module CN_Names = struct
  let var_name x            = Sym.pp_string x
  let wild_var_name n       = "_" ^ string_of_int n
  let named_expr_name       = "_cn_named"
  let uninterpreted_name x  = Sym.pp_string x

  let struct_name x         = Sym.pp_string x
  let struct_con_name x     = Sym.pp_string x
  let struct_field_name x   = Id.pp_string x

  let datatype_name x       = Sym.pp_string x
  let datatype_con_name x   = Sym.pp_string x
  let datatype_field_name x = Id.pp_string x
end


type solver_frame =
  { mutable commands: SMT.sexp list
    (** Ack-style SMT commands, most recent first. *)

  ; declared_defaults: SMT.sexp BT_Table.t
    (** The names of the "default" constant for a type. *)

  ; mutable uninterpreted_functions: SMT.sexp SymMap.t
    (** Uninterpreted functions that we've declared. *)
  }

let empty_solver_frame =
  { commands                = []
  ; declared_defaults       = BT_Table.create 50
  ; uninterpreted_functions = SymMap.empty
  }


type solver =
  { smt_solver: SMT.solver
    (** The SMT solver connection. *)

  ; mutable cur_frame:   solver_frame
  ; mutable prev_frames: solver_frame list
    (** Push/pop model. Current frame, and previous frames. *)

  ; mutable name_seed: int
    (** Used to generate names. *)
    (* XXX: This could, perhaps, go in the frame.  Then when we pop frames,
       we'd go back to the old numbers, which should be OK, I think? *)

  ; globals: Global.t
  }

(** Lookup something in one of the existing frames *)
let search_frames s f = List.find_map f (s.cur_frame :: s.prev_frames)


(** Start a new scope. *)
let push s =
  SMT.ack_command s.smt_solver (SMT.push 1);
  s.prev_frames <- s.cur_frame :: s.prev_frames;
  s.cur_frame   <- empty_solver_frame

(** Return to the previous scope.  Assumes that there is a previous scope. *)
let pop s n =
  SMT.ack_command s.smt_solver (SMT.pop n);
  let rec drop count xs =
            match xs with
            | new_cur :: new_rest ->
              if count = 1
                then begin s.cur_frame <- new_cur; s.prev_frames <- new_rest end
                else drop (count - 1) new_rest
            | _ -> assert false
  in
  drop n s.prev_frames

(** Do an ack_style command. These are logged. *)
let ack_command s cmd =
  SMT.ack_command s.smt_solver cmd;
  s.cur_frame.commands <- cmd :: s.cur_frame.commands

(** Generate a fersh name *)
let fresh_name s x =
  let n = s.name_seed in
  s.name_seed <- s.name_seed + 1;
  x ^ "_" ^ string_of_int n

(** Declare an uninterpreted function *)
let declare_uninterpreted s name args_ts res_t =
  let check f = SymMap.find_opt name f.uninterpreted_functions in
  match search_frames s check with
  | Some e -> e
  | None ->
    let sname = CN_Names.uninterpreted_name name in
    ack_command s (SMT.declare_fun sname args_ts res_t);
    let e = SMT.atom sname in
    s.cur_frame.uninterpreted_functions <-
      SymMap.add name e s.cur_frame.uninterpreted_functions;
    e






exception Unsupported

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
              | _ -> raise Unsupported

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
end

(* XXX: we should define a datatype to match the CN C types? *)
module CN_CType = struct
  let name      = "cn_ctype"
  let t         = SMT.atom name
  let declare s = ack_command s (SMT.declare_sort name 0)
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
  | CType           -> CN_CType.t
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


let to_iterm bt t = IT (t, bt, Cerb_location.unknown) (* XXX? *)

(** Translate an SMT value to a CN term *)
let rec
  get_ivalue bt sexp = to_iterm bt (get_value bt sexp)
and
  get_value bt (sexp: SMT.sexp) =
  let bad () = raise (SMT.UnexpectedSolverResponse sexp) in
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
                   | _ -> raise Unsupported
        in Const (if Z.equal base Z.zero && Z.equal addr Z.zero
                    then Null
                    else Pointer { alloc_id = base; addr = addr }
                 )
      | _ -> bad ()
      end

  | Alloc_id        -> Const (Alloc_id (CN_AllocId.from_sexp sexp))

  | CType           -> raise Unsupported    (* ? *)

  | List elT ->
    begin match SMT.to_con sexp with
    | (con,[])    when String.equal con CN_List.nil_name -> Nil elT
    | (con,[h;t]) when String.equal con CN_List.cons_name ->
        Cons (get_ivalue elT h, get_ivalue bt t)
    | _ -> bad ()
    end

  | Set bt          -> raise Unsupported
  | Map (k, v)      -> raise Unsupported

  | Tuple bts ->
    let (_con,vals) = SMT.to_con sexp in
    Tuple (List.map2 get_ivalue bts vals)

  | Struct tag      -> raise Unsupported (** XXX *)
  | Datatype tag    -> raise Unsupported (** XXX *)

  | Record members  ->
    let (_con,vals) = SMT.to_con sexp in
    let mk_field (l,bt) e = (l, get_ivalue bt e) in
    Record (List.map2 mk_field members vals)


(** {1 Term to SMT} *)

(** Declare a variable of the given type.  Should be called by typing,
    when variables are added to the current scope. *)
let declare_var s x bt =
  let ty   = translate_base_type bt in
  let name = CN_Names.var_name x in
  SMT.ack_command s.smt_solver (SMT.declare name ty)


(** Translate a constant to SMT *)
let rec translate_const s co =
  match co with
  | Z z             -> SMT.int_zk z
  | Bits ((_,w), z) -> SMT.bv_k w z
  | Q q             -> SMT.real_k q

  | Pointer p ->
    begin match Memory.intptr_bt with
    | Bits (_,w) ->
        SMT.app_ CN_Pointer.name [ SMT.int_zk p.alloc_id; SMT.bv_k w p.addr ]
    | _ -> raise Unsupported
    end

  | Alloc_id z -> CN_AllocId.to_sexp z
  | Bool b     -> SMT.bool_k b
  | Unit       -> SMT.atom (CN_Tuple.name 0)

  | Null ->
    translate_const s (Pointer { alloc_id = Z.of_int 0; addr = Z.of_int 0 })

  | CType_const _ -> raise Unsupported (* XXX *)

  | Default t ->
    let check f = BT_Table.find_opt f.declared_defaults t in
    match search_frames s check with
    | Some e -> e
    | None ->
      let name  = fresh_name s "cn_default" in
      let ty    = translate_base_type t in
      ack_command s (SMT.declare name ty);
      let e     = SMT.atom name in
      BT_Table.add s.cur_frame.declared_defaults t e;
      e

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


(** [bv rw w e] counts the leading zeroes in [e], which should
be a bit-vector of width `[w]`.  The result is a bit-vector of with `[rw]`.
Note that this duplicates `e`, so it should be a simple expression.
*)
let bv_clz result_sz =
  let result k   = SMT.bv_k result_sz k in
  let eq_0 sz tm = SMT.eq tm (SMT.bv_k sz Z.zero) in

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


(** Translat a CN term to SMT *)
let rec translate_term s iterm =
  let xxx ()        = raise Unsupported in
  let bad ()        = assert false in
  let here          = IT.loc iterm in
  let struct_decls  = s.globals.struct_decls in
  let maybe_name e k =
        if SMT.is_atom e
          then k e
          else let x = fresh_name s CN_Names.named_expr_name in
               SMT.let_ [(x,e)] (k (SMT.atom x)) in

  match IT.term iterm with
  | Const c -> translate_const s c

  | Sym x -> SMT.atom (CN_Names.var_name x)

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

    | BWCLZNoSMT ->
      begin match IT.basetype iterm with
      | BT.Bits (_,w) -> maybe_name (translate_term s e1) (bv_clz w w)
      | _             -> failwith "solver: BWCLZNoSMT: not a bitwise type"
      end

    | BWCTZNoSMT -> xxx ()
    end

  | Binop (op,e1,e2) ->
    begin match op with
    | And -> xxx ()
    | Or -> xxx ()
    | Impl -> xxx ()
    | Add -> xxx ()
    | Sub -> xxx ()
    | Mul -> xxx ()
    | MulNoSMT -> xxx ()
    | Div -> xxx ()
    | DivNoSMT -> xxx ()
    | Exp -> xxx ()
    | ExpNoSMT -> xxx ()
    | Rem -> xxx ()
    | RemNoSMT -> xxx ()
    | Mod -> xxx ()
    | ModNoSMT -> xxx ()
    | XORNoSMT -> xxx ()
    | BWAndNoSMT -> xxx ()
    | BWOrNoSMT -> xxx ()
    | ShiftLeft -> xxx ()
    | ShiftRight -> xxx ()
    | LT -> xxx ()
    | LE -> xxx ()
    | Min -> xxx ()
    | Max -> xxx ()
    | EQ -> xxx ()
    | LTPointer -> xxx ()
    | LEPointer -> xxx ()
    | SetUnion -> xxx ()
    | SetIntersection -> xxx ()
    | SetDifference -> xxx ()
    | SetMember -> xxx ()
    | Subset -> xxx ()
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
           else bad ()
         in
         if i1 > i2 then translate_term s (IT.bool_ true here)
                    else translate_term s (aux i1)


  (* Tuples *)

  | Tuple es -> CN_Tuple.con (List.map (translate_term s) es)
  | NthTuple (n, e1) ->
    begin match IT.basetype e1 with
    | Tuple ts ->  CN_Tuple.get (List.length ts) n (translate_term s e1)
    | _ -> bad ()
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
        | None -> raise Unsupported
        end
    | _ -> bad ()
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
  | Nil bt -> xxx ()
  | Cons (e1,e2) -> xxx ()
  | Head e1 -> xxx ()
  | Tail e1 -> xxx ()
  | NthList (x,y,z) -> xxx ()
  | ArrayToList (x,y,z) -> xxx ()


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

  | MapDef ((x,y),z) -> xxx ()

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
        let vars  = List.mapi (fun i _x -> CN_Names.wild_var_name i) fs in
        let cond  = SMT.match_datatype v
                      [ (SMT.PCon (cname,vars), nested_cond)
                      ; (SMT.PVar (CN_Names.wild_var_name 0), SMT.bool_k false)
                      ] in
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
      CN_Pointer.con (SMT.int_k 0) (bv_cast Memory.intptr_bt (IT.bt t) smt_term)

    | Loc, Bits _ ->
      bv_cast cbt Memory.intptr_bt (CN_Pointer.get_addr smt_term)

    | Loc, Alloc_id  -> CN_Pointer.get_alloc smt_term

    | Real, Integer  -> SMT.real_to_int smt_term
    | Integer, Real  -> SMT.int_to_real smt_term
    | Bits _, Bits _ -> bv_cast cbt (IT.bt t) smt_term

    | _ ->
       assert false
    end


(** {1 Solver Initialization} *)

let declare_datatype s name info =
  let mk_con_field (l,t) =
        (CN_Names.datatype_field_name l, translate_base_type t) in
  let mk_con c =
    let ci = SymMap.find c s.globals.datatype_constrs in
    (CN_Names.datatype_con_name c, List.map mk_con_field ci.c_params) in
  let cons = List.map mk_con info.dt_constrs in
  ack_command s (SMT.declare_datatype (CN_Names.datatype_name name) [] cons)

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
  for arity = 0 to 32 do
    CN_Tuple.declare s arity
  done;
  CN_CType.declare s;
  CN_List.declare s;
  CN_Pointer.declare s;

  (* structs should go before datatypes *)
  SymMap.iter (declare_struct s) s.globals.struct_decls;
  SymMap.iter (declare_datatype s) s.globals.datatypes


let make globals =
  let s = { smt_solver  = SMT.new_solver SMT.z3
          ; cur_frame   = empty_solver_frame
          ; prev_frames = []
          ; name_seed   = 0
          ; globals     = globals
          }
  in declare_solver_basics s; s





