module BT = Cn.BaseTypes
module IT = Cn.IndexTerms
open Cn
open Eval
open OUnit2

let test_tuple =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let bt = BT.Datatype (Sym.fresh_named "bt") in
  let it_res = IT.num_lit_ (Z.of_int 21) BT.Integer here in
  let it_tuple = IT.tuple_ [ IT.sym_ (Sym.fresh (), bt, here); it_res ] here in
  let it_nth = IT.nthTuple_ ~item_bt:BT.Integer (1, it_tuple) here in
  let printer r = match r with Ok it -> Pp.plain (IT.pp it) | Error err -> err in
  assert_equal
    ~printer
    ~cmp:(Result.equal ~ok:IT.equal ~error:(fun _ _ -> false))
    ~msg:"Lazy evaluation did not step"
    (Ok it_res)
    (eval ~mode:Lazy it_nth);
  assert_bool
    "Strict evaluation did not get stuck on free variables"
    (eval ~mode:Strict it_nth |> Result.is_error)


let test_struct =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let bt = BT.Datatype (Sym.fresh_named "bt") in
  let mem_id = Id.id "member" in
  let it_res = IT.num_lit_ (Z.of_int 21) BT.Integer here in
  let it_struct =
    IT.struct_
      ( Sym.fresh (),
        [ (Id.id "filler", IT.sym_ (Sym.fresh (), bt, here)); (mem_id, it_res) ] )
      here
  in
  let it_member = IT.member_ ~member_bt:BT.Integer (it_struct, mem_id) here in
  let printer r = match r with Ok it -> Pp.plain (IT.pp it) | Error err -> err in
  assert_equal
    ~printer
    ~cmp:(Result.equal ~ok:IT.equal ~error:(fun _ _ -> false))
    ~msg:"Lazy evaluation did not step"
    (Ok it_res)
    (eval ~mode:Lazy it_member);
  assert_bool
    "Strict evaluation did not get stuck on free variables"
    (eval ~mode:Strict it_member |> Result.is_error)


let test_record =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let bt = BT.Datatype (Sym.fresh_named "bt") in
  let mem_id = Id.id "member" in
  let it_res = IT.num_lit_ (Z.of_int 21) BT.Integer here in
  let it_record =
    IT.record_
      [ (Id.id "filler", IT.sym_ (Sym.fresh (), bt, here)); (mem_id, it_res) ]
      here
  in
  let it_member = IT.recordMember_ ~member_bt:BT.Integer (it_record, mem_id) here in
  let printer r = match r with Ok it -> Pp.plain (IT.pp it) | Error err -> err in
  assert_equal
    ~printer
    ~cmp:(Result.equal ~ok:IT.equal ~error:(fun _ _ -> false))
    ~msg:"Lazy evaluation did not step"
    (Ok it_res)
    (eval ~mode:Lazy it_member);
  assert_bool
    "Strict evaluation did not get stuck on free variables"
    (eval ~mode:Strict it_member |> Result.is_error)


let test_constructor =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let constr_sym = Sym.fresh_named "constr" in
  let member = Id.id "abc" in
  let bt = BT.Datatype (Sym.fresh_named "bt") in
  let it_constr =
    IT.IT
      (Constructor (constr_sym, [ (member, IT.sym_ (Sym.fresh (), bt, here)) ]), bt, here)
  in
  let it_match =
    IT.IT
      ( Match
          ( it_constr,
            [ ( Pat
                  ( PConstructor (constr_sym, [ (member, Pat (PWild, bt, here)) ]),
                    bt,
                    here ),
                IT.bool_ true here )
            ] ),
        BT.Bool,
        here )
  in
  let printer r = match r with Ok it -> Pp.plain (IT.pp it) | Error err -> err in
  assert_equal
    ~printer
    ~cmp:(Result.equal ~ok:IT.equal ~error:(fun _ _ -> false))
    ~msg:"Lazy evaluation did not step"
    (Ok (IT.bool_ true here))
    (eval ~mode:Lazy it_match);
  assert_bool
    "Strict evaluation did not get stuck on free variables"
    (eval ~mode:Strict it_match |> Result.is_error)


let test_apply_rename =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let x_sym = Sym.fresh_named "x" in
  let y_sym = Sym.fresh_named "y" in
  let y_sym' = Sym.fresh_named "y" in
  let it mode =
    IT.let_
      ( (x_sym, IT.sym_ (y_sym, BT.Integer, here)),
        IT.let_
          ( (y_sym', IT.num_lit_ (Z.of_int 10) BT.Integer here),
            IT.add_
              (IT.sym_ (x_sym, BT.Integer, here), IT.sym_ (y_sym', BT.Integer, here))
              here )
          here )
      here
    |> partial_eval ~mode
    |> IT.subst (IT.make_subst [ (y_sym, IT.num_lit_ (Z.of_int 20) BT.Integer here) ])
    |> eval ~mode
  in
  let printer r = match r with Ok it -> Pp.plain (IT.pp it) | Error err -> err in
  assert_equal
    ~printer
    ~msg:"Strict evalution failed"
    (Ok (IT.num_lit_ (Z.of_int 30) BT.Integer here))
    (it Strict);
  assert_equal
    ~printer
    ~msg:"Lazy evalution failed"
    (Ok (IT.num_lit_ (Z.of_int 30) BT.Integer here))
    (it Lazy)


let test_partial_eval_arith =
  TestUtils.test_name __FUNCTION__
  >:: fun _ ->
  let here = Locations.other __FUNCTION__ in
  let num_lit n = IT.num_lit_ n BT.Integer here in
  let x = Z.random_bits 1000 in
  let y = Z.random_bits 1000 in
  let z = Z.random_bits 1000 in
  let w = Z.random_bits 1000 in
  let it_sym = IT.sym_ (Sym.fresh (), BT.Integer, here) in
  let it_math =
    let open IT in
    (((num_lit x %+ num_lit y) here %- num_lit z) here %* num_lit w) here
  in
  let it = IT.mul_no_smt_ (it_sym, it_math) here in
  assert_equal
    ~cmp:IT.equal
    ~printer:(fun it -> Pp.plain @@ IT.pp it)
    (IT.mul_no_smt_
       ( it_sym,
         num_lit
           (let open Z in
            (x + y - z) * w) )
       here)
    (partial_eval it)


let tests =
  TestUtils.test_suite_name __FILE__
  >::: [ test_tuple;
         test_struct;
         test_record;
         test_constructor;
         test_apply_rename;
         test_partial_eval_arith
       ]
