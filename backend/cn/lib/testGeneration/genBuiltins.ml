module BT = BaseTypes
module IT = IndexTerms
module GT = GenTerms
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils

let gen_syms_bits (name : string) : (BT.t * Sym.t) list =
  let aux (bt : BT.t) : BT.t * Sym.t =
    match BT.is_bits_bt bt with
    | Some (sgn, bits) ->
      let bt = BT.Bits (sgn, bits) in
      ( bt,
        Sym.fresh_named
          (String.concat
             "_"
             [ "cn_gen";
               name;
               Option.get (Utils.get_typedef_string (CtA.bt_to_ail_ctype bt))
             ]) )
    | None -> failwith __LOC__
  in
  [ aux (BT.Bits (Unsigned, 8));
    aux (BT.Bits (Signed, 8));
    aux (BT.Bits (Unsigned, 16));
    aux (BT.Bits (Signed, 16));
    aux (BT.Bits (Unsigned, 32));
    aux (BT.Bits (Signed, 32));
    aux (BT.Bits (Unsigned, 64));
    aux (BT.Bits (Signed, 64))
  ]


let min_sym = Sym.fresh_named "min"

let gt_gen_sym_db = gen_syms_bits "gt"

let gt_gen (it_min : IT.t) (bt : BT.t) loc : GT.t =
  let fsym = List.assoc BT.equal bt gt_gen_sym_db in
  GT.call_ (fsym, [ (min_sym, it_min) ]) bt loc


let max_sym = Sym.fresh_named "max"

let lt_gen_sym_db = gen_syms_bits "lt"

let lt_gen (it_max : IT.t) (bt : BT.t) loc : GT.t =
  let fsym = List.assoc BT.equal bt lt_gen_sym_db in
  GT.call_ (fsym, [ (max_sym, it_max) ]) bt loc


let range_gen_sym_db = gen_syms_bits "range"

let range_gen (it_min : IT.t) (it_max : IT.t) (bt : BT.t) loc : GT.t =
  let fsym = List.assoc BT.equal bt range_gen_sym_db in
  GT.call_ (fsym, [ (min_sym, it_min); (max_sym, it_max) ]) bt loc


let mult_sym = Sym.fresh_named "mult"

let mult_gen_sym_db = gen_syms_bits "mult"

let mult_gen (it_mult : IT.t) (bt : BT.t) loc : GT.t =
  let fsym = List.assoc BT.equal bt mult_gen_sym_db in
  GT.call_ (fsym, [ (mult_sym, it_mult) ]) bt loc


let mult_range_gen_sym_db = gen_syms_bits "mult_range"

let mult_range_gen (it_mult : IT.t) (it_min : IT.t) (it_max : IT.t) (bt : BT.t) loc : GT.t
  =
  let fsym = List.assoc BT.equal bt mult_range_gen_sym_db in
  GT.call_ (fsym, [ (mult_sym, it_mult); (min_sym, it_min); (max_sym, it_max) ]) bt loc
