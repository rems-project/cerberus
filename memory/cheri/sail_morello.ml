open Sail_lib;;
module Big_int = Nat_big_num;;

let rec zeq_unit ((_, _) : (unit * unit)) : bool = sail_call (fun r -> true)

and zneq_int ((zx, zy) : (Big_int.num * Big_int.num)) : bool = sail_call (fun r ->
  not (eq_int (zx, zy)))

and zneq_bool ((zx, zy) : (bool * bool)) : bool = sail_call (fun r ->
  not (eq_bool (zx, zy)))

and z__id (zx : (Big_int.num)) : Big_int.num = sail_call (fun r -> zx)

type  zbits = (bit) list;;

let string_of_zbits (gs19 : zbits) = string_of_bits gs19;;

let rec zneq_bits ((zx, zy) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  not (eq_list (zx, zy)))

and zsail_mask ((zlen, zv) : (Big_int.num * (bit) list)) : (bit) list = sail_call (fun r ->
  if (lteq (zlen, (length zv))) then (vector_truncate (zv, zlen)) else (zero_extend (zv, zlen)))

and zsail_ones (zn : (Big_int.num)) : (bit) list = sail_call (fun r ->
  not_vec (zeros zn))

and zslice_mask ((zn, zi, zl) : (Big_int.num * Big_int.num * Big_int.num)) : (bit) list = sail_call (fun r ->
  if (gteq (zl, zn)) then (shiftl ((zsail_ones zn), zi)) else (let zone = (zsail_mask (zn, ([B1]))) in
  shiftl ((sub_vec ((shiftl (zone, zl)), zone)), zi)))

and z_shl_int_general ((zm, zn) : (Big_int.num * Big_int.num)) : Big_int.num = sail_call (fun r ->
  if (gteq (zn, Big_int.zero)) then (shl_int (zm, zn)) else (shr_int (zm, (negate zn))))

and z_shr_int_general ((zm, zn) : (Big_int.num * Big_int.num)) : Big_int.num = sail_call (fun r ->
  if (gteq (zn, Big_int.zero)) then (shr_int (zm, zn)) else (shl_int (zm, (negate zn))))

and zfdiv_int ((zn, zm) : (Big_int.num * Big_int.num)) : Big_int.num = sail_call (fun r ->
  if ((lt (zn, Big_int.zero)) && (gt (zm, Big_int.zero))) then (sub_int ((tdiv_int ((add_int (zn, (Big_int.of_int (1)))), zm)), (Big_int.of_int (1)))) else (if ((gt (zn, Big_int.zero)) && (lt (zm, Big_int.zero))) then (sub_int ((tdiv_int ((sub_int (zn, (Big_int.of_int (1)))), zm)), (Big_int.of_int (1)))) else (tdiv_int (zn, zm))))

and zfmod_int ((zn, zm) : (Big_int.num * Big_int.num)) : Big_int.num = sail_call (fun r ->
  sub_int (zn, (mult (zm, (zfdiv_int (zn, zm))))))

type 'za zoption = | ZSome of 'za | ZNone of unit;;

let string_of_zoption _ = "VARIANT";;

let rec zundefined_option : 'za. ('za) -> ('za) zoption = fun ztyp_a -> sail_call (fun r ->
  let zu_0 = (undefined_unit ()) in
  let zu_1 = ztyp_a in
  internal_pick [ZSome zu_1; ZNone zu_0])

and zis_none : 'za. (('za) zoption) -> bool = fun zopt -> sail_call (fun r ->
  begin match zopt with | ZSome (_) -> false | ZNone (()) -> true end)

and zis_some : 'za. (('za) zoption) -> bool = fun zopt -> sail_call (fun r ->
  begin match zopt with | ZSome (_) -> true | ZNone (()) -> false end)

and zeq_bits_int ((zx, zy) : ((bit) list * Big_int.num)) : bool = sail_call (fun r ->
  eq_int ((uint zx), zy))

and zOnes (zn : (Big_int.num)) : (bit) list = sail_call (fun r -> zsail_ones zn)

and zZeros (zn : (Big_int.num)) : (bit) list = sail_call (fun r -> zeros zn)

and zBit (zb : ((bit) list)) : bit = sail_call (fun r ->
  access (zb, Big_int.zero))

and zinteger_subrange ((zi, zhi, zlo) : (Big_int.num * Big_int.num * Big_int.num)) : (bit) list = sail_call (fun r ->
  get_slice_int ((add_int ((sub_int (zhi, zlo)), (Big_int.of_int (1)))), zi, zlo))

and zSlice_int ((zi, zl, zn) : (Big_int.num * Big_int.num * Big_int.num)) : (bit) list = sail_call (fun r ->
  get_slice_int (zn, zi, zl))

let zCAP_FLAGS_LO_BIT = (Big_int.of_int (56));;

let zCAP_VALUE_HI_BIT = (Big_int.of_int (63));;

let zCAP_VALUE_LO_BIT = Big_int.zero;;

let zCAP_VALUE_NUM_BITS = (add_int ((sub_int (zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT)), (Big_int.of_int (1))));;

let zCAP_BASE_HI_BIT = (Big_int.of_int (79));;

let zCAP_BASE_LO_BIT = (Big_int.of_int (64));;

let zCAP_MW = (add_int ((sub_int (zCAP_BASE_HI_BIT, zCAP_BASE_LO_BIT)), (Big_int.of_int (1))));;

let rec zCapBoundsUsesValue (zexp : (Big_int.num)) : bool = sail_call (fun r ->
  r.return (lt ((add_int (zexp, zCAP_MW)), zCAP_VALUE_NUM_BITS)))

let zCAP_BASE_EXP_HI_BIT = (Big_int.of_int (66));;

let zCAP_LIMIT_EXP_HI_BIT = (Big_int.of_int (82));;

let zCAP_LIMIT_LO_BIT = (Big_int.of_int (80));;

let zCAP_IE_BIT = (Big_int.of_int (94));;

let rec zCapIsInternalExponent (zc : ((bit) list)) : bool = sail_call (fun r ->
  r.return (eq_list ([access (zc, zCAP_IE_BIT)], [B0])))

and zCapGetExponent (zc : ((bit) list)) : Big_int.num = sail_call (fun r ->
  if (zCapIsInternalExponent zc) then (let znexp = (append ((subrange (zc, zCAP_LIMIT_EXP_HI_BIT, zCAP_LIMIT_LO_BIT)), (subrange (zc, zCAP_BASE_EXP_HI_BIT, zCAP_BASE_LO_BIT)))) in
  r.return (uint (not_vec znexp))) else (r.return Big_int.zero))

and zCapGetValue (zc : ((bit) list)) : (bit) list = sail_call (fun r ->
  r.return (subrange (zc, zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT)))

let zCAP_BOUND_NUM_BITS = (add_int (zCAP_VALUE_NUM_BITS, (Big_int.of_int (1))));;

let zCAP_BOUND_MAX = (zSlice_int ((shl_int ((Big_int.of_int (1)), zCAP_VALUE_NUM_BITS)), Big_int.zero, zCAP_BOUND_NUM_BITS));;

let zCAP_BOUND_MIN = (zSlice_int ((uint [B0; B0; B0; B0]), Big_int.zero, zCAP_BOUND_NUM_BITS));;

let zCAP_MAX_ENCODEABLE_EXPONENT = (Big_int.of_int (63));;

let zCAP_MAX_EXPONENT = (add_int ((sub_int (zCAP_VALUE_NUM_BITS, zCAP_MW)), (Big_int.of_int (2))));;

let rec zCapBoundsAddress (zaddress : ((bit) list)) : (bit) list = sail_call (fun r ->
  r.return (sign_extend ((subrange (zaddress, (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))), Big_int.zero)), zCAP_VALUE_NUM_BITS)))

let zCAP_BASE_MANTISSA_LO_BIT = (Big_int.of_int (67));;

let rec zCapGetBottom (zc : ((bit) list)) : (bit) list = sail_call (fun r ->
  if (zCapIsInternalExponent zc) then (r.return (append ((subrange (zc, zCAP_BASE_HI_BIT, zCAP_BASE_MANTISSA_LO_BIT)), [B0; B0; B0]))) else (r.return (subrange (zc, zCAP_BASE_HI_BIT, zCAP_BASE_LO_BIT))))

let zCAP_LIMIT_HI_BIT = (Big_int.of_int (93));;

let zCAP_LIMIT_MANTISSA_LO_BIT = (Big_int.of_int (83));;

let rec zCapUnsignedLessThan ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  r.return (lt ((uint za), (uint zb))))

and zCapGetTop (zc : ((bit) list)) : (bit) list = sail_call (fun r ->
  let zlmsb = ref ([B0; B0] : (bit) list) in
  let zlcarry = ref ([B0; B0] : (bit) list) in
  let zb = (zCapGetBottom zc) in
  let zt = ref ((undefined_bitvector (add_int ((sub_int ((Big_int.of_int (79)), (Big_int.of_int (64)))), (Big_int.of_int (1))))) : (bit) list) in
  begin
    if (zCapIsInternalExponent zc) then (begin
      zlmsb := ([B0; B1]);
      zt := (append ((append ([B0; B0], (subrange (zc, zCAP_LIMIT_HI_BIT, zCAP_LIMIT_MANTISSA_LO_BIT)))), [B0; B0; B0]))
    end) else (zt := (append ([B0; B0], (subrange (zc, zCAP_LIMIT_HI_BIT, zCAP_LIMIT_LO_BIT)))));
    if (zCapUnsignedLessThan ((subrange (!zt, (sub_int (zCAP_MW, (Big_int.of_int (3)))), Big_int.zero)), (subrange (zb, (sub_int (zCAP_MW, (Big_int.of_int (3)))), Big_int.zero)))) then (zlcarry := ([B0; B1])) else ();
    zt := (update_subrange (!zt, (sub_int (zCAP_MW, (Big_int.of_int (1)))), (sub_int (zCAP_MW, (Big_int.of_int (2)))), (add_vec ((add_vec ((subrange (zb, (sub_int (zCAP_MW, (Big_int.of_int (1)))), (sub_int (zCAP_MW, (Big_int.of_int (2)))))), !zlmsb)), !zlcarry))));
    r.return !zt
  end)

and zCapIsExponentOutOfRange (zc : ((bit) list)) : bool = sail_call (fun r ->
  let zexp = (zCapGetExponent zc) in
  r.return ((gt (zexp, zCAP_MAX_EXPONENT)) && (lt (zexp, zCAP_MAX_ENCODEABLE_EXPONENT))))

and zCapUnsignedGreaterThan ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  r.return (gt ((uint za), (uint zb))))

and zCapGetBounds (zc : ((bit) list)) : ((bit) list * (bit) list * bool) = sail_call (fun r ->
  let zexp = (zCapGetExponent zc) in
  begin
    if (eq_int (zexp, zCAP_MAX_ENCODEABLE_EXPONENT)) then (r.return (zCAP_BOUND_MIN, zCAP_BOUND_MAX, true)) else ();
    if (zCapIsExponentOutOfRange zc) then (r.return (zCAP_BOUND_MIN, zCAP_BOUND_MAX, false)) else ();
    let zbase = ref ((undefined_bitvector (Big_int.of_int (66))) : (bit) list) in
    let zlimit = ref ((undefined_bitvector (Big_int.of_int (66))) : (bit) list) in
    let zbottom = (zCapGetBottom zc) in
    let ztop = (zCapGetTop zc) in
    begin
      zbase := (set_slice ((Big_int.of_int (66)), zexp, !zbase, Big_int.zero, (zZeros zexp)));
      zlimit := (set_slice ((Big_int.of_int (66)), zexp, !zlimit, Big_int.zero, (zZeros zexp)));
      assert (lt ((sub_int ((add_int ((z__id zexp), (Big_int.of_int (16)))), (Big_int.of_int (1)))), (Big_int.of_int (66))));
      zbase := (update_subrange (!zbase, (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (1)))), zexp, zbottom));
      zlimit := (update_subrange (!zlimit, (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (1)))), zexp, ztop));
      let za = (append ([B0; B0], (zCapBoundsAddress (zCapGetValue zc)))) in
      let zA3 = (subrange (za, (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (1)))), (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (3)))))) in
      let zB3 = (subrange (zbottom, (sub_int (zCAP_MW, (Big_int.of_int (1)))), (sub_int (zCAP_MW, (Big_int.of_int (3)))))) in
      let zT3 = (subrange (ztop, (sub_int (zCAP_MW, (Big_int.of_int (1)))), (sub_int (zCAP_MW, (Big_int.of_int (3)))))) in
      let zR3 = (sub_vec (zB3, [B0; B0; B1])) in
      let zaHi = ref (Big_int.zero : Big_int.num) in
      begin
        if (zCapUnsignedLessThan (zA3, zR3)) then (zaHi := ((Big_int.of_int (1)))) else (zaHi := (Big_int.zero));
        let zaHi = !zaHi in
        let zbHi = ref (Big_int.zero : Big_int.num) in
        begin
          if (zCapUnsignedLessThan (zB3, zR3)) then (zbHi := ((Big_int.of_int (1)))) else (zbHi := (Big_int.zero));
          let zbHi = !zbHi in
          let ztHi = ref (Big_int.zero : Big_int.num) in
          begin
            if (zCapUnsignedLessThan (zT3, zR3)) then (ztHi := ((Big_int.of_int (1)))) else (ztHi := (Big_int.zero));
            let ztHi = !ztHi in
            let zcorrection_base = (sub_int (zbHi, zaHi)) in
            let zcorrection_limit = (sub_int (ztHi, zaHi)) in
            begin
              if (lt ((add_int (zexp, zCAP_MW)), (add_int (zCAP_MAX_EXPONENT, zCAP_MW)))) then (let zatop = (subrange (za, (Big_int.of_int (65)), (add_int (zexp, zCAP_MW)))) in
              begin
                zbase := (update_subrange (!zbase, (Big_int.of_int (65)), (add_int (zexp, zCAP_MW)), (add_vec_int (zatop, zcorrection_base))));
                zlimit := (update_subrange (!zlimit, (Big_int.of_int (65)), (add_int (zexp, zCAP_MW)), (add_vec_int (zatop, zcorrection_limit))))
              end) else ();
              let zl2 = (subrange (!zlimit, (Big_int.of_int (64)), (Big_int.of_int (63)))) in
              let zb2 = (append ([B0], [access (!zbase, (Big_int.of_int (63)))])) in
              begin
                if ((lt (zexp, (sub_int (zCAP_MAX_EXPONENT, (Big_int.of_int (1)))))) && (zCapUnsignedGreaterThan ((sub_vec (zl2, zb2)), [B0; B1]))) then (zlimit := (update (!zlimit, (Big_int.of_int (64)), (zBit (not_vec [access (!zlimit, (Big_int.of_int (64)))]))))) else ();
                r.return (append ([B0], (subrange (!zbase, (Big_int.of_int (63)), Big_int.zero))), subrange (!zlimit, (Big_int.of_int (64)), Big_int.zero), true)
              end
            end
          end
        end
      end
    end
  end)

and zCapBoundsEqual ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  let zabase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zalimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zavalid = ref ((undefined_bool ()) : bool) in
  let zbbase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zblimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zbvalid = ref ((undefined_bool ()) : bool) in
  begin
    (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds za) in
    begin zabase := (ztup__0); zalimit := (ztup__1); zavalid := (ztup__2) end);
    (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds zb) in
    begin zbbase := (ztup__0); zblimit := (ztup__1); zbvalid := (ztup__2) end);
    r.return ((((eq_list (!zabase, !zbbase)) && (eq_list (!zalimit, !zblimit))) && !zavalid) && !zbvalid)
  end)

and zCapIsRepresentable ((zc, zaddress) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  let znewc = ref (zc : (bit) list) in
  begin
    znewc := (update_subrange (!znewc, zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT, zaddress));
    r.return (zCapBoundsEqual (zc, !znewc))
  end)

let zCAP_TAG_BIT = (Big_int.of_int (128));;

let rec zCapSetTag ((zc, zt) : ((bit) list * (bit) list)) : (bit) list = sail_call (fun r ->
  let zr = ref (zc : (bit) list) in
  begin
    zr := (update (!zr, zCAP_TAG_BIT, (zBit [access (zt, Big_int.zero)])));
    r.return !zr
  end)

and zCapWithTagClear (zc : ((bit) list)) : (bit) list = sail_call (fun r ->
  r.return (zCapSetTag (zc, (zero_extend ([B0], (Big_int.of_int (64)))))))

and zCapSetValue ((zc__arg, zv) : ((bit) list * (bit) list)) : (bit) list = sail_call (fun r ->
  let zc = ref (zc__arg : (bit) list) in
  let zoldv = (zCapGetValue !zc) in
  begin
    if (not (zCapIsRepresentable (!zc, zv))) then (zc := (zCapWithTagClear !zc)) else ();
    zc := (update_subrange (!zc, zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT, zv));
    if ((zCapBoundsUsesValue (zCapGetExponent !zc)) && (zneq_bits ([access (zv, (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))))], [access (zoldv, (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))))]))) then (zc := (zCapWithTagClear !zc)) else ();
    r.return !zc
  end)

let zCAP_PERMS_HI_BIT = (Big_int.of_int (127));;

let zCAP_PERMS_LO_BIT = (Big_int.of_int (110));;

let zCAP_PERMS_NUM_BITS = (add_int ((sub_int (zCAP_PERMS_HI_BIT, zCAP_PERMS_LO_BIT)), (Big_int.of_int (1))));;

let rec zCapGetPermissions (zc : ((bit) list)) : (bit) list = sail_call (fun r ->
  r.return (subrange (zc, zCAP_PERMS_HI_BIT, zCAP_PERMS_LO_BIT)))

let zCAP_LENGTH_NUM_BITS = (add_int (zCAP_VALUE_NUM_BITS, (Big_int.of_int (1))));;

let rec zCapUnsignedGreaterThanOrEqual ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  r.return (gteq ((uint za), (uint zb))))

and zCapIsRepresentableFast ((zc, zincrement_name__arg) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  let zincrement_name = ref (zincrement_name__arg : (bit) list) in
  let zB3 = ref ((undefined_bitvector (add_int (Big_int.zero, (add_int ((sub_int ((sub_int ((add_int ((sub_int ((Big_int.of_int (79)), (Big_int.of_int (64)))), (Big_int.of_int (1)))), (Big_int.of_int (1)))), (sub_int ((add_int ((sub_int ((Big_int.of_int (79)), (Big_int.of_int (64)))), (Big_int.of_int (1)))), (Big_int.of_int (3)))))), (Big_int.of_int (1))))))) : (bit) list) in
  let zR = ref ((undefined_bitvector (Big_int.of_int (16))) : (bit) list) in
  let zR3 = ref ((undefined_bitvector (Big_int.of_int (3))) : (bit) list) in
  let za_mid = ref ((undefined_bitvector (add_int (Big_int.zero, (add_int ((sub_int ((sub_int ((add_int ((sub_int ((Big_int.of_int (79)), (Big_int.of_int (64)))), (Big_int.of_int (1)))), (Big_int.of_int (1)))), Big_int.zero)), (Big_int.of_int (1))))))) : (bit) list) in
  let zdiff = ref ((undefined_bitvector (Big_int.of_int (16))) : (bit) list) in
  let zdiff1 = ref ((undefined_bitvector (Big_int.of_int (16))) : (bit) list) in
  let zi_mid = ref ((undefined_bitvector (add_int (Big_int.zero, (add_int ((sub_int ((sub_int ((add_int ((sub_int ((Big_int.of_int (79)), (Big_int.of_int (64)))), (Big_int.of_int (1)))), (Big_int.of_int (1)))), Big_int.zero)), (Big_int.of_int (1))))))) : (bit) list) in
  let zi_top = ref ((undefined_bitvector (Big_int.of_int (64))) : (bit) list) in
  let zexp = (zCapGetExponent zc) in
  if (gteq (zexp, (sub_int (zCAP_MAX_EXPONENT, (Big_int.of_int (2)))))) then (r.return true) else (let za = ref ((zCapGetValue zc) : (bit) list) in
  let za = (zCapBoundsAddress !za) in
  let zincrement_name = (zCapBoundsAddress !zincrement_name) in
  let zi_top = (arith_shiftr (zincrement_name, (add_int (zexp, zCAP_MW)))) in
  let zi_mid = (subrange ((shiftr (zincrement_name, zexp)), (sub_int (zCAP_MW, (Big_int.of_int (1)))), Big_int.zero)) in
  let za_mid = (subrange ((shiftr (za, zexp)), (sub_int (zCAP_MW, (Big_int.of_int (1)))), Big_int.zero)) in
  let zB3 = (subrange ((zCapGetBottom zc), (sub_int (zCAP_MW, (Big_int.of_int (1)))), (sub_int (zCAP_MW, (Big_int.of_int (3)))))) in
  let zR3 = (sub_vec (zB3, [B0; B0; B1])) in
  let zR = (append (zR3, (zZeros (sub_int (zCAP_MW, (Big_int.of_int (3))))))) in
  let zdiff = (sub_vec (zR, za_mid)) in
  let zdiff1 = (sub_vec_int (zdiff, (Big_int.of_int (1)))) in
  if (zeq_bits_int (zi_top, Big_int.zero)) then (r.return (zCapUnsignedLessThan (zi_mid, zdiff1))) else (if (eq_list (zi_top, (zOnes zCAP_VALUE_NUM_BITS))) then (r.return ((zCapUnsignedGreaterThanOrEqual (zi_mid, zdiff)) && (zneq_bits (zR, za_mid)))) else (r.return false))))

and zCapAdd ((zc, zincrement_name) : ((bit) list * (bit) list)) : (bit) list = sail_call (fun r ->
  let znewc = ref (zc : (bit) list) in
  begin
    znewc := (update_subrange (!znewc, zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT, (add_vec ((zCapGetValue zc), zincrement_name))));
    if (not (zCapIsRepresentableFast (zc, zincrement_name))) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
    if (zCapIsExponentOutOfRange zc) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
    if ((zCapBoundsUsesValue (zCapGetExponent zc)) && (zneq_bits ([access ((zCapGetValue zc), (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))))], [access ((zCapGetValue !znewc), (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))))]))) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
    r.return !znewc
  end)

and zCapNull (() : (unit)) : (bit) list = sail_call (fun r ->
  let zc = (zZeros (Big_int.of_int (129))) in
  r.return zc)

and zCapUnsignedLessThanOrEqual ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  r.return (lteq ((uint za), (uint zb))))

and zCapIsRangeInBounds ((zc, zstart_address, zlength) : ((bit) list * (bit) list * (bit) list)) : bool = sail_call (fun r ->
  let zbase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zlimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zvalid_name = ref ((undefined_bool ()) : bool) in
  begin
    (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds zc) in
    begin zbase := (ztup__0); zlimit := (ztup__1); zvalid_name := (ztup__2) end);
    let zstart_ext = (append ([B0], zstart_address)) in
    let zlimit_ext = (add_vec (zstart_ext, zlength)) in
    r.return (((zCapUnsignedGreaterThanOrEqual (zstart_ext, !zbase)) && (zCapUnsignedLessThanOrEqual (zlimit_ext, !zlimit))) && !zvalid_name)
  end)

and zCapSetBounds ((zc, zreq_len, zexact) : ((bit) list * (bit) list * bool)) : (bit) list = sail_call (fun r ->
  let zL_ie = ref ((undefined_bitvector (Big_int.of_int (13))) : (bit) list) in
  let zobase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zolimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zovalid = ref ((undefined_bool ()) : bool) in
  begin
    assert (zCapUnsignedLessThanOrEqual (zreq_len, zCAP_BOUND_MAX));
    let zexp = ref ((sub_int (zCAP_MAX_EXPONENT, (count_leading_zeros (subrange (zreq_len, zCAP_VALUE_NUM_BITS, (sub_int (zCAP_MW, (Big_int.of_int (1))))))))) : Big_int.num) in
    let zie = ((zneq_int (!zexp, Big_int.zero)) || (eq_list ([access (zreq_len, (sub_int (zCAP_MW, (Big_int.of_int (2)))))], [B1]))) in
    let zbase = (zCapGetValue zc) in
    let zabase = (if (zCapBoundsUsesValue (zCapGetExponent zc)) then (zCapBoundsAddress zbase) else zbase) in
    let zreq_base = (append ([B0; B0], zabase)) in
    let zreq_top = (add_vec (zreq_base, (append ([B0], zreq_len)))) in
    let zBbits = ref ((subrange (zreq_base, (sub_int (zCAP_MW, (Big_int.of_int (1)))), Big_int.zero)) : (bit) list) in
    let zTBits = ref ((subrange (zreq_top, (sub_int (zCAP_MW, (Big_int.of_int (1)))), Big_int.zero)) : (bit) list) in
    let zlostTop = ref (false : bool) in
    let zlostBottom = ref (false : bool) in
    let zincrementE_name = ref (false : bool) in
    begin
      if zie then (let zB_ie = ref ((let zexp = !zexp in
      begin
        assert ((lteq (Big_int.zero, (add_int ((z__id zexp), (Big_int.of_int (3)))))) && (lt ((sub_int ((add_int ((z__id zexp), (Big_int.of_int (16)))), (Big_int.of_int (1)))), (Big_int.of_int (66)))));
        subrange (zreq_base, (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (1)))), (add_int (zexp, (Big_int.of_int (3)))))
      end) : (bit) list) in
      let zT_ie = ref ((let zexp = !zexp in
      begin
        assert ((lteq (Big_int.zero, (add_int ((z__id zexp), (Big_int.of_int (3)))))) && (lt ((sub_int ((add_int ((z__id zexp), (Big_int.of_int (16)))), (Big_int.of_int (1)))), (Big_int.of_int (66)))));
        subrange (zreq_top, (sub_int ((add_int (zexp, zCAP_MW)), (Big_int.of_int (1)))), (add_int (zexp, (Big_int.of_int (3)))))
      end) : (bit) list) in
      let zmaskLo = (let zexp = !zexp in
      begin
        assert (gteq ((add_int ((z__id zexp), (Big_int.of_int (3)))), Big_int.zero));
        assert (gteq ((Big_int.of_int (66)), (add_int ((z__id zexp), (Big_int.of_int (3))))));
        zero_extend ((zOnes (add_int (zexp, (Big_int.of_int (3))))), (add_int (zCAP_VALUE_NUM_BITS, (Big_int.of_int (2)))))
      end) in
      begin
        zlostBottom := (zneq_bits ((and_vec (zreq_base, zmaskLo)), (zZeros (add_int (zCAP_VALUE_NUM_BITS, (Big_int.of_int (2)))))));
        zlostTop := (zneq_bits ((and_vec (zreq_top, zmaskLo)), (zZeros (add_int (zCAP_VALUE_NUM_BITS, (Big_int.of_int (2)))))));
        if !zlostTop then (zT_ie := (add_vec_int (!zT_ie, (Big_int.of_int (1))))) else ();
        let zL_ie = (sub_vec (!zT_ie, !zB_ie)) in
        begin
          (let zexp = !zexp in
          if (eq_list ([access (zL_ie, (sub_int (zCAP_MW, (Big_int.of_int (4)))))], [B1])) then (begin
            zincrementE_name := (true);
            zlostBottom := (!zlostBottom || (eq_list ([access (!zB_ie, Big_int.zero)], [B1])));
            zlostTop := (!zlostTop || (eq_list ([access (!zT_ie, Big_int.zero)], [B1])));
            assert (lt (zexp, zCAP_MAX_EXPONENT));
            assert (lteq (Big_int.zero, (add_int ((z__id zexp), (Big_int.of_int (4))))));
            zB_ie := (subrange (zreq_base, (add_int (zexp, zCAP_MW)), (add_int (zexp, (Big_int.of_int (4))))));
            zT_ie := (subrange (zreq_top, (add_int (zexp, zCAP_MW)), (add_int (zexp, (Big_int.of_int (4))))));
            if !zlostTop then (zT_ie := (add_vec_int (!zT_ie, (Big_int.of_int (1))))) else ()
          end) else ());
          if (eq_bool (!zincrementE_name, true)) then (zexp := (add_int (!zexp, (Big_int.of_int (1))))) else ();
          zBbits := (append (!zB_ie, [B0; B0; B0]));
          zTBits := (append (!zT_ie, [B0; B0; B0]))
        end
      end) else ();
      let zexp = !zexp in
      let znewc = ref (zc : (bit) list) in
      begin
        (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds zc) in
        begin
          zobase := (ztup__0);
          zolimit := (ztup__1);
          zovalid := (ztup__2)
        end);
        if (((not (zCapUnsignedGreaterThanOrEqual ((slice (zreq_base, Big_int.zero, zCAP_BOUND_NUM_BITS)), !zobase))) || (not (zCapUnsignedLessThanOrEqual ((slice (zreq_top, Big_int.zero, zCAP_BOUND_NUM_BITS)), !zolimit)))) || (not !zovalid)) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
        if zie then (begin
          znewc := (update (!znewc, zCAP_IE_BIT, (zBit [B0])));
          znewc := (update_subrange (!znewc, zCAP_BASE_EXP_HI_BIT, zCAP_BASE_LO_BIT, (not_vec (zinteger_subrange (zexp, (Big_int.of_int (2)), Big_int.zero)))));
          znewc := (update_subrange (!znewc, zCAP_LIMIT_EXP_HI_BIT, zCAP_LIMIT_LO_BIT, (not_vec (zinteger_subrange (zexp, (Big_int.of_int (5)), (Big_int.of_int (3)))))))
        end) else (begin
          znewc := (update (!znewc, zCAP_IE_BIT, (zBit [B1])));
          znewc := (update_subrange (!znewc, zCAP_BASE_EXP_HI_BIT, zCAP_BASE_LO_BIT, (subrange (!zBbits, (Big_int.of_int (2)), Big_int.zero))));
          znewc := (update_subrange (!znewc, zCAP_LIMIT_EXP_HI_BIT, zCAP_LIMIT_LO_BIT, (subrange (!zTBits, (Big_int.of_int (2)), Big_int.zero))))
        end);
        znewc := (update_subrange (!znewc, zCAP_BASE_HI_BIT, zCAP_BASE_MANTISSA_LO_BIT, (subrange (!zBbits, (sub_int (zCAP_MW, (Big_int.of_int (1)))), (Big_int.of_int (3))))));
        znewc := (update_subrange (!znewc, zCAP_LIMIT_HI_BIT, zCAP_LIMIT_MANTISSA_LO_BIT, (subrange (!zTBits, (sub_int (zCAP_MW, (Big_int.of_int (3)))), (Big_int.of_int (3))))));
        let zfrom_large = (not (zCapBoundsUsesValue (zCapGetExponent zc))) in
        let zto_small = (zCapBoundsUsesValue zexp) in
        begin
          if ((zfrom_large && zto_small) && (zneq_bits ((sign_extend ((subrange (zbase, (sub_int (zCAP_FLAGS_LO_BIT, (Big_int.of_int (1)))), Big_int.zero)), (Big_int.of_int (64)))), zbase))) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
          if (zexact && (!zlostBottom || !zlostTop)) then (znewc := (update (!znewc, zCAP_TAG_BIT, (zBit [B0])))) else ();
          r.return !znewc
        end
      end
    end
  end)

and zCapGetRepresentableMask (zlen : ((bit) list)) : (bit) list = sail_call (fun r ->
  let zc = ref ((zCapNull ()) : (bit) list) in
  let ztest_base = (sub_vec ((zOnes zCAP_VALUE_NUM_BITS), zlen)) in
  let ztest_length = (zero_extend (zlen, zCAP_LENGTH_NUM_BITS)) in
  begin
    zc := (update_subrange (!zc, zCAP_VALUE_HI_BIT, zCAP_VALUE_LO_BIT, ztest_base));
    let zc = (zCapSetBounds (!zc, ztest_length, false)) in
    let zexp1 = ref (Big_int.zero : Big_int.num) in
    begin
      if (zCapIsInternalExponent zc) then (zexp1 := (add_int ((zCapGetExponent zc), (Big_int.of_int (3))))) else ();
      let zexp1 = !zexp1 in
      begin
        assert (gteq ((sub_int ((Big_int.of_int (64)), (z__id zexp1))), Big_int.zero));
        assert (gteq ((z__id zexp1), Big_int.zero));
        r.return (append ((zOnes (sub_int (zCAP_VALUE_NUM_BITS, zexp1))), (zZeros zexp1)))
      end
    end
  end)

and zCapIsSubSetOf ((za, zb) : ((bit) list * (bit) list)) : bool = sail_call (fun r ->
  let zabase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zalimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zavalid = ref ((undefined_bool ()) : bool) in
  let zbbase = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zblimit = ref ((undefined_bitvector (add_int ((add_int ((sub_int ((Big_int.of_int (63)), Big_int.zero)), (Big_int.of_int (1)))), (Big_int.of_int (1))))) : (bit) list) in
  let zbvalid = ref ((undefined_bool ()) : bool) in
  begin
    (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds za) in
    begin zabase := (ztup__0); zalimit := (ztup__1); zavalid := (ztup__2) end);
    (let (ztup__0, ztup__1, ztup__2) = (zCapGetBounds zb) in
    begin zbbase := (ztup__0); zblimit := (ztup__1); zbvalid := (ztup__2) end);
    let zboundsSubset = ((zCapUnsignedGreaterThanOrEqual (!zabase, !zbbase)) && (zCapUnsignedLessThanOrEqual (!zalimit, !zblimit))) in
    let zpermsSubset = (eq_list ((and_vec ((zCapGetPermissions za), (not_vec (zCapGetPermissions zb)))), (zZeros zCAP_PERMS_NUM_BITS))) in
    r.return (((zboundsSubset && zpermsSubset) && !zavalid) && !zbvalid)
  end)

let zinitializze_registers () = ();;

