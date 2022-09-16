(**
   Capabilty encoding decoding unit tests. To run:
   dune exec ./captest.exe
 *)

open OUnit2
open Morello
open Morello_capability

module Z = struct
  include Nat_big_num
  let format = Z.format
end

module EZ =
struct
  type t = Z.num
  let compare = Z.compare
  let pp_printer f z =
    Format.pp_print_string f (Z.format "%#x" z)
  let pp_print_sep = OUnitDiff.pp_comma_separator
end

module ListZ = OUnitDiff.ListSimpleMake(EZ)

(* let string_of_char_list l =
  let open List in
  "[" ^
    (String.concat ";" @@ map string_of_int @@ map int_of_char l)
    ^ "]" *)

let string_of_bit_list l =
  let open List in
  let open Sail_lib in
  "[" ^
    (String.concat ";" @@ map string_of_bit l)
    ^ "]"

let indexed_string_of_bit_list l =
  let open List in
  let open Sail_lib in
  let bits = map string_of_bit l in
  let ibits = mapi (Printf.sprintf "bit %3d:%s") bits in
  "\n" ^
    (String.concat "\n" @@ ibits)
    ^ "\n"

let cap_bits_indexed_str b =
  let bit_list_of_char c =
    Sail_lib.get_slice_int' (8, (Z.of_int (int_of_char c)), 0) in
  let bits = List.concat (List.map bit_list_of_char b) in
  indexed_string_of_bit_list bits

let cap_bits_str b =
  let bit_list_of_char c =
    Sail_lib.get_slice_int' (8, (Z.of_int (int_of_char c)), 0) in
  let bits = List.concat (List.map bit_list_of_char b) in
  string_of_bit_list bits

let cap_bits_diff (fmt:Format.formatter) (c1,c2) =
  let bit_list_of_char c =
    Sail_lib.get_slice_int' (8, (Z.of_int (int_of_char c)), 0) in
  let b1 = List.map Sail_lib.string_of_bit @@ List.concat (List.map bit_list_of_char c1) in
  let b2 = List.map Sail_lib.string_of_bit @@ List.concat (List.map bit_list_of_char c2) in
  assert(List.length b1 = List.length b2);
  let open Format in
  pp_force_newline fmt ();
  for i = 0 to (List.length b1)-1 do
    let x0 = List.nth b1 i in
    let x1 = List.nth b2 i in
    if x0 <> x1 then
      Format.fprintf fmt "bit %03d: expected %s: but got: %s\n" i x0 x1;
  done

let string_diff fmt (a,b) =
  let open Format in
  pp_print_newline fmt ();
  pp_open_box fmt 0;
  pp_open_hbox fmt () ;
  pp_print_string fmt "Expected: '";
  pp_print_string fmt a;
  pp_print_string fmt "'";
  pp_close_box fmt  ();
  pp_print_newline fmt ();
  pp_open_hbox fmt () ;
  pp_print_string fmt "Received: '";
  pp_print_string fmt b;
  pp_print_string fmt "'";
  pp_close_box fmt ();
  pp_close_box fmt ()

let tests = "morello_caps" >::: [


      "C0" >:: (fun _ -> assert_bool "C0 exists"
                           (let c0 = cap_c0 () in
                            c0 = c0)
               );

      "encode C0 tag" >:: (fun _ ->
        assert_equal
          false
          (snd (encode true (cap_c0 ())))
      );

      "encode C0 bytes" >:: (fun _ ->
        (* C0 does not encode to all zeros due to compresison limitations *)
        let b = List.map char_of_int [0;0;0;0;0;0;0;0;5;0;1;0;0;0;0;0] in
        assert_equal
          ~pp_diff:cap_bits_diff
          ~printer:cap_bits_str
          b
          (fst (encode true (cap_c0 ())))
      );

      "decode C0" >:: (fun _ ->
        let b = List.init 16 (fun _ -> '\000') in
        match decode b false with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:equal
             ~printer:Morello_capability.show
             c (cap_c0 ())
      );

      "decode alt C0" >:: (fun _ ->
        let b = List.map char_of_int [0;0;0;0;0;0;0;0;5;0;1;0;0;0;0;0] in
        match decode b false with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:equal
             ~printer:Morello_capability.show
             c (cap_c0 ())
      );
      
      "encode/decode C0" >:: (fun _ ->
        let c0 = cap_c0 () in
        let (b,t) = encode true c0 in
        match decode b t with
        | None -> assert_failure "decoding failed"
        | Some c0' ->
           assert_equal
             ~cmp:equal
             ~printer:Morello_capability.show
             c0 c0'
      );

      "encode/decode odd" >:: (fun _ ->
        let c = alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let (b,t) = encode true c in
        match decode b t with
        | None -> assert_failure "decoding failed"
        | Some c' ->
           assert_equal
             ~cmp:equal
             ~printer:Morello_capability.show
             c c'
      );

      "encode/decode even" >:: (fun _ ->
        let c = alloc_cap (Z.of_int (0xfffffff4)) (Z.of_int 16) in
        let (b,t) = encode true c in
        match decode b t with
        | None -> assert_failure "decoding failed"
        | Some c' ->
           assert_equal
             ~cmp:equal
             ~printer:Morello_capability.show
             c c'
      );

      "encode/decode/encode" >:: (fun _ ->
        let c = alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let (b,t) = encode true c in
        match decode b t with
        | None -> assert_failure "decoding failed"
        | Some c' ->
           let (b',_) = encode true c' in
           assert_equal
             ~printer:cap_bits_indexed_str
             b b'
      );

      "decode_value" >:: (fun _ ->
        let b = List.map char_of_int [120;255;247;255;255;255;0;0;120;255;124;127;0;64;93;220] in
        match decode b true with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff78)
             (cap_get_value c)
      );

      "decode_bounds" >:: (fun _ ->
        let b = List.map char_of_int [120;255;247;255;255;255;0;0;120;255;124;127;0;64;93;220] in
        match decode b true with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff7c)
             (snd (cap_get_bounds c))
      );

      "encode value and bounds" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 0xfffffff7ff78) (Z.of_int 4) in
        let (b,t) = encode true c in
        match decode b t with
        | None -> assert_failure "decoding failed"
        | Some c' ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff78)
             (cap_get_value c');
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff7c)
             (snd (cap_get_bounds c'))
      );

      "two_decode" >:: (fun _ ->
        let b1 = List.map char_of_int [0;14;192;0;127;240;255;236;0;0;0;0;255;255;255;236] in
        let mc1 = decode b1 true in
        let b2 = List.map char_of_int  [42;14;192;0;127;240;255;236;0;0;0;0;255;255;255;236] in
        let mc2 = decode b2 true in
        match mc1,mc2 with
        | None, _ -> assert_failure "1st decode failed"
        | _, None -> assert_failure "2nd decode failed"
        | Some c1, Some c2 ->
           if cap_get_value c1 = cap_get_value c2 then
             assert_failure "vlaue of c1 = value c2 while it should not"
      );

      "C0 is_null_derived" >:: (fun _ ->
        let c = cap_c0 () in
        assert_bool
          "C0 is not null derived!"
          (Morello_capability.cap_is_null_derived c)
      );

      "alloc_cap not is_null_derived" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_bool
          "alloc_cap is null derived"
          (not (Morello_capability.cap_is_null_derived c))
      );

      "alloc_cap value" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 1)
          (cap_get_value c));

      "alloc_cap lower bound" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 1)
          (fst (cap_get_bounds c)));

      "alloc_cap upper bound" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 11)
          (snd (cap_get_bounds c)));

      "strfcap C0 addr" >:: (fun _ ->
        let c = cap_c0 () in
        match Morello_capability.strfcap "%a" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0" s'
      );

      "strfcap C0 perm" >:: (fun _ ->
        let c = cap_c0 () in
        match Morello_capability.strfcap "%P" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "" s'
      );

      "strfcap alloc_cap perm" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 1) (Z.of_int 10) in
        match Morello_capability.strfcap "%P" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "rwRW" s'
      );

      "strfcap C0 hex addr" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "ffff" s'
      );

      "strfcap C0 Hex addr" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%Xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "FFFF" s'
      );

      "strfcap C0 0x Hex addr" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%#Xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0XFFFF" s'
      );

      "strfcap C0 padded Hex addr" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%10xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "      ffff" s'
      );

      "strfcap C0-derived C-format" >:: (fun _ ->
        let c = cap_c0 () in
        match Morello_capability.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0x0" s'
      );

      "strfcap not C0-derived C-format" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0xffff [rwRW,0xffff-0x20008]" s'
      );

      "strfcap v-format" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match Morello_capability.strfcap "%v" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "1" s'
      );

      "strfcap C0 v-format" >:: (fun _ ->
        let c = cap_c0 () in
        match Morello_capability.strfcap "%v" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0" s'
      );

      "strfcap invalid" >:: (fun _ ->
        let c = alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        let c = cap_invalidate c in
        match Morello_capability.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0xffff [rwRW,0xffff-0x20008] (invald)" s'
      );

      "representable_alignment_mask" >:: (fun _ ->
        let l = ["0";"1";"0x3e8";"0xffffff";"0xffffffffffffffff"] in
        let em = ["0xffffffffffffffff";"0xffffffffffffffff";"0xffffffffffffffff";
                  "0xffffffffffffe000"; "0xffe0000000000000"] in
        let emz = List.map Z.of_string em in
        let lz = List.map Z.of_string l in
        let m = List.map representable_alignment_mask lz in
        ListZ.assert_equal
          emz
          m
      );

      "representable_length" >:: (fun _ ->
        let l = ["0";"1";"0x3e8";"0xffffff";"0xffffffffffffffff"] in
        let em = ["0";"1";"0x3e8";
                  "0x1000000"; "0"] in
        let emz = List.map Z.of_string em in
        let lz = List.map Z.of_string l in
        let m = List.map representable_length lz in
        ListZ.assert_equal
          emz
          m
      )

    ]

let _ = run_test_tt_main tests
