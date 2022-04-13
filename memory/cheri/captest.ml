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

let string_of_char_list l =
  let open List in
  "[" ^
    (String.concat ";" @@ map string_of_int @@ map int_of_char l)
    ^ "]"

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

let tests = "test suite for Morello" >::: [


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
        assert_equal
          ~printer:cap_bits_str
          (List.init 16 (fun _ -> '\000'))
          (fst (encode false (cap_c0 ())))
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
        let (b,t) = encode false c0 in
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
             ~printer:(Z.format "%x")
             (Z.of_int 0xfffffff7ff78)
             (cap_get_value c)
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
      )
    ]

let _ = run_test_tt_main tests
