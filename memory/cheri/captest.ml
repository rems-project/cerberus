open OUnit2
open Morello
open Morello_capability

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

let cap_bits_str b =
  let bit_list_of_char c =
    Sail_lib.get_slice_int' (8, (Z.of_int (int_of_char c)), 0) in
  let bits = List.concat (List.map bit_list_of_char b) in
  indexed_string_of_bit_list bits

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
          (fst (encode true (cap_c0 ())))
      )
    ]

let _ = run_test_tt_main tests
