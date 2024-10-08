(**
   Capabilty encoding decoding unit tests. To run:
   dune exec ./coqcaptest.exe
 *)

open OUnit2
open Strfcap

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

open CapabilitiesGS
open MorelloCapsGS

module M = struct
  include MorelloCapabilityWithStrfcap
  include TestCaps
  
  let cap_1 : t = TestCaps.c1
  let cap_1_bytes = TestCaps.c1_bytes
  let cap_2 : t = TestCaps.c2
  let cap_2_bytes = TestCaps.c2_bytes
  let cap_3_bytes = TestCaps.c3_bytes

  let deep_eqb a b =
    get_ghost_state a = get_ghost_state b
    && cap_is_valid a = cap_is_valid b
    && cap_get_value a = cap_get_value b
    && cap_get_offset a = cap_get_offset b
    && cap_get_obj_type a = cap_get_obj_type b
    && cap_get_bounds a = cap_get_bounds b
    && cap_get_seal a = cap_get_seal b
    && cap_get_flags a = cap_get_flags b
    && cap_get_perms a = cap_get_perms b
end

let str_of_bool b =
  if b then "1" else "0"

let string_of_bool_list l =
  let open List in
  "[" ^
    (String.concat "" @@ map str_of_bool l)
    ^ "]"

let cap_bits_diff (fmt:Format.formatter) (c1,c2) =
  let nth_bit x n = x land (1 lsl n) <> 0 in
  let bitarray length x = List.init length (nth_bit x) in
  let bit_list_of_char c = bitarray 8 (int_of_char c) in
  let b1 = List.concat (List.map bit_list_of_char c1) in
  let b2 = List.concat (List.map bit_list_of_char c2) in
  assert(List.length b1 = List.length b2);
  let open Format in
  pp_force_newline fmt ();
  for i = 0 to (List.length b1)-1 do
    let x0 = List.nth b1 i in
    let x1 = List.nth b2 i in
    if x0 <> x1 then
      Format.fprintf fmt "bit %03d: expected %s: but got: %s\n"
        i
        (str_of_bool x0)
        (str_of_bool x1);
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

let debug_print_cap c =
  match M.strfcap "%C" c with
  | Some s -> s
  | None -> M.to_string c (* fallback *)

let tests = "coq_morello_caps" >::: [


      "C0" >:: (fun _ -> assert_bool "C0 exists"
                           (let c0 = M.cap_c0 () in
                            c0 = c0)
               );

      "encode C0 tag" >:: (fun _ ->
        match M.encode (M.cap_c0 ()) with
        | None -> assert_failure "encode failed"
        | Some (bytes, tag) ->  assert_equal false tag
      );

      "encode C0 bytes" >:: (fun _ ->
        (* C0 does not M.encode to all zeros due to compresison limitations *)
        match M.encode (M.cap_c0 ()) with
        | None -> assert_failure "encode failed"
        | Some (bytes, tag) ->
           let b = List.map char_of_int [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0] in
           assert_equal
             ~pp_diff:cap_bits_diff
             b
             bytes
      );

      "encode C1 bytes" >:: (fun _ ->
        (* C1 corresponds to https://www.morello-project.org/capinfo?c=0x1%3A900000007F1CFF15%3A00000000FFFFFF15 *)
        let expected_bytes = M.cap_1_bytes in
        match M.encode M.cap_1 with
        | None -> assert_failure "encode failed"
        | Some (actual_bytes, t) ->
           assert_equal
             ~pp_diff:cap_bits_diff
            expected_bytes
            actual_bytes 
      );

      "decode C1 bytes" >:: (fun _ ->
        match M.decode M.c1_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:M.deep_eqb
             ~printer:M.to_string
             M.cap_1
             c
      );

      "decode C1 bytes (value)" >:: (fun _ ->
        match M.decode M.c1_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (M.cap_get_value M.cap_1)
             (M.cap_get_value c)
      );

      "decode C1 bytes (flags)" >:: (fun _ ->
        match M.decode M.c1_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:string_of_bool_list
             (M.cap_get_flags M.cap_1)
             (M.cap_get_flags c)
      );

      "decode/strfcap/perm C1" >:: (fun _ ->
        (* C1 corresponds to https://www.morello-project.org/capinfo?c=0x1%3A900000007F1CFF15%3A00000000FFFFFF15 *)
        let bytes_ = M.cap_1_bytes in 
        match M.decode bytes_ true with
        | None -> assert_failure "decode failed"
        | Some c -> 
          match M.strfcap "%P" c with 
          | None -> assert_failure "strfcap failed"
          | Some s' ->
             assert_equal
               ~pp_diff:string_diff
               "rR" s'  
      );

      "decode C0" >:: (fun _ ->
        let b = List.init 16 (fun _ -> '\000') in
        match M.decode b false with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:M.deep_eqb
             ~printer:debug_print_cap
             c (M.cap_c0 ())
      );

      "decode alt C0" >:: (fun _ ->
        let b = List.map char_of_int [0;0;0;0;0;0;0;0;5;0;1;0;0;0;0;0] in
        match M.decode b false with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:M.deep_eqb
             ~printer:M.to_string
             c (M.cap_c0 ())
      );
      
      "encode/decode C0" >:: (fun _ ->
        let c0 = M.cap_c0 () in
        match M.encode c0 with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c0' ->
                assert_equal
                  ~cmp:M.deep_eqb
                  ~printer:M.to_string
                  c0 c0'
           end
      );

      "encode/decode odd" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in

        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                assert_equal
                  ~cmp:M.deep_eqb
                  ~printer:debug_print_cap
                  c c'
           end
      );

      "encode/decode even" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int (0xfffffff4)) (Z.of_int 16) in
        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                assert_equal
                  ~cmp:M.deep_eqb
                  ~printer:debug_print_cap
                  c c'
           end
      );

      "encode/decode C1" >:: (fun _ ->
        let c = M.cap_1  in
        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                assert_equal
                  ~cmp:M.deep_eqb
                  ~printer:debug_print_cap
                  c c'
           end
      );

      "encode/decode/getFlags C1" >:: (fun _ ->
        let c = M.cap_1  in
        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                assert_equal
                  ~printer:string_of_bool_list
                  (M.cap_get_flags c)
                  (M.cap_get_flags c')
           end
      );

      "encode/decode/encode" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                begin
                  match M.encode c' with
                  | None -> assert_failure "2nd M.encode failed"
                  | Some (b', _) ->
                     assert_equal
                       ~pp_diff:cap_bits_diff
                       b b'
                end
           end
      );

      "decode_value" >:: (fun _ ->
        let b = List.map char_of_int [120;255;247;255;255;255;0;0;120;255;124;127;0;64;93;220] in
        match M.decode b true with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff78)
             (M.cap_get_value c)
      );

      "decode_bounds" >:: (fun _ ->
        let b = List.map char_of_int [120;255;247;255;255;255;0;0;120;255;124;127;0;64;93;220] in
        match M.decode b true with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_int 0xfffffff7ff7c)
             (snd (M.cap_get_bounds c))
      );

      "encode value and bounds" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 0xfffffff7ff78) (Z.of_int 4) in
        match M.encode c with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c' ->
                assert_equal
                  ~printer:(Z.format "%#x")
                  (Z.of_int 0xfffffff7ff78)
                  (M.cap_get_value c');
                assert_equal
                  ~printer:(Z.format "%#x")
                  (Z.of_int 0xfffffff7ff7c)
                  (snd (M.cap_get_bounds c'))
           end
      );

      "two.decode" >:: (fun _ ->
        let b1 = List.map char_of_int [0;14;192;0;127;240;255;236;0;0;0;0;255;255;255;236] in
        let mc1 = M.decode b1 true in
        let b2 = List.map char_of_int  [42;14;192;0;127;240;255;236;0;0;0;0;255;255;255;236] in
        let mc2 = M.decode b2 true in
        match mc1,mc2 with
        | None, _ -> assert_failure "1st decode failed"
        | _, None -> assert_failure "2nd decode failed"
        | Some c1, Some c2 ->
           if M.cap_get_value c1 = M.cap_get_value c2 then
             assert_failure "vlaue of c1 = value c2 while it should not"
      );

      "C0 is_null_derived" >:: (fun _ ->
        let c = M.cap_c0 () in
        assert_bool
          "C0 is not null derived!"
          (M.cap_is_null_derived c)
      );

      "alloc_cap not is_null_derived" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_bool
          "alloc_cap is null derived"
          (not (M.cap_is_null_derived c))
      );

      "alloc_cap value" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 1)
          (M.cap_get_value c));

      "alloc_cap lower bound" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 1)
          (fst (M.cap_get_bounds c)));

      "alloc_cap upper bound" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 1) (Z.of_int 10) in
        assert_equal
          ~printer:(Z.format "%#x")
          (Z.of_int 11)
          (snd (M.cap_get_bounds c)));

      "strfcap C0 addr" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%a" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0" s'
      );

      "strfcap C0 hex len" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%xl" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "ffffffffffffffff" s'
      );

      "strfcap C0 hex top" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%xt" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "ffffffffffffffff" s'
      );

      "strfcap C0 perm" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%P" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "" s'
      );

      "strfcap M.alloc_cap perm" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 1) (Z.of_int 10) in
        match M.strfcap "%P" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "rwRW" s'
      );

      "strfcap C0 hex addr" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "ffff" s'
      );

      "strfcap C0 Hex addr" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%Xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "FFFF" s'
      );

      "strfcap C0 0x Hex addr" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%#Xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0XFFFF" s'
      );

      "strfcap C0 padded Hex addr" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%10xa" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "      ffff" s'
      );

      "strfcap C0-derived C-format" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0x0" s'
      );

      "strfcap not C0-derived C-format" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0xffff [rwRW,0xffff-0x10009]" s'
      );

      "strfcap T-format" >:: (fun _ ->
        let c0 = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        let c1 = M.cap_invalidate c0 in
        match M.strfcap "%C" c0, M.strfcap "%T%C" c1 with
        | Some s0, Some s1 ->
           assert_equal
             ~pp_diff:string_diff
             s0 s1
        | _ , _ -> assert_failure "strfcap failed"
      );

      "strfcap v-format" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        match M.strfcap "%v" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "1" s'
      );

      "strfcap C0 v-format" >:: (fun _ ->
        let c = M.cap_c0 () in
        match M.strfcap "%v" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0" s'
      );

      "strfcap invalid" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int 65535) (Z.of_int 10) in
        let c = M.cap_invalidate c in
        match M.strfcap "%C" c with
        | None -> assert_failure "strfcap failed"
        | Some s' ->
           assert_equal
             ~pp_diff:string_diff
             "0xffff [rwRW,0xffff-0x10009] (invalid)" s'
      );

      "representable_alignment_mask" >:: (fun _ ->
        let l = ["0";"1";"0x3e8";"0xffffff";"0xffffffffffffffff"] in
        let em = ["0xffffffffffffffff";"0xffffffffffffffff";"0xffffffffffffffff";
                  "0xffffffffffffe000"; "0xffe0000000000000"] in
        let emz = List.map Z.of_string em in
        let lz = List.map Z.of_string l in
        let m = List.map M.representable_alignment_mask lz in
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
        let m = List.map M.representable_length lz in
        ListZ.assert_equal
          emz
          m
      );

      (* default ghost state on alloc *)
      "alloc_gs" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let gs = M.get_ghost_state c in
        assert_equal false gs.bounds_unspecified;
        assert_equal false gs.tag_unspecified
      );

      (* setter test *)
      "change_gs" >:: (fun _ ->
        let c = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let c = M.set_ghost_state c {
                    tag_unspecified=true;
                    bounds_unspecified=true
                  }
        in
        let gs = M.get_ghost_state c in
        assert_equal true gs.bounds_unspecified;
        assert_equal true gs.tag_unspecified
      );

      (* Exact compare does not take tag into account *)
      "gs_exact_compare" >:: (fun _ ->
        let c0 = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let c1 = M.set_ghost_state c0 {
                     tag_unspecified=true;
                     bounds_unspecified=true
                   }
        in
        assert_equal
          ~cmp:M.eqb
          ~printer:debug_print_cap
          c0 c1
      );

      (* ghost state is not preserved in encoding *)
      "encode/decode gs" >:: (fun _ ->
        let c0 = M.alloc_cap (Z.of_int (0xfffffff3)) (Z.of_int 16) in
        let c0 = M.set_ghost_state c0 {
                     tag_unspecified=true;
                     bounds_unspecified=true
                   }
        in
        match M.encode c0 with
        | None -> assert_failure "encode failed"
        | Some (b, t) ->
           begin
             match M.decode b t with
             | None -> assert_failure "decoding failed"
             | Some c1 ->
                let gs1 = M.get_ghost_state c1 in
                assert_equal false gs1.bounds_unspecified;
                assert_equal false gs1.tag_unspecified
           end
      );

      "C1 representabitiy" >:: (fun _ ->
        assert_bool
          "7FFFE6EC should not be representable"
          (not (M.cap_ptraddr_representable M.cap_1 (Z.of_string "0x7FFFE6EC")))
      );

      "C2 representabitiy" >:: (fun _ ->
        assert_bool
          "7FFFE6EC should not be representable"
          (not (M.cap_ptraddr_representable M.cap_2 (Z.of_string "0x7FFFE6EC")))
      );

      "encode C2 bytes" >:: (fun _ ->
        let expected_bytes = M.c2_bytes in
        match M.encode M.cap_2 with
        | None -> assert_failure "encode failed"
        | Some (actual_bytes, t) ->
           assert_equal
             ~pp_diff:cap_bits_diff
            expected_bytes
            actual_bytes 
      );

      "decode C2 bytes" >:: (fun _ ->
        match M.decode M.c2_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~cmp:M.deep_eqb
             ~printer:M.to_string
             M.cap_2
             c
      );

      "decode C2 bytes (value)" >:: (fun _ ->
        match M.decode M.c2_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (M.cap_get_value M.cap_2)
             (M.cap_get_value c)
      );

      "decode C2 bytes (base)" >:: (fun _ ->
        match M.decode M.c2_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (fst (M.cap_get_bounds c))
             (fst (M.cap_get_bounds M.cap_2))
      );

      "decode C2 bytes (limit)" >:: (fun _ ->
        match M.decode M.c2_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (snd (M.cap_get_bounds c))
             (snd (M.cap_get_bounds M.cap_2))
      );

      "decode C3 bytes (value)" >:: (fun _ ->
        match M.decode M.c3_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:(Z.format "%#x")
             (Z.of_string "0x2a000000ffffe6d0")
             (M.cap_get_value c)
      );

      "decode C3 bytes (flags)" >:: (fun _ ->
        match M.decode M.c3_bytes true  with
        | None -> assert_failure "decode failed"
        | Some c ->
           assert_equal
             ~printer:string_of_bool_list
             (List.rev [false; false; true; false; true; false; true; false])
             (M.cap_get_flags c)
      );


      "C3 decode/encode" >:: (fun _ ->
        match M.decode M.c3_bytes true with
        | None -> assert_failure "decoding failed"
        | Some c ->
           begin
             match M.encode c with
             | None -> assert_failure "2nd M.encode failed"
             | Some (b', _) ->
                assert_equal
                  ~pp_diff:cap_bits_diff
                  M.c3_bytes b'
           end
      );

    ]

let _ = run_test_tt_main tests
