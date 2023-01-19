open Morello

module MorelloCapabilityWithStrfcap = struct
  include MorelloCapability

  let is_sealed c =
    match cap_get_seal c with
    | Cap_Unsealed -> false
    | _ -> true

    (* Helper function to check if sealed entry capability *)
  let is_sentry c =
    match cap_get_seal c with
    | Cap_SEntry -> true
    | _ -> false

  let flags_as_str tag c =
      let attrs =
        let a f s l = if f then s::l else l in
        let gs = (get_ghost_state c).tag_unspecified in
        a gs "notag"
        @@ (a ((not tag) && (not gs)) "invalid")
        @@ a (is_sentry c) "sentry"
        @@ a ((not (is_sentry c)) && is_sealed c) "sealed" []
      in
      if List.length attrs = 0 then ""
      else " (" ^ String.concat "," attrs ^ ")"

  (** String representation of permission using
      format string as in strfcap(3) *)
  let strfcap: string -> t -> string option = fun formats capability ->
    let module State = struct
        type num_state = | Initial | Precision | Width | Final
      end in
    let is_digit = function '0' .. '9' -> true | _ -> false in
    let as_digit c = Char.code c - Char.code '0' in
    let as_string = Printf.sprintf "%c" in
    let explode s = List.of_seq (String.to_seq s) in
    let (@) s = function
      | None -> None
      | Some t -> Some (s ^ t)
    in
    let rec loop tag cap = function
      | [] -> Some ""
      | '%'::fs -> strf tag cap false fs
      | c::fs -> as_string c @ loop tag cap fs
    and strf tag cap alt = function
      | [] ->
         (* unexpected end of format specifiction *)
         None
      | '#'::fs -> strf tag cap true fs (* mutiple # are allowed *)
      | '%'::fs -> "%" @ loop tag cap fs
      (* non-numeric formats *)
      | 'A'::fs ->
         let s = flags_as_str tag cap in
         s @ loop tag cap fs
      | 'B'::fs ->
         (*
         let bits = encode_to_bits true cap in
         let z = uint bits in
         Some (Z.format "%02hhx" z)
          *)
         None (* TODO: format not implemented *)
      | 'C'::fs ->
         if cap_is_null_derived cap then
           numf State.Initial (-1) (-1) false true 'x' tag cap ('a'::fs)
         else
           begin
             match loop tag cap (explode "%#xa [%P,%#xb-%#xt]%? %A") with
             | None -> None
             | Some s -> s  @ loop tag cap fs
           end
      | 'P'::fs ->
         let s = MorelloPermission.to_string (cap_get_perms cap) in
         s @ loop tag cap fs
      | 'T'::fs -> loop true cap fs
      | '?'::fs -> skip tag cap fs
      (* try numeric formats *)
      | x::fs as f -> numf State.Initial 1 1 false alt 'd' tag cap f
    and numf state width prec right_pad alt number_fmt tag cap f =
      let strnum z =
        (* TODO(CHERI) In C implementation of "strfcap" the
           following code is used to format numbers:

           *fmtp++ = '%';
           if (alt)
           *fmtp++ = '#';
           if (right_pad)
           *fmtp++ = '-';
           *fmtp++ = '*';
           *fmtp++ = '.';
           *fmtp++ = '*';
           *fmtp++ = 'l';
           *fmtp++ = number_fmt;
           *fmtp = '\0';
           snprintf(tmp, sizeof(tmp), fmt, width, precision, number);

           Unforntunately [Z.format] does not support precision
           specification for integers, so we just ignore it for
           now.
         *)
        let fmt  =
          "%"
          ^ (if alt then "#" else "")
          ^ (if right_pad then "-" else "")
          ^ (if width > 0 then Stdlib.string_of_int width else "")
          ^ (as_string number_fmt)
        in
        (if prec <> -1 then (* Precision specification is not supported *) () );
        Z.format fmt z
      in
      match state, f with
      | _, [] ->
         (* unexpected end of numeric format specifiction *)
         None
      (* width *)
      | Initial, c::fs when is_digit c ->
         if c='0' then
           begin
             (* leading zero in width not allowed in format specification *)
             None
           end
         else numf State.Width (as_digit c) prec right_pad alt number_fmt tag cap fs
      | Width, c::fs when is_digit c ->
         numf State.Width (width*10+(as_digit c)) prec right_pad alt number_fmt tag cap fs

      (* precision *)
      | Width, '.'::fs | Initial, '.'::fs ->
         numf State.Precision width 0 right_pad alt number_fmt tag cap fs
      | Precision, c::fs when is_digit c ->
         numf State.Precision width (prec*10+(as_digit c)) right_pad alt number_fmt tag cap fs

      (* right pad. could be specificed anywhere and repeated *)
      | _, '-'::fs ->
         numf State.Initial width prec true alt number_fmt tag cap fs

      (* alt pad. could be specificed anywhere and repeated *)
      | _, '#'::fs ->
         numf State.Final width prec right_pad true number_fmt tag cap fs

      (* hex could be specificed anywhere and repeated *)
      | _, ('x' as d)::fs
        | _, ('X' as d)::fs ->
         numf State.Final width prec right_pad alt d tag cap fs

      (* collaps to final *)
      | Width, _
        | Precision, _
        | Initial, _ -> numf State.Final width prec right_pad alt number_fmt tag cap f

      (* Actual numeric options *)
      | Final, 'a'::fs ->
         let z = cap_get_value cap in
         strnum z @ loop tag cap fs
      | Final, 'b'::fs ->
         (if (get_ghost_state cap).bounds_unspecified
          then "?"
          else strnum (fst (cap_get_bounds cap)))
         @ loop tag cap fs
      | Final, 'l'::fs ->
         (if (get_ghost_state cap).bounds_unspecified
          then "?"
          else
            let (base,limit) = cap_get_bounds cap in
            let z = Z.sub limit base in
            strnum z)
         @ loop tag cap fs
      | Final, 'o'::fs ->
         (if (get_ghost_state cap).bounds_unspecified
          then "?"
          else
            let base = fst (cap_get_bounds cap) in
            let addr = cap_get_value cap in
            let z = Z.sub addr base in
            strnum z)
         @ loop tag cap fs
      | Final, 'p'::fs ->
         let z = MorelloPermission.to_raw (cap_get_perms cap) in
         strnum z @ loop tag cap fs
      | Final, 's'::fs ->
         let z = cap_get_obj_type cap in
         strnum z @ loop tag cap fs
      | Final, 'S'::fs ->
         let s =
           match cap_get_seal cap with
           | Cap_Unsealed -> "<unsealed>"
           | Cap_SEntry -> "<sentry>"
           | _ -> strnum cap.obj_type
         in
         s @ loop tag cap fs
      | Final, 't'::fs ->
         let (base,limit) = cap_get_bounds cap in
         (if (get_ghost_state cap).bounds_unspecified
          then "?"
          else
            let z = Z.add base limit in
            strnum z)
         @ loop tag cap fs
      | Final, 'v'::fs ->
         let z = if cap_is_valid cap then Z.succ Z.zero else Z.zero in
         strnum z @ loop tag cap fs
      | Final, c::_ ->
         (* Unknown format specifier *)
         None
    and skip tag cap = function
      | [] -> None
      | ('%'::fs) as f -> loop tag cap f
      | _::fs -> skip tag cap fs
    in loop (cap_is_valid capability) capability (explode formats)

end
