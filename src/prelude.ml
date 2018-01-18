let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code
