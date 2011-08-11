let print d =
  Pprint.Channel.pretty 40. 80 Pervasives.stdout d

let to_string d =
  Pprint.Formatter.pretty 40. 80 Format.str_formatter d;
  Format.flush_str_formatter ()

let to_plain_string d =
  Pprint.Formatter.compact Format.str_formatter d;
  Format.flush_str_formatter ()
