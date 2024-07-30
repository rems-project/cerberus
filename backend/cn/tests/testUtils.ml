let test_name fun_name =
  fun_name |> String.split_on_char '.' |> Cn.List.last |> Option.get


let test_suite_name filename =
  filename |> Filename.basename |> Filename.chop_extension |> String.capitalize_ascii
