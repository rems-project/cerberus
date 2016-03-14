

let () =
  for i = 0 to Array.length Sys.argv - 1 do
    let ic   = open_in Sys.argv.(i) in
    let defs = Cparser_driver.parse ic in
    close_in ic;
    
  done
