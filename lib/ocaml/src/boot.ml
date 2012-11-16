let outOfHomeomorphism msg = Pervasives.failwith ("[OutOfHomeomorphism exception> " ^ msg)
let debug str = Pervasives.failwith ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m")
let print_debug str k = Obj.magic (Pervasives.print_endline ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m")); k
