open Sibylfs

module N = Nat_big_num

type fs =
  | File of string * Bytes.t * int * Unix.file_perm
  | Dir of string * fs array * Unix.file_perm

let contents file size =
  let ic = open_in file in
  let buf = Bytes.create size in
  really_input ic buf 0 size;
  close_in ic;
  buf

let rec fs_read dir =
  let files = Sys.readdir dir in
  Unix.chdir dir;
  Array.map (fun file ->
     let stats = Unix.stat file in
     if stats.st_kind = S_DIR then
       let content = fs_read file in
       let () = Unix.chdir ".." in
       Dir (file, content, stats.st_perm)
     else
       File (file, contents file stats.st_size, stats.st_size, stats.st_perm)
    ) files

let force (st, res) =
  match res with
  | Either.Right x -> (st, N.of_int x)
  | Either.Left _ -> assert false

let rec fs_write st =
  let open_flag = Nat_big_num.of_int 0O50 (* O_CREAT | O_RDWR *) in
  function
  | File (name, content, size, perm) ->
    let (st, fd) = force @@ run_open st name open_flag (Some (N.of_int perm)) in
    let (st, _) = run_write st fd (List.of_seq @@ Bytes.to_seq content) (N.of_int size) in
    let (st, _) = run_close st fd in
    st
  | Dir (name, contents, perm) ->
    let (st, _) = run_mkdir st name (N.of_int perm) in
    let (st, _) = run_chdir st name in
    let st = Array.fold_left fs_write st contents in
    let (st, _) = run_chdir st ".." in
    st

let initialise root =
  let cur = Unix.getcwd () in
  Unix.chdir root;
  let st = Array.fold_left fs_write fs_initial_state @@ fs_read root in
  Unix.chdir cur;
  st
