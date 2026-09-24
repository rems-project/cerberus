open Fs_spec
open Fs_types

let first fset =
  match Lem_support.list_from_finset fset with
  | v::_ -> v
  | _ -> failwith "sibylfs: first"

let last_ fset =
  match List.rev (Lem_support.list_from_finset fset) with
  | v::_ -> v
  | _ -> failwith "sibylfs: first"


module Fs_error = struct
  type t = Fs_types.error
  let to_sexp = Fs_types.sexp_of_error
end

module Fs_state = struct
  type t = Dir_heap.Dir_heap_types.dh_os_state
  let initial_state = Dir_heap.Dir_heap_ops.dh_init_state ARCH_POSIX false
  let to_sexp = Dir_heap.Dir_heap_types.sexp_of_dh_os_state
end

type fs_stat = Fs_types.ty_stats

let return_normal = function
  | OS_normal v -> v
  | OS_special (_, str) -> failwith ("return_normal: special: " ^ str)

let return_nat = function
  | RV_none -> 0
  | RV_num n -> n
  | _ -> failwith "return_nat"

let return_bytes = function
  | RV_none -> [] (* used by readdir *)
  | RV_bytes bs -> List_array.to_list bs
  | _ -> failwith "return_bytes"

let dest_uid (User_id n) = n

let dest_gid (Group_id n) = n

let return_stat = function
  | RV_stats st -> st
  | _ -> failwith "return_stat"

let fs_dev st =
  Z.of_int st.st_dev

let fs_ino st =
  Z.of_int (dest_Inode st.st_ino)

(* NOTE: values from https://git.musl-libc.org/cgit/musl/tree/include/sys/stat.h *)
let dest_file_kind = function
  | S_IFBLK -> Z.of_int 0O060000
  | S_IFCHR -> Z.of_int 0O020000
  | S_IFIFO -> Z.of_int 0O010000
  | S_IFREG -> Z.of_int 0O100000
  | S_IFDIR -> Z.of_int 0O040000
  | S_IFLNK -> Z.of_int 0O120000
  | S_IFSOCK -> Z.of_int 0O140000

let fs_mode st =
  Z.(of_int32 (dest_file_perm st.st_perm) + dest_file_kind st.st_kind)

let fs_nlink st =
  Z.of_int st.st_nlink

let fs_uid st =
  Z.of_int (dest_uid st.st_uid)

let fs_gid st =
  Z.of_int (dest_gid st.st_gid)

let fs_rdev st =
  Z.of_int st.st_rdev

let fs_size st =
  Z.of_int64 st.st_size

(* let fs_atime st =
  Z.of_int (dest_float_t st.st_atime) *)

(* let fs_mtime st =
  Z.of_int (dest_float_t st.st_mtime) *)

(* let fs_ctime st =
  Z.of_int (dest_float_t st.st_ctime) *)

let return_value return = function
  | Value v -> Either.Right (return v)
  | Error e -> Either.Left e

let run st return os_op =
  let open Dir_heap.Dir_heap_ops in
  let pid = Pid 1 in
  let lab = OS_CALL (pid, os_op) in
  (* do the call transition *)
  let st_oper = return_normal (first (dh_trans st lab)) in
  (* do a tau transition *)
  let st_tau  = return_normal (first (dh_trans st_oper OS_TAU)) in
  let result = first (dh_allowed_results_for_pid pid st_tau) in
  (* get state from the chosen value *)
  let st' = return_normal (first (dh_trans st_tau (OS_RETURN (pid, result)))) in
  (st', return_value return result)

let run_last st return os_op =
  let open Dir_heap.Dir_heap_ops in
  let pid = Pid 1 in
  let lab = OS_CALL (pid, os_op) in
  (* do the call transition *)
  let st_oper = return_normal (last_ (dh_trans st lab)) in
  (* do a tau transition *)
  let st_tau  = return_normal (last_ (dh_trans st_oper OS_TAU)) in
  let result = last_ (dh_allowed_results_for_pid pid st_tau) in
  (* get state from the chosen value *)
  let st' = return_normal (last_ (dh_trans st_tau (OS_RETURN (pid, result)))) in
  (st', return_value return result)


let file_perm_of_int n =
  File_perm (Z.to_int32 n)

let fd_of_int n =
  FD (Z.to_int n)

let uid_of_int n =
  User_id (Z.to_int n)

let gid_of_int n =
  Group_id (Z.to_int n)

let run_mkdir st path perm_code =
  run st return_nat (OS_MKDIR (CS_Some path, file_perm_of_int perm_code))

let run_open st path open_flags perm_code_opt =
  let file_perm_opt =
    match perm_code_opt with
    | Some perm_code -> Some (file_perm_of_int perm_code)
    | None -> Some (file_perm_of_int (Z.of_int 0O777)) (* TODO *)
  in
  run st return_nat @@ OS_OPEN (CS_Some path, Z.to_int32 open_flags, file_perm_opt)

let run_close st fd =
  run st return_nat @@ OS_CLOSE (fd_of_int fd)

let run_write st fd buf size =
  run st return_nat @@ OS_WRITE (fd_of_int fd, List_array.of_list buf, Z.to_int size)

let run_read st fd size =
  run_last st return_bytes @@ OS_READ (fd_of_int fd, Z.to_int size)

let run_pwrite st fd buf size off =
  run st return_nat @@ OS_PWRITE (fd_of_int fd, List_array.of_list buf, Z.to_int size, Z.to_int off)

let run_pread st fd size off =
  run_last st return_bytes @@ OS_PREAD (fd_of_int fd, Z.to_int size, Z.to_int off)

let run_rename st oldpath newpath =
  run st return_nat @@ OS_RENAME (CS_Some oldpath, CS_Some newpath)

let run_umask st mode =
  run st return_nat @@ OS_UMASK (file_perm_of_int mode)

let run_chmod st path mode =
  run st return_nat @@ OS_CHMOD (CS_Some path, file_perm_of_int mode)

let run_chdir st path =
  run st return_nat @@ OS_CHDIR (CS_Some path)

let run_chown st path uid gid =
  run st return_nat @@ OS_CHOWN (CS_Some path, uid_of_int uid, gid_of_int gid)

let run_link st oldpath newpath =
  run st return_nat @@ OS_LINK (CS_Some oldpath, CS_Some newpath)

let run_readlink st path =
  run st return_bytes @@ OS_READLINK (CS_Some path)

let run_symlink st target lpath =
  run st return_nat @@ OS_SYMLINK (CS_Some target, CS_Some lpath)

let run_rmdir st path =
  run st return_nat @@ OS_RMDIR (CS_Some path)

let run_truncate st path len =
  run st return_nat @@ OS_TRUNCATE (CS_Some path, Z.to_int len)

let run_unlink st path =
  run st return_nat @@ OS_UNLINK (CS_Some path)

let run_lseek st fd off whence =
  run st return_nat @@ OS_LSEEK (fd_of_int fd, Z.to_int off, Z.to_int whence)

let run_stat st path =
  run st return_stat @@ OS_STAT (CS_Some path)

let run_lstat st path =
  run st return_stat @@ OS_LSTAT (CS_Some path)

let run_opendir st path =
  run st return_nat @@ OS_OPENDIR (CS_Some path)

let run_readdir st dh =
  run st return_bytes @@ OS_READDIR (DH (Z.to_int dh))

let run_rewinddir st dh =
  fst @@ run st return_nat (OS_REWINDDIR (DH (Z.to_int dh)))

let run_closedir st dh =
  run st return_nat @@ OS_CLOSEDIR (DH (Z.to_int dh))
