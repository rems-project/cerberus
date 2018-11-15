(****************************************************************************)
(*  Copyright (c) 2013, 2014, 2015, Tom Ridge, David Sheets, Thomas Tuerk,  *)
(*  Andrea Giugliano (as part of the SibylFS project)                       *)
(*                                                                          *)
(*  Permission to use, copy, modify, and/or distribute this software for    *)
(*  any purpose with or without fee is hereby granted, provided that the    *)
(*  above copyright notice and this permission notice appear in all         *)
(*  copies.                                                                 *)
(*                                                                          *)
(*  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL           *)
(*  WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED           *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE        *)
(*  AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL    *)
(*  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR   *)
(*  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER          *)
(*  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR        *)
(*  PERFORMANCE OF THIS SOFTWARE.                                           *)
(*                                                                          *)
(*  Meta:                                                                   *)
(*    - Headers maintained using headache.                                  *)
(*    - License source: http://opensource.org/licenses/ISC                  *)
(****************************************************************************)

(* a printer for labels; a counterpart to the parser *)

open Lem_support
open Fs_spec.Fs_types
open Fs_dict_wrappers

let string_of_perm p = Format.sprintf "0o%03lo" (dest_file_perm p)
let string_of_perm_opt p_opt = begin match p_opt with
  | None -> ""
  | Some p -> string_of_perm p
end

let string_of_bytes bs = 
  let raw_string = (List_array.to_string bs) in
  let esc_string = String.escaped raw_string in
    ("\"" ^ esc_string ^ "\"") 

let string_of_name n = 
  let esc_string = String.escaped n in
    ("\"" ^ esc_string ^ "\"") 

let string_of_error e = (match e with
      E2BIG           -> "E2BIG"
    | EACCES          -> "EACCES"
    | EAGAIN          -> "EAGAIN"
    | EBADF           -> "EBADF"
    | EBUSY           -> "EBUSY"
    | ECHILD          -> "ECHILD"
    | EDEADLK         -> "EDEADLK"
    | EDOM            -> "EDOM"
    | EEXIST          -> "EEXIST"
    | EFAULT          -> "EFAULT"
    | EFBIG           -> "EFBIG"
    | EINTR           -> "EINTR"
    | EINVAL          -> "EINVAL"
    | EIO             -> "EIO"
    | EISDIR          -> "EISDIR"
    | EMFILE          -> "EMFILE"
    | EMLINK          -> "EMLINK"
    | ENAMETOOLONG    -> "ENAMETOOLONG"
    | ENFILE          -> "ENFILE"
    | ENODEV          -> "ENODEV"
    | ENOENT          -> "ENOENT"
    | ENOEXEC         -> "ENOEXEC"
    | ENOLCK          -> "ENOLCK"
    | ENOMEM          -> "ENOMEM"
    | ENOSPC          -> "ENOSPC"
    | ENOSYS          -> "ENOSYS"
    | ENOTDIR         -> "ENOTDIR"
    | ENOTEMPTY       -> "ENOTEMPTY"
    | ENOTTY          -> "ENOTTY"
    | ENXIO           -> "ENXIO"
    | EPERM           -> "EPERM"
    | EPIPE           -> "EPIPE"
    | ERANGE          -> "ERANGE"
    | EROFS           -> "EROFS"
    | ESPIPE          -> "ESPIPE"
    | ESRCH           -> "ESRCH"
    | EXDEV           -> "EXDEV"
    | EWOULDBLOCK     -> "EWOULDBLOCK"
    | EINPROGRESS     -> "EINPROGRESS"
    | EALREADY        -> "EALREADY"
    | ENOTSOCK        -> "ENOTSOCK"
    | EDESTADDRREQ    -> "EDESTADDRREQ"
    | EMSGSIZE        -> "EMSGSIZE"
    | EPROTOTYPE      -> "EPROTOTYPE"
    | ENOPROTOOPT     -> "ENOPROTOOPT"
    | EPROTONOSUPPORT -> "EPROTONOSUPPORT"
    | ESOCKTNOSUPPORT -> "ESOCKTNOSUPPORT"
    | EOPNOTSUPP      -> "EOPNOTSUPP"
    | EPFNOSUPPORT    -> "EPFNOSUPPORT"
    | EAFNOSUPPORT    -> "EAFNOSUPPORT"
    | EADDRINUSE      -> "EADDRINUSE"
    | EADDRNOTAVAIL   -> "EADDRNOTAVAIL"
    | ENETDOWN        -> "ENETDOWN"
    | ENETUNREACH     -> "ENETUNREACH"
    | ENETRESET       -> "ENETRESET"
    | ECONNABORTED    -> "ECONNABORTED"
    | ECONNRESET      -> "ECONNRESET"
    | ENOBUFS         -> "ENOBUFS"
    | EISCONN         -> "EISCONN"
    | ENOTCONN        -> "ENOTCONN"
    | ESHUTDOWN       -> "ESHUTDOWN"
    | ETOOMANYREFS    -> "ETOOMANYREFS"
    | ETIMEDOUT       -> "ETIMEDOUT"
    | ECONNREFUSED    -> "ECONNREFUSED"
    | EHOSTDOWN       -> "EHOSTDOWN"
    | EHOSTUNREACH    -> "EHOSTUNREACH"
    | ELOOP           -> "ELOOP"
    | EOVERFLOW       -> "EOVERFLOW"
    | EUNKNOWNERR(i)  -> ("EUNKNOWNERR("^(string_of_int i)^")"))

(* probably these need to use filename safe characters *)
let string_of_arch = function
  | ARCH_LINUX -> "Linux"
  | ARCH_POSIX -> "Posix"
  | ARCH_MAC_OS_X -> "Mac_OS_X"

let string_of_flag f = (match f with
  | O_EXEC         -> "O_EXEC"
  | O_RDONLY       -> "O_RDONLY"
  | O_RDWR         -> "O_RDWR"
  | O_SEARCH       -> "O_SEARCH"
  | O_WRONLY       -> "O_WRONLY"
  | O_APPEND       -> "O_APPEND"
  | O_CLOEXEC      -> "O_CLOEXEC"
  | O_CREAT        -> "O_CREAT"
  | O_DIRECTORY    -> "O_DIRECTORY"
  | O_DSYNC        -> "O_DSYNC"
  | O_EXCL         -> "O_EXCL"
  | O_NOCTTY       -> "O_NOCTTY"
  | O_NOFOLLOW     -> "O_NOFOLLOW"
  | O_NONBLOCK     -> "O_NONBLOCK"
  | O_RSYNC        -> "O_RSYNC"
  | O_SYNC         -> "O_SYNC"
  | O_TRUNC        -> "O_TRUNC"
  | O_TTY_INIT     -> "O_TTY_INIT"
)

let string_of_flags fs = (
  let fs = list_from_finset fs in
  "["^(String.concat ";" (List.map string_of_flag fs))^"]")

let string_of_int_flags arch fs = (
  let fs = arch.arch_open_flags_of_int fs in
  string_of_flags fs)

let string_of_seek_command c = (match c with
  | SEEK_CUR  -> "SEEK_CUR"
  | SEEK_SET  -> "SEEK_SET"
  | SEEK_END  -> "SEEK_END"
  | SEEK_DATA -> "SEEK_DATA"
  | SEEK_HOLE -> "SEEK_HOLE"
)

let string_of_int_seek_command arch i = (
  match arch.arch_seek_command_of_int i with
   | None -> string_of_int i
   | Some c -> string_of_seek_command c
)

let lem_of_int_seek_command i = string_of_int i

let string_of_cstring s = (match s with
  | CS_Null -> "null"
  | CS_Some s -> Printf.sprintf "%S" s)

let string_of_fd fd = (match fd with
    | FD n -> "(FD "^(string_of_int n)^")")

let string_of_dh dh = (match dh with
    | DH n -> "(DH "^(string_of_int n)^")")

let string_of_uid u = (match u with
    | User_id n -> "(User_id "^(string_of_int n)^")")

let string_of_gid g = (match g with
    | Group_id n -> "(Group_id "^(string_of_int n)^")")

let simple_string_of_uid uid = (match uid with
  | User_id n -> string_of_int n)

let simple_string_of_gid gid = (match gid with
  | Group_id n -> string_of_int n)


let string_of_os_ext_cmd arch cmd = (match cmd with
  | OS_OPEN_CLOSE (p,fs,p') -> ("open_close "^(string_of_cstring p)^" "^(string_of_int_flags arch fs)^(match p' with None -> "" | _ -> " "^(string_of_perm_opt p'))^"")
  | OS_ADD_USER_TO_GROUP(uid,gid) -> ("add_user_to_group "^(string_of_uid uid)^" "^(string_of_gid gid)^"")
  | OS_DET_PREAD (fd,len,ofs) -> ("pread! "^(string_of_fd fd)^" "^(string_of_int len)^" "^(string_of_int ofs)^"")
  | OS_DET_PWRITE (fd,bs,len,ofs) -> ("pwrite! "^(string_of_fd fd)^" "^(string_of_bytes bs)^" "^(string_of_int len)^" "^(string_of_int ofs)^"")
  | OS_DET_READ (fd,sz) -> ("read! "^(string_of_fd fd)^" "^(string_of_int sz))
  | OS_DET_WRITE (fd,bs,sz) -> ("write! "^(string_of_fd fd)^" "^(string_of_bytes bs)^" "^(string_of_int sz))
)

let string_of_label arch cmd = 
(match cmd with
  | OS_CLOSE(fd) -> ("close "^(string_of_fd fd))
  | OS_LINK (s,d) -> ("link "^(string_of_cstring s)^" "^(string_of_cstring d)^"")
  | OS_MKDIR (s,p) -> ("mkdir "^(string_of_cstring s)^" "^(string_of_perm p))
  | OS_OPEN (p,fs,p') -> ("open "^(string_of_cstring p)^" "^(string_of_int_flags arch fs)^(match p' with None -> "" | _ -> " "^(string_of_perm_opt p'))^"")
  | OS_PREAD (fd,len,ofs) -> ("pread "^(string_of_fd fd)^" "^(string_of_int len)^" "^(string_of_int ofs)^"")
  | OS_PWRITE (fd,bs,len,ofs) -> ("pwrite "^(string_of_fd fd)^" "^(string_of_bytes bs)^" "^(string_of_int len)^" "^(string_of_int ofs)^"")
  | OS_READ (fd,sz) -> ("read "^(string_of_fd fd)^" "^(string_of_int sz))
  | OS_WRITE (fd,bs,sz) -> ("write "^(string_of_fd fd)^" "^(string_of_bytes bs)^" "^(string_of_int sz))
  | OS_OPENDIR p -> ("opendir "^(string_of_cstring p)^"")
  | OS_CLOSEDIR dh -> ("closedir "^(string_of_dh dh)^"")
  | OS_READDIR dh -> ("readdir "^(string_of_dh dh)^"")
  | OS_REWINDDIR dh -> ("rewinddir "^(string_of_dh dh)^"")
  | OS_READLINK p -> ("readlink "^(string_of_cstring p)^"")
  | OS_RENAME (s,d) -> ("rename "^(string_of_cstring s)^" "^(string_of_cstring d)^"")
  | OS_RMDIR p -> ("rmdir "^(string_of_cstring p)^"")
  | OS_STAT p -> ("stat "^(string_of_cstring p)^"")
  | OS_LSTAT p -> ("lstat "^(string_of_cstring p)^"")
  | OS_SYMLINK(s,d) -> ("symlink "^(string_of_cstring s)^" "^(string_of_cstring d)^"")
  | OS_TRUNCATE (p,l) -> ("truncate "^(string_of_cstring p)^" "^(string_of_int l)^"")
  | OS_UNLINK p -> ("unlink "^(string_of_cstring p)^"")
  | OS_UMASK(p) -> ("umask "^(string_of_perm p))
  | OS_CHMOD(s,p) -> ("chmod "^(string_of_cstring s)^" "^(string_of_perm p))
  | OS_CHDIR s -> ("chdir "^(string_of_cstring s))
  | OS_CHOWN(s,u,g) -> ("chown "^(string_of_cstring s)^" "^(string_of_uid u)^" "^(string_of_gid g)^"")
  | OS_LSEEK(fd,ofs,int_seek_c) -> ("lseek "^(string_of_fd fd)^" "^(string_of_int ofs) ^" " ^ (string_of_int_seek_command arch int_seek_c))
  | OS_EXTENDED_CMD cmd' -> string_of_os_ext_cmd arch cmd' 
)


let string_of_lbls arch lbls = (String.concat "\n" (List.map (string_of_label arch) lbls))

let string_of_kind k = (
  match k with 
    S_IFBLK  -> "S_IFBLK"
  | S_IFCHR  -> "S_IFCHR"
  | S_IFIFO  -> "S_IFIFO"
  | S_IFREG  -> "S_IFREG"
  | S_IFDIR  -> "S_IFDIR"
  | S_IFLNK  -> "S_IFLNK" 
  | S_IFSOCK -> "S_IFSOCK")

let string_of_inode (Inode n) = string_of_int n

let string_of_monad_special_state = (function
   Impossible -> "Impossible"
 | Implementation_defined -> "Implementation_defined"
 | Unspecified -> "Unspecified" 
 | Undefined -> "Undefined"
 | FIXME -> "FIXME"
)

let string_of_os_special_state = (function
    OS_normal _ -> "OS_normal ..."
  | OS_special (ss, m) -> "OS_special (" ^ (string_of_monad_special_state ss) ^
       ", \"" ^ m ^ "\")"
)

let string_of_ret_value v = (match v with
  | RV_none -> "RV_none"
  | RV_num(i) -> ("RV_num("^(string_of_int i)^")")
  | RV_file_perm(p) -> ("RV_file_perm("^(string_of_perm p)^")")
  | RV_bytes(bs) -> (
    "RV_bytes("^(string_of_bytes bs)^")")
  | RV_names(ns) -> (
    "["^(String.concat ";" (List.map string_of_name ns))^"]") 
  | RV_stats(s) -> (
    let open Unix.LargeFile in
    let (d,i,k,p,n,u,g,r,s,a,m,c) = 
      (s.st_dev,s.st_ino,s.st_kind,s.st_perm,s.st_nlink,s.st_uid,s.st_gid,s.st_rdev,s.st_size,s.st_atime,s.st_mtime,s.st_ctime)
    in
    ("RV_stat { "^
      "st_dev="^(string_of_int d)^"; "^ 
      "st_ino="^(string_of_inode i)^"; "^
      "st_kind="^(string_of_kind k)^"; "^
      "st_perm="^(string_of_perm p)^"; "^ 
      "st_nlink="^(string_of_int n)^"; "^
      "st_uid="^(simple_string_of_uid u)^"; "^ 
      "st_gid="^(simple_string_of_gid g)^"; "^ 
      "st_rdev="^(string_of_int r)^"; "^
      "st_size="^(Int64.to_string s)^"; "^
(* times are not implemented in the main branch 
      "st_atim="^string_of_timestamp a^"; "^
      "st_mtim="^string_of_timestamp m^"; "^
      "st_ctim="^string_of_timestamp c^"; "^
*)
      "}")))

let string_of_rv_error_or_value ev = (match ev with
  | Error e -> ("Error("^(string_of_error e)^")")
  | Value v -> ("Value("^(string_of_ret_value v)^")"))

let input_string_of_rv_error_or_value ev = (match ev with
  | Error e -> (string_of_error e)
  | Value v -> (string_of_ret_value v)
)

let string_of_pid pid = (match pid with
  | Pid n -> ("Pid "^(string_of_int n)))

let string_of_os_label arch lbl = (match lbl with
  | OS_CALL(pid,lbl) -> ("OS_CALL("^(string_of_pid pid)^","^(string_of_label arch lbl)^")")
  | OS_RETURN(pid,rv) -> ("OS_RETURN("^(string_of_pid pid)^","^(string_of_rv_error_or_value rv)^")")
  | OS_CREATE(pid,uid,gid) -> ("OS_CREATE("^(string_of_pid pid)^","^(string_of_uid uid) ^ "," ^ (string_of_gid gid) ^ ")")
  | OS_DESTROY(pid) -> ("OS_DESTROY("^(string_of_pid pid)^")")
  | OS_TAU -> "OS_TAU")

let input_string_of_os_label drop_pid arch lbl = (match lbl with
  | OS_CALL(pid,lbl) -> ((if drop_pid then "" else (string_of_pid pid)^" -> ")^(string_of_label arch lbl))
  | OS_RETURN(pid,rv) -> ((if drop_pid then "" else ((string_of_pid pid)^" <- "))^(input_string_of_rv_error_or_value rv))
  | OS_CREATE(pid,uid,gid) -> ((string_of_pid pid)^" -> create "^(string_of_uid uid) ^ " " ^ (string_of_gid gid))
  | OS_DESTROY(pid) -> ((string_of_pid pid)^" -> destroy")
  | OS_TAU -> "Tau")

let lem_of_perm p = Format.sprintf "File_perm 0O%03lo" (dest_file_perm p)
let lem_of_perm_opt p_opt = begin match p_opt with
  | None -> "Nothing"
  | Some p -> "Just(" ^ lem_of_perm p ^ ")"
end

let lem_of_string s = "\"" ^ s ^ "\""

let lem_of_cstring s = (match s with
  | CS_Null -> "CS_Null"
  | CS_Some s -> "CS_Some "^ (lem_of_string s))

let lem_of_fd fd = string_of_fd fd
let lem_of_uid u = string_of_uid u
let lem_of_gid g = string_of_gid g

let lem_of_int i = string_of_int i
let lem_of_int_flags i = Int32.to_string i

let lem_of_bytes bs = 
  let raw_string = (List_array.to_string bs) in
  ("of_string" ^ lem_of_string raw_string)

let lem_of_error e = string_of_error e

let lem_of_ret_value v = (match v with
  | RV_file_perm(p) -> ("RV_file_perm("^(lem_of_perm p)^")")
  | _ -> string_of_ret_value v)

let lem_of_rv_error_or_value ev = (match ev with
  | Error e -> ("Error("^(lem_of_error e)^")")
  | Value v -> ("Value("^(lem_of_ret_value v)^")"))
(*
let lem_of_label lbl = (match lbl with
  | OS_CLOSE(fd) -> ("OS_CLOSE "^(lem_of_fd fd))
  | OS_LINK (s,d) -> ("OS_LINK("^(lem_of_cstring s)^", "^(lem_of_cstring d)^")")
  | OS_MKDIR (s,p) -> ("OS_MKDIR("^(lem_of_cstring s)^", "^(lem_of_perm p)^")")
  | OS_OPEN (p,fs,p') -> ("OS_OPEN("^(lem_of_cstring p)^", "^(lem_of_int_flags fs) ^ ", " ^ (lem_of_perm_opt p')^")")
  | OS_OPEN_CLOSE (p,fs,p') -> ("OS_OPEN_CLOSE("^(lem_of_cstring p)^", "^(lem_of_int_flags fs) ^ ", "^ (lem_of_perm_opt p') ^ ")")
  | OS_PREAD (fd,i,j) -> ("OS_PREAD("^(lem_of_fd fd)^", "^(lem_of_int i)^", "^(lem_of_int j)^")")
  | OS_PWRITE (fd,bs,len,ofs) -> ("OS_PWRITE("^(lem_of_fd fd)^", "^(lem_of_bytes bs)^", "^(lem_of_int len)^", "^(lem_of_int ofs)^")")
  | OS_READ (fd,sz) -> ("OS_READ("^(lem_of_fd fd)^", "^(lem_of_int sz)^")")
  | OS_READDIR p -> ("OS_READDIR "^(lem_of_cstring p)^"")
  | OS_READLINK p -> ("OS_READLINK "^(lem_of_cstring p)^"")
  | OS_RENAME (s,d) -> ("OS_RENAME("^(lem_of_cstring s)^", "^(lem_of_cstring d)^")")
  | OS_RMDIR p -> ("OS_RMDIR "^(lem_of_cstring p)^"")
  | OS_STAT p -> ("OS_STAT "^(lem_of_cstring p)^"")
  | OS_SYMLINK(s,d) -> ("OS_SYMLINK("^(lem_of_cstring s)^", "^(lem_of_cstring d)^")")
  | OS_TRUNCATE (p,l) -> ("OS_TRUNCATE("^(lem_of_cstring p)^", "^(lem_of_int l)^")")
  | OS_UNLINK p -> ("OS_UNLINK "^(lem_of_cstring p)^"")
  | OS_WRITE (fd,s,sz) -> ("OS_WRITE("^(lem_of_fd fd)^", "^(lem_of_bytes s)^", "^(lem_of_int sz))
  | OS_ADD_USER_TO_GROUP(uid,gid) -> ("OS_ADD_USER_TO_GROUP("^(lem_of_uid uid)^","^(lem_of_gid gid)^")")
  | OS_UMASK p -> ("OS_UMASK("^(lem_of_perm p)^")")
  | OS_CHDIR s -> ("OS_CHDIR("^(lem_of_cstring s)^")")
  | OS_CHMOD(s,p) -> ("OS_CHMOD("^(lem_of_cstring s)^", "^(lem_of_perm p)^")")
  | OS_CHOWN(s,u,g) -> ("OS_CHOWN("^(lem_of_cstring s)^", "^(lem_of_uid u)^" "^(lem_of_gid g)^"")
  | OS_LSEEK(fd,ofs,int_seek_c) -> ("OS_LSEEK("^(lem_of_fd fd)^","^(lem_of_int ofs) ^"," ^ (lem_of_int_seek_command int_seek_c)^")")
)

let lem_of_os_label lbl = (match lbl with
  | OS_CALL(pid,lbl) -> ("OS_CALL("^(string_of_pid pid)^", "^(lem_of_label lbl)^")")
  | OS_RETURN(pid,rv) -> ("OS_RETURN("^(string_of_pid pid)^", "^(lem_of_rv_error_or_value rv)^")")
  | OS_CREATE(pid,uid,gid) -> ("OS_CREATE("^(string_of_pid pid)^", "^(string_of_uid uid) ^ ", " ^ (string_of_gid gid) ^ ")")
  | OS_DESTROY(pid) -> ("OS_DESTROY "^(string_of_pid pid)^"")
  | OS_TAU -> "OS_TAU")
*)

let lem_of_os_label lbl = failwith "lem_of_os_label: NOT IMPLEMENTED CURRENTLY, NEEDS FIXING AND TESTING"
