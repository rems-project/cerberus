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

module Fs_spec_intf : sig 
  module Fs_types :
    sig
      type ty_bytes = Abstract_string.t
      type file_contents = ty_bytes
      type name = string [@@deriving sexp]
      type size_t = int [@@deriving sexp]
      type off_t = int [@@deriving sexp]
      type float_t = Float of int [@@deriving sexp]
      type cstring = CS_Null | CS_Some of string [@@deriving sexp]
      val bytes_of_cstring :
        cstring -> ty_bytes
      val cstring_of_bytes :
        ty_bytes -> cstring
      type ty_fd = FD of int [@@deriving sexp]
      val ty_fd_compare : ty_fd -> ty_fd -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_ty_fd_dict :
        ty_fd Lem_basic_classes.setType_class
      val dest_FD : ty_fd -> int
      type ty_dh = DH of int [@@deriving sexp]
      val ty_dh_compare : ty_dh -> ty_dh -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_ty_dh_dict :
        ty_dh Lem_basic_classes.setType_class
      val dest_DH : ty_dh -> int
      type inode = Inode of int [@@deriving sexp]
      val inode_compare : inode -> inode -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_inode_dict :
        inode Lem_basic_classes.setType_class
      val dest_Inode : inode -> int
      type error =
          E2BIG
        | EACCES
        | EAGAIN
        | EBADF
        | EBUSY
        | ECHILD
        | EDEADLK
        | EDOM
        | EEXIST
        | EFAULT
        | EFBIG
        | EINTR
        | EINVAL
        | EIO
        | EISDIR
        | EMFILE
        | EMLINK
        | ENAMETOOLONG
        | ENFILE
        | ENODEV
        | ENOENT
        | ENOEXEC
        | ENOLCK
        | ENOMEM
        | ENOSPC
        | ENOSYS
        | ENOTDIR
        | ENOTEMPTY
        | ENOTTY
        | ENXIO
        | EPERM
        | EPIPE
        | ERANGE
        | EROFS
        | ESPIPE
        | ESRCH
        | EXDEV
        | EWOULDBLOCK
        | EINPROGRESS
        | EALREADY
        | ENOTSOCK
        | EDESTADDRREQ
        | EMSGSIZE
        | EPROTOTYPE
        | ENOPROTOOPT
        | EPROTONOSUPPORT
        | ESOCKTNOSUPPORT
        | EOPNOTSUPP
        | EPFNOSUPPORT
        | EAFNOSUPPORT
        | EADDRINUSE
        | EADDRNOTAVAIL
        | ENETDOWN
        | ENETUNREACH
        | ENETRESET
        | ECONNABORTED
        | ECONNRESET
        | ENOBUFS
        | EISCONN
        | ENOTCONN
        | ESHUTDOWN
        | ETOOMANYREFS
        | ETIMEDOUT
        | ECONNREFUSED
        | EHOSTDOWN
        | EHOSTUNREACH
        | ELOOP
        | EOVERFLOW
        | EUNKNOWNERR of int
      [@@deriving sexp]
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_error_dict :
        error Lem_basic_classes.eq_class
      type 'a error_or_value = Error of error | Value of 'a [@@deriving sexp]
      val error_or_valueEqual :
        'a Lem_basic_classes.eq_class ->
        'a error_or_value -> 'a error_or_value -> bool
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_error_or_value_dict :
        'a Lem_basic_classes.eq_class ->
        'a error_or_value Lem_basic_classes.eq_class
      val is_Error : 'a error_or_value -> bool
      val is_Value : 'a error_or_value -> bool
      type int_open_flags = Int32.t [@@deriving sexp]
      type open_flag =
          O_EXEC
        | O_RDONLY
        | O_RDWR
        | O_SEARCH
        | O_WRONLY
        | O_APPEND
        | O_CLOEXEC
        | O_CREAT
        | O_DIRECTORY
        | O_DSYNC
        | O_EXCL
        | O_NOCTTY
        | O_NOFOLLOW
        | O_NONBLOCK
        | O_RSYNC
        | O_SYNC
        | O_TRUNC
        | O_TTY_INIT
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_open_flag_dict :
        open_flag Lem_basic_classes.eq_class
      val open_flags : open_flag Lem_support.finset
      val access_mode_flags : open_flag Lem_support.finset
      val open_flag_set_access_mode_ok : open_flag Lem_support.finset -> bool
      type file_perm = File_perm of Int32.t [@@deriving sexp]
      val dest_file_perm : file_perm -> Int32.t
      type int_seek_command = int [@@deriving sexp]
      type seek_command =
          SEEK_SET
        | SEEK_CUR
        | SEEK_END
        | SEEK_DATA
        | SEEK_HOLE
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_seek_command_dict :
        seek_command Lem_basic_classes.eq_class
      type file_kind =
          S_IFBLK
        | S_IFCHR
        | S_IFIFO
        | S_IFREG
        | S_IFDIR
        | S_IFLNK
        | S_IFSOCK [@@deriving sexp]
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_file_kind_dict :
        file_kind Lem_basic_classes.eq_class
      type uid = User_id of int [@@deriving sexp]
      val uid_compare : uid -> uid -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_uid_dict :
        uid Lem_basic_classes.setType_class
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_uid_dict :
        uid Lem_basic_classes.eq_class
      val root_uid : uid
      type gid = Group_id of int [@@deriving sexp]
      val gid_compare : gid -> gid -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_gid_dict :
        gid Lem_basic_classes.setType_class
      val root_gid : gid
      type ty_stats = {
        st_dev : int;
        st_ino : inode;
        st_kind : file_kind;
        st_perm : file_perm;
        st_nlink : int;
        st_uid : uid;
        st_gid : gid;
        st_rdev : int;
        st_size : Int64.t;
        st_atime : float_t;
        st_mtime : float_t;
        st_ctime : float_t;
      } [@@deriving sexp]
(*
      val default_st_dev : int
      val default_st_rdev : int
      val default_st_perm : file_perm
      val default_st_nlink : int
      val default_st_uid : uid
      val default_st_gid : gid
      val default_st_atime : float_t
      val default_st_mtime : float_t
      val default_st_ctime : float_t
*)
      type ret_value =
          RV_none
        | RV_num of int
        | RV_bytes of ty_bytes
        | RV_names of name list
        | RV_stats of ty_stats
        | RV_file_perm of file_perm
      [@@deriving sexp]
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_ret_value_dict :
        ret_value Lem_basic_classes.eq_class
      val dest_RV_bytes : ret_value -> ty_bytes
      val dummy_return_value : ret_value
      type ('dir_ref, 'file_ref) entry =
          Dir_ref_entry of 'dir_ref
        | File_ref_entry of 'file_ref
      val is_dir_ref_entry : ('a, 'b) entry -> bool
      val is_file_ref_entry : ('a, 'b) entry -> bool
      val dest_dir_ref_entry : ('a, 'b) entry -> 'a
      val dest_file_ref_entry : ('a, 'b) entry -> 'b
      type ty_name_list = Name_list of (name * name list)
      val ty_name_list_to_list : ty_name_list -> name list
      val make_ty_name_list : name list -> ty_name_list
      val nl_starts_with_slash : ty_name_list -> bool
      val nl_only_slash : ty_name_list -> bool
      val name_list_ends_with_slash : name list -> bool
      val is_absolute_path_aux : int -> string list -> bool
      val is_absolute_path : string list -> bool
      val is_root_path : string list -> bool
      val is_simple_path : string list -> bool
      val is_simple_absolute_path : string list -> bool
      type 'dir_ref ty_realpath_rec = {
        rp_cwd : 'dir_ref;
        rp_nl : ty_name_list;
        rp_ns : name list;
      }
      type ('dir_ref, 'file_ref) ty_realpath =
          RP_ok of 'dir_ref ty_realpath_rec
        | RP_err of (error * ty_name_list)
      val wf_ty_realpath_rec : 'a ty_realpath_rec -> bool
      val wf_ty_realpath : ('a, 'b) ty_realpath -> bool
      val realpath_proper_subdir :
        'a ty_realpath_rec -> 'b ty_realpath_rec -> bool
      type( 'dir_ref, 'file_ref) rn_error_extra = {
        re_cwd: 'dir_ref;
        re_nl:  ty_name_list option; (* the name list that was being resolved, needed for raising errors with respect to trailing slashes *)
        re_rn:  ( ('dir_ref, 'file_ref)res_name)option (* the resolved name (an RN_file) if we ignore trailing slashes *)
      } 
      and ('dir_ref, 'file_ref) res_name =
          RN_dir of ('dir_ref * 'dir_ref ty_realpath_rec)
        | RN_file of ('dir_ref * name * 'file_ref * 'dir_ref ty_realpath_rec)
        | RN_none of ('dir_ref * name * 'dir_ref ty_realpath_rec)
        | RN_error of
            (error * ( 'dir_ref, 'file_ref) rn_error_extra) [@@deriving sexp]
      val is_RN_dir : ('a, 'b) res_name -> bool
      val is_RN_file : ('a, 'b) res_name -> bool
      val is_RN_none : ('a, 'b) res_name -> bool
      val is_RN_error : ('a, 'b) res_name -> bool
      val wf_res_name : ('a, 'b) res_name -> bool
      val name_list_of_res_name : ('a, 'b) res_name -> ty_name_list option
      val rn_ends_with_slash : ('a, 'b) res_name -> bool
      type sysconf_value = SC_SYMLOOP_MAX
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_sysconf_value_dict :
        sysconf_value Lem_basic_classes.setType_class
      val sysconf_default : sysconf_value -> int
      type ty_os_ext_command =
          OS_OPEN_CLOSE of (cstring * int_open_flags * file_perm option)
        | OS_ADD_USER_TO_GROUP of (uid * gid)
        | OS_DET_PREAD of (ty_fd * size_t * off_t)
        | OS_DET_READ of (ty_fd * size_t)
        | OS_DET_PWRITE of (ty_fd * ty_bytes * size_t * off_t)
        | OS_DET_WRITE of (ty_fd * ty_bytes * size_t)
      [@@deriving sexp]
      val paths_of_ty_os_ext_command : ty_os_ext_command -> cstring list
      type ty_os_command =
          OS_CLOSE of ty_fd
        | OS_LINK of (cstring * cstring)
        | OS_MKDIR of (cstring * file_perm)
        | OS_OPEN of (cstring * int_open_flags * file_perm option)
        | OS_PREAD of (ty_fd * size_t * off_t)
        | OS_READ of (ty_fd * size_t)
        | OS_READDIR of ty_dh
        | OS_OPENDIR of cstring
        | OS_REWINDDIR of ty_dh
        | OS_CLOSEDIR of ty_dh
        | OS_READLINK of cstring
        | OS_RENAME of (cstring * cstring)
        | OS_RMDIR of cstring
        | OS_STAT of cstring
        | OS_LSTAT of cstring
        | OS_SYMLINK of (cstring * cstring)
        | OS_TRUNCATE of (cstring * off_t)
        | OS_UNLINK of cstring
        | OS_PWRITE of (ty_fd * ty_bytes * size_t * off_t)
        | OS_WRITE of (ty_fd * ty_bytes * size_t)
        | OS_UMASK of file_perm
        | OS_CHMOD of (cstring * file_perm)
        | OS_CHOWN of (cstring * uid * gid)
        | OS_CHDIR of cstring
        | OS_LSEEK of (ty_fd * off_t * int_seek_command)
        | OS_EXTENDED_CMD of ty_os_ext_command
      [@@deriving sexp]
      val paths_of_ty_os_command : ty_os_command -> cstring list
      type ty_arch = ARCH_LINUX | ARCH_POSIX | ARCH_MAC_OS_X | ARCH_FREEBSD
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_ty_arch_dict :
        ty_arch Lem_basic_classes.eq_class
      type architecture = {
        arch_abs_path_slash_slash : bool;
        arch_linux_non_posix : bool;
        arch_link_directories : bool;
        arch_open_flags_of_int : int_open_flags -> open_flag Lem_support.finset;
        arch_int_of_open_flags : open_flag Lem_support.finset -> int_open_flags;
        arch_seek_command_of_int : int_seek_command -> seek_command option;
        arch_int_of_seek_command : seek_command -> int_seek_command;
        arch_allows_dir_read : bool;
        arch_group_from_parent_dir : bool;
        arch_allows_removing_from_protected_dir_if_writeable : bool;
      }
      type ('dir_ref, 'file_ref, 'jimpl) perm_ops = {
        pops_set_perm_file : 'jimpl -> file_perm -> 'file_ref -> 'jimpl;
        pops_set_perm_dir : 'jimpl -> file_perm -> 'dir_ref -> 'jimpl;
        pops_chown_file : 'jimpl -> uid * gid -> 'file_ref -> 'jimpl;
        pops_chown_dir : 'jimpl -> uid * gid -> 'dir_ref -> 'jimpl;
        pops_uid_is_superuser : 'jimpl -> uid -> bool;
      }
(*      val perm_ops_noops : unit -> ('a, 'b, 'c) perm_ops *)
      type ('dir_ref, 'file_ref, 'jimpl) check_permissions 
      type 'dir_ref ty_od_handle (* = OD_handle of (int * 'dir_ref) *)
      type ty_od_entry (* = OD_removed of name | OD_added of name *)
      type ('dir_ref, 'file_ref, 'jimpl) fs_ops 
      (* we can't remove this type altogether because it is visible
         e.g. in resolve functions, although they could now get the env
         from the state (except that the env is changed during
         permissions processing FIXME *)
      type ('dir_ref, 'file_ref, 'jimpl) environment (* = {
        env_ops : ('dir_ref, 'file_ref, 'jimpl) fs_ops;
        env_arch : ty_arch;
        env_prms : ('dir_ref, 'file_ref, 'jimpl) check_permissions;
        env_perm_ops : ('dir_ref, 'file_ref, 'jimpl) perm_ops;
      } *)
      type ty_pid = Pid of int [@@deriving sexp]
      val ty_pid_compare : ty_pid -> ty_pid -> int
      val instance_Basic_classes_SetType_Fs_spec_Fs_types_ty_pid_dict :
        ty_pid Lem_basic_classes.setType_class
      val instance_Basic_classes_Eq_Fs_spec_Fs_types_ty_pid_dict :
        ty_pid Lem_basic_classes.eq_class
      val dest_PID : ty_pid -> int
      type os_label =
          OS_CALL of (ty_pid * ty_os_command)
        | OS_RETURN of (ty_pid * ret_value error_or_value)
        | OS_CREATE of (ty_pid * uid * gid)
        | OS_DESTROY of ty_pid
        | OS_TAU [@@deriving sexp]
      type ('dir_ref, 'file_ref, 'jimpl) ty_os_state (* = {
        oss_pid_table : (ty_pid, 'dir_ref per_process_state) Fs_prelude.fmap;
        oss_fid_table :
          (ty_fid, ('dir_ref, 'file_ref) fid_state) Fs_prelude.fmap;
        oss_group_table : (gid, uid Lem_support.finset) Fs_prelude.fmap;
        oss_fs_state : 'jimpl;
      } *)
      val os_state_to_fs_state : ('a, 'b, 'c) ty_os_state -> 'c
      (* the following is needed e.g. for functions like resolve that are used by testing, although resolve could now take the env directly from the state - except that permissions changes the env FIXME *)
      val os_state_to_env: ('a, 'b, 'c) ty_os_state -> ('a, 'b, 'c) environment 
      type monad_special_state =
          Impossible
        | Implementation_defined
        | Unspecified
        | Undefined
        | FIXME
      [@@deriving sexp]
      type ('impl, 'ja) monad_state =
          Normal_state of ('impl * 'ja)
        | Error_state of ('impl * error)
        | Special_state of (monad_special_state * string)
      val is_Normal_state : ('a, 'b) monad_state -> bool
      val is_Error_state : ('a, 'b) monad_state -> bool
      val is_Error_state_err : error -> ('a, 'b) monad_state -> bool
      val is_Special_state : ('a, 'b) monad_state -> bool
      val is_Impossible_state : ('a, 'b) monad_state -> bool
      val dest_Normal_state : ('a, 'b) monad_state -> 'a * 'b
      val dest_Error_state : ('a, 'b) monad_state -> 'a * error
      val dest_Special_state :
        ('a, 'b) monad_state -> monad_special_state * string
      val monad_state_shallow_eq :
        'a Lem_basic_classes.eq_class ->
        ('b, 'a) monad_state -> ('b, 'a) monad_state -> bool
      type ('dir_ref, 'file_ref, 'impl) os_state_or_special =
          OS_normal of ('dir_ref, 'file_ref, 'impl) ty_os_state
        | OS_special of (monad_special_state * string) [@@deriving sexp]
      val is_OS_normal : ('a, 'b, 'c) os_state_or_special -> bool
      val is_OS_special : ('a, 'b, 'c) os_state_or_special -> bool
      val dest_OS_normal :
        ('a, 'b, 'c) os_state_or_special -> ('a, 'b, 'c) ty_os_state
      val dest_OS_special :
        ('a, 'b, 'c) os_state_or_special -> monad_special_state * string
    end
  module Fs_arch :
    sig
(*
      val linux_int_of_open_flag : Fs_types.open_flag -> int32 option
      val posix_int_of_open_flag : Fs_types.open_flag -> int32 option
      val gen_arch_open_flags_of_int :
        (Fs_types.open_flag -> int32 option) ->
        int32 -> Fs_types.open_flag Lem_support.finset
      val linux_arch_open_flags_of_int :
        Fs_types.int_open_flags -> Fs_types.open_flag Lem_support.finset
      val posix_arch_open_flags_of_int :
        Fs_types.int_open_flags -> Fs_types.open_flag Lem_support.finset
      val gen_arch_int_of_open_flags :
        ('a -> int32 option) -> 'a Lem_support.finset -> int32
      val linux_arch_int_of_open_flags :
        Fs_types.open_flag Lem_support.finset -> int32
      val posix_arch_int_of_open_flags :
        Fs_types.open_flag Lem_support.finset -> int32
      val linux_arch_int_of_seek_command : Fs_types.seek_command -> int
      val posix_arch_int_of_seek_command : Fs_types.seek_command -> int
      val linux_arch_seek_command_of_int : int -> Fs_types.seek_command option
      val posix_arch_seek_command_of_int : int -> Fs_types.seek_command option
      val linux_arch : Fs_types.architecture
      val posix_test_arch : Fs_types.architecture
      val mac_os_x_test_arch : Fs_types.architecture
*)
      val architecture_of_ty_arch : Fs_types.ty_arch -> Fs_types.architecture
(*      val default_arch : Fs_types.ty_arch
      val is_linux_arch : ('a, 'b, 'c) Fs_types.environment -> bool
      val is_mac_os_x_arch : ('a, 'b, 'c) Fs_types.environment -> bool
      val arch_allows_dir_links : ('a, 'b, 'c) Fs_types.environment -> bool
*)
    end

  module Resolve :
    sig
      val split_path_string : string -> Fs_types.ty_name_list
      val path_starts_with_exactly_two_slashes : Fs_types.cstring -> bool
      val process_path :
        ('a, 'b, 'c) Fs_types.environment ->
        'c ->
        'a ->
        Fs_types.ty_os_command ->
        Fs_types.cstring -> ('a, 'b) Fs_types.res_name
      val process_path_from_root :
        ('a, 'b, 'c) Fs_types.environment ->
        'c ->
        Fs_types.ty_os_command ->
        Fs_types.cstring -> ('a, 'b) Fs_types.res_name
    end
  end (* Fs_spec_intf *)

module Dir_heap_intf : sig
  module Dir_heap_types :
    sig
      (* expose these types for testpath *)
      type dh_dir_ref = Dir_ref of Fs_spec_intf.Fs_types.inode
      type dh_file_ref = File_ref of Fs_spec_intf.Fs_types.inode 
      type dir_heap_state (* = {
        dhs_state_fs : dir_heap_state_fs;
        dhs_state_config : dir_heap_state_config;
      } *)
(*      val dh_initial_state : dir_heap_state *)
(*      type dh_environment =
          (dh_dir_ref, dh_file_ref, dir_heap_state)
          Fs_spec_intf.Fs_types.environment*)
      (* expose that this is ty_os_state, so we can use generic spec functions for dh_os_state *)
      type dh_os_state =
          (dh_dir_ref, dh_file_ref, dir_heap_state)
          Fs_spec_intf.Fs_types.ty_os_state
      type dh_os_state_or_special =
          (dh_dir_ref, dh_file_ref, dir_heap_state)
          Fs_spec_intf.Fs_types.os_state_or_special [@@deriving sexp]
    end
  module Dir_heap_ops :
    sig
      val dh_trans :
        Dir_heap_types.dh_os_state ->
        Fs_spec_intf.Fs_types.os_label ->
        Dir_heap_types.dh_os_state_or_special Lem_support.finset
      val dh_init_state : 
        Fs_spec_intf.Fs_types.ty_arch -> bool -> Dir_heap_types.dh_os_state
      (* FIXME not clear what this means when we are nondet on eg size
         of a directory; it should be understood that this is the
         allowable results "up to some notion of equivalence", where this
         notion is defined eg in os_trans_pid_core *)
      val dh_allowed_results_for_pid : 
        Fs_spec_intf.Fs_types.ty_pid ->
        Dir_heap_types.dh_os_state ->
        Fs_spec_intf.Fs_types.ret_value Fs_spec_intf.Fs_types.error_or_value Lem_support.finset
    end
end (* Dir_heap_intf *)

module Fs_dump_intf : sig
  type file = {
    file_path : string;
    file_node : int;
    file_size : int;
    file_sha : string;
  } [@@deriving sexp]
  type dir = { dir_path : string; dir_node : int; } [@@deriving sexp]
  type symlink = { link_path : string; link_val : string; } [@@deriving sexp]
  type error =
    Fs_spec_intf.Fs_types.error * string * string (* call, path *) [@@deriving sexp]
  type entry =
  | DE_file of file
  | DE_dir of dir
  | DE_symlink of symlink
  | DE_error of error
  [@@deriving sexp]
  val path : entry -> string
  type t = entry list [@@deriving sexp]
  val spec_dump_of_path :
    Dir_heap_intf.Dir_heap_types.dh_os_state -> string -> t
end (* Fs_dump_intf *)

module Fs_printer_intf : sig

  val string_of_perm : Fs_spec_intf.Fs_types.file_perm -> string
  val string_of_perm_opt :
    Fs_spec_intf.Fs_types.file_perm option -> string
  val string_of_bytes : Fs_spec_intf.Fs_types.ty_bytes -> string
  val string_of_name : string -> string
  val string_of_error : Fs_spec_intf.Fs_types.error -> string
  val string_of_arch : Fs_spec_intf.Fs_types.ty_arch -> string
  val string_of_flag : Fs_spec_intf.Fs_types.open_flag -> string
  val string_of_flags :
    Fs_spec_intf.Fs_types.open_flag Lem_support.finset -> string
  val string_of_int_flags :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.int_open_flags -> string
  val string_of_seek_command :
    Fs_spec_intf.Fs_types.seek_command -> string
  val string_of_int_seek_command :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.int_seek_command -> string
(*  val lem_of_int_seek_command : int -> string *)
  val string_of_cstring : Fs_spec_intf.Fs_types.cstring -> string
  val string_of_fd : Fs_spec_intf.Fs_types.ty_fd -> string
  val string_of_dh : Fs_spec_intf.Fs_types.ty_dh -> string
  val string_of_uid : Fs_spec_intf.Fs_types.uid -> string
  val string_of_gid : Fs_spec_intf.Fs_types.gid -> string
  val simple_string_of_uid : Fs_spec_intf.Fs_types.uid -> string
  val simple_string_of_gid : Fs_spec_intf.Fs_types.gid -> string
  val string_of_os_ext_cmd :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.ty_os_ext_command -> string
  val string_of_label :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.ty_os_command -> string
  val string_of_lbls :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.ty_os_command list -> string
  val string_of_kind : Fs_spec_intf.Fs_types.file_kind -> string
  val string_of_inode : Fs_spec_intf.Fs_types.inode -> string
  val string_of_monad_special_state :
    Fs_spec_intf.Fs_types.monad_special_state -> string
  val string_of_os_special_state :
    ('a, 'b, 'c) Fs_spec_intf.Fs_types.os_state_or_special ->
    string
  val string_of_ret_value :
    Fs_spec_intf.Fs_types.ret_value -> string
  val string_of_rv_error_or_value :
    Fs_spec_intf.Fs_types.ret_value
    Fs_spec_intf.Fs_types.error_or_value -> string
  val input_string_of_rv_error_or_value :
    Fs_spec_intf.Fs_types.ret_value
    Fs_spec_intf.Fs_types.error_or_value -> string
  val string_of_pid : Fs_spec_intf.Fs_types.ty_pid -> string
  val string_of_os_label :
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.os_label -> string
  val input_string_of_os_label :
    bool ->
    Fs_spec_intf.Fs_types.architecture ->
    Fs_spec_intf.Fs_types.os_label -> string
(*
  val lem_of_perm : Fs_spec_intf.Fs_types.file_perm -> string
  val lem_of_perm_opt :
    Fs_spec_intf.Fs_types.file_perm option -> string
  val lem_of_string : string -> string
  val lem_of_cstring : Fs_spec_intf.Fs_types.cstring -> string
  val lem_of_fd : Fs_spec_intf.Fs_types.ty_fd -> string
  val lem_of_uid : Fs_spec_intf.Fs_types.uid -> string
  val lem_of_gid : Fs_spec_intf.Fs_types.gid -> string
  val lem_of_int : int -> string
  val lem_of_int_flags : int32 -> string
  val lem_of_error : Fs_spec_intf.Fs_types.error -> string
  val lem_of_ret_value : Fs_spec_intf.Fs_types.ret_value -> string
  val lem_of_rv_error_or_value :
    Fs_spec_intf.Fs_types.ret_value
    Fs_spec_intf.Fs_types.error_or_value -> string
  val lem_of_os_label : 'a -> 'b
*)  
  
end (* Fs_printer_intf *)
