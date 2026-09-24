module Fs_error : sig
  type t
  val to_sexp : t -> Sexplib0.Sexp.t
end

module Fs_state : sig
  type t
  val initial_state : t
  val to_sexp : t -> Sexplib0.Sexp.t
end

type fs_stat
val fs_dev : fs_stat -> Z.t
val fs_ino : fs_stat -> Z.t
val fs_mode : fs_stat -> Z.t
val fs_nlink : fs_stat -> Z.t
val fs_uid : fs_stat -> Z.t
val fs_gid : fs_stat -> Z.t
val fs_rdev : fs_stat -> Z.t
val fs_size : fs_stat -> Z.t
(*
val fs_atime : fs_stat -> Z.t
val fs_mtime : fs_stat -> Z.t
val fs_ctime : fs_stat -> Z.t
*)
val run_mkdir : Fs_state.t -> string -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_open : Fs_state.t -> string -> Z.t -> Z.t option -> Fs_state.t * (Fs_error.t, int) Either.either
val run_close : Fs_state.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_write : Fs_state.t -> Z.t -> char list -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_read : Fs_state.t -> Z.t -> Z.t -> Fs_state.t * (Fs_error.t, char list) Either.either
val run_pwrite : Fs_state.t -> Z.t -> char list -> Z.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_pread : Fs_state.t -> Z.t -> Z.t -> Z.t -> Fs_state.t * (Fs_error.t, char list) Either.either
val run_rename : Fs_state.t -> string -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_umask : Fs_state.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_chmod : Fs_state.t -> string -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_chdir : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_chown : Fs_state.t -> string -> Z.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_link : Fs_state.t -> string -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_readlink : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, char list) Either.either
val run_symlink : Fs_state.t -> string -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_rmdir : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_truncate : Fs_state.t -> string -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_unlink : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_lseek : Fs_state.t -> Z.t -> Z.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
val run_stat : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, fs_stat) Either.either
val run_lstat : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, fs_stat) Either.either
val run_opendir : Fs_state.t -> string -> Fs_state.t * (Fs_error.t, int) Either.either
val run_readdir : Fs_state.t -> Z.t -> Fs_state.t * (Fs_error.t, char list) Either.either
val run_rewinddir : Fs_state.t -> Z.t -> Fs_state.t
val run_closedir : Fs_state.t -> Z.t -> Fs_state.t * (Fs_error.t, int) Either.either
