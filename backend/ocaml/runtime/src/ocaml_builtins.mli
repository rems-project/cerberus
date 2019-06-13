module M = Impl_mem

(* TODO: not sure about these types yet *)

val builtin_any_bounded_int: ('a -> 'b M.memM) -> M.integer_value -> M.integer_value -> 'b M.memM
val builtin_errno: ('a -> 'b M.memM) -> 'b M.memM
val builtin_printf: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_vprintf: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_vsnprintf: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'f -> 'b M.memM
val builtin_rename: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_exit: ('a -> 'b M.memM) -> 'b M.memM
val builtin_mkdir: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_stat: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_lstat: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_chmod: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_chown: ('a -> 'b M.memM) -> 'c -> 'd -> 'f -> 'b M.memM
val builtin_opendir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_open: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_write: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_pwrite: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_link: ('a -> 'b M.memM) -> 'c -> 'e -> 'b M.memM
val builtin_readlink: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_symlink: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_rmdir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_truncate: ('a -> 'b M.memM) -> 'c -> 'd -> 'b M.memM
val builtin_unlink: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_lseek: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_ctz: ('a -> 'b M.memM) -> 'b M.memM
val builtin_umask: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_chdir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_readdir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_rewinddir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_closedir: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_read: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
val builtin_close: ('a -> 'b M.memM) -> 'c -> 'b M.memM
val builtin_pread: ('a -> 'b M.memM) -> 'c -> 'd -> 'e -> 'b M.memM
