(** [c_file_to_ail includes nostdinc fname] uses Cerberus to preprocess, parse
    and also type-check the C source file [fname]. All the directory in of the
    [includes] list are passed to the C preprocessor through the ["-I"] option
    (they are hence searched for header files). If [nostdinc] then the default
    system directories are not searched for header files. In case of error, an
    a message is displayed and the program exits with error code [-1]. *)
val c_file_to_ail : string list -> bool -> string -> Ail_to_coq.typed_ail

(** [cpp_lines includes nostdinc fname] preprocesses the C source file [fname]
    using Cerberus, and returns the list of the lines of the output. The flags
    [includes] and [nostdinc] have the same effect as for [c_file_to_ail]. *)
val cpp_lines : string list -> bool -> string -> string list
