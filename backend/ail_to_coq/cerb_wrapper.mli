(** [c_file_to_ail fname] uses the Cerberus frontend to preprocess, parse, and
    type-check the C source file [fname]. In case of error an error message is
    displayed and the program fails with error code [-1]. *)
val c_file_to_ail : string -> Ail_to_coq.typed_ail
