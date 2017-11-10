(* Created by Victor Gomes 2017-10-04 *)

(* Based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11" *)

module IdSet = Set.Make(String)

type context = IdSet.t

let cerb_builtin_types =
  [ "jmp_buf";        "sig_atomic_t";     "va_list";
    "ptrdiff_t";      "wchar_t";
    "int8_t";         "int16_t";        "int32_t";        "int64_t";
    "uint8_t";        "uint16_t";       "uint32_t";       "uint64_t";
    "int_least8_t";   "int_least16_t";  "int_least32_t";  "int_least64_t";
    "uint_least8_t";  "uint_least16_t"; "uint_least32_t"; "uint_least64_t";
    "int_fast8_t";    "int_fast16_t";   "int_fast32_t";   "int_fast64_t";
    "uint_fast8_t";   "uint_fast16_t";  "uint_fast32_t";  "uint_fast64_t";
    "intptr_t";       "uintptr_t";
    "intmax_t";       "uintmax_t";
    "size_t";         "ssize_t";
    "FILE";
    "fpos_t";
    "cnd_t";
    "thrd_t";
    "tss_t";          "mtx_t";
    "once_flag";
    "time_t";         "timer_t";        "clock_t";        "clockid_t";
    "suseconds_t";
    "blkcnt_t";       "blksize_t";
    "dev_t";          "fsblkcnt_t";     "fsfilcnt_t";
    "gid_t";          "id_t";           "uid_t";          "pid_t";
    "key_t";          "mode_t";         "ino_t";          "nlink_t";
    "nlink_t";        "off_t";
    "pthread_attr_t"; "pthread_barrier_t"; "pthread_barrierattr_t";
    "pthread_cond_t"; "pthread_condattr_t"; "pthread_key_t";
    "pthread_mutex_t"; "pthread_mutexattr_t"; "pthread_once_t";
    "pthread_rwloc_t"; "pthread_rwlockattr_t"; "pthread_spinlock_t";
    "pthread_t";
    "trace_attr_t";   "trace_event_id_t";   "trace_event_set_t";
    "trace_id_t";
  ]

let current =
  List.map (fun s -> "__cerbty_" ^ s) cerb_builtin_types
  |> IdSet.of_list
  |> ref

let declare_typedefname id =
  current := IdSet.add id !current

let declare_varname id =
  current := IdSet.remove id !current

let is_typedefname id =
  IdSet.mem id !current

let save_context () = !current

let restore_context ctxt =
  current := ctxt

type decl_sort =
  | DeclId
  | DeclFun of context
  | DeclOther

type declarator =
  { id:      string;
    sort:    decl_sort;
    pointer: Cabs.pointer_declarator option;
    direct:  Cabs.direct_declarator;
  }

let identifier decl = decl.id

let cabs_of_declarator d = Cabs.Declarator (d.pointer, d.direct)

let cabs_of_declarator_option = function
  | Some d -> Some (cabs_of_declarator d)
  | None -> None

let pointer_decl pdecl d =
  { d with pointer= Some pdecl;
           sort=    DeclOther;
  }

let identifier_decl loc str =
  { id=      str;
    sort=    DeclId;
    pointer= None;
    direct=  Cabs.DDecl_identifier (Cabs.CabsIdentifier (loc, str));
  }

let declarator_decl d =
  { d with direct= Cabs.DDecl_declarator (cabs_of_declarator d);
           sort=   DeclOther;
  }

let array_decl arrdecl d =
  { d with direct= Cabs.DDecl_array (d.direct, arrdecl);
           sort=   DeclOther;
  }

let fun_decl ptys ctxt d =
  { d with direct= Cabs.DDecl_function (d.direct, ptys);
           sort=   DeclFun ctxt;
  }

let reinstall_function_context d =
  match d.sort with
  | DeclFun ctxt -> restore_context ctxt; declare_varname d.id
  | _ -> ()
