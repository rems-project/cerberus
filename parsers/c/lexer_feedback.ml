(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2017                                                              *)
(*    Victor Gomes                                                                  *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(************************************************************************************)

(* Based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11" *)

open Cerb_frontend

module IdSet = Set.Make(String)

type context = IdSet.t

let cerb_builtin_types =
  [ "jmp_buf";        "sig_atomic_t";     "va_list";
    "ptrdiff_t";      "wchar_t";
    "int8_t";         "int16_t";        "int32_t";        "int64_t";          "int128_t";
    "uint8_t";        "uint16_t";       "uint32_t";       "uint64_t";         "uint128_t";
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
(* TODO(KKK): talk to victor *)
    "max_align_t"
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
  | DeclFunIds of context * Symbol.identifier list
  | DeclPtr of Cabs.pointer_declarator
  | DeclOther
and declarator =
  { id:      string;
    sort:    decl_sort;
    direct:  Cabs.direct_declarator;
  }

let identifier decl = decl.id

let cabs_of_declarator d =
  match d.sort with
  | DeclPtr p -> Cabs.Declarator (Some p, d.direct)
  | _ -> Cabs.Declarator (None, d.direct)

let cabs_of_declarator_option = function
  | Some d -> Some (cabs_of_declarator d)
  | None -> None

let pointer_decl pdecl d =
  { d with sort=    DeclPtr pdecl;
  }

let identifier_decl attrs (Symbol.Identifier(_, str) as i) =
  { id=      str;
    sort=    DeclId;
    direct=  Cabs.DDecl_identifier (attrs, i);
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

let fun_ids_decl ids_opt ctxt d =
  { d with direct= Cabs.DDecl_function (d.direct, Params ([], false));
           sort=   DeclFunIds (ctxt, ids_opt);
  }

let reinstall_function_context d =
  match d.sort with
  | DeclFun ctxt -> restore_context ctxt; declare_varname d.id
  | _ -> ()

let create_function_definition loc attr_opt specifs d stmt rev_dlist_opt =
  let xs = match attr_opt with
    | None ->
        []
    | Some z ->
        List.map (fun ((ns, id), args_opt) ->
          let open Annot in
          { attr_ns=   ns
          ; attr_id=   id
          ; attr_args= match args_opt with None -> [] | Some z -> z }
        ) (List.concat z) in
  match d.sort, rev_dlist_opt with
  | DeclFunIds (_, ids), None ->
    let open Cabs in
    let signed_int_specifiers =
      { storage_classes= [];
        type_specifiers= [TSpec (Location_ocaml.unknown, TSpec_int)];
        type_qualifiers= [];
        function_specifiers= [];
        alignment_specifiers= [];
      } in
    let params = List.map (fun id ->
        PDeclaration_decl (signed_int_specifiers,
                           Declarator (None,  DDecl_identifier (Annot.no_attributes, id)))
      ) ids in
    let direct_declarator =
      match d.direct with
      | DDecl_function (ddecl, _) -> DDecl_function (ddecl, Params (params, false))
      | _ -> assert false in
    let decl = Cabs.Declarator (None, direct_declarator) in
    Cabs.FunDef (loc, Annot.Attrs xs, specifs, decl, stmt)
  | DeclFunIds (_, ids), Some rev_dlist ->
    assert false
  | _, _ ->
    Cabs.FunDef (loc, Annot.Attrs xs, specifs, cabs_of_declarator d, stmt)

