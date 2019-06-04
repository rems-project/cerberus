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

(* These are the basic types for producing dumps of a filesystem state. *)

(* basic types                       *)

open Sexplib.Std

type file = {
  file_path : string;
  file_node : int;
  file_size : int;
  file_sha  : string;
} with sexp

type dir = {
  dir_path : string;
  dir_node : int;
} with sexp

type symlink = {
  link_path : string;
  link_val  : string;
} with sexp

type error = Fs_spec.Fs_types.error * string * string (* call, path *)
with sexp

type entry =
| DE_file    of file
| DE_dir     of dir
| DE_symlink of symlink
| DE_error   of error
with sexp

let path = function
  | DE_file    { file_path = p }
  | DE_dir     { dir_path  = p }
  | DE_symlink { link_path = p }
  | DE_error   (_,_,p)           -> p

type t = entry list with sexp


(* dumping the spec state *)

(* The following code and types etc should be eliminated from the
   interface - we only need spec_dump_of_path function; we should also
   eliminate all the code below - making dumps of the spec is much
   simpler than dumping a real world fs *)

module Path = struct

type t = string list

let split_string delimiter name =
  let rec doit part acc =
    let open String in
    let len = length part in
    let idx = try index part delimiter with _ -> len in
    let fst = sub part 0 idx in
    let idx' = idx + 1 in
    if idx' <= len then
      let rt = sub part idx' (len - idx') in
      doit rt (fst :: acc)
    else
      fst :: acc
  in
  List.rev (doit name [])

let of_string : string -> t = split_string '/'
let to_string (p:t) : string = String.concat "/" p

let concat p1 p2 = match List.rev p1, p2 with
  | "" :: p1, "" :: p2 | "" :: p1, p2 | p1, "" :: p2 | p1, p2 ->
    List.rev_append p1 p2

let resolve path =
  let rec remove_dots parts outp = match parts, outp with
    | ".."::r, a::rt -> remove_dots r  rt
    | ".."::r, []    -> raise Not_found
    | "."::r , rt    -> remove_dots r  rt
    | r::rs  , rt    -> remove_dots rs (r :: rt)
    | []     , rt    -> List.rev rt
  in
  remove_dots path []

end



(* The module type [dump_fs_operations] abstracts the operations
   needed to greate a dump of a fs *)
module type Dump_fs_operations = sig  
  type state 
  type dir_status
  val ls_path : state -> Path.t -> string list
  val kind_of_path : state -> Path.t -> Unix.file_kind
  val sha1_of_path : state -> Path.t -> (int * string)
  val readlink : state -> Path.t -> string
  val inode_of_file_path : state -> Path.t -> int
  val inode_of_dir_path : state -> Path.t -> int
  val enter_dir : Path.t -> dir_status
  val leave_dir : Path.t -> dir_status -> unit
end

module Make(DO : Dump_fs_operations) = struct
  (* [find_of_path state path] returns the files and directories in a dir *)
  let find_of_path s0 p =
    let xs = List.map (fun n -> Path.concat p [n]) (DO.ls_path s0 p) in
    List.partition (fun p -> DO.kind_of_path s0 p <> Unix.S_DIR) xs

  let entry_of_path (s : DO.state) path =
    let path_s = Path.to_string path in
    try
      let k = DO.kind_of_path s path in
      match k with
      | Unix.S_REG ->
        let file_size, file_sha = DO.sha1_of_path s path in
        DE_file {
          file_path = path_s;
          file_node = DO.inode_of_file_path s path;
          file_size; file_sha;
        }
      | Unix.S_DIR -> DE_dir {
        dir_path = path_s; dir_node = DO.inode_of_dir_path s path;
      }
      | Unix.S_LNK -> DE_symlink {
        link_path = path_s; link_val = DO.readlink s path;
      }
      | _ -> failwith ("fs_dump iu0 impossible: we only deal with files, dirs and links" ^ path_s)
    with
    | e ->
      let exc = Printexc.to_string e in
      let bt  = Printexc.get_backtrace () in
      let msg = Printf.sprintf "unknown error for %s:\n%s\nBacktrace:\n%s"
        path_s exc bt
      in
      failwith ("fs_dump lcm impossible: "^msg)

  let rec entries_of_path (s : DO.state) (path : Path.t) : entry list =
    let path_status = DO.enter_dir path in
    let fs, sub_dirs = find_of_path s path in

    let des_direct = List.rev_map (entry_of_path s) (path :: fs) in
    let des_sub = List.flatten (List.map (entries_of_path s) sub_dirs) in
    DO.leave_dir path path_status;

    List.rev_append des_direct des_sub

  let of_path (s : DO.state) (path_s : string) : t =
    let path = Path.of_string path_s in
    entries_of_path s path

end

module Spec_dump_fs_ops (M : sig
  type state
  type dir_ref
  type file_ref
  val env : (dir_ref, file_ref, state) Fs_spec.Fs_types.environment 
end) : Dump_fs_operations with type state = M.state = struct

  open Sha1
  open Fs_dict_wrappers
  open Fs_spec.Fs_types
  open Fs_spec.Resolve
  module List_array = List_array


  type state = M.state
  type dir_status = unit

  (* we want to perform path resolution, but this is dependent on the
     command; here, we DON'T want to follow symlinks, which we force by
     using the OS_READLINK command, which indeed defaults to not
     following symlinks *)
  let dummy_os_command = OS_READLINK (CS_Null)

  let process_path_spec s0 path =
    let path_cs = CS_Some (Path.to_string path) in
    process_path_from_root M.env s0 dummy_os_command path_cs

  let readall (s0 : state) (p : Path.t) =
    try
      match process_path_spec s0 p with
      | RN_file (_, _, i0_ref, _) ->
         let (_, ret) = M.env.env_ops.fops_read s0 i0_ref in
         let bs = dest_RV_bytes ret in
         List_array.to_string bs
      | _ -> (failwith "fs_dump readall 1")
    with _ -> (failwith "fs_dump readall 2")

  let readlink s p = readall s p

  (* sha1 of contents of file *)
  let sha1_of_path s0 p =
    let s = readall s0 p in
    (String.length s, Sha1.to_hex (Sha1.string s))

  let get_stat (s0 : M.state) (p : Path.t) =
    try
      match process_path_spec s0 p with
      | RN_file (_, _, i0_ref, _) -> M.env.env_ops.fops_stat_file s0 i0_ref 
      | RN_dir (d0_ref, _) -> M.env.env_ops.fops_stat_dir s0 d0_ref 
      | _ -> (failwith "fs_dump get_stat 1")
    with _ -> (failwith "fs_dump get_stat 2")

  let inode_of_file_path s p =
    let st = get_stat s p in
    dest_Inode (st.st_ino)

  let inode_of_dir_path s p =
    let st = get_stat s p in
    dest_Inode (st.st_ino)

  let kind_of_path s p =
    let st = get_stat s p in
    match st.st_kind with
      | S_IFLNK -> Unix.S_LNK
      | S_IFDIR -> Unix.S_DIR
      | S_IFREG -> Unix.S_REG
      | _ -> (failwith "fs_dump dj1 impossible: kind_of_path")

  let ls_path (s0 : M.state) (p : Path.t) : string list =
    let path_cs = CS_Some (Path.to_string p) in
    let res_name = process_path_from_root
      M.env s0 dummy_os_command (* FIXME was true = follow_last_symlink *)
      path_cs
    in
    let d0_ref = match res_name with
      | RN_dir (d0_ref, _) -> d0_ref
      | _ -> (failwith "fs_dump cpk impossible: ls_path")
    in
    let _, es = M.env.env_ops.fops_readdir s0 d0_ref in
    es

  let enter_dir p = ()
  let leave_dir p () = ()

end

open Dir_heap.Dir_heap_types



open Fs_spec


module type R = sig val of_path: dir_heap_state -> string -> t end

let spec_dump_of_path : 
  dh_os_state ->
  string ->
  t
  = fun s0 p0 -> 
    let open Fs_spec.Fs_types in
    let env0 = s0.oss_env in
    let s0 = s0.oss_fs_state in
    (* the following is obviously awful!!!! don't use functors that are properly dependent on dynamic values *)
    let dump_ops = (module (Spec_dump_fs_ops (struct 
        type state = dir_heap_state
        type dir_ref = dh_dir_ref
        type file_ref = dh_file_ref
        let env = env0
      end)) : Dump_fs_operations with type state = dir_heap_state)
    in
    let dump = (module Make ((val dump_ops)) : R) in (* N.B. double brackets! *)
    let module Dump = (val dump) in
    Dump.of_path s0 p0

(*  let dump_of_path (s0:os_state) p = Dump.of_path s0.oss_fs_state p *)


