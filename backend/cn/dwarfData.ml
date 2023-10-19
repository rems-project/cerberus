open Analyse
open BinaryVerificationTypes
open BinaryVerificationTypes.Make(Typing)
open Dwarf
module StringMap = Map.Make(String)

let function_ranges filename_elf filename_objdump =
  let elf_test = Elf.parse_elf_file filename_elf in
  let analysis = Collected.mk_analysis elf_test filename_objdump None in
  let compilation_units = analysis.sdt.Dwarf.sd_compilation_units in
  let subroutines = List.concat_map (fun cu -> cu.scu_subroutines) compilation_units in
  List.fold_left (fun m ss ->
      let m_option =
        let open Option in
        let@ fname = ss.ss_name in
        let@ pc_ranges = ss.ss_pc_ranges in
        return @@ StringMap.add fname pc_ranges m
      in Option.value m_option ~default:m
    ) StringMap.empty subroutines

let rec fromToZ step (a, b) =
  let a' = Z.add a (Z.of_int step) in
  if Z.geq a b
    then []
    else a :: fromToZ step (a', b)

let get_instructions fsym f = when_args_exist @@ fun args ->
  let fns_map = function_ranges args.filename_elf args.filename_objdump in
  let fname = Sym.pp_string fsym in
  let instr_ranges = StringMap.find fname fns_map in
  f @@ List.concat_map (fromToZ 4) instr_ranges


let rec last = function
  | [] -> assert false
  | [x] -> x
  | _ :: xs -> last xs


let map_third f (a, b, c) = (a, b, f c)

let function_graphs args =
  let elf_test = Elf.parse_elf_file args.filename_elf in
  let analysis = Collected.mk_analysis elf_test args.filename_objdump None in
  CallGraph.mk_call_graph elf_test analysis


let call_graph_find_fname fname graph =
  List.find (fun ((_, _, fnames), _) -> Stdlib.List.mem fname fnames) graph

let call_graph_find_index index graph =
  List.find (fun ((_, index', _), _) -> index == index') graph


let get_callees fsym f = when_args_exist @@ fun args ->
  let call_graph, _call_graph_transitive = function_graphs args in
  let fname = Sym.pp_string fsym in
  let _caller, callees = call_graph_find_fname fname call_graph in
  let callees = List.map (fun (addr, _index, fnames) -> (addr, last fnames)) callees in
  f callees


(** Caution! Function does not check for recursion (cycles in the graph). Will loop on recursive inputs *)
let rec max_call_depth graph caller_index =
  let _caller, callees = call_graph_find_index caller_index graph in
  let m = List.fold_left (fun prev_max (_addr, callee_index, _fnames) ->
    max_call_depth graph callee_index |> max prev_max) 0 callees
  in m + 1

let get_stack_size fsym f = when_args_exist_m @@ fun args ->
  let _call_graph, call_graph_transitive = function_graphs args in
  let fname = Sym.pp_string fsym in
  let (_addr, index, _fnames), callees = call_graph_find_fname fname call_graph_transitive in
  let single_stack_size = 128 in
  f @@ max_call_depth call_graph_transitive index * single_stack_size