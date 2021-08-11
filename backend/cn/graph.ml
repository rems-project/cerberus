(* this is not space efficient: the edges duplicate the node data *)


module type I = sig

  type t
  val compare : t -> t -> int
  val equal : t -> t -> bool

end


module type S = sig

  type node
  type 'label t
  val empty : 'label t
  val add_node : node -> 'label t -> 'label t
  val find_node_opt : (node -> bool) -> 'label t -> node option
  val find_node : (node -> bool) -> 'label t -> node
  val exists_node : (node -> bool) -> 'label t -> bool
  val remove_node : node -> 'label t -> 'label t
  val add_edge : node * node -> 'label -> 'label t -> 'label t
  val find_edge_opt : (node * node -> bool) -> 'label t -> ((node * node) * 'label) option
  val find_edge : (node * node -> bool) -> 'label t -> (node * node) * 'label
  val have_edge : node * node -> 'label t -> bool
  val exists_edge : (node * node -> 'label -> bool) -> 'label t -> bool
  val fold_edges : (node * node -> 'label -> 'a -> 'a) -> 'label t -> 'a -> 'a
  val remove_edge : node * node -> 'label t -> 'label t
  val edge_label : node * node -> 'label t -> 'label option
  val linearise : 'label t -> node list

end



module Make(V : I) : (S with type node = V.t) = struct

  type node = V.t

  module VPair = struct 
    type t = node * node
    let compare a b = 
      Lem_basic_classes.pairCompare V.compare V.compare a b
  end

  module VRelMap = Map.Make(VPair)

  type 'label t = { 
      nodes : node list;
      edges : 'label VRelMap.t;
    }

  let empty = 
    { nodes = []; edges = VRelMap.empty }

  let add_node n g = 
    { g with nodes = n :: g.nodes }
  
  let find_node_opt f g = 
    List.find_opt f g.nodes

  let find_node f g = 
    List.find f g.nodes

  let exists_node f g = 
    List.exists f g.nodes

  let remove_node n g = 
    { g with nodes = List.filter (fun n' -> not (V.equal n n')) g.nodes }

  let find_edge_opt f g = 
    VRelMap.find_first_opt f g.edges

  let find_edge f g = 
    VRelMap.find_first f g.edges

  let have_edge (n1, n2) g = 
    VRelMap.mem (n1, n2) g.edges

  let add_edge (n1, n2) label g = 
    { g with edges = VRelMap.add (n1, n2) label g.edges }

  let exists_edge f g = 
    VRelMap.exists f g.edges

  let fold_edges f g a = 
    VRelMap.fold f g.edges a

  let remove_edge (n1, n2) g = 
    { g with edges = VRelMap.remove (n1, n2) g.edges }

  let edge_label (n1, n2) g = 
    VRelMap.find_opt (n1, n2) g.edges

  let linearise graph = 
    let no_incoming_edges graph n = 
      not (exists_edge (fun (_, n2) _ -> V.equal n n2) graph)
    in
    let order = [] in
    let inits, others = List.partition (no_incoming_edges graph) graph.nodes in
    let rec aux graph inits others order =
      match inits with
      | [] -> (List.rev order, others)
      | init :: inits ->
         let order = init :: order in
         let (graph, inits, others) = 
           fold_edges (fun (n1, n2) _ (graph, inits, others) ->
               if V.equal init n1 then
                 let graph = remove_edge (n1, n2) graph in
                 let new_inits, others = List.partition (no_incoming_edges graph) others in
                 (graph, inits @ new_inits, others)
               else 
                 (graph, inits, others)
             ) graph (graph, inits, others)
         in
         aux graph inits others order
    in
    let (order, not_yet_ordered) = aux graph inits others order in
    order @ not_yet_ordered



end
