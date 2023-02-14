

enum {
  NUM_NODES = 16
};

struct node;

typedef struct node * tree;

struct node {
  int v;
  tree nodes[NUM_NODES];
};

#ifdef CN_MODE
#define CN(foo) foo
#else
#define CN(foo)
#endif

#ifdef CN_MODE

function (integer) num_nodes ()

int cn_get_num_nodes (void)
/*@ cn_function num_nodes @*/
{
  return NUM_NODES;
}

datatype tree {
  Empty_Tree {},
  Node {integer v, list <datatype tree> children}
}

function (map <integer, datatype tree>) default_children ()

predicate {datatype tree t, integer v, map <integer, datatype tree> children}
  Tree (pointer p)
{
  if (p == NULL) {
    return {t = Empty_Tree {}, v = 0, children = default_children ()};
  }
  else {
    let V = Owned<int>((pointer)(((integer)p) + (offsetof (node, v))));
    let nodes_ptr = ((pointer)((((integer)p) + (offsetof (node, nodes)))));
    let Ns = each (integer i; (0 <= i) && (i < (num_nodes ())))
      {Indirect_Tree((pointer)(((integer)nodes_ptr) + (i * (sizeof <tree>))))};
    let ts = array_to_list (Ns.t, 0, num_nodes ());
    return {t = Node {v = V.value, children = ts}, v = V.value, children = Ns.t};
  }
}

predicate {datatype tree t} Indirect_Tree (pointer p) {
  let V = Owned<tree>(p);
  let T = Tree(V.value);
  return {t = T.t};
}

datatype arc_in_array {
  Arc_In_Array {map <integer, integer> arr, integer i, integer len}
}

function (boolean) in_tree (datatype tree t, datatype arc_in_array arc)
function (integer) tree_v (datatype tree t, datatype arc_in_array arc)


void
in_tree_tree_v_lemma (tree t, int *path, int i, int path_len)
/*@ trusted @*/
/*@ requires let T = Tree(t) @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < path_len))
    {Owned<typeof(i)>(path + (j * 4))} @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures T2.children == {T.children}@start @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < path_len))
    {Owned<typeof(i)>(path + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures let arc = Arc_In_Array {arr = Xs2.value, i = i, len = path_len} @*/
/*@ ensures let arc2 = Arc_In_Array {arr = Xs2.value, i = i + 1, len = path_len} @*/
/*@ ensures (in_tree(T2.t, arc)) == ((T2.t ?? (Node {}))
    ? ((i >= path_len) ? true
        : (in_tree(nth_list(Xs2.value[i], T2.t.children, Empty_Tree {}), arc2)))
    : false) @*/
/*@ ensures (tree_v(T2.t, arc)) == ((T2.t ?? (Node {}))
    ? ((i >= path_len) ? (T2.t.v)
        : (tree_v(nth_list(Xs2.value[i], T2.t.children, Empty_Tree {}), arc2)))
    : 0) @*/
{
}

#endif

int
lookup_rec (tree t, int *path, int i, int path_len, int *v)
/*@ requires let T = Tree(t) @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < path_len))
    {Owned<typeof(i)>(path + (j * 4))} @*/
/*@ requires ((0 <= path_len) && (0 <= i) && (i <= path_len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < path_len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ requires let V = Owned(v) @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures T2.children == {T.children}@start @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < path_len))
    {Owned<typeof(i)>(path + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures let V2 = Owned(v) @*/
/*@ ensures let arc = Arc_In_Array {arr = Xs2.value, i = i, len = path_len} @*/
/*@ ensures ((return == 0) && (not (in_tree (T2.t, arc))))
  || ((return == 1) && (in_tree (T2.t, arc)) && ((tree_v (T2.t, arc)) == V2.value)) @*/
{
  int idx = 0;
  int r = 0;
  if (! t) {
    CN(unpack Tree(t));
    CN(in_tree_tree_v_lemma(t, path, i, path_len));
    return 0;
  }
  if (i >= path_len) {
    *v = t->v;
    CN(in_tree_tree_v_lemma(t, path, i, path_len));
    return 1;
  }
  CN(instantiate i);
  idx = path[i];
  CN(unpack Tree(t));
  CN(unpack Indirect_Tree(t->nodes + idx));
  r = lookup_rec(t->nodes[idx], path, i + 1, path_len, v);
  CN(pack Indirect_Tree(t->nodes + idx));
  CN(in_tree_tree_v_lemma(t, path, i, path_len));
  CN(unpack Tree(t));
  if (r)
    return 1;
  else
    return 0;
}

#ifdef NOT_CURRENTLY_WORKING
int
lookup (tree t, int *path, int path_len, int *v)
/*@ requires let T = Tree(t) @*/
/*@ requires let A = Arc(path, 0, path_len) @*/
/*@ requires let V = Owned(v) @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures let A2 = Arc(path, 0, path_len) @*/
/*@ ensures A2.arc == {A.arc}@start @*/
/*@ ensures let V2 = Owned(v) @*/
/*@ ensures ((return == 0) && ((T2.t[A2.arc]) == Node_None {}))
  || ((return == 1) && ((T2.t[A2.arc]) == Node {v = V2.value})) @*/
{
  int i;

  for (i = 0; i < path_len; i ++)
  {
    if (! t) {
      return 0;
    }
    t = t->nodes[path[i]];
  }
  if (! t) {
    return 0;
  }
  *v = t->v;
  return 1;
}
#endif

