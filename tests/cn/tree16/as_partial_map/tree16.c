

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

datatype tree_arc {
  Arc_End {},
  Arc_Step {integer i, datatype tree_arc tail}
}

datatype tree_node_option {
  Node_None {},
  Node {integer v}
}

function (map<datatype tree_arc, datatype tree_node_option>) empty ()
function (map<datatype tree_arc, datatype tree_node_option>) construct
    (integer v, map<integer, map<datatype tree_arc, datatype tree_node_option> > ts)

function (map<integer, map<datatype tree_arc, datatype tree_node_option> >) default_ns ()

predicate {map<datatype tree_arc, datatype tree_node_option> t,
        integer v, map<integer, map<datatype tree_arc, datatype tree_node_option> > ns}
  Tree (pointer p)
{
  if (p == NULL) {
    return {t = (empty ()), v = 0, ns = default_ns ()};
  }
  else {
    let V = Owned<int>((pointer)(((integer)p) + (offsetof (node, v))));
    let nodes_ptr = ((pointer)((((integer)p) + (offsetof (node, nodes)))));
    let Ns = each (integer i; (0 <= i) && (i < (num_nodes ())))
      {Indirect_Tree((pointer)(((integer)nodes_ptr) + (i * (sizeof <tree>))))};
    let t = construct (V.value, Ns.t);
    return {t = t, v = V.value, ns = Ns.t};
  }
}

predicate {map<datatype tree_arc, datatype tree_node_option> t} Indirect_Tree (pointer p) {
  let V = Owned<tree>(p);
  let T = Tree(V.value);
  return {t = T.t};
}

function (datatype tree_arc) mk_arc (map <integer, integer> m, integer i, integer len)

predicate {datatype tree_arc arc, map<integer, integer> xs}
        Arc (pointer p, integer i, integer len) {
  assert (0 <= len);
  assert (i <= len);
  assert (0 <= i);
  let Xs = each (integer j; (0 <= j) && (j < len))
    {Owned<signed int>(p + (j * sizeof<signed int>))};
  assert (each (integer j; (0 <= j) && (j < len))
    {(0 <= (Xs.value)[j]) && ((Xs.value)[j] < (num_nodes ()))});
  return {arc = mk_arc(Xs.value, i, len), xs = Xs.value};
}

void
mk_arc_end_lemma (int *xs, int i, int len)
/*@ trusted @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < len))
    {Owned<int>(xs + (j * 4))} @*/
/*@ requires ((0 <= len) && (0 <= i) && (i <= len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ requires i >= len @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < len))
    {Owned<int>(xs + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures (mk_arc(Xs2.value, i, len)) == Arc_End {} @*/
{}

void
mk_arc_step_lemma (int *xs, int i, int len)
/*@ trusted @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < len))
    {Owned<int>(xs + (j * 4))} @*/
/*@ requires ((0 <= len) && (0 <= i) && (i <= len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ requires i < len @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < len))
    {Owned<int>(xs + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures (mk_arc(Xs2.value, i, len)) ==
    Arc_Step {i = Xs2.value[i], tail = mk_arc(Xs2.value, i + 1, len)} @*/
{}

void
empty_lemma (int *path, int i, int path_len)
/*@ trusted @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ requires ((0 <= path_len) && (0 <= i) && (i <= path_len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < path_len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures ((empty ())[mk_arc(Xs2.value, i, path_len)]) == Node_None {} @*/
{
}

void
construct_empty_lemma (tree t)
/*@ trusted @*/
/*@ requires let T = Tree(t) @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures T2.v == {T.v}@start @*/
/*@ ensures T2.ns == {T.ns}@start @*/
/*@ ensures ((construct (T2.v, T2.ns))[Arc_End {}]) == Node {v = T2.v} @*/
{
}

void
construct_step_lemma (tree t, int *path, int i, int path_len, int idx)
/*@ trusted @*/
/*@ requires let T = Tree(t) @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ requires ((0 <= path_len) && (0 <= i) && (i <= path_len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < path_len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ requires (0 <= idx) && (idx < (num_nodes ())) @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures T2.v == {T.v}@start @*/
/*@ ensures T2.ns == {T.ns}@start @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures ((construct (T2.v, T2.ns))[Arc_Step
        {i = idx, tail = mk_arc(Xs2.value, i + 1, path_len)}]) ==
  ((T2.ns[idx])[mk_arc(Xs2.value, i + 1, path_len)]) @*/
{
}


#endif

int
lookup_rec (tree t, int *path, int i, int path_len, int *v)
/*@ requires let T = Tree(t) @*/
/*@ requires let Xs = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ requires ((0 <= path_len) && (0 <= i) && (i <= path_len)) @*/
/*@ requires each (integer j; (0 <= j) && (j < path_len))
    {(0 <= ((Xs.value)[j])) && (((Xs.value)[j]) < (num_nodes ()))} @*/
/*@ requires let V = Owned(v) @*/
/*@ ensures let T2 = Tree(t) @*/
/*@ ensures T2.t == {T.t}@start @*/
/*@ ensures let Xs2 = each (integer j; (0 <= j) && (j < path_len))
    {Owned<int>(path + (j * 4))} @*/
/*@ ensures Xs2.value == {Xs.value}@start @*/
/*@ ensures let V2 = Owned(v) @*/
/*@ ensures ((return == 0) && ((T2.t[mk_arc(Xs2.value, i, path_len)]) == Node_None {}))
  || ((return == 1) && ((T2.t[mk_arc(Xs2.value, i, path_len)]) == Node {v = V2.value})) @*/
{
  int idx = 0;
  int r = 0;
  if (! t) {
    CN(unpack Tree(t));
    empty_lemma(path, i, path_len);
    return 0;
  }
  if (i >= path_len) {
    *v = t->v;
    mk_arc_end_lemma(path, i, path_len);
    construct_empty_lemma (t);
    return 1;
  }
  CN(mk_arc_step_lemma(path, i, path_len));
  CN(instantiate i);
  idx = path[i];
  CN(unpack Tree(t));
  CN(unpack Indirect_Tree(t->nodes + idx));
  r = lookup_rec(t->nodes[idx], path, i + 1, path_len, v);
  CN(pack Indirect_Tree(t->nodes + idx));
  construct_step_lemma (t, path, i, path_len, idx);
  return r;
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

