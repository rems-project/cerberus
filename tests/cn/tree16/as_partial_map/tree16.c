

enum {
  NUM_NODES = 16,
  LEN_LIMIT = (1 << 16),
};

struct node;

typedef struct node * tree;

struct node {
  int v;
  tree nodes[NUM_NODES];
};

/*@
function (i32) num_nodes ()
@*/

int cn_get_num_nodes (void)
/*@ cn_function num_nodes; @*/
{
  return NUM_NODES;
}

/*@
datatype tree_arc {
  Arc_End {},
  Arc_Step {i32 i, datatype tree_arc tail}
}

datatype tree_node_option {
  Node_None {},
  Node {i32 v}
}

function (map<datatype tree_arc, datatype tree_node_option>) empty ()
function (map<datatype tree_arc, datatype tree_node_option>) construct
    (i32 v, map<i32, map<datatype tree_arc, datatype tree_node_option> > ts)

function (map<i32, map<datatype tree_arc, datatype tree_node_option> >) default_ns ()

predicate {map<datatype tree_arc, datatype tree_node_option> t,
        i32 v, map<i32, map<datatype tree_arc, datatype tree_node_option> > ns}
  Tree (pointer p)
{
  if (is_null(p)) {
    return {t: (empty ()), v: 0i32, ns: default_ns ()};
  }
  else {
    take P = Owned<struct node>(p);
    let V = P.v;
    let nodes_ptr = member_shift<node>(p,nodes);
    take Ns = each (i32 i; (0i32 <= i) && (i < (num_nodes ())))
      {Indirect_Tree(array_shift<tree>(nodes_ptr, i))};
    let t = construct (V, Ns);
    return {t: t, v: V, ns: Ns};
  }
}

predicate (map <datatype tree_arc, datatype tree_node_option>) Indirect_Tree (pointer p) {
  take V = Owned<tree>(p);
  take T = Tree(V);
  return T.t;
}

function (datatype tree_arc) mk_arc (map <i32, i32> m, i32 i, i32 len)

predicate {datatype tree_arc arc, map<i32, i32> xs}
        Arc (pointer p, i32 i, i32 len) {
  assert (0i32 <= len);
  assert (i <= len);
  assert (0i32 <= i);
  take Xs = each (i32 j; (0i32 <= j) && (j < len))
    {Owned(array_shift<signed int>(p, j))};
  assert (each (i32 j; (0i32 <= j) && (j < len))
    {(0i32 <= Xs[j]) && (Xs[j] < (num_nodes ()))});
  return {arc: mk_arc(Xs, i, len), xs: Xs};
}

lemma mk_arc_lemma (map <i32, i32> m, i32 i, i32 len)
  requires
    ((0i32 <= len) && (0i32 <= i) && (i <= len));
    len <= LEN_LIMIT;
  ensures (mk_arc(m, i, len)) ==
    (i < len ?
        Arc_Step {i: m[i], tail: mk_arc(m, i + 1i32, len)} :
        Arc_End {});

lemma empty_lemma (datatype tree_arc arc)
  requires true;
  ensures ((empty ())[arc]) == Node_None {};

function (datatype tree_node_option) construct_app_rhs (i32 v,
        map<i32, map<datatype tree_arc, datatype tree_node_option> > ns,
        datatype tree_arc arc)
{
  match arc {
    Arc_End {} => {
      Node {v: v}
    }
    Arc_Step {i: i, tail: tail} => {
     ns[i][tail]
    }
  }
}

function (boolean) arc_first_idx_valid (datatype tree_arc arc)
{
  match arc {
    Arc_End {} => {
      true
    }
    Arc_Step {i: i, tail: tail} => {
      (0i32 <= i) && (i < num_nodes())
    }
  }
}


lemma construct_lemma (i32 v,
        map<i32, map<datatype tree_arc, datatype tree_node_option> > ns,
        datatype tree_arc arc)
  requires
    arc_first_idx_valid(arc);
  ensures
    ((construct(v, ns))[arc]) == (construct_app_rhs(v, ns, arc));

@*/

int
lookup_rec (tree t, int *path, int i, int path_len, int *v)
/*@ requires
             path_len <= LEN_LIMIT;
             take T = Tree(t);
             take Xs = each (i32 j; (0i32 <= j) && (j < path_len))
                            {Owned(array_shift(path, j))};
             ((0i32 <= path_len) && (0i32 <= i) && (i <= path_len));
             each (i32 j; (0i32 <= j) && (j < path_len))
                  {(0i32 <= (Xs[j])) && ((Xs[j]) < (num_nodes ()))};
             take V = Owned(v);
             let arc = mk_arc(Xs, i, path_len);
    ensures take T2 = Tree(t);
            T2.t == {T.t}@start;
            take Xs2 = each (i32 j; (0i32 <= j) && (j < path_len))
                            {Owned(array_shift(path, j))};
            Xs2 == {Xs}@start;
            take V2 = Owned(v);
            ((return == 0i32) && ((T2.t[arc]) == Node_None {}))
              || ((return == 1i32) && ((T2.t[arc]) == Node {v: V2})); @*/
{
  int idx = 0;
  int r = 0;
  if (! t) {
    /*@ apply empty_lemma(arc); @*/
    return 0;
  }
  if (i >= path_len) {
    *v = t->v;
    /*@ apply mk_arc_lemma(Xs, i, path_len); @*/
    /*@ apply construct_lemma (T.v, T.ns, arc); @*/
    return 1;
  }
  /*@ apply mk_arc_lemma(Xs, i, path_len); @*/
  /*@ extract Owned<int>, i; @*/
  /*@ instantiate i; @*/
  idx = path[i];
  /*@ extract Indirect_Tree, idx; @*/
  r = lookup_rec(t->nodes[idx], path, i + 1, path_len, v);
  /*@ apply construct_lemma (T.v, T.ns, arc); @*/
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
  || ((return == 1) && ((T2.t[A2.arc]) == Node {v: V2})) @*/
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

