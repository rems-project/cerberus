/* The a/b node types. */

struct a_node;
struct b_node;

struct a_node {
  int k;
  int v;
  struct b_node *left;
  struct b_node *right;
};

struct b_node {
  struct a_node *even;
  struct a_node *odd;
};

/* The A/B tree types as datatypes. */

/*@
datatype a_tree {
  A_Leaf {},
  A_Node {i32 k, i32 v, datatype b_tree left, datatype b_tree right}
}

datatype b_tree {
  B_Leaf {},
  B_Node {datatype a_tree even, datatype a_tree odd}
}
@*/

/* The predicates relating A/B trees to their C encoding. */

/*@
predicate {datatype a_tree t} A_Tree (pointer p) {
  if (is_null(p)) {
    return {t: A_Leaf {}};
  }
  else {
    take V = RW<struct a_node>(p);
    assert ((is_null(V.left) || !addr_eq(V.left, NULL))
      && (is_null(V.right) || !addr_eq(V.right, NULL)));
    take L = B_Tree(V.left);
    take R = B_Tree(V.right);
    return {t: A_Node {k: V.k, v: V.v, left: L.t, right: R.t}};
  }
}

predicate {datatype b_tree t} B_Tree (pointer p) {
  if (is_null(p)) {
    return {t: B_Leaf {}};
  }
  else {
    take V = RW<struct b_node>(p);
    assert ((is_null(V.even) || !addr_eq(V.even, NULL))
      && (is_null(V.odd) || !addr_eq(V.odd, NULL)));
    take E = A_Tree(V.even);
    take O = A_Tree(V.odd);
    return {t: B_Node {even: E.t, odd: O.t}};
  }
}
@*/
