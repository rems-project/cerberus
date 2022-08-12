

struct tree_node {
  int v;
  struct tree_node *left;
  struct tree_node *right;
};

predicate {integer size} Tree (pointer p) {
  if ( p == NULL ) {
    return { size = 0 };
  }
  else {
    let point = Owned<struct tree_node>(p);
    let left = Tree (point.value.left);
    let right = Tree (point.value.right);
    return { size = left.size + right.size + 1 };
  }
}

#define NULL ((void *)0)

[[cn::requires("Tree(t)")]]
[[cn::ensures("Tree(return)")]]
struct tree_node *
rev_tree (struct tree_node *t) {
  struct tree_node *tmp;

  if (t == NULL) {
    return t;
  }

  unpack Tree (t);

  tmp = rev_tree (t->left);
  t->left = rev_tree (t->right);
  t->right = tmp;

  pack Tree (t);

  return t;
}

