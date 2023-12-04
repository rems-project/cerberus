

struct tree_node {
  int v;
  struct tree_node *left;
  struct tree_node *right;
};

/*@
predicate {integer size} Tree (pointer p) {
  if (is_null(p)) {
    return { size: 0 };
  }
  else {
    take point = Owned<struct tree_node>(p);
    take left = Tree (point.left);
    take right = Tree (point.right);
    return { size: left.size + right.size + 1 };
  }
}
@*/

#define NULL ((void *)0)

struct tree_node *
rev_tree (struct tree_node *t)
/*@ requires take T = Tree(t) @*/
/*@ ensures take T2 = Tree(return) @*/
{
  struct tree_node *tmp;

  if (t == NULL) {
    return t;
  }


  tmp = rev_tree (t->left);
  t->left = rev_tree (t->right);
  t->right = tmp;


  return t;
}

