

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
/*@ requires take T = Tree(t);
    ensures take T2 = Tree(return); @*/
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

/*

      Tree:

        2
    /      \
   1         3
  / \       /  \
null null  null  4
                / \
              null null

*/

int main(void)
/*@ trusted; @*/
{
  struct tree_node l = {.v = 1, .left = 0, .right = 0};
  struct tree_node r2 = {.v = 4, .left = 0, .right = 0};
  struct tree_node r = {.v = 3, .left = 0, .right = &r2};
  struct tree_node tree = {.v = 2, .left = &l, .right = &r};

  struct tree_node *reversed_tree = rev_tree(&tree);
}
