/* A silly example of a tree with two node types that point at
   each other, the equivalent mutually-recursive datatype, and
   conversion of that type and some lemmas to Coq. */

#include <assert.h>
#include <stddef.h>
#include <limits.h>
#include "mutual_rec.h"

unsigned int global_val;

/* Walk a tree and sum the values. Only proven safe. */

void walk_b_tree (struct b_node *p);

void
walk_a_tree (struct a_node *p)
/*@ accesses global_val;
    requires take T = A_Tree (p);
    ensures take T2 = A_Tree (p); @*/
{
  if (! p)
    return;
  global_val += p->v;
  walk_b_tree(p->left);
  walk_b_tree(p->right);
}

void
walk_b_tree (struct b_node *p)
/*@ accesses global_val;
    requires take T = B_Tree (p);
    ensures take T2 = B_Tree (p); @*/
{
  if (! p)
    return;
  walk_a_tree(p->even);
  walk_a_tree(p->odd);
}
