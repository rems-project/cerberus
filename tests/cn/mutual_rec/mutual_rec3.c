/* A silly example of a tree with two node types that point at
   each other, the equivalent mutually-recursive datatype, and
   conversion of that type and some lemmas to Coq. */

#include <assert.h>
#include <stddef.h>
#include <limits.h>
#include "mutual_rec.h"


/* Coerce a tree to encode a particular value, if it is of the right shape. If
   of the wrong shape, return NULL. Proven to return exactly the right value,
   if not NULL. */

struct a_node *
predef_a_tree (struct a_node *p)
/*@ requires take T = A_Tree (p); @*/
/*@ ensures take T2 = A_Tree (p); @*/
/*@ ensures is_null(return) || (T2.t == A_Node {k: 1i32, v: 0i32,
    left: B_Node {even: A_Leaf {}, odd: A_Leaf {}}, right: B_Leaf {}}); @*/
{
  struct b_node *l = NULL;
  if (! p || ! p->left || p->right) {
    return NULL;
  }
  l = p->left;
  if (l->odd || l->even) {
    return NULL;
  }
  p->k = 1;
  p->v = 0;
  return p;
}
