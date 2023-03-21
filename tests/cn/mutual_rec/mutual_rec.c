/* A silly example of a tree with two node types that point at
   each other, the equivalent mutually-recursive datatype, and
   conversion of that type and some lemmas to Coq. */

#include <assert.h>
#include <stddef.h>
#include <limits.h>



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

#ifdef CN_MODE
#define CN(foo) foo
#else
#define CN(foo)
#endif

#ifdef CN_MODE

/* The A/B tree types as datatypes. */

datatype a_tree {
  A_Leaf {},
  A_Node {integer k, integer v, datatype b_tree left, datatype b_tree right}
}

datatype b_tree {
  B_Leaf {},
  B_Node {datatype a_tree even, datatype a_tree odd}
}

/* The predicates relating A/B trees to their C encoding. */

predicate {datatype a_tree t} A_Tree (pointer p) {
  if (p == ((pointer) 0)) {
    return {t = A_Leaf {}};
  }
  else {
    take V = Owned<struct a_node>(p);
    take L = B_Tree(V.value.left);
    take R = B_Tree(V.value.right);
    return {t = A_Node {k = V.value.k, v = V.value.v, left = L.t, right = R.t}};
  }
}

predicate {datatype b_tree t} B_Tree (pointer p) {
  if (p == ((pointer) 0)) {
    return {t = B_Leaf {}};
  }
  else {
    take V = Owned<struct b_node>(p);
    take E = A_Tree(V.value.even);
    take O = A_Tree(V.value.odd);
    return {t = B_Node {even = E.t, odd = O.t}};
  }
}


#endif

unsigned int global_val;

/* Walk a tree and sum the values. Only proven safe. */

void walk_b_tree (struct b_node *p);

void
walk_a_tree (struct a_node *p)
/*@ accesses global_val @*/
/*@ requires take T = A_Tree (p) @*/
/*@ ensures take T2 = A_Tree (p) @*/
{
  if (! p)
    return;
  global_val += p->v;
  walk_b_tree(p->left);
  walk_b_tree(p->right);
}

void
walk_b_tree (struct b_node *p)
/*@ accesses global_val @*/
/*@ requires take T = B_Tree (p) @*/
/*@ ensures take T2 = B_Tree (p) @*/
{
  if (! p)
    return;
  walk_a_tree(p->even);
  walk_a_tree(p->odd);
}

/* Coerce a tree to encode a particular value, if it is of the right shape. If
   of the wrong shape, return NULL. Proven to return exactly the right value,
   if not NULL. */

struct a_node *
predef_a_tree (struct a_node *p)
/*@ requires take T = A_Tree (p) @*/
/*@ ensures take T2 = A_Tree (p) @*/
/*@ ensures (return == ((pointer) 0)) || (T2.t == A_Node {k = 1, v = 0,
    left = B_Node {even = A_Leaf {}, odd = A_Leaf {}}, right = B_Leaf {}}) @*/
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
  /*@ unpack B_Tree((*p).right); @*/
  /*@ unpack A_Tree((*l).odd); @*/
  /*@ unpack A_Tree((*l).even); @*/
  return p;
}

#ifdef CN_MODE

/* Setup for reasoning about the list of keys of an A/B tree. */

datatype key_list {
  K_Nil {},
  K_Cons {integer k, datatype key_list tail}
}

function (datatype key_list) a_tree_keys (datatype a_tree t)

function (datatype key_list) b_tree_keys (datatype b_tree t)

function (datatype key_list) inc_list (datatype key_list xs)

function (datatype key_list) concat (datatype key_list xs, datatype key_list ys)

function (datatype key_list) double_list (datatype key_list xs)

function (datatype key_list) merge (datatype key_list xs, datatype key_list ys)

/* Lemmas that boil down to the definitions of the above. */

void
a_tree_keys_leaf_lemma (void)
/*@ trusted @*/
/*@ ensures (a_tree_keys (A_Leaf {})) == (K_Nil {}) @*/
{
  return;
}

void
b_tree_keys_leaf_lemma (void)
/*@ trusted @*/
/*@ ensures (b_tree_keys (B_Leaf {})) == (K_Nil {}) @*/
{
  return;
}

void
inc_list_nil_lemma (void)
/*@ trusted @*/
/*@ ensures (inc_list (K_Nil {})) == (K_Nil {}) @*/
{
  return;
}

void
a_tree_keys_node_lemma (int k, int v, struct b_node *left, struct b_node *right)
/*@ trusted @*/
/*@ requires take L = B_Tree (left) @*/
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take L2 = B_Tree (left) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures L2.t == L.t @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (a_tree_keys (A_Node {k = k, v = v, left = L2.t, right = R2.t}))
  == (concat (b_tree_keys(L2.t), K_Cons {k = k, tail = (b_tree_keys(R2.t))})) @*/
{
  return;
}

void
b_tree_keys_node_lemma (struct a_node *even, struct a_node *odd)
/*@ trusted @*/
/*@ requires take E = A_Tree (even) @*/
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take E2 = A_Tree (even) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures E2.t == E.t @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (b_tree_keys (B_Node {even = E2.t, odd = O2.t}))
  == (merge (double_list (a_tree_keys (E2.t)), inc_list (double_list (a_tree_keys (O2.t))))) @*/
{
  return;
}

/* A lemma about increment of concat. */
void
a_tree_keys_node_concat_inc_lemma (int k, struct b_node *left, struct b_node *right)
/*@ trusted @*/
/*@ requires take L = B_Tree (left) @*/
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take L2 = B_Tree (left) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures L2.t == L.t @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (inc_list (concat (b_tree_keys(L2.t), K_Cons {k = k, tail = (b_tree_keys(R2.t))})))
  == (concat (inc_list (b_tree_keys(L2.t)), inc_list (K_Cons {k = k, tail = (b_tree_keys(R2.t))})))
@*/
{
  return;
}

/* A lemma about increment of cons. */
void
a_tree_keys_node_concat_cons_inc_lemma (int k, struct b_node *right)
/*@ trusted @*/
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (inc_list (K_Cons {k = k, tail = (b_tree_keys(R2.t))}))
  == (K_Cons {k = k + 1, tail = inc_list (b_tree_keys(R2.t))}) @*/
{
  return;
}

/* A lemma about increment of merge. */
void
b_tree_keys_node_merge_inc_lemma (struct a_node *even, struct a_node *odd)
/*@ trusted @*/
/*@ requires take E = A_Tree (even) @*/
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take E2 = A_Tree (even) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures E2.t == E.t @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (inc_list (merge (double_list (a_tree_keys (E2.t)),
        inc_list (double_list (a_tree_keys (O2.t))))))
  == (merge (inc_list (double_list (a_tree_keys (E2.t))),
        inc_list (inc_list (double_list (a_tree_keys (O2.t)))))) @*/

{
  return;
}

/* A lemma about flipping a merge. The merge has to sort, to some degree, to
   allow us to prove list equality rather than weaker multiset equality. */
void
b_tree_keys_node_merge_flip_lemma (struct a_node *even, struct a_node *odd)
/*@ trusted @*/
/*@ requires take E = A_Tree (even) @*/
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take E2 = A_Tree (even) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures E2.t == E.t @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (merge (inc_list (double_list (a_tree_keys (E2.t))),
        inc_list (inc_list (double_list (a_tree_keys (O2.t))))))
  == (merge (inc_list (inc_list (double_list (a_tree_keys (O2.t)))),
        inc_list (double_list (a_tree_keys (E2.t))))) @*/
{
  return;
}

/* A lemma about composing increments and multiplies. */
void
b_tree_keys_node_inc_inc_double_lemma (struct a_node *odd)
/*@ trusted @*/
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (inc_list (inc_list (double_list (a_tree_keys (O2.t)))))
  == (double_list (inc_list (a_tree_keys (O2.t)))) @*/
{
  return;
}



#endif

/* unannotated versions
int
inc_a_tree (struct a_node *p) {
  if (! p) {
    return 1;
  }
  if (p->k >= INT_MAX) {
    return 0;
  }
  p->k ++;
  return inc_b_tree(p->left) && inc_b_tree(p->right);
}

int
inc_b_tree (struct b_node *p)
{
  struct a_node *tmp = NULL;
  if (! p) {
    return 1;
  }
  tmp = p->odd;
  p->odd = p->even;
  p->even = tmp;
  return inc_a_tree(tmp);
}
*/

int inc_b_tree (struct b_node *p);

int
inc_a_tree (struct a_node *p)
/*@ requires take T = A_Tree (p) @*/
/*@ ensures take T2 = A_Tree (p) @*/
/*@ ensures (return == 0) || ((a_tree_keys(T2.t)) == (inc_list(a_tree_keys(T.t)))) @*/
{
  int r = 0;
  if (! p) {
    /*@ unpack A_Tree(p) @*/
    a_tree_keys_leaf_lemma();
    inc_list_nil_lemma();
    return 1;
  }
  if (p->k >= INT_MAX) {
    return 0;
  }
  a_tree_keys_node_lemma(p->k, p->v, p->left, p->right);
  a_tree_keys_node_concat_inc_lemma(p->k, p->left, p->right);
  a_tree_keys_node_concat_cons_inc_lemma(p->k, p->right);
  p->k ++;
  r = inc_b_tree(p->left) && inc_b_tree(p->right);
  a_tree_keys_node_lemma(p->k, p->v, p->left, p->right);
  return r;
}

int
inc_b_tree (struct b_node *p)
/*@ requires take T = B_Tree (p) @*/
/*@ ensures take T2 = B_Tree (p) @*/
/*@ ensures (return == 0) || ((b_tree_keys(T2.t)) == (inc_list(b_tree_keys(T.t)))) @*/
{
  struct a_node *tmp = NULL;
  int r = 0;
  if (! p) {
    /*@ unpack B_Tree(p); @*/
    b_tree_keys_leaf_lemma();
    inc_list_nil_lemma();
    return 1;
  }
  b_tree_keys_node_lemma(p->even, p->odd);
  b_tree_keys_node_merge_inc_lemma(p->even, p->odd);
  b_tree_keys_node_merge_flip_lemma(p->even, p->odd);
  b_tree_keys_node_inc_inc_double_lemma(p->odd);
  tmp = p->odd;
  p->odd = p->even;
  p->even = tmp;
  r = inc_a_tree(tmp);
  b_tree_keys_node_lemma (p->even, p->odd);
  return r;
}





