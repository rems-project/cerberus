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
    take V = Owned<struct a_node>(p);
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
    take V = Owned<struct b_node>(p);
    assert ((is_null(V.even) || !addr_eq(V.even, NULL))
      && (is_null(V.odd) || !addr_eq(V.odd, NULL)));
    take E = A_Tree(V.even);
    take O = A_Tree(V.odd);
    return {t: B_Node {even: E.t, odd: O.t}};
  }
}
@*/


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
/*@ ensures is_null(return) || (T2.t == A_Node {k: 1i32, v: 0i32,
    left: B_Node {even: A_Leaf {}, odd: A_Leaf {}}, right: B_Leaf {}}) @*/
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

/* Setup for reasoning about the list of keys of an A/B tree. */

/*@
datatype key_list {
  K_Nil {},
  K_Cons {i32 k, datatype key_list tail}
}

function (datatype key_list) a_tree_keys (datatype a_tree t)

function (datatype key_list) b_tree_keys (datatype b_tree t)

function (datatype key_list) inc_list (datatype key_list xs)

function (datatype key_list) concat (datatype key_list xs, datatype key_list ys)

function (datatype key_list) double_list (datatype key_list xs)

function (datatype key_list) merge (datatype key_list xs, datatype key_list ys)
@*/

/* Lemmas that boil down to the definitions of the above. */

/*@
lemma inc_list_lemma (datatype key_list xs)
  requires true
  ensures (inc_list (xs)) == (match xs {
    K_Nil {} => {K_Nil {}}
    K_Cons {k: k, tail: ys} => {K_Cons {k: k + 1i32, tail: inc_list (ys)}}
  })

lemma a_tree_keys_lemma (datatype a_tree atree)
  requires true
  ensures (a_tree_keys (atree)) == (match atree {
    A_Leaf {} => {K_Nil {}}
    A_Node {k: k, v: v, left: l, right: r} => {
        concat (b_tree_keys(l), K_Cons {k: k, tail: b_tree_keys(r)})}
  })

lemma b_tree_keys_lemma (datatype b_tree btree)
  requires true
  ensures (b_tree_keys (btree)) == (match btree {
    B_Leaf {} => {K_Nil {}}
    B_Node {even: e, odd: o} => {
        merge (double_list (a_tree_keys (e)), inc_list (double_list (a_tree_keys (o))))}
  })
@*/

void
a_tree_keys_node_lemma (int k, int v, struct b_node *left, struct b_node *right)
/*@ requires take L = B_Tree (left) @*/
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take L2 = B_Tree (left) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures L2.t == L.t @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (a_tree_keys (A_Node {k: k, v: v, left: L2.t, right: R2.t}))
  == (concat (b_tree_keys(L2.t), K_Cons {k: k, tail: (b_tree_keys(R2.t))})) @*/
{
  /*@ apply a_tree_keys_lemma (A_Node {k: k, v: v, left: L.t, right: R.t}); @*/
  return;
}

void
b_tree_keys_node_lemma (struct a_node *even, struct a_node *odd)
/*@ requires take E = A_Tree (even) @*/
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take E2 = A_Tree (even) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures E2.t == E.t @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (b_tree_keys (B_Node {even: E2.t, odd: O2.t}))
  == (merge (double_list (a_tree_keys (E2.t)), inc_list (double_list (a_tree_keys (O2.t))))) @*/
{
  /*@ apply b_tree_keys_lemma (B_Node {even: E.t, odd: O.t}); @*/
  return;
}

/* A lemma about increment of concat. */
/*@
lemma inc_concat_lemma (datatype key_list xs, datatype key_list ys)
  requires true
  ensures inc_list (concat (xs, ys)) == concat (inc_list (xs), inc_list (ys))
@*/

void
a_tree_keys_node_concat_inc_lemma (int k, struct b_node *left, struct b_node *right)
/*@ requires take L = B_Tree (left) @*/
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take L2 = B_Tree (left) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures L2.t == L.t @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (inc_list (concat (b_tree_keys(L2.t), K_Cons {k: k, tail: (b_tree_keys(R2.t))})))
  == (concat (inc_list (b_tree_keys(L2.t)), inc_list (K_Cons {k: k, tail: (b_tree_keys(R2.t))})))
@*/
{
  /*@ apply inc_concat_lemma (b_tree_keys(L.t), K_Cons {k: k, tail: (b_tree_keys(R.t))}); @*/
  return;
}

void
a_tree_keys_node_concat_cons_inc_lemma (int k, struct b_node *right)
/*@ requires take R = B_Tree (right) @*/
/*@ ensures take R2 = B_Tree (right) @*/
/*@ ensures R2.t == R.t @*/
/*@ ensures (inc_list (K_Cons {k: k, tail: (b_tree_keys(R2.t))}))
  == (K_Cons {k: k + 1i32, tail: inc_list (b_tree_keys(R2.t))}) @*/
{
  /*@ apply inc_list_lemma (K_Cons {k: k, tail: b_tree_keys(R.t)}); @*/
  return;
}

/* A lemma about increment of cons. */
/*@
lemma inc_merge_double_lemma (datatype key_list xs, datatype key_list ys)
  requires true
  ensures inc_list (merge (double_list (xs), inc_list (double_list (ys))))
    == merge (inc_list (double_list (xs)), inc_list (inc_list (double_list (ys))))
@*/

void
b_tree_keys_node_merge_inc_lemma (struct a_node *even, struct a_node *odd)
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
  /*@ apply inc_merge_double_lemma (a_tree_keys (E.t), a_tree_keys (O.t)); @*/
  return;
}

/* A lemma about flipping a merge. The merge has to sort, to some degree, to
   allow us to prove list equality rather than weaker multiset equality. */
/*@
lemma flip_merge_lemma (datatype key_list xs, datatype key_list ys)
  requires true
  ensures merge (inc_list (double_list (xs)), inc_list (inc_list (double_list (ys))))
    == merge (inc_list (inc_list (double_list (ys))), inc_list (double_list (xs)))
@*/

void
b_tree_keys_node_merge_flip_lemma (struct a_node *even, struct a_node *odd)
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
  /*@ apply flip_merge_lemma (a_tree_keys (E.t), a_tree_keys (O.t)); @*/
  return;
}

/* A lemma about composing increments and multiplies. */
/*@
lemma inc_double_lemma (datatype key_list xs)
  requires true
  ensures double_list (inc_list (xs)) == inc_list (inc_list (double_list (xs)))
@*/

void
b_tree_keys_node_inc_inc_double_lemma (struct a_node *odd)
/*@ requires take O = A_Tree (odd) @*/
/*@ ensures take O2 = A_Tree (odd) @*/
/*@ ensures O2.t == O.t @*/
/*@ ensures (inc_list (inc_list (double_list (a_tree_keys (O2.t)))))
  == (double_list (inc_list (a_tree_keys (O2.t)))) @*/
{
  /*@ apply inc_double_lemma (a_tree_keys (O.t)); @*/
  return;
}

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
/*@ requires is_null(p) || !addr_eq(p, NULL) @*/
/*@ requires take T = A_Tree (p) @*/
/*@ ensures take T2 = A_Tree (p) @*/
/*@ ensures (return == 0i32) || ((a_tree_keys(T2.t)) == (inc_list(a_tree_keys(T.t)))) @*/
{
  int r = 0;
  /*@ apply a_tree_keys_lemma(T.t); @*/
  if (! p) {
    /*@ apply inc_list_lemma(K_Nil {}); @*/
    return 1;
  }
  if (p->k >= INT_MAX) {
    return 0;
  }
  a_tree_keys_node_concat_inc_lemma(p->k, p->left, p->right);
  a_tree_keys_node_concat_cons_inc_lemma(p->k, p->right);
  p->k ++;
  r = inc_b_tree(p->left) && inc_b_tree(p->right);
  a_tree_keys_node_lemma(p->k, p->v, p->left, p->right);
  return r;
}

int
inc_b_tree (struct b_node *p)
/*@ requires is_null(p) || !addr_eq(p, NULL) @*/
/*@ requires take T = B_Tree (p) @*/
/*@ ensures take T2 = B_Tree (p) @*/
/*@ ensures (return == 0i32) || ((b_tree_keys(T2.t)) == (inc_list(b_tree_keys(T.t)))) @*/
{
  struct a_node *tmp = NULL;
  int r = 0;
  /*@ apply b_tree_keys_lemma(T.t); @*/
  if (! p) {
    /*@ apply inc_list_lemma(K_Nil {}); @*/
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





