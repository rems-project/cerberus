/* A silly example of a tree with two node types that point at
   each other, the equivalent mutually-recursive datatype, and
   conversion of that type and some lemmas to Coq. */

#include <assert.h>
#include <stddef.h>
#include <limits.h>
#include "mutual_rec.h"


enum {
  enum_INT_MIN = INT_MIN,
  enum_INT_MAX = INT_MAX,
};

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
  requires
    (match xs {
      K_Nil {} => {true}
      K_Cons {k: k, tail: ys} => {enum_INT_MIN <= k && k < enum_INT_MAX}
    });
  ensures (inc_list (xs)) == (match xs {
    K_Nil {} => {K_Nil {}}
    K_Cons {k: k, tail: ys} => {K_Cons {k: k + 1i32, tail: inc_list (ys)}}
  });

lemma a_tree_keys_lemma (datatype a_tree atree)
  requires true;
  ensures (a_tree_keys (atree)) == (match atree {
    A_Leaf {} => {K_Nil {}}
    A_Node {k: k, v: v, left: l, right: r} => {
        concat (b_tree_keys(l), K_Cons {k: k, tail: b_tree_keys(r)})}
  });

lemma b_tree_keys_lemma (datatype b_tree btree)
  requires true;
  ensures (b_tree_keys (btree)) == (match btree {
    B_Leaf {} => {K_Nil {}}
    B_Node {even: e, odd: o} => {
        merge (double_list (a_tree_keys (e)), inc_list (double_list (a_tree_keys (o))))}
  });
@*/

void
a_tree_keys_node_lemma (int k, int v, struct b_node *left, struct b_node *right)
/*@ requires take L = B_Tree (left);
             take R = B_Tree (right);
    ensures take L2 = B_Tree (left);
            take R2 = B_Tree (right);
            L2.t == L.t;
            R2.t == R.t;
            (a_tree_keys (A_Node {k: k, v: v, left: L2.t, right: R2.t}))
  == (concat (b_tree_keys(L2.t), K_Cons {k: k, tail: (b_tree_keys(R2.t))})); @*/
{
  /*@ apply a_tree_keys_lemma (A_Node {k: k, v: v, left: L.t, right: R.t}); @*/
  return;
}

void
b_tree_keys_node_lemma (struct a_node *even, struct a_node *odd)
/*@ requires take E = A_Tree (even);
             take O = A_Tree (odd);
    ensures take E2 = A_Tree (even);
            take O2 = A_Tree (odd);
            E2.t == E.t;
            O2.t == O.t;
            (b_tree_keys (B_Node {even: E2.t, odd: O2.t}))
  == (merge (double_list (a_tree_keys (E2.t)), inc_list (double_list (a_tree_keys (O2.t))))); @*/
{
  /*@ apply b_tree_keys_lemma (B_Node {even: E.t, odd: O.t}); @*/
  return;
}

/* A lemma about increment of concat. */
/*@
lemma inc_concat_lemma (datatype key_list xs, datatype key_list ys)
  requires true;
  ensures inc_list (concat (xs, ys)) == concat (inc_list (xs), inc_list (ys));
@*/

void
a_tree_keys_node_concat_inc_lemma (int k, struct b_node *left, struct b_node *right)
/*@ requires take L = B_Tree (left);
             take R = B_Tree (right);
    ensures take L2 = B_Tree (left);
            take R2 = B_Tree (right);
            L2.t == L.t;
            R2.t == R.t;
            (inc_list (concat (b_tree_keys(L2.t), K_Cons {k: k, tail: (b_tree_keys(R2.t))})))
  == (concat (inc_list (b_tree_keys(L2.t)), inc_list (K_Cons {k: k, tail: (b_tree_keys(R2.t))})));
@*/
{
  /*@ apply inc_concat_lemma (b_tree_keys(L.t), K_Cons {k: k, tail: (b_tree_keys(R.t))}); @*/
  return;
}

void
a_tree_keys_node_concat_cons_inc_lemma (int k, struct b_node *right)
/*@ requires take R = B_Tree (right);
             k < enum_INT_MAX;
    ensures take R2 = B_Tree (right);
            R2.t == R.t;
            (inc_list (K_Cons {k: k, tail: (b_tree_keys(R2.t))}))
  == (K_Cons {k: k + 1i32, tail: inc_list (b_tree_keys(R2.t))}); @*/
{
  /*@ apply inc_list_lemma (K_Cons {k: k, tail: b_tree_keys(R.t)}); @*/
  return;
}

/* A lemma about increment of cons. */
/*@
lemma inc_merge_double_lemma (datatype key_list xs, datatype key_list ys)
  requires true;
  ensures inc_list (merge (double_list (xs), inc_list (double_list (ys))))
    == merge (inc_list (double_list (xs)), inc_list (inc_list (double_list (ys))));
@*/

void
b_tree_keys_node_merge_inc_lemma (struct a_node *even, struct a_node *odd)
/*@ requires take E = A_Tree (even);
             take O = A_Tree (odd);
    ensures take E2 = A_Tree (even);
            take O2 = A_Tree (odd);
            E2.t == E.t;
            O2.t == O.t;
            (inc_list (merge (double_list (a_tree_keys (E2.t)),
        inc_list (double_list (a_tree_keys (O2.t))))))
  == (merge (inc_list (double_list (a_tree_keys (E2.t))),
        inc_list (inc_list (double_list (a_tree_keys (O2.t)))))); @*/

{
  /*@ apply inc_merge_double_lemma (a_tree_keys (E.t), a_tree_keys (O.t)); @*/
  return;
}

/* A lemma about flipping a merge. The merge has to sort, to some degree, to
   allow us to prove list equality rather than weaker multiset equality. */
/*@
lemma flip_merge_lemma (datatype key_list xs, datatype key_list ys)
  requires true;
  ensures merge (inc_list (double_list (xs)), inc_list (inc_list (double_list (ys))))
    == merge (inc_list (inc_list (double_list (ys))), inc_list (double_list (xs)));
@*/

void
b_tree_keys_node_merge_flip_lemma (struct a_node *even, struct a_node *odd)
/*@ requires take E = A_Tree (even);
             take O = A_Tree (odd);
    ensures take E2 = A_Tree (even);
            take O2 = A_Tree (odd);
            E2.t == E.t;
            O2.t == O.t;
            (merge (inc_list (double_list (a_tree_keys (E2.t))),
        inc_list (inc_list (double_list (a_tree_keys (O2.t))))))
  == (merge (inc_list (inc_list (double_list (a_tree_keys (O2.t)))),
        inc_list (double_list (a_tree_keys (E2.t))))); @*/
{
  /*@ apply flip_merge_lemma (a_tree_keys (E.t), a_tree_keys (O.t)); @*/
  return;
}

/* A lemma about composing increments and multiplies. */
/*@
lemma inc_double_lemma (datatype key_list xs)
  requires true;
  ensures double_list (inc_list (xs)) == inc_list (inc_list (double_list (xs)));
@*/

void
b_tree_keys_node_inc_inc_double_lemma (struct a_node *odd)
/*@ requires take O = A_Tree (odd);
    ensures take O2 = A_Tree (odd);
            O2.t == O.t;
            (inc_list (inc_list (double_list (a_tree_keys (O2.t)))))
  == (double_list (inc_list (a_tree_keys (O2.t)))); @*/
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
/*@ requires is_null(p) || !addr_eq(p, NULL);
             take T = A_Tree (p);
    ensures take T2 = A_Tree (p);
            (return == 0i32) || ((a_tree_keys(T2.t)) == (inc_list(a_tree_keys(T.t)))); @*/
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
/*@ requires is_null(p) || !addr_eq(p, NULL);
             take T = B_Tree (p);
    ensures take T2 = B_Tree (p);
            (return == 0i32) || ((b_tree_keys(T2.t)) == (inc_list(b_tree_keys(T.t)))); @*/
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





