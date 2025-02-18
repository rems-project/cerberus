#include "stdlib.h"

void *cn_malloc(unsigned long size);
void cn_free_sized(void*, size_t len);

struct sllist {
  int head;
  struct sllist* tail;
};

/*@
datatype List {
  Nil {},
  Cons {i32 Head, datatype List Tail}
}

predicate (datatype List) SLList_At(pointer p) {
  if (is_null(p)) {
    return Nil{};
  } else {
    take H = Owned<struct sllist>(p);
    take T = SLList_At(H.tail);
    return (Cons { Head: H.head, Tail: T });
  }
}
@*/
/*@
function (i32) Hd (datatype List L) {
  match L {
    Nil {} => {
      0i32
    }
    Cons {Head : H, Tail : _} => {
      H
    }
  }
}

function (datatype List) Tl (datatype List L) {
  match L {
    Nil {} => {
      Nil{}
    }
    Cons {Head : _, Tail : T} => {
      T
    }
  }
}
@*/
/*@
function [rec] (datatype List) Snoc(datatype List Xs, i32 Y) {
  match Xs {
    Nil {} => {
      Cons {Head: Y, Tail: Nil{}}
    }
    Cons {Head: X, Tail: Zs}  => {
      Cons{Head: X, Tail: Snoc (Zs, Y)}
    }
  }
}
@*/

struct queue {
  struct queue_cell* front;
  struct queue_cell* back;
};
struct queue_cell {
  int first;
  struct queue_cell* next;
};
/*@
predicate (datatype List) QueuePtr_At (pointer q) {
  take Q = Owned<struct queue>(q);
  assert (   (is_null(Q.front)  && is_null(Q.back)) 
          || (!is_null(Q.front) && !is_null(Q.back)));
  take L = QueueFB(Q.front, Q.back);
  return L;
}
@*/
/*@
predicate (datatype List) QueueFB (pointer front, pointer back) {
  if (is_null(front)) {
    return Nil{};
  } else {
    take B = Owned<struct queue_cell>(back);
    assert (is_null(B.next));
    assert (ptr_eq(front, back) || !addr_eq(front, back));
    take L = QueueAux (front, back);
    return Snoc(L, B.first);
  }
}
@*/
/*@
predicate (datatype List) QueueAux (pointer f, pointer b) {
  if (ptr_eq(f,b)) {
    return Nil{};
  } else {
    take F = Owned<struct queue_cell>(f);
    assert (!is_null(F.next));  
    assert (ptr_eq(F.next, b) || !addr_eq(F.next, b));
    take B = QueueAux(F.next, b);
    return Cons{Head: F.first, Tail: B};
  }
}
@*/

struct queue* empty_queue ()
/* --BEGIN-- */
/*@ ensures take ret = QueuePtr_At(return);
            ret == Nil{};
@*/
/* --END-- */
{
  struct queue *p = cn_malloc(sizeof(struct queue));
  p->front = 0;
  p->back = 0;
  return p;
}
/*@
lemma push_lemma (pointer front, pointer p)
  requires
      ptr_eq(front, p) || !addr_eq(front, p);
      take Q = QueueAux(front, p);
      take P = Owned<struct queue_cell>(p);
  ensures
      ptr_eq(front, P.next) || !addr_eq(front, P.next);
      take Q_post = QueueAux(front, P.next);
      Q_post == Snoc(Q, P.first);
@*/

void push_queue (int x, struct queue *q)
/*@ requires take Q = QueuePtr_At(q);
    ensures take Q_post = QueuePtr_At(q);
            Q_post == Snoc (Q, x);
@*/
{
  struct queue_cell *c = cn_malloc(sizeof(struct queue_cell));
  c->first = x;
  c->next = 0;
  if (q->back == 0) {
    q->front = c;
    q->back = c;
    return;
  } else {
    struct queue_cell *oldback = q->back;
    q->back->next = c;
    q->back = c;
    /*@ apply push_lemma (q->front, oldback); @*/
    return;
  }
}
/*@
lemma snoc_facts (pointer front, pointer back, i32 x)
  requires
      take Q = QueueAux(front, back);
      take B = Owned<struct queue_cell>(back);
  ensures
      take Q_post = QueueAux(front, back);
      take B_post = Owned<struct queue_cell>(back);
      Q == Q_post; B == B_post;
      let L = Snoc (Cons{Head: x, Tail: Q}, B.first);
      Hd(L) == x;
      Tl(L) == Snoc (Q, B.first);
@*/

int pop_queue (struct queue *q)
/*@ requires take Q = QueuePtr_At(q);
             Q != Nil{};
    ensures take Q_post = QueuePtr_At(q);
            Q_post == Tl(Q);
            return == Hd(Q);
@*/
{
  /*@ split_case is_null(q->front); @*/
  struct queue_cell* h = q->front;
  if (h == q->back) {
    /*@ assert ((alloc_id) h == (alloc_id) (q->back)); @*/
    int x = h->first;
    cn_free_sized(h, sizeof(struct queue_cell));
    q->front = 0;
    q->back = 0;
    /*@ unfold Snoc(Nil{}, x); @*/
    return 1;
  } else {
    int x = h->first;
    /*@ apply snoc_facts(h->next, q->back, x); @*/
    q->front = h->next;
    cn_free_sized(h, sizeof(struct queue_cell));
    return x;
  }
}
