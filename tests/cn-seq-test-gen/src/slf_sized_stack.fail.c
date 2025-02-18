#include "stdlib.h"

void *cn_malloc(unsigned long size);
void cn_free_sized(void*, size_t len);

struct int_list {
  int head;
  struct int_list* tail;
};

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/
/*@
function (i32) hd (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0i32
    }
    Seq_Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      Seq_Nil {}
    }
    Seq_Cons {head : _, tail : tail} => {
      tail
    }
  }
}
@*/
struct int_list* IntList_nil()
/*@ ensures take ret = IntList(return);
            ret == Seq_Nil{};
 @*/
{
  return 0;
}
struct int_list* IntList_cons(int h, struct int_list* t)
/*@ requires take l = IntList(t);
    ensures take ret = IntList(return);
            ret == Seq_Cons{ head: h, tail: l};
 @*/
{
  struct int_list *p = (struct int_list *)cn_malloc(sizeof(struct int_list));
  p->head = h;
  p->tail = t;
  return p;
}

/*@
function [rec] (u32) length(datatype seq xs) {
  match xs {
    Seq_Nil {} => {
      0u32
    }
    Seq_Cons {head : h, tail : zs}  => {
      1u32 + length(zs)
    }
  }
}
@*/
unsigned int IntList_length (struct int_list *xs)
/*@ requires take L1 = IntList(xs);
    ensures take L1_ = IntList(xs);
            L1 == L1_;
            return == length(L1);
@*/
{
  if (xs == 0) {
    /*@ unfold length(L1); @*/
    return 1; // bug
  } else {
    /*@ unfold length(L1); @*/
    return 1 + IntList_length (xs->tail);
  }
}

struct sized_stack {
  unsigned int size;
  struct int_list* data;
};
/*@
type_synonym sizeAndData = {u32 s, datatype seq d}

predicate (sizeAndData) SizedStack(pointer p) {
    take S = Owned<struct sized_stack>(p);
    let s = S.size;
    take d = IntList(S.data);
    assert(s == length(d));
    return { s: s, d: d };
}
@*/
struct sized_stack* create()
/*@ ensures take S = SizedStack(return);
            S.s == 0u32;
@*/
{
  struct sized_stack *p = (struct sized_stack *)cn_malloc(sizeof(struct sized_stack));
  p->size = 0;
  p->data = 0;
  /*@ unfold length(Seq_Nil {}); @*/
  return p;
}
unsigned int sizeOf (struct sized_stack *p)
/*@ requires take S = SizedStack(p);
    ensures take S_ = SizedStack(p);
            S_ == S;
            return == S.s;
@*/
{
  return p->size;
}
void push (struct sized_stack *p, int x)
/*@ requires take S = SizedStack(p);
    ensures take S_ = SizedStack(p);
            S_.d == Seq_Cons {head:x, tail:S.d};
@*/
{
  struct int_list *data = IntList_cons(x, p->data);
  //p->size++; no inc size 
  p->data = data;
  /*@ unfold length (Seq_Cons {head: x, tail: S.d}); @*/
}
int pop (struct sized_stack *p)
/*@ requires take S = SizedStack(p);
             S.s > 0u32;
    ensures  take S_ = SizedStack(p);
             S_.d == tl(S.d);
@*/
{
  struct int_list *data = p->data;
  if (data != 0) {
    int head = data->head;
    struct int_list *tail = data->tail;
    cn_free_sized(data, sizeof(struct int_list));
    p->data = tail;
    p->size--;
    /*@ unfold length(S.d); @*/
    return head;
  }
  return 42;
}
int top (struct sized_stack *p)
/*@ requires take S = SizedStack(p);
             S.s > 0u32;
    ensures  take S_ = SizedStack(p);
             S_ == S;
             return == hd(S.d);
@*/
{
  /*@ unfold length(S.d); @*/
  // from S.s > 0u32 it follows that the 'else' branch is impossible
  if (p->data != 0) {
    return (p->data)->head;
  }
  else {
    // provably dead code
    return 42;
  }
}
