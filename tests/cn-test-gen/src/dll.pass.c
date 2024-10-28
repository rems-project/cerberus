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
struct sllist* slnil()
/*@ ensures take Ret = SLList_At(return);
            Ret == Nil{};
 @*/
{
  return 0;
}
struct sllist* slcons(int h, struct sllist* t)
/*@ requires take T = SLList_At(t);
    ensures take Ret = SLList_At(return);
            Ret == Cons{ Head: h, Tail: T};
 @*/
{
  struct sllist *p = cn_malloc(sizeof(struct sllist));
  p->head = h;
  p->tail = t;
  return p;
}
/*@
function [rec] (datatype List) Append(datatype List L1, datatype List L2) {
  match L1 {
    Nil {} => {
      L2
    }
    Cons {Head : H, Tail : T}  => {
      Cons {Head: H, Tail: Append(T, L2)}
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

/*@
function [rec] (datatype List) RevList(datatype List L) {
  match L {
    Nil {} => {
      Nil {}
    }
    Cons {Head : H, Tail : T}  => {
      Snoc (RevList(T), H)
    }
  }
}
@*/
struct dllist {
  int data;
  struct dllist* prev;
  struct dllist* next;
};
/*@
datatype Dll {
    Empty_Dll    {},
    Nonempty_Dll {datatype List left, 
                  struct dllist curr, 
                  datatype List right}
}
@*/
/*@
function (datatype List) Right_Sublist (datatype Dll L) {
    match L {
        Empty_Dll {} => { Nil{} }
        Nonempty_Dll {left: _, curr: _, right: r} => { r }
    }
}

function (datatype List) Left_Sublist (datatype Dll L) {
    match L {
        Empty_Dll {} => { Nil {} }
        Nonempty_Dll {left: l, curr: _, right: _} => { l }
    }
}

function (struct dllist) Node (datatype Dll L) {
    match L {
        Empty_Dll {} => {  struct dllist { data: 0i32, prev: NULL, next: NULL } }
        Nonempty_Dll {left: _, curr: n, right: _} => { n }
    }
}

predicate (datatype Dll) Dll_at (pointer p) {
    if (is_null(p)) {
        return Empty_Dll{};
    } else {
        take n = Owned<struct dllist>(p);
        take L = Own_Backwards(n.prev, p, n);
        take R = Own_Forwards(n.next, p, n);
        return Nonempty_Dll{left: L, curr: n, right: R};
    }
}

predicate (datatype List) Own_Forwards (pointer p, 
                                        pointer prev_pointer, 
                                        struct dllist prev_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = Owned<struct dllist>(p);
        assert (ptr_eq(P.prev, prev_pointer));
        assert(ptr_eq(prev_dllist.next, p));
        take T = Own_Forwards(P.next, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}

predicate (datatype List) Own_Backwards (pointer p, 
                                         pointer next_pointer, 
                                         struct dllist next_dllist) {
    if (is_null(p)) {
        return Nil{};
    } else {
        take P = Owned<struct dllist>(p);
        assert (ptr_eq(P.next, next_pointer));
        assert(ptr_eq(next_dllist.prev, p));
        take T = Own_Backwards(P.prev, p, P);
        return Cons{Head: P.data, Tail: T};
    }
}
@*/

struct dllist *singleton(int element)
/*@ ensures take Ret = Dll_at(return);
        Ret == Nonempty_Dll {
                 left: Nil{}, 
                 curr: struct dllist {prev: NULL, 
                                      data: element, 
                                      next: NULL}, 
                 right: Nil{}};
@*/
{
   struct dllist *n = cn_malloc(sizeof(struct dllist));
   n->data = element;
   n->prev = 0;
   n->next = 0;
   return n;
}
// Adds after the given node and returns a pointer to the new node
struct dllist *add(int element, struct dllist *n)
/*@ requires take Before = Dll_at(n);
    ensures  take After = Dll_at(return);
             is_null(n) ? 
                After == Nonempty_Dll { 
                           left: Nil{}, 
                           curr: Node(After), 
                           right: Nil{}}
              : After == Nonempty_Dll { 
                           left: Cons {Head: Node(Before).data, 
                                       Tail: Left_Sublist(Before)}, 
                           curr: Node(After), 
                           right: Right_Sublist(Before)};
@*/
{
    struct dllist *new_dllist = cn_malloc(sizeof(struct dllist));
    new_dllist->data = element;
    new_dllist->prev = 0;
    new_dllist->next = 0;
    if (n == 0) //empty list case
    {
        new_dllist->prev = 0;
        new_dllist->next = 0;
        return new_dllist;
    } else {
        /*@ split_case(is_null(n->prev)); @*/
        new_dllist->next = n->next;
        new_dllist->prev = n;
        if (n->next != 0) {
            /*@ split_case(is_null(n->next->next)); @*/
            n->next->prev = new_dllist;
        }
        n->next = new_dllist;
        return new_dllist;
    }
}

struct dllist_and_int {
  struct dllist* dllist;
  int data;
};

// Remove the given node from the list and returns another pointer 
// to somewhere in the list, or a null pointer if the list is empty
struct dllist_and_int *list_remove(struct dllist *n)
/*@ requires !is_null(n);
             take Before = Dll_at(n);
             let Del = Node(Before);
    ensures  take Ret = Owned<struct dllist_and_int>(return);
             take After = Dll_at(Ret.dllist);
             Ret.data == Del.data;
             (is_null(Del.prev) && is_null(Del.next)) 
               ? After == Empty_Dll{}
               : (!is_null(Del.next) ? 
                    After == Nonempty_Dll {left: Left_Sublist(Before), 
                                           curr: Node(After), 
                                           right: Tl(Right_Sublist(Before))}
                   : After == Nonempty_Dll {left: Tl(Left_Sublist(Before)), 
                                            curr: Node(After), 
                                            right: Right_Sublist(Before)});
@*/
{
    struct dllist *temp = 0;
    if (n->prev != 0) {
        /*@ split_case(is_null(n->prev->prev)); @*/
        n->prev->next = n->next;
        temp = n->prev;
    }
    if (n->next != 0) {
        /*@ split_case(is_null(n->next->next)); @*/
        n->next->prev = n->prev;
        temp = n->next;
    }
    struct dllist_and_int *pair = cn_malloc(sizeof(struct dllist_and_int));
    pair->dllist = temp;
    pair->data = n->data;
    cn_free_sized(n, sizeof(struct dllist));
    return pair;
}
