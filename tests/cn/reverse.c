struct node { int head; struct node* tail; };

/*@
datatype seq {
  Nil {},
  Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Nil{};
  } else {
    take H = RW<struct node>(p);
    take tl = IntList(H.tail);
    return (Cons { head: H.head, tail: tl });
  }
}

function (i32) hd (datatype seq xs) {
  match xs {
    Nil {} => {
      0i32
    }
    Cons {head : h, tail : _} => {
      h
    }
  }
}

function (datatype seq) tl (datatype seq xs) {
  match xs {
    Nil {} => {
      Nil {}
    }
    Cons {head : _, tail : tail} => {
      tail
    }
  }
}

function [rec] (datatype seq) append(datatype seq xs, datatype seq ys) {
  match xs {
    Nil {} => {
      ys
    }
    Cons {head : h, tail : zs}  => {
      Cons {head: h, tail: append(zs, ys)}
    }
  }
}

function [rec] (datatype seq) snoc(datatype seq xs, i32 y) {
  match xs {
    Nil {} => {
      Cons {head: y, tail: Nil {}}
    }
    Cons {head : h, tail : zs}  => {
      Cons {head: h, tail: (snoc(zs, y))}
    }
  }
}

function [rec] (datatype seq) rev(datatype seq xs) {
  match xs {
    Nil {} => {
      Nil {}
    }
    Cons {head : h, tail : zs}  => {
      snoc (rev(zs), h)
    }
  }
}


lemma append_nil (datatype seq l1)
  requires true;
  ensures append(l1, Nil {}) == l1;

lemma append_cons (datatype seq l1, i32 x, datatype seq l2)
  requires true;
  ensures append(l1, Cons {head: x, tail: l2})
          == append(snoc(l1, x), l2);
@*/


struct node *reverse(struct node *xs)
/*@ requires take L = IntList(xs);
    ensures  take L_ = IntList(return);
             L_ == rev(L);
@*/
{

  struct node *last = 0;
  struct node *cur = xs;
  /*@ apply append_nil(rev(L)); @*/
  while(1)
  /*@ inv take L1 = IntList(last);
          take L2 = IntList(cur);
          append(rev(L2), L1) == rev(L);
  @*/
  {
    if (cur == 0) {
      /*@ unfold rev(Nil {}); @*/
      /*@ unfold append(Nil {}, L1); @*/

      return last;
    }
    struct node *tmp = cur->tail;
    cur->tail = last;
    last = cur;
    cur = tmp;
    /*@ unfold rev(L2); @*/
    /*@ apply append_cons (rev (tl(L2)), hd(L2), L1); @*/
  }
}

int main(void)
/*@ trusted; @*/
{
  struct node n3 = {.head = 3, .tail = 0};
  struct node n2 = {.head = 5, .tail = &n3};
  struct node n1 = {.head = 1, .tail = &n2};

  struct node *rev_n1 = reverse(&n1);
  return 0;
}
